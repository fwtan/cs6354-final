// Description: ppm predictor for cbp3.
// Modified from the implementation: https://www.jilp.org/cbp/Pierre.tar.bz2.uue

#include <stdio.h>
#include <cassert>
#include <string.h>
#include <inttypes.h>
#include <cstddef>
#include <cstdlib>
#include <bitset>

using namespace std;
#include "cbp3_def.h"
#include "cbp3_framework.h"

#define ASSERT(cond) if (!(cond)) {printf("assert line %d\n",__LINE__); exit(EXIT_FAILURE);}

// number of global tables (those indexed with global history)
#define NHIST 4 
// base 2 logarithm of number of entries in bimodal table
#define LOGB 12 // 4096
// base 2 logarithm of number of entry in each global table
#define LOGG 10 // 1024
// number of bits for each up-down saturating counters
#define CBITS 3
// number of bits for each "meta" counter
#define MBITS 1
// number of tag bits in each global table entry
#define TBITS 8
// maximum global history length used
#define MAXHIST 81

typedef uint32_t address_t;
typedef bitset<MAXHIST> history_t;

// this is the cyclic shift register for folding 
// a long global history into a smaller number of bits

class folded_history 
{
public:
	unsigned comp;
	int CLENGTH;
	int OLENGTH;
	int OUTPOINT;
	
	folded_history () {}

	void init(int original_length, int compressed_length) 
	{
		comp = 0;	// folded history
		OLENGTH = original_length;
		CLENGTH = compressed_length;
		OUTPOINT = OLENGTH % CLENGTH;
		ASSERT(OLENGTH < MAXHIST);
	}
	
	void update(history_t h)
    {
		ASSERT((comp>>CLENGTH)==0);
		comp = (comp << 1) | h[0]; 		// update the last history
		comp ^= h[OLENGTH] << OUTPOINT;	
		comp ^= (comp >> CLENGTH);
		comp &= (1<<CLENGTH)-1;
    }
};

class PREDICTOR
{
public:
	// bimodal table entry
	class bentry 
	{
	public:
		int8_t ctr;  // saturating counter
		int8_t meta; // meta-predictor
		bentry() 
		{
			ctr = (1 << (CBITS-1));
			for (int i=0; i<NHIST; i++) 
			{
				meta = (1 << (MBITS-1));
			}
      	}
    };

    // global table entry
	class gentry 
	{
	public:
		int8_t ctr;
		uint16_t tag;
		bool ubit;
		gentry() 
		{
			ctr = (1 << (CBITS-1));
			tag = 0;
			ubit = false;
		}
    };

    // predictor storage data
    history_t ghist; // global history register
    folded_history ch_i[NHIST];    // CSRs for history table
    folded_history ch_t[2][NHIST]; // CSRs for tag
    bentry* btable; // bimodal table
    gentry* gtable[NHIST]; // history table


	PREDICTOR()
	{
		ghist = 0;
		// Order from longest to shortest
		ch_i[0].init(80, LOGG); // 80-bit global history
		ch_i[1].init(40, LOGG); // 40-bit global history
		ch_i[2].init(20, LOGG); // 20-bit global history
		ch_i[3].init(10, LOGG); // 10-bit global history
		for (int i=0; i<NHIST; i++) 
		{
			// tag
			ch_t[0][i].init(ch_i[i].OLENGTH, TBITS);
			ch_t[1][i].init(ch_i[i].OLENGTH, TBITS-1);
		}
		btable = new bentry [1<<LOGB];
		for (int i=0; i<NHIST; i++) 
		{
			gtable[i] = new gentry [1<<LOGG];
		}
	}


    // index function for the bimodal table
    int bindex(address_t pc) 
    {
		return(pc & ((1<<LOGB)-1));
    }

    // index function for the global tables
	int gindex(address_t pc, int bank)
	{
		// XOR hashing
		int index = pc ^ (pc>>LOGG) ^ ch_i[bank].comp;
		return(index & ((1<<LOGG)-1));
	}

    // index function for the tags
	uint16_t gtag(address_t pc, int bank)
	{
		// Weird label to reduce alias
		int tag = pc ^ ch_t[0][bank].comp ^ (ch_t[1][bank].comp << 1);
		return(tag & ((1<<TBITS)-1));
	}

    // most significant bit of up-down saturating counter
	bool ctrpred(int8_t ctr, int nbits)
	{
		return((ctr >> (nbits-1)) != 0);
    }

    // up-down saturating counter
	void ctrupdate(int8_t & ctr, bool taken, int nbits)
	{
		if (taken) 
		{
			if (ctr < ((1<<nbits)-1)) 
			{
				ctr++;
			}
		} 
		else 
		{
			if (ctr > 0) 
			{
				ctr--;
			}
		}
    }

    // prediction given by longest matching global history
    bool read_prediction(address_t pc, int & bank)
    {
		int index;
		bank = NHIST;
		for (int i=0; i < NHIST; i++) 
		{
			index = gindex(pc,i);
			if (gtable[i][index].tag == gtag(pc,i)) 
			{
				bank = i;
				break;
			}
		}
		if (bank < NHIST) 
		{
			return ctrpred(gtable[bank][index].ctr,CBITS);
		} 
		else 
		{
			return ctrpred(btable[bindex(pc)].ctr,CBITS);
		}
	}

    // PREDICTION
	bool get_prediction(const cbp3_uop_dynamic_t* uop)
	{
		int bank;
		bool prediction = true;
		if (uop->type & IS_BR_CONDITIONAL) 
		{
			address_t pc = uop->pc;
			prediction = read_prediction(pc, bank);
		}
		return prediction;
    }


    // PREDICTOR UPDATE
	void update_predictor(const cbp3_uop_dynamic_t* uop, bool taken)
	{
		bool pred_taken, btaken;
		int bank, bi, gi[NHIST];
		if (uop->type & IS_BR_CONDITIONAL) 
		{
			address_t pc = uop->pc; bi = bindex(pc);
			// in a real processor, it is not necessary to re-read the predictor at update
			// it suffices to propagate the prediction along with the branch instruction
			pred_taken = read_prediction(pc, bank);
			btaken = ctrpred(btable[bi].ctr,CBITS);
			// steal new entries only if prediction was wrong 
			// and the matching bank is not the longest one
			if ((pred_taken != taken) && (bank > 0)) 
			{
				bool choose_random = true;
				// If there is any entry of which the u bit is reset
				for (int i=0; i<bank; i++) 
				{
					gi[i] = gindex(pc,i);
					choose_random = choose_random && (gtable[i][gi[i]].ubit);
				}
				// if m bit is reset, use btaken
				bool init_taken = (ctrpred(btable[bi].meta,MBITS))? taken : btaken;
				if (choose_random) 
				{
					int i = (unsigned) random() % bank;
					// steal tag
					gtable[i][gi[i]].tag = gtag(pc,i);
					// initialize counter
					gtable[i][gi[i]].ctr = (1<<(CBITS-1)) - ((init_taken)? 0:1);
					gtable[i][gi[i]].ubit = false;
				} 
				else 
				{
					// steal tags
					for (int i=0; i<bank; i++) 
					{
						if (! gtable[i][gi[i]].ubit) 
						{
							gtable[i][gi[i]].tag = gtag(pc,i);
							gtable[i][gi[i]].ctr = (1<<(CBITS-1)) - ((init_taken)? 0:1);
							gtable[i][gi[i]].ubit = false;
						}
					}
	    		}
	  		}

			// update the counter
			if (bank < NHIST) 
			{
				gi[bank] = gindex(pc,bank);
				ASSERT(pred_taken == ctrpred(gtable[bank][gi[bank]].ctr,CBITS));
				ctrupdate(gtable[bank][gi[bank]].ctr,taken,CBITS);
			} 
			else 
			{
				ctrupdate(btable[bi].ctr,taken,CBITS);
			}

			// update the meta counter and the useful bit
			if (pred_taken != btaken) 
			{
				ASSERT(bank < NHIST);
				ctrupdate(btable[bi].meta,(pred_taken==taken),MBITS);
				gtable[bank][gi[bank]].ubit = (pred_taken == taken);
			}

			// update global history and circular shift registers
			ghist = (ghist << 1) | (history_t) taken;
			for (int i=0; i<NHIST; i++)
			{
				ch_i[i].update(ghist);
				ch_t[0][i].update(ghist);
				ch_t[1][i].update(ghist);
			}
		}
    }
};


PREDICTOR* g_predictor = 0;

void PredictorInit() 
{
    g_predictor = new PREDICTOR();
}

void PredictorReset() 
{
    if(g_predictor != 0)
    {
        delete g_predictor;
        g_predictor = new PREDICTOR();
    }
}

void PredictorRunACycle() 
{
    // get info about what uops are processed at each pipeline stage
    const cbp3_cycle_activity_t *cycle_info = get_cycle_info();
    // make prediction at fetch stage
    for (int i = 0; i < cycle_info->num_fetch; i++) 
    {
        uint32_t fe_ptr = cycle_info->fetch_q[i];
        const cbp3_uop_dynamic_t *uop = &fetch_entry(fe_ptr)->uop;
        if (uop->type & IS_BR_CONDITIONAL)
        {
            bool gpred = g_predictor->get_prediction(uop);
            // report prediction:
            // you need to provide direction predictions for conditional branches,
            // targets of conditional branches are available at fetch stage.
            // for indirect branches, you need to provide target predictions.
            // you can report multiple predictions for the same branch
            // the framework will use the last reported prediction to calculate 
            // misprediction penalty
            assert(report_pred(fe_ptr, false, gpred));

            g_predictor->update_predictor(uop, uop->br_taken);
        }
    }
}

void PredictorRunEnd() 
{
    
}

void PredictorExit() 
{
    delete g_predictor;
    g_predictor = 0;
}
