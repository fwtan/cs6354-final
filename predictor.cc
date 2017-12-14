// Description: tage predictor for cbp3.
// Modified from the implementation: ftp://ftp.irisa.fr/local/caps/TAGE.tar.gz

#include <stdio.h>
#include <cassert>
#include <string.h>
#include <inttypes.h>
#include <cstddef>
#include <cstdlib>
#include <bitset>
#include <math.h>

using namespace std;
#include "cbp3_def.h"
#include "cbp3_framework.h"

#define ASSERT(cond) if (!(cond)) {printf("assert line %d\n",__LINE__); exit(EXIT_FAILURE);}

#define FIVECOMPONENT
#ifdef FIVECOMPONENT
// a 64 Kbits predictor with 4 tagged tables
#define LOGB 13
#define NHIST 4
#define TBITS 9
#define LOGG (LOGB-3)
#endif

//#define FOURTEENCOMPONENT
#ifdef FOURTEENCOMPONENT
// a 64,5 Kbits predictor with 13 tagged tables
#define LOGB 13
#define NHIST 13
#define TBITS 15
#define LOGG (LOGB-5)
#endif


// the predictor features NHIST tagged components + a base bimodal component
// a tagged entry in tagged table Ti (0<= i< NHIST)  features a TBITS-(i+ (NHIST & 1))/2 tag, a CBITS prediction counter and a 2-bit useful counter. 
// Tagged components feature 2**LOGG entries
// on the bimodal table: hysteresis is shared among 4 counters: total size 5*2**(LOGB-2)
// Remark a contrario from JILP paper, T0 is the table with the longest history, Sorry !

// default predictor
// by default a 63.5  Kbits predictor, featuring 7 tagged components and a base bimodal component: NHIST = 7, LOGB =13, LOGG=9, CBITS=3
// 10 Kbits  for the bimodal table.
// 8.5 Kbits for T0
// 8 Kbits   for T1 and T2
// 7.5 Kbits for T3 and T4
// 7 Kbits   for T5 and T6

// number of bits for each up-down saturating counters
#ifndef CBITS
#define CBITS 3
#endif
// number of global prediction tables
#ifndef NHIST
#define NHIST 7
#endif
// base 2 logarithm of number of entries in bimodal table
#ifndef LOGB
#define LOGB 13
#endif
// base 2 logarithm of number of entries on each tagged component
#ifndef LOGG
#define LOGG (LOGB-4)
#endif
// total width of an entry in the tagged table with the longest history length
#ifndef TBITS
#define TBITS 12
#endif
//AS: we use Geometric history length
//AS: maximum global history length used and minimum history length
#define MAXHIST 131
#define MINHIST 5

typedef uint32_t address_t;
typedef bitset<MAXHIST> history_t;

// Cyclic Shift Register (CSR) for folding 
// a long global history into a smaller number of bits
class folded_history
{
public:
    unsigned comp;
    int CLENGTH;
    int OLENGTH;
    int OUTPOINT;
    
    folded_history() {}
    
    void init(int original_length, int compressed_length)
    {
        comp = 0;
        OLENGTH = original_length;
        CLENGTH = compressed_length;
        OUTPOINT = OLENGTH % CLENGTH;
        ASSERT (OLENGTH < MAXHIST);
    }
    
    void update(history_t h)
    {
        ASSERT ((comp >> CLENGTH) == 0);
        comp = (comp << 1) | h[0];
        comp ^= h[OLENGTH] << OUTPOINT;
        comp ^= (comp >> CLENGTH);
        comp &= (1 << CLENGTH) - 1;
    }
};


class PREDICTOR
{
public:
    // bimodal table entry
    class bentry
    {
    public:
        int8_t hyst;
        int8_t pred;
        
        bentry ()
        {
            pred = 0;
            hyst = 1;
        }
    };
    
    // global table entry
    class gentry
    {
    public:
        int8_t ctr;
        uint16_t tag;
        int8_t ubit;
        
        gentry ()
        {
            ctr = 0;
            tag = 0;
            ubit = 0;
        }
    };
    
    // predictor storage data
    int PWIN;
    // 4 bits to determine whether newly allocated entries should be considered as
    // valid or not for delivering  the prediction
    int TICK;

    int phist; // path history
    history_t ghist; // branch history
    folded_history ch_i[NHIST]; // CSRs for global table hashing
    folded_history ch_t[2][NHIST]; // CSRs for tag computation
    bentry *btable; // bimodal table
    gentry *gtable[NHIST]; // history tables

    int m[NHIST]; // used for storing the history lengths

    PREDICTOR()
    {
        int STORAGESIZE = 0;
        ghist = 0;
        // computes the geometric history lengths   
        m[0] = MAXHIST - 1;
        m[NHIST - 1] = MINHIST;
        for (int i = 1; i < NHIST - 1; i++)
        {
            m[NHIST - 1 - i] = 
                (int)(((double) MINHIST*pow((double)(MAXHIST-1)/(double)MINHIST, (double)(i)/(double)((NHIST-1))))+0.5);
        }
        
        for (int i = NHIST - 1; i >= 0; i--)
        {
            ch_i[i].init (m[i], (LOGG));
            STORAGESIZE += (1 << LOGG) * (5 + TBITS - ((i + (NHIST & 1)) / 2));
        }
        
        STORAGESIZE += (1 << LOGB) + (1 << (LOGB - 2));
        
        for (int i = 0; i < NHIST; i++)
        {
            ch_t[0][i].init (ch_i[i].OLENGTH, TBITS - ((i + (NHIST & 1)) / 2));
            ch_t[1][i].init (ch_i[i].OLENGTH, TBITS - ((i + (NHIST & 1)) / 2) - 1);
        }
        
        btable = new bentry[1 << LOGB];
        for (int i = 0; i < NHIST; i++)
        {
            gtable[i] = new gentry[1 << (LOGG)];
        }
    }

    ~PREDICTOR()
    {
        if (btable)
		{
			delete btable;
			btable = 0;
		}

		for (int i=0; i<NHIST; i++) 
		{
			if (gtable[i])
			{
				delete gtable[i];
				gtable[i] = 0;
			}
		}
    }
    
    
    // index function for the bimodal table
    int bindex(address_t pc)
    {
        return (pc & ((1 << (LOGB)) - 1));
    }

    // indexes to the different tables are computed only once and store in GI and BI
    int GI[NHIST];
    int BI;

    // index function for the global tables: 
    // includes path history as in the OGEHL predictor
    // F serves to mix path history
    int F(int A, int size, int bank)
    {
        int A1, A2;
        A = A & ((1 << size) - 1);
        A1 = (A & ((1 << LOGG) - 1));
        A2 = (A >> LOGG);
        A2 = ((A2 << bank) & ((1 << LOGG) - 1)) + (A2 >> (LOGG - bank));
        A = A1 ^ A2;
        A = ((A << bank) & ((1 << LOGG) - 1)) + (A >> (LOGG - bank));
        return (A);
    }
    
    // index function for the history tables
    int gindex(address_t pc, int bank)
    {
        int index;
        if (m[bank] >= 16)
        {
            index = pc ^ (pc >> ((LOGG - (NHIST - bank - 1)))) ^ ch_i[bank].comp ^ F (phist, 16, bank);
        }
        else
        {
            index = pc ^ (pc >> (LOGG - NHIST + bank + 1)) ^ ch_i[bank].comp ^ F (phist, m[bank], bank);
        }
        return (index & ((1 << (LOGG)) - 1));
    }
    
    // tag computation
    uint16_t gtag(address_t pc, int bank)
    {
        int tag = pc ^ ch_t[0][bank].comp ^ (ch_t[1][bank].comp << 1);
        return (tag & ((1 << (TBITS - ((bank + (NHIST & 1)) / 2))) - 1));
        //does not use the same length for all the components
    }
    
    // up-down saturating counter
    void ctrupdate(int8_t & ctr, bool taken, int nbits)
    {
        if(taken)
        {
            if (ctr < ((1 << (nbits - 1)) - 1))
            {
                ctr++;
            }
        }
        else
        {
            if (ctr > -(1 << (nbits - 1)))
            {
                ctr--;
            }
        }
    }
    
    int altbank;
    // prediction given by longest matching global history
    // altpred contains the alternate prediction
    bool read_prediction(address_t pc, int &bank, bool & altpred)
    {
        bank = NHIST;
        altbank = NHIST;
        {
            for (int i = 0; i < NHIST; i++)
            {
                if (gtable[i][GI[i]].tag == gtag (pc, i))
                {
	                bank = i;
                    break;
                }
            }
            
            for (int i = bank + 1; i < NHIST; i++)
            {
                if (gtable[i][GI[i]].tag == gtag (pc, i))
                {
                    altbank = i;
                    break;
                }
            }
            
            if (bank < NHIST)
            {
                if (altbank < NHIST)
                {
                    altpred = (gtable[altbank][GI[altbank]].ctr >= 0);
                }
                else
                {
                    altpred = getbim(pc);
                }
                // if the entry is recognized as a newly allocated entry and 
                // counter PWIN is negative use the alternate prediction
                // see section 3.2.4
                if ((PWIN < 0) || (abs (2 * gtable[bank][GI[bank]].ctr + 1) != 1) || (gtable[bank][GI[bank]].ubit != 0))
                {
                    return (gtable[bank][GI[bank]].ctr >= 0);
                }
                else
                {
                    return (altpred);
                }
            }
            else
            {
                altpred = getbim (pc);
                return altpred;
            }
        }
    }

    // PREDICTION
    bool pred_taken, alttaken;
    int bank;
    bool predict(const cbp3_uop_dynamic_t* uop)
    {
        if (uop->type & IS_BR_CONDITIONAL) 
        {
            address_t pc = uop->pc;
            // computes the table addresses
            for (int i = 0; i < NHIST; i++)
            {
                GI[i] = gindex(pc, i);
            }

            BI = bindex(pc);
            pred_taken = read_prediction(pc, bank, alttaken);
            // bank contains the number of the matching table, NHIST if no match
            // pred_taken is the prediction
            // alttaken is the alternate prediction
        }
        return pred_taken;
    }
    
    bool getbim(address_t pc)
    {
        return (btable[BI].pred > 0);
    }
    
    // update  the bimodal predictor
    void baseupdate (address_t pc, bool Taken)
    {
        // just a normal 2-bit counter apart that hysteresis is shared
        if (Taken == getbim(pc))
        {
            if(Taken)
            {
                if(btable[BI].pred)
                {
                    btable[BI >> 2].hyst = 1;
                }
            }
            else
            {
                if (!btable[BI].pred)
                {
                    btable[BI >> 2].hyst = 0;
                }
            }
        }
        else
        {
            int inter = (btable[BI].pred << 1) + btable[BI >> 2].hyst;
            if(Taken)
            {
                if(inter < 3)
                {
                    inter += 1;
                }
            }
            else
            {
                if (inter > 0)
                {
                    inter--;
                }
            }

            btable[BI].pred = inter >> 1;
            btable[BI >> 2].hyst = (inter & 1);
        }
    }
    
    // simple pseudo random number generator based on linear feedback shift register
    int Seed;
    int MYRANDOM()
    {
        Seed = ((1 << 2 * NHIST) + 1) * Seed + 0xf3f531;
        Seed = (Seed & ((1 << (2 * (NHIST))) - 1));
        return Seed;
    }
    
    // PREDICTOR UPDATE
    void update_predictor(const cbp3_uop_dynamic_t* uop, bool taken)
    {
        int NRAND = MYRANDOM ();
        if (uop->type & IS_BR_CONDITIONAL)
        {
            address_t pc = uop->pc;

            // in a real processor, it is not necessary to re-read the predictor at update
            // it suffices to propagate the prediction along with the branch instruction
            bool ALLOC = ((pred_taken != taken) & (bank > 0));
            if(bank < NHIST)
            {
                bool loctaken = (gtable[bank][GI[bank]].ctr >= 0);
                bool PseudoNewAlloc = (abs (2 * gtable[bank][GI[bank]].ctr + 1) == 1) && (gtable[bank][GI[bank]].ubit == 0);
                
                // is entry "pseudo-new allocated" 
                if (PseudoNewAlloc)
                {
                    if (loctaken == taken)
                    {
                        ALLOC = false;
                    }
                    // if the provider component  was delivering the correct prediction; no need to allocate a new entry
                    // even if the overall prediction was false
                    // see section 3.2.4
                    if (loctaken != alttaken)
                    {
                        if (alttaken == taken)
                        {
                            if(PWIN < 7)
                            {
                                PWIN++;
                            }
                        }
                        else
                        {
                            if(PWIN > -8)
                            {
                                PWIN--;
                            }
                        }
                    }
                }
            }

            // try to allocate a new entries only if prediction was wrong
            if(ALLOC)
            {
                // is there some "unuseful" entry to allocate
                int8_t min = 3;
                for(int i = 0; i < bank; i++)
                {
                    if (gtable[i][GI[i]].ubit < min)
                    {
                        min = gtable[i][GI[i]].ubit;
                    }
                }
                
                if(min > 0)
                {
                    // NO UNUSEFUL ENTRY TO ALLOCATE: age all possible targets, but do not allocate
                    for(int i = bank - 1; i >= 0; i--)
                    {
                        gtable[i][GI[i]].ubit--;
                    }
                }
                else
                {
                    // YES: allocate one entry, but apply some randomness
                    // bank I is twice more probable than bank I-1     

                    int Y = NRAND & ((1 << (bank - 1)) - 1);
                    int X = bank - 1;
                    while((Y & 1) != 0)
                    {
                        X--;
                        Y >>= 1;
                    }
                    
                    for (int i = X; i >= 0; i--)
                    {
                        int T = i;
                        if ((gtable[T][GI[T]].ubit == min))
                        {
                            gtable[T][GI[T]].tag = gtag (pc, T);
                            gtable[T][GI[T]].ctr = (taken) ? 0 : -1;
                            gtable[T][GI[T]].ubit = 0;
                            break;
                        }
                    }
                }
            }
            
            //periodic reset of ubit: reset is not complete but bit by bit
            TICK++;
            if((TICK & ((1 << 18) - 1)) == 0)
            {
                int X = (TICK >> 18) & 1;
                if ((X & 1) == 0) X = 2;
                for (int i = 0; i < NHIST; i++)
                    for (int j = 0; j < (1 << LOGG); j++)
                        gtable[i][j].ubit = gtable[i][j].ubit & X;
            }

            // update the counter that provided the prediction, and only this counter
            if(bank < NHIST)
            {
                ctrupdate (gtable[bank][GI[bank]].ctr, taken, CBITS);
            }
            else
            {
                baseupdate (pc, taken);
            }
            
            // update the ubit counter
            if((pred_taken != alttaken))
            {
                ASSERT (bank < NHIST);
                if (pred_taken == taken)
                {
                    if (gtable[bank][GI[bank]].ubit < 3)
                        gtable[bank][GI[bank]].ubit++;
                }
                else
                {
                    if (gtable[bank][GI[bank]].ubit > 0)
                        gtable[bank][GI[bank]].ubit--;
                }
            }
        }

        // update global history and cyclic shift registers
        // use also history on unconditional branches as for OGEHL predictors.    
        ghist = (ghist << 1);
        if ((!(uop->type & IS_BR_CONDITIONAL)) | (taken))
            ghist |= (history_t) 1;

        phist = (phist << 1) + (uop->pc & 1);
        phist = (phist & ((1 << 16) - 1));
        for (int i = 0; i < NHIST; i++)
        {
            ch_i[i].update (ghist);
            ch_t[0][i].update (ghist);
            ch_t[1][i].update (ghist);
        }
    }
};



////////////////////////////////////////////////////////////////
// Implementation of the interfaces for the simulator
////////////////////////////////////////////////////////////////
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
	// also update the history at fetch stage 
    for (int i = 0; i < cycle_info->num_fetch; i++) 
    {
        uint32_t fe_ptr = cycle_info->fetch_q[i];
        const cbp3_uop_dynamic_t *uop = &fetch_entry(fe_ptr)->uop;
        if (uop->type & IS_BR_CONDITIONAL)
        {
            bool gpred = g_predictor->predict(uop);
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
