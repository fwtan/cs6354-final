// Description: o-gehl predictor for cbp3.
// Modified from the implmentation: https://www.jilp.org/cbp/Andre.tar.bz2.uue

#include <stdio.h>
#include <cassert>
#include <string.h>
#include <inttypes.h>
#include <cstddef>
#include <cstdlib>
#include <bitset>
#include <math.h>
#include <vector>

using namespace std;
#include "cbp3_def.h"
#include "cbp3_framework.h"

// comment the line #define OGEHL to obtain unoptimized GEHL
#define OGEHL

// 8 gtables
#define NTABLE 8

// T1: (1 << (LOGPRED-1)) = 1K entries
// else: (1 << LOGPRED) = 2K entries
#ifndef LOGPRED
#define LOGPRED 11
#endif

// using both branch history and path history
// unconditional control-flow instructions are inserted in the global history. 
#define FULLPATH

// T2-T7: 4-bit counters
// T0,T1: 5-bit counters
#ifndef MAXCOUNTER
#define MAXCOUNTER 7
#define MINCOUNTER -MAXCOUNTER-1
#endif

// Parameters for OGEHL
#ifdef OGEHL
#define MAXTHRESUPDATE 31
// Special configuration for the CBP challenge: 
// 5-bit counters used on tables T0 and T1
// T1 features only 1K entries
#define CBP
// GLENGTH: L(M)
#define GLENGTH 200
// L1
#define L1 3
// PLENGTH: the maximum path history length
#define PLENGTH 16
// AC: 9-bit counter
#define THRES 256
// TC: 7-bit counter
#define THRESFIT 64
// Dynamic history length fitting
#define DYNHISTFIT
// NTABLE + 3 distinct history lengths
#define EXTRAHIST 3
// Dynamic update threshold fitting
#define DYNTHRESFIT

//Parameters for GEHL
#else
// GLENGTH: L(M)
#define GLENGTH 125
// L1
#define L1 3
// No path history
#define PLENGTH 0
// Only NTABLE distinct history lengths
#define EXTRAHIST 0
#endif

int LOGSIZE;
long long ghist[(GLENGTH >> 6) + 1];
long long phist;

// INDEX is used to compute the indexes of the tables:
// 1) NENTRY * LOGSIZE bits are regularly picked from the vector of bits constituted with the branch history, the PC and the path history.
// 2) these NENTRY * LOGSIZE bits are reduced to LOGSIZE bits through NENTRY-1 exclusive OR

#define NENTRY 3
// NENTRY is the maximum number of entries on the exclusive-OR gates in the computation of the indexing functions
static int T[NENTRY * LOGPRED + 1];
int
#define ADDWIDTH 8
// the number of bits of the PC address considered for bit picking
INDEX ( const long long Add, // PC address
		const long long * histo, const long long phisto,
		const int m, const int funct)
{
	long long inter, Hh, Res;
	int x, i, shift, PT, MinAdd, FUNCT, plength;
	
	// First build a NENTRY * LOGSIZE vector of bits from histo, phisto and Add (PC)
	if (m < PLENGTH)	plength = m;
	else				plength = PLENGTH;
	MinAdd = NENTRY * LOGSIZE - m - plength;
	if (MinAdd > 20)	MinAdd = 20;
	
	if (MinAdd >= 8)
	{
		// Use all the bits from the phisto, hiso and at least 8 bits from Add
		inter =	((histo[0] & ((1 << m) - 1)) << (MinAdd + plength)) +
		((Add & ((1 << MinAdd) - 1)) << plength) +
		((phisto & ((1 << plength) - 1)));
	}
	else
    {
		// Some bits must be rejected from a total of m+plength+ADDWIDTH
		for (x = 0; x < NENTRY * LOGSIZE; x++)
		{
			T[x] = ((x * (ADDWIDTH + m + plength - 1)) / (NENTRY * LOGSIZE - 1));
		}
		T[NENTRY * LOGSIZE] = ADDWIDTH + m + plength;
		inter = 0;
		// Branch history
		Hh = histo[0];
		Hh >>= T[0];
		inter = (Hh & 1);
		PT = 1;
		for (i = 1; T[i] < m; i++)
		{
			if ((T[i] & 0xffc0) == (T[i - 1] & 0xffc0))
			{
				shift = T[i] - T[i - 1];
			}
		  	else
			{
				Hh = histo[PT];
				PT++;
				shift = T[i] & 63;
			}
			inter = (inter << 1);
			Hh = Hh >> shift;
			inter ^= (Hh & 1);
		}
		// PC
		Hh = Add;
		for (; T[i] < m + ADDWIDTH; i++)
		{
			shift = T[i] - m;
			inter = (inter << 1);
			inter ^= ((Hh >> shift) & 1);
		}
		// Path history
		Hh = phisto;
		for (; T[i] < m + plength + ADDWIDTH; i++)
		{
			shift = T[i] - (m + ADDWIDTH);
			inter = (inter << 1);
			inter ^= ((Hh >> shift) & 1);
		}
	}
	
	// inter: NENTRY*LOGSIZE -> LOGSIZE via NENTRY-entry XOR gates
	FUNCT = funct;
	Res = inter & ((1 << LOGSIZE) - 1);
	for (i = 1; i < NENTRY; i++)
    {
		inter = inter >> LOGSIZE;
		Res ^= ((inter & ((1 << LOGSIZE) - 1)) >> FUNCT) ^ 
				((inter & ((1 << FUNCT) - 1)) << ((LOGSIZE - FUNCT)));
		FUNCT = (FUNCT + 1) % LOGSIZE;
	}
	return ((int) Res);
};

class PREDICTOR
{
public:
	int UsedHistLength[NTABLE], HistLength[NTABLE + EXTRAHIST];
	int AC, TC, thresupdate, maxcounter, mincounter, Minitag; 
	
	// T1: 1K entries
	// Else: 2K entries
	char pred[NTABLE][1 << LOGPRED];
	// Tables 0 and 1 are 5-bit counters 
	// Other tables are 4-bit counters
	// Total storage for counters on the 8 tables 10+5+8+8+8+8+8+8 = 63Kbits
	#ifdef DYNHISTFIT
	char MINITAG[(1 << (LOGPRED - 1))];
	// 1K 1-bit tag associated with Table 7
	// Total storage amount for the submitted predictor 63K + 1K = 64Kbits
	#endif
	void init()
	{
		int i, j;
		double initset, glength, tt, Pow;


		for (j = 0; j < (1 << LOGPRED); j++)
			for (i = 0; i < NTABLE; i++)
				pred[i][j] = 0;
		#ifdef OGEHL
		for (j = 0; j < (1 << (LOGPRED-1)); j++)	
			MINITAG[j] = 0;
		#endif
		TC=0; AC=0;
		thresupdate=NTABLE;
		
		// Initialize histories ghist and phist
		for (i = 0; i < (GLENGTH >> 6) + 1; i++)
			ghist[i] = 0;
		phist = 0;

		// History lengths
		glength = (double) (GLENGTH);
		initset = (double) L1;
		tt = glength / initset;
		Pow = pow (tt, ((double) 1) / (double) (NTABLE - 2 + EXTRAHIST));
		HistLength[0] = 0;
		HistLength[1] = L1;
		for (i = 2; i < NTABLE + EXTRAHIST; i++)
			HistLength[i] = (int) ((initset * pow (Pow, (double) (i - 1))) + 0.5);

		// Initialize the history lengths used for each of the predictor tables
		for (i = 0; i < NTABLE; i++)
			UsedHistLength[i] = HistLength[i];
	}

	PREDICTOR() { init(); }
	
	bool predict(const cbp3_uop_dynamic_t* uop) const
	{
		bool prediction = false;
		long long Add;
		int Sum, i;
		int indexg[NTABLE];
		if (uop->type & IS_BR_CONDITIONAL)
		{
			Sum = NTABLE / 2;
			LOGSIZE = LOGPRED;
			Add = (long long) uop->pc;
			for (i = 0; i < (NTABLE); i++)
			{
			#ifdef CBP
				// T1: 1K entries
				if (i == 1)	LOGSIZE--;
			#endif
				// last factor (i & 3) + 1 is put in order to avoid similar combination 
				// of bits in the index for adjacent tables
				indexg[i] =	INDEX (Add, ghist, phist, UsedHistLength[i], (i & 3) + 1);
			#ifdef CBP
				if (i == 1)	LOGSIZE++;
			#endif
				Sum += pred[i][indexg[i]];
			}
			prediction = (Sum >= 0);
		}
		return prediction;
	}
	
	void update_predictor(const cbp3_uop_dynamic_t* uop, bool taken)
	{
		bool prediction = false;
		long long Add;
		int Sum;
		int indexg[NTABLE], i;
		
		// Recompute the prediction
		Add = (long long) uop->pc;
		if (uop->type & IS_BR_CONDITIONAL)
		{
			Sum = NTABLE / 2;
			LOGSIZE = LOGPRED;
			for (i = 0; i < (NTABLE); i++)
			{
			#ifdef CBP
				if (i == 1)	LOGSIZE--;
			#endif
				indexg[i] = INDEX (Add, ghist, phist, UsedHistLength[i], (i & 3) + 1);
			#ifdef CBP
	    		if (i == 1)	LOGSIZE++;
			#endif
				Sum += pred[i][indexg[i]];
			}
			prediction = (Sum >= 0);

		#ifdef DYNTHRESFIT
			// Dynamic threshold fitting
			if (prediction != taken)
			{
				TC += 1;
				if (TC > THRESFIT - 1)
				{
					TC = THRESFIT - 1;
					if (thresupdate < MAXTHRESUPDATE)
					{
						TC = 0;
						thresupdate++;
					}
				}
			}
			else if ((Sum < thresupdate) && (Sum >= -thresupdate))
			{
				TC--;
				if (TC < -THRESFIT)
				{
					TC = -THRESFIT;
					if (thresupdate > 0)
					{
						thresupdate--; TC=0;
					}
				}
			}        
			// if the number of updates on correct predictions using the high threshold is higher than twice the number of updates on mispredictions, then use the low threshold
		#else
			thresupdate = NTABLE;
		#endif
			
			if((prediction != taken) || ((Sum < thresupdate) && (Sum >= -thresupdate)))
			{
				// update the counters
				for (i = 0; i < NTABLE; i++)
				{
					if (taken)
					{
					#ifdef CBP
						//T0 and T1 implements 5-bit counters
						if (i <= 1)
							maxcounter = 2 * MAXCOUNTER + 1;
						else
					#endif
							maxcounter = MAXCOUNTER;
						if (pred[i][indexg[i]] < maxcounter)
							pred[i][indexg[i]]++;
					}
					else
					{
					#ifdef CBP
					//T0 and T1 implements 5-bit counters
						if (i <= 1)
							mincounter = 2 * (MINCOUNTER);
						else
					#endif
							mincounter = MINCOUNTER;
						if (pred[i][indexg[i]] > mincounter)
							pred[i][indexg[i]]--;
					}
				}
				
			#ifdef DYNHISTFIT
				// dynamic history length fitting
				// 1 tag bit is associated with each even entry in table T7
				if ((indexg[NTABLE - 1] & 1) == 0)
				{
					if ((prediction != taken))
					{
						Minitag = MINITAG[indexg[NTABLE - 1] >> 1];
						if (Minitag != ((int) (Add & 1)))
						{
							AC -= 4;
							if (AC < -THRES)
							{
								//when AC becomes saturated negative, high level of aliasing is considered, then "short" history lengthes are used
								AC = -THRES;
								UsedHistLength[6] = HistLength[6];
								UsedHistLength[4] = HistLength[4];
								UsedHistLength[2] = HistLength[2];
							}
						}
						else
						{
							AC++;
							if (AC > THRES - 1)
			  				{
								//when AC becomes  saturated positive, low level of aliasing is considered, then "long" history lengthes are used
								AC = THRES - 1;
			    				UsedHistLength[6] = HistLength[NTABLE + 2];
								UsedHistLength[4] = HistLength[NTABLE + 1];
								UsedHistLength[2] = HistLength[NTABLE];
							}
						}
					}
					MINITAG[indexg[NTABLE - 1] >> 1] = (char) (Add & 1);
				}
			#endif
			}
		}

		// update the branch history and the path history
		#ifdef FULLPATH
			phist = (phist << 1) + (Add & 1);
		#endif
		#ifndef FULLPATH
			if (uop->type & IS_BR_CONDITIONAL)
		#endif
			{
				for (i = (GLENGTH >> 6); i > 0; i--)
					ghist[i] = (ghist[i] << 1) + (ghist[i - 1] < 0);
				ghist[0] = ghist[0] << 1;

				if (((uop->type & IS_BR_CONDITIONAL) && (taken)) | (!(uop->type & IS_BR_CONDITIONAL)))
					ghist[0]++;
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
