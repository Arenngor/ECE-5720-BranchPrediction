/******************************
 * Rowan Antonuccio
 * A02184507
 * 10/28/21
 * Branch Predictor
 * ECE 5720 USU
******************************/
#include <stdio.h>
#include <stdlib.h>
#include <cassert>
#include <string.h>
#include <inttypes.h>
#include <iostream>
#include <math.h>
#include "cbp3_def.h"
#include "cbp3_framework.h"

using namespace std;

bool gpred = true;
uint16_t TwoBit[4096] = {0};

uint16_t GShare[16777216] = {0};

uint16_t GSel[16777216] = {0};

uint16_t H(uint32_t addr, int TableSize) { //hash function for 2-bit and G-Select
  uint16_t hash;
  hash = floor(TableSize * (fmod(addr * .618033, 1)));
  return hash;
}

void Bin(int arr[], int n) //convert int to decimal for addresses
{
  int k = log2(n);
  while (n > 0) {
    arr[k--] = n % 2;
    n /= 2;
  }
}

int Dec(int arr[], int n) //convert decimal to int for addresses 
{
  int ans = 0;
  for (int i = 0; i < n; i++)
    ans += arr[i] << (n - i - 1);
  return ans;
}

uint32_t brh_fetch;
uint32_t brh_retire;
uint32_t runs;

void PredictorInit() {
  runs = 0;//reset runs
}

void PredictorReset() {//prints which predictor was used

  brh_fetch = 0;
  brh_retire = 0;
  if (runs == 0)
    cout << "Two Bit" << endl;
  else if (runs == 1)
    cout << "G-Select" << endl;
  else if (runs == 2)
    cout << "G-Share" << endl;
}

void PredictorRunACycle() {
  // get info about what uops are processed at each pipeline stage
  const cbp3_cycle_activity_t * cycle_info = get_cycle_info();

  // make prediction at fetch stage
  for (int i = 0; i < cycle_info -> num_fetch; i++) {
    uint32_t fe_ptr = cycle_info -> fetch_q[i];
    const cbp3_uop_dynamic_t * uop = & fetch_entry(fe_ptr) -> uop;

    if (!(uop -> type & IS_BR_CONDITIONAL)) continue;
    if (runs == 0) { //begin 2-bit		

      uint16_t i = H(uop -> pc, 4096); //gather address before run

      switch (TwoBit[i]) { //make prediction
      case 1: {
        gpred = false;
        break;
      }
      case 2: {
        gpred = false;
        break;
      }
      case 3: {
        gpred = true;
        break;
      }
      case 4: {
        gpred = true;
        break;
      }
      default:
        break;
      }
      /*
	  if(TwoBit[i] == 1)
	  {
		gpred = false;
	  }
	  else if(TwoBit[i] == 2)
	  {
		gpred = false;
	  }
	  else if(TwoBit[i] == 3)
	  {
		gpred = true;
	  }
	  else if(TwoBit[i] == 4)
	  {
		gpred = true;
	  }
	  else
	  {
		break;
	  }
	*/
      // originally planned to use an else if but it runs much slower than a switch
      //update prediction table
      if (TwoBit[i] == 0) {
        TwoBit[i] = 3; //default to weak
      }
      if (uop -> br_taken == true) { //set taken towards strongly taken
        switch (TwoBit[i]) {
        case 1: {
          TwoBit[i] = 2;
          break;
        }
        case 2: {
          TwoBit[i] = 3;
          break;
        }
        case 3: {
          TwoBit[i] = 4;
          break;
        }
        case 4: {
          TwoBit[i] = 4;
          break;
        }
        default:
          break;
        }
      } else { //set not taken towards strongly not taken
        switch (TwoBit[i]) {
        case 1: {
          TwoBit[i] = 1;
          break;
        }
        case 2: {
          TwoBit[i] = 1;
          break;
        }
        case 3: {
          TwoBit[i] = 2;
          break;
        }
        case 4: {
          TwoBit[i] = 3;
          break;
        }
        default:
          break;
        }
      }

      assert(report_pred(fe_ptr, false, gpred)); //send result

    } 
    else if (runs == 1) {//begin GSelect	

      int arr0[32], arr1[32], arr2[32];
      Bin(arr0, uop -> pc); //grab binary address from pc
      Bin(arr1, brh_fetch); //grab history
      for (int i = 0; i < 16; i++) { //iterate through history and concatenate
        arr2[i] = arr1[i];
      }
      for (int i = 16; i < 32; i++) {
        arr2[i] = arr0[i - 16];
      }
      int unconvval = Dec(arr2, 32); //convert back to Decimal
      uint16_t i = H(unconvval, 16777216); //hash the value

      switch (GSel[i]) { //make first prediction
      case 1: {
        gpred = false;
        break;
      }
      case 2: {
        gpred = false;
        break;
      }
      case 3: {
        gpred = true;
        break;
      }
      case 4: {
        gpred = true;
        break;
      }
      default:
        break;
      }

      if (GSel[i] == 0) {
        GSel[i] = 3; //default to weak
      }
      if (uop -> br_taken == true) { //if taken shift to strongly taken
        switch (GSel[i]) {
        case 1: {
          GSel[i] = 2;
          break;
        }
        case 2: {
          GSel[i] = 3;
          break;
        }
        case 3: {
          GSel[i] = 4;
          break;
        }
        case 4: {
          GSel[i] = 4;
          break;
        }
        default:
          break;
        }
      } else { //if not taken shift away from strongly taken towards strongly not taken
        switch (GSel[i]) {
        case 1: {
          GSel[i] = 1;
          break;
        }
        case 2: {
          GSel[i] = 1;
          break;
        }
        case 3: {
          GSel[i] = 2;
          break;
        }
        case 4: {
          GSel[i] = 3;
          break;
        }
        default:
          break;
        }
      }

      assert(report_pred(fe_ptr, false, gpred)); //send result   

    } else if (runs == 2) { //begin GShare

      uint32_t i = fmod((uop -> pc ^ brh_fetch), 16777216); //use XOR to get index value

      switch (GShare[i]) { //make first prediction
      case 1: {
        gpred = false;
        break;
      }
      case 2: {
        gpred = false;
        break;
      }
      case 3: {
        gpred = true;
        break;
      }
      case 4: {
        gpred = true;
        break;
      }
      default:
        break;
      }

      if (GShare[i] == 0) {
        GShare[i] = 3; //default to weak
      }
      if (uop -> br_taken == true) { //if taken shift to strongly taken
        switch (GShare[i]) {
        case 1: {
          GShare[i] = 2;
          break;
        }
        case 2: {
          GShare[i] = 3;
          break;
        }
        case 3: {
          GShare[i] = 4;
          break;
        }
        case 4: {
          GShare[i] = 4;
          break;
        }
        default:
          break;
        }
      } else { //if not taken shift to strongly not taken
        switch (GShare[i]) {
        case 1: {
          GShare[i] = 1;
          break;
        }
        case 2: {
          GShare[i] = 1;
          break;
        }
        case 3: {
          GShare[i] = 2;
          break;
        }
        case 4: {
          GShare[i] = 3;
          break;
        }
        default:
          break;
        }
      }
      assert(report_pred(fe_ptr, false, gpred)); //return result
    }
    brh_fetch = ((brh_fetch << 1) | uop -> br_taken); //use shifting to store result in the history table	
  }

  for (int i = 0; i < cycle_info -> num_retire; i++) {
    uint32_t rob_ptr = cycle_info -> retire_q[i];
    const cbp3_uop_dynamic_t * uop = & rob_entry(rob_ptr) -> uop;

    if (!(uop -> type & IS_BR_CONDITIONAL)) continue;
    if (runs == 0) {} else if (runs == 1) {} else if (runs == 2) {}
  }
}

void PredictorRunEnd() {
  runs++;
  if (runs < 3)
    rewind_marked = true;
}

void PredictorExit() {
}