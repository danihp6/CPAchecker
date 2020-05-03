/*  Copyright (C) 2018  Martin Spiessl
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

#include <stdio.h>
#include <stdbool.h>


// do not define DEBUG to remove debug output
//#define DEBUG
// do not define REGULAROUTPUT to suppress output to stdout also:
//#define REGULAROUTPUT

// For verification, define VERIFY in next line:
#define VERIFY

#ifdef VERIFY 
  extern void __VERIFIER_error(void);
  extern int  __VERIFIER_nondet_int();
  extern void __VERIFIER_assume(int  ) ;
  #define VERIFIER_ERROR() __VERIFIER_error()
#endif
#ifndef VERIFY
  #define VERIFIER_ERROR() do {} while (0)
#endif


#ifdef DEBUG
#define debug_print(...) \
            fprintf(stderr, __VA_ARGS__)
#endif
#ifndef DEBUG
#define debug_print(...) do {} while (0)
#endif
#ifdef REGULAROUTPUT
#define regular_print(...) \
            fprintf(stdout, __VA_ARGS__)
#endif
#ifndef REGULAROUTPUT
#define regular_print(...) do {} while (0)
#endif


// colors for the traffic light:
enum color {Red, Yellow, Green, Off};
#ifdef REGULAROUTPUT 
// matching indices to enum values is dirty, do not do this:
const char * colorNames[] = {"Red\t", "Yellow", "Green", "Off\t"};
#endif


// Automaton state variables:
enum color stateA = Off;
enum color stateB = Off;
enum color stateC = Off;
enum color stateD = Off;
unsigned int stepNumber = 0;
bool dir = false;
int switchState = 0;

// Variables for state checks (verification):
enum color lastA = Off;
enum color lastB = Off;
enum color lastC = Off;
enum color lastD = Off;


//###################### Automata Section  ######################

// TRAFFIC LIGHT LAYOUT:
//     |  |
//  ___|A |___
//         C
//  __B    ___
//     | D|
//     |  |


// Advances light A by one step. Also only function
// to affect the switching direction dir!
void stepA() {
  if (!switchState) {
    stateA = Off;
    return;
  }
  switch (stateA) {
    case Red:
      stateA = Yellow;
      break;
    case Yellow:
      if (dir) {
        stateA = Green;
        dir = !dir;
      } else {
        stateA = Red;
        dir = !dir;
      }
      break;
    case Green:
      stateA = Yellow;
      break;
    case Off:
      if (switchState) {
        stateA = Green;
        dir = false;
      }
      break;
  }
}

// Light D shall mimic light A (opposing lanes)
void stepD() {
  stateD = stateA;
}


// Advances light C by one step. No need to switch dir
// since this is already handled by stepA()!
void stepC() {
  if (!switchState) {
    stateC = Off;
    return;
  }
  switch (stateC) {
    case Red:
      stateC = Yellow;
      break;
    case Yellow:
      if (!dir) {
        stateC = Red;
      } else {
        stateC = Green;
      }
      break;
    case Green:
      stateC = Yellow;
      break;
    case Off:
      if (switchState) {
        stateC = Red;
      }
      break;
  }
}

// Light B shall mimic light C (opposing lanes)
void stepB() {
  stateB = stateC;
}

void printStates() {
  regular_print("[%05u] A: %s\tB: %s\tC: %s\tD: %s\t\n",
         stepNumber,
         colorNames[stateA],
         colorNames[stateB],
         colorNames[stateC],
         colorNames[stateD]);
}

void stepLights() {
  stepA();
  stepC();
  stepB();
  stepD();
  printStates();
  stepNumber++;
}

bool successorsValid(
    enum color firstColor,
    enum color secondColor) {
  // switching off can easily be captured in the beginning:
  if (secondColor == Off) {
    return true;
  }
  // now look at other transitions:
  switch (firstColor) {
    case Red:
      // it shall switch to Yellow or stay Red:
      return secondColor == Yellow  || secondColor == firstColor;
    case Yellow:
      // three possibilities: switch to green, to red, or stay yellow:
      return secondColor == Green ||
             secondColor == Red ||
             secondColor == firstColor;
    case Green:
      // it shall switch to Yellow or stay Green:
      return secondColor == Yellow  || secondColor == firstColor;
    case Off:
      // it shall stay Off or start with Red or Green:
      return secondColor == firstColor ||
             secondColor == Red ||
             secondColor == Green;
  }

}

bool propertiesHold() {
  bool violationOccurred = false;
  if (stateA==Green && dir) {
    debug_print("[%05u] Violation of invariant: When light A is green, the direction has to be false!\n",stepNumber);
    violationOccurred = true;
  }
  if (!(stateA==stateD)) {
    debug_print("[%05u] Violation of opposing equality property for A<->C!\n",stepNumber);
    violationOccurred = true;
  }
  if (!(stateB==stateC)) {
    debug_print("[%05u] Violation of opposing equality property for B<->D!\n",stepNumber);
    violationOccurred = true;
  }
  if (!successorsValid(lastA,stateA)) {
    debug_print("[%05u] Violation of sequence for A!\n",stepNumber);
    violationOccurred = true;
  }
  if (!successorsValid(lastB,stateB)) {
    debug_print("[%05u] Violation of sequence for B!\n",stepNumber);
    violationOccurred = true;
  }
  if (!successorsValid(lastC,stateC)) {
    debug_print("[%05u] Violation of sequence for C!\n",stepNumber);
    violationOccurred = true;
  }
  if (!successorsValid(lastD,stateD)) {
    debug_print("[%05u] Violation of sequence for D!\n",stepNumber);
    violationOccurred = true;
  }

  //update for next time:
  lastA=stateA;
  lastB=stateB;
  lastC=stateC;
  lastD=stateD;
  return !violationOccurred;
}

#ifndef VERIFY
void getUserInput() {
  char input[2] = "-";
  while (!(input[0]=='1' || input[0]=='0')) {
    regular_print("Please enter 0 or 1 to indicate traffic light status!");
    scanf("%1s",input);
  }
  switchState = (input[0]=='1'?true:false);
}
#endif
#ifdef VERIFY
void getUserInput() {
  switchState = __VERIFIER_nondet_int();
  __VERIFIER_assume(switchState==0 || switchState==1);
}
#endif
int main() {
  //Show initial state:
  printStates();
  // check initial switching of the traffic lights:
  if (!propertiesHold()) {
      VERIFIER_ERROR();
  };
  // query input, step and check forever:
  for (;;) {
    getUserInput();
    stepLights();
    if (!propertiesHold()) {
      VERIFIER_ERROR();
    }
  }
  return 0;
}