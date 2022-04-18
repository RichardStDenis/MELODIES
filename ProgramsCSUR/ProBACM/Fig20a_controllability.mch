// Controllability (generation of a set of words).
// Author: Richard St-Denis, Universite de Sherbrooke, 2022.

MACHINE controllability

SETS
  State  = {x0, x1, x2, x3, x4, x5, x6, x7, x8, x9};
  Action = {a0, a1, a2, a3, a4, a5, a6, a7, a8, a9}

CONSTANTS
  G, H, L_G, L_H, // Automata and languages for free and legal behaviors
  bound           // Bound on the length of sequences

DEFINITIONS
  SET_PREF_MAX_INITIALISATIONS == 1;
  SET_PREF_MAX_OPERATIONS == 1;
  SET_PREF_SMT == FALSE;
  SET_PREF_SYMBOLIC == FALSE;
  SET_PREF_TIME_OUT == 100000000;
  "LibraryIO.def";

  GetWords(A, bnd) ==
    UNION(i_).(i_ : 1..succ(bnd) | {seqA_ |
      #(seqS_).(seqA_ : seq(A'actions) & seqS_ : seq(A'states) &
                size(seqS_) = i_ & size(seqA_) = pred(i_) &
                seqS_(1) : {A'initialState} &
                !(k_).(k_ : 1..pred(i_) =>
                  (seqS_(k_),seqA_(k_),seqS_(succ(k_))) : A'transitions ) ) });

  Controllability(L, K, Act_u) ==
    !(w_, a_).(w_ : K & a_ : Act_u => (w_<-a_ : L => w_<-a_ : K))

PROPERTIES
  G = rec(states: State,     initialState: x0,        // Automaton for the free behavior
          actions: Action,   ctrlActions: {a2, a4, a7, a8, a9},
          transitions: {(x0, a1, x1), (x0, a2, x2), (x0, a6, x6), (x1, a0, x0),
                        (x2, a3, x3), (x3, a4, x4), (x4, a5, x5),
                        (x6, a7, x7), (x8, a9, x9), (x9, a8, x8)} ) &
  H = rec(states: (State - {x5, x7}),    // \/ {x4},  // Automaton for the legal behavior
          initialState: x0,
          actions: (Action - {a5, a7}),  // \/ {a4},
          transitions: G'transitions - {(x4, a5, x5), (x6, a7, x7)} - {(x3, a4, x4)}
         ) &
  bound = 7 &
  L_G = GetWords(G, bound) & L_H = GetWords(H, bound)

OPERATIONS
  VerifyCtrl = SELECT Controllability(L_G, L_H, G'actions-G'ctrlActions) THEN
    PRINT("L_H is controllable") ELSE PRINT("L_H is not controllable.") END END