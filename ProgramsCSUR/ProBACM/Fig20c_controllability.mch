// Controllability (generation of a set of traces with the aid of the iterate operator).
// Author: Richard St-Denis, Universite de Sherbrooke, 2022.

MACHINE controllability

SETS
  State  = {x0, x1, x2, x3, x4, x5, x6, x7, x8, x9};
  Action = {a0, a1, a2, a3, a4, a5, a6, a7, a8, a9}

CONSTANTS
  G, H, L_G, L_H, // Automata and languages for free and legal behaviors
  bound           // Bound on the length of sequences

ABSTRACT_CONSTANTS TraceRelG, TraceRelH

DEFINITIONS
  SET_PREF_MAX_INITIALISATIONS == 1;
  SET_PREF_MAX_OPERATIONS == 1;
  SET_PREF_SMT == TRUE;
  SET_PREF_SYMBOLIC == TRUE;
  SET_PREF_TIME_OUT == 100000000;
  "LibraryIO.def";

  Trace == struct(actions: seq(Action), state: State);

  ExtendTrace(A) == {t1,t2 | {t1,t2} <: Trace &
    #(a_).((t1'state,a_,t2'state) : A'transitions & t2'actions = t1'actions<-a_) };
  GetTraces(A, bnd, rel_) ==
    {rec(actions: [], state: A'initialState)} \/
    UNION(k_).(k_ : 1..bnd | iterate(rel_, k_)
              [{rec(actions: [], state: A'initialState)}] );
  GetWords(T) == UNION(t_).(t_ : T | {t_'actions});

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

  TraceRelG = ExtendTrace(G) & L_G = GetWords(GetTraces(G, bound, TraceRelG)) &
  TraceRelH = ExtendTrace(H) & L_H = GetWords(GetTraces(H, bound, TraceRelH))

OPERATIONS
  VerifyCtrl = SELECT Controllability(L_G, L_H, G'actions-G'ctrlActions) THEN
    PRINT("L_H is controllable") ELSE PRINT("L_H is not controllable.") END END