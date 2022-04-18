// Proper vertex coloring problem (without I/O and with a deferred set of colors).
// Richard St-Denis, Universite de Sherbrooke, 2022.

MACHINE Proper_Vertex_Coloring

DEFINITIONS
  "LibraryIo.def";
  "Theories/Fig9_graph.def";
  SET_PREF_MAX_OPERATIONS == 1;
  SET_PREF_TIME_OUT == 500000;
  scope_Color == 6;   // or SET_PREF_DEFAULT_SETSIZE == 6 in general
  // Extension of the graph theory
  Coloring(f, DOM, RAN) == f : DOM --> RAN;   // Total coloring function
  Colored(g, f) == !(v_).(v_ : g'vertices =>
                               f(v_) /: UNION(u_).(u_ : Adjacent(g, v_) | {f(u_)}) );
  MinumumColoring(g, f, C) == Colored(g, f) &
    not (#(f_).(Coloring(f_, g'vertices, C) & Colored(g, f_) & card(ran(f_)) < card(ran(f)))); 
// Instance of the proper vertex coloring problem
SETS
  Vertex = {v1, v2, v3, v4, v5};
  Color                                       // Set of admissible colors

CONSTANTS G

PROPERTIES
  Graph(G) &
  G = rec(vertices: {v1, v2, v3, v4, v5},
          edges: SymClosure({(v1,v2), (v1,v3), (v1,v4), (v1,v5), (v2,v3), (v4,v5)}) )

OPERATIONS
  // Operation for checking if the graph is undirected
  c__undirected = PRE not(Undirected(G)) THEN skip END;
  // Operation for getting a minimum proper vertex coloring
  r__min_colored = ANY phi WHERE Coloring(phi, G'vertices, Color) & MinumumColoring(G, phi, Color) THEN
                     PRINT("The minimum coloring: "); PRINT(phi) END;
  // Operation for solving the proper vertex coloring problem
  r__colored = ANY phi WHERE Coloring(phi, G'vertices, Color) & Colored(G, phi) THEN
                 PRINT("The coloring: "); PRINT(phi) END END