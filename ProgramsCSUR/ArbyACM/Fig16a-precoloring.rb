# Precoloring extension problem (with a partial coloring in a constraint and
#   anonymous and named colors and no partial instance).
# Author: Richard St-Denis, Universite de Sherbrooke, 2022.

require '/home/ubuntu/ArbyACM/Theories/Fig7-graph.rb'
alloy :GraphColoring do open GraphTheory
  # Extension of the graph theory
  sig Color [] {}           # Set of admissible colors
  abstract sig Coloring [   # Proper vertex coloring
    colors: (set Color),
    phi: Vertex ** one(Color) ] {Vertex.(this.phi).in? colors}
  pred colored[g: (one Graph), pvc: (one Coloring)] {
    all(v: g.vertices) {not (v.(pvc.phi).in? adjacent[g,v].(pvc.phi))} }
  # Instance of the coloring problem
  one sig V1 extends Vertex [] {}
  one sig V2 extends Vertex [] {}
  one sig V3 extends Vertex [] {}
  one sig V4 extends Vertex [] {}
  one sig V5 extends Vertex [] {}
# one sig V6 extends Vertex [] {}
  one sig G extends Graph [] {vertices == V1 + V2 + V3 + V4 + V5}
  fact {G.(edges) == sym_closure[V1**V2 + V1**V3 + V1**V4 + V1**V5 + V2**V3 + V4**V5]}
# one sig G extends Graph [] {vertices == V1 + V2 + V3 + V4 + V5 + V6}
# fact {G.(edges) == sym_closure[V1**V2 + V1**V3 + V1**V4 + V1**V5 + V1**V6 + 
#                                V2**V3 + V2**V4 + V2**V5 + V2**V6 +
#                                V3**V4 + V3**V5 + V3**V6 +
#                                V4**V5 + V4**V6 + V5**V6 ]}
  # Putting "edges == sym_closure[V1**V2 + V1**V3 + V1**V4 + V1**V5 + V2**V3 + V4**V5]"
  # in the fact of G is not accepted by ARby
  one sig Green extends Color [] {}
  one sig Red extends Color [] {}
# one sig Blue extends Color [] {}
# one sig Yellow extends Color [] {}
# one sig Pink extends Color [] {}
# one sig Brown extends Color [] {}
  one sig C extends Coloring [] {(V1**Red + V5**Green).in? phi}

  # Commands for solving the precoloring extension problem 
  assertion c__undirected {undirected[G]}
  check :c__undirected, 1, Int => 5
  run :colored, 1, Int => 5, Color=>exactly(6) end

# pred r__colored[pvc: (one Coloring)] {colored[G, C] and pvc == C}
# run :r__colored, 1, Int => 5, Color=>exactly(6) end 

module Main
  cntrex = GraphColoring.check_c__undirected
  if cntrex.sat? then puts "The predicate is violated." end
  sol = GraphColoring.run_colored; puts sol['$colored_pvc'].phi unless sol.unsat? end
# sol = GraphColoring.run_r__colored
# puts sol['$r__colored_pvc'].phi unless sol.unsat? end
# bnds = Arby::Ast::Bounds.new; bnds.bound_int(-16..15)
# sol = GraphColoring.solve(:r__colored, bnds)
# puts sol['$r__colored_pvc'].phi unless sol.unsat? end
