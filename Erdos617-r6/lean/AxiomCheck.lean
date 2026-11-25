import Erdos617_r6_proof

-- Expected signature:
-- Erdos617.erdos617_r6 : ∀ (C : Erdos617.EdgeColoring (6 * 6 + 1) 6), ¬Erdos617.IsBalanced C
#check @Erdos617.erdos617_r6

-- Expected axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos617.erdos617_r6
#print axioms Erdos617.single_graph_relaxation_fails_c5
#print axioms Erdos617.no_2r_plus_1_alpha_le_2
#print axioms Erdos617.r6_exact_two_partitions
