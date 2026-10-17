import APSPAlgorithm
import AsymptoticCosts

/-!
The machine package recompiles these existing mathematical proof sources with
its own Lean 4.33.1 toolchain and mathlib pin. It does not import the Lean 4.31
project's compiled artifacts. Their correctness and asymptotic lemmas alone
do not prove an implementation or a machine execution bound.
-/

#check ThinMatrix.APSPAlgorithm.fastAPSP_correct
#check ThinMatrix.AsymptoticCosts.completeCostBigO

#print axioms ThinMatrix.APSPAlgorithm.fastAPSP_correct
#print axioms ThinMatrix.AsymptoticCosts.completeCostBigO

