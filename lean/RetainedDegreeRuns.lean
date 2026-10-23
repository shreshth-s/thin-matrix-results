import LowRequestLocator

set_option autoImplicit false

/-! The actual run indices enumerate each integer from -m through m once.
The same run is passed to both sources. This is a proof reindexing only. -/
namespace ThinMatrix.RetainedDegreeRuns
open SourceFormation
open scoped BigOperators

theorem runIndex_runValue (m : ℕ) (i : Fin (2*m+1)) :
    runIndex m (runValue m i) (runValue_mem m i)=i := by
  apply Fin.ext
  simp [runIndex,runValue]

theorem runValue_injective (m : ℕ) : Function.Injective (runValue m) := by
  intro i j h
  apply Fin.ext
  unfold runValue at h
  omega

theorem sum_runs {R : Type*} [AddCommMonoid R] (m : ℕ) (F : ℤ → R) :
    (∑ i : Fin (2*m+1), F (runValue m i))=∑ d∈Finset.Icc (-(m:ℤ)) (m:ℤ), F d := by
  classical
  refine Finset.sum_bij (fun i _ => runValue m i) ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_Icc.mpr (runValue_mem m i)
  · intro i _ j _ h; exact runValue_injective m h
  · intro d hd
    exact ⟨runIndex m d (Finset.mem_Icc.mp hd),Finset.mem_univ _,runValue_runIndex m d _⟩
  · intro i _; rfl

#print axioms runIndex_runValue
#print axioms runValue_injective
#print axioms sum_runs
end ThinMatrix.RetainedDegreeRuns
