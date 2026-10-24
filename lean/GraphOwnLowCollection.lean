import GraphOwnLowIdentity
import RootProductCollection

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

/-! Sum every translation-list pair, degree run and strict channel once over
original-ID scalar outputs. This collector does not materialize unrequested
cyclic coefficients and includes family-index decoding and shape allocation. -/
namespace ThinMatrix.GraphOwnLowCollection
open BinaryCell BinaryGroupedCoordinates ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
abbrev M := FoldedBackendExecution.windowQuerySize n
abbrev B := CompactBlocks.blockCount n h
abbrev Rows := Vector (Vector Cell (B (n:=n) (h:=h))) (M (n:=n))
abbrev T := J p.m*(J p.m*((2*p.m+1)*channelCount p.m p.t))
abbrev Family := Fin (J p.m) → Fin (J p.m) → Fin (2*p.m+1) → Fin (channelCount p.m p.t) → Run (Rows (n:=n) (h:=h))

def child (family : Family f p) (s : Fin (T f p)) : Run (Rows (n:=n) (h:=h)) :=
  let u := finProdFinEquiv.symm s
  let v := finProdFinEquiv.symm u.2
  let run := finProdFinEquiv.symm v.2
  let out := family u.1 v.1 run.1 run.2
  ⟨out.value,out.bitSteps,out.control+64⟩

def execute (family : Family f p) :=
  let out := RootProductCollection.execute (Vector.replicate (T f p) ()) (child f p family)
    (fun rows j => rows.get j)
  (⟨out.value,out.bitSteps,out.control+3*T f p+8⟩ : Run _)

theorem value (family : Family f p) (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    view ((RootProductCollection.output (execute f p family).value j).get block)=
      ∑ u, ∑ v, ∑ run, ∑ c, view (((family u v run c).value.get j).get block) := by
  change view ((RootProductCollection.output (RootProductCollection.execute _ _ _).value j).get block)=_
  rw [RootProductCollection.execute_value]
  rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,child,Equiv.symm_apply_apply]
  simp_rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]
  simp_rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]

theorem correct (input : BinaryFoldedFormation.Inputs n) (family : Family f p)
    (hc : ∀ u v run c j block,view (((family u v run c).value.get j).get block)=
      GraphWeightedRootProducts.sourceValue (GraphOwnRootSpec.graph f p input block j)
        (GraphOwnRootSpec.pairIndex f p u v run c (GraphOwnRootSpec.physical f p input.target j))
        input.target (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient)
    (j : Fin (M (n:=n))) (block : Fin (B (n:=n) (h:=h))) :
    view ((RootProductCollection.output (execute f p family).value j).get block)=
      LowRequestLocator.value (GraphOwnRootSpec.graph f p input block j) input.target
        (GraphOwnRootSpec.physical f p input.target j).bandL
        (GraphOwnRootSpec.physical f p input.target j).bandR j
        (GraphOwnRootSpec.physical f p input.target j).coefficient := by
  rw [value]
  simp_rw [hc]
  exact GraphOwnLowIdentity.family f p input block j

theorem bits (family : Family f p) (A : ℕ) (budget : Fin (T f p) → ℕ)
    (ha : ∀ s j block,(view (((child f p family s).value.get j).get block)).natAbs≤A)
    (hb : ∀ s,(child f p family s).bitSteps≤budget s) :
    (execute f p family).bitSteps≤RootProductCollection.bitBudget budget (M (n:=n)) (B (n:=n) (h:=h)) A :=
  RootProductCollection.execute_bits _ _ _ A budget ha hb

theorem control (family : Family f p) (budget : Fin (T f p) → ℕ)
    (hb : ∀ s,(child f p family s).control≤budget s) :
    (execute f p family).control≤RootProductCollection.controlBudget budget (M (n:=n)) (B (n:=n) (h:=h))+3*T f p+8 :=
  Nat.add_le_add_right (Nat.add_le_add_right (RootProductCollection.execute_control _ _ _ budget hb) _) _

#print axioms value
#print axioms correct
#print axioms bits
#print axioms control
end ThinMatrix.GraphOwnLowCollection
