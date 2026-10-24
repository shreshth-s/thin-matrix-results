import GraphOwnBandTypeRate
import SharedCompletionWidths

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThinMatrix.GraphOwnBandUniformFit
open GraphAdaptiveRootBatch GraphOwnBandPriced GraphOwnBandTypeRate
open scoped BigOperators
variable {n h r S : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (base : Index f p)
  (scheme : RectangularBatch.Scheme) (targets : GraphOwnBandTargets.Prepared f p (S:=S))

/-- All selected-occurrence lengths are bounded by the one original query
count; no shape is multiplied by the number of opposite bands. -/
theorem selected_size
    (hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S)
    (htree : GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value)
    (g : Fin (G f p (S:=S))) :
    (labels f p base targets.requests targets.masks (GraphOwnBandTargets.tree f p targets base.right) g).size ≤ M (n:=n) := by
  rw [labels_size]
  have hh := Finset.single_le_sum (f:=fun g => count f p base (GraphOwnBandTargets.tree f p targets base.right) g)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  rw [count_total f p base targets.requests _ hb htree] at hh
  exact hh

 theorem power_bounds (U : ℕ) (hD : 0 < D f p base)
    (hb : ∀ i,(targets.requests.get i).bandL<S ∧ (targets.requests.get i).bandR<S)
    (htree : GraphOwnBandTargets.tree f p targets base.right=(GraphOwnBandRouter.run base.right targets.requests hb).value)
    (hG : 1 ≤ G f p (S:=S))
    (hfit : SharedCompletionTile.col (D f p base) ≤ Q f p)
    (hgeom : p.L ≤ U) (hM : M (n:=n) ≤ 2^U)
    (hs : D f p base ≤ 2^U) (hQ : Q f p ≤ 2^U)
    (hA : SharedCompletionTile.row (D f p base) ≤ 2^U)
    (hZ : SharedCompletionTile.col (D f p base) ≤ 2^U)
    (hg : G f p (S:=S) ≤ 2^U) (hH : H f p base ≤ 2^U) (hW : W f p ≤ 2^U) :
    Fits f p base scheme targets (scheme.q.size+3*U+30) := by
  have size_bound (x : ℕ) (hx : x ≤ 2^U) : x.size ≤ U+1 :=
    (Nat.size_le_size hx).trans_eq Nat.size_pow
  have hss := size_bound _ hs
  have hgs := size_bound _ hg
  have hHs := size_bound _ hH
  have hWs := size_bound _ hW
  refine ⟨hG,hfit,by omega,by omega,?_,by omega,by omega,by omega⟩
  intro g
  have hl := (selected_size f p base targets hb htree g).trans hM
  have dims := SharedCompletionTile.dimensions (D f p base) hD
  have hh := SharedCompletionWidths.span_size _ _ _ _ _ U dims.1 dims.2.1 hl hs hQ hA hZ
  omega

#print axioms selected_size
#print axioms power_bounds
end ThinMatrix.GraphOwnBandUniformFit
