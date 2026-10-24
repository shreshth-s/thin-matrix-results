import SelectedHighQueries
import GraphBandSharing

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-! Retain cropped HIGH encoders once per source side and band. Pair table
construction consumes those retained encoders and performs no source encoding.
All cyclic coefficients persist in both preparation stages. -/
namespace ThinMatrix.RetainedHighSources
open ExactHalfSourcePlan SourceFormation BinaryHighExecution
open scoped BigOperators

abbrev Side (L m q : ℕ) := Vector (Vector (Vector (StoredEncoding q (2*L)) (2*m+1)) (J m)) (J m)
abbrev Encoded (L m q : ℕ) := Side L m q × Side L m q

def raw {L m q : ℕ} (sources : ExactHalfBandSources.Families L m q) (right : Bool)
    (u v : Fin (J m)) (run : Fin (2*m+1)) : BinarySourceFormation.RawStore L q :=
  (if right then (((sources.get u).get v).2) else (((sources.get u).get v).1)).get run

def prepareSide {L m q : ℕ} (t cap : ℕ) (right : Bool) (sources : ExactHalfBandSources.Families L m q) :
    Program (Side L m q) :=
  vectorBuild (J m) fun u => vectorBuild (J m) fun v => vectorBuild (2*m+1) fun run =>
    let out := BinaryCroppedHighEncoder.execute L m t q cap (!right) (raw sources right u v run)
    ⟨out,out.bitSteps+8⟩

theorem side_get {L m q : ℕ} (t cap : ℕ) (right : Bool) (sources : ExactHalfBandSources.Families L m q)
    (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((prepareSide t cap right sources).value.get u).get v).get run=
      BinaryCroppedHighEncoder.execute L m t q cap (!right) (raw sources right u v run) := by
  simp only [prepareSide,vectorBuild_get]

noncomputable def sideBudget (L m t q cap A : ℕ) : ℕ :=
  ((2*m+1)*(BinaryCroppedHighEncoder.totalBudget L m t q cap A+16)+8)*J m*J m+8*J m

theorem side_work {L m q : ℕ} (t cap A : ℕ) (right : Bool) (sources : ExactHalfBandSources.Families L m q)
    (hq : 1 ≤ q) (hA : ∀ u v run,RawBound (raw sources right u v run) A) :
    (prepareSide t cap right sources).operations ≤ sideBudget L m t q cap A := by
  have hr (u v : Fin (J m)) := vectorBuild_cost (2*m+1)
    (BinaryCroppedHighEncoder.totalBudget L m t q cap A+8) (fun run => let out := BinaryCroppedHighEncoder.execute L m t q cap (!right) (raw sources right u v run)
      (⟨out,out.bitSteps+8⟩ : Program (StoredEncoding q (2*L))))
    (fun run =>
      Nat.add_le_add_right (BinaryCroppedHighEncoder.execute_price cap A (!right) _ (hA u v run) hq) 8)
  have hv (u : Fin (J m)) := vectorBuild_cost (J m) _ _ (hr u)
  have hu := vectorBuild_cost (J m) _ _ hv
  exact hu.trans_eq (by unfold sideBudget; ring)

def prepare {L m q : ℕ} (t cap : ℕ) (sources : ExactHalfBandSources.Families L m q) : Program (Encoded L m q) :=
  let left := prepareSide t cap false sources
  let right := prepareSide t cap true sources
  ⟨(left.value,right.value),left.operations+right.operations+8⟩

theorem prepare_work {L m q : ℕ} (t cap A : ℕ) (sources : ExactHalfBandSources.Families L m q)
    (hq : 1 ≤ q) (hA : ∀ right u v run,RawBound (raw sources right u v run) A) :
    (prepare t cap sources).operations ≤ 2*sideBudget L m t q cap A+8 := by
  have hl := side_work t cap A false sources hq (hA false)
  have hr := side_work t cap A true sources hq (hA true)
  change (prepareSide t cap false sources).operations+(prepareSide t cap true sources).operations+8 ≤ _
  omega

def bank {L m q K : ℕ} (t cap : ℕ) (sources : Vector (ExactHalfBandSources.Families L m q) K) :
    Program (Vector (Encoded L m q) K) := vectorBuild K (fun i => prepare t cap (sources.get i))

theorem bank_get {L m q K : ℕ} (t cap : ℕ) (sources : Vector (ExactHalfBandSources.Families L m q) K) (i : Fin K) :
    (bank t cap sources).value.get i=(prepare t cap (sources.get i)).value := by
  simp only [bank,vectorBuild_get]

theorem bank_work {L m q K : ℕ} (t cap A : ℕ) (sources : Vector (ExactHalfBandSources.Families L m q) K)
    (hq : 1 ≤ q) (hA : ∀ i right u v run,RawBound (raw (sources.get i) right u v run) A) :
    (bank t cap sources).operations ≤ K*(2*sideBudget L m t q cap A+16) := by
  have hh := vectorBuild_cost K _ _ (fun i => prepare_work t cap A (sources.get i) hq (hA i))
  simpa only [bank,Nat.add_assoc,Nat.mul_comm] using hh

/-- Only box products and recurrence run here; encoders are retained inputs. -/
def pair {L m t q : ℕ} (magnitude : ℕ) (left right : StoredEncoding q (2*L)) : BinaryHighTable.Result (BinaryHighTable.Table q) :=
  BinaryHighTable.prepare (L:=L) (m:=m) (t:=t) magnitude left.table right.table

theorem pair_matches {L m t q : ℕ} (cap A : ℕ) (X Y : BinarySourceFormation.RawStore L q) :
    (pair (L:=L) (m:=m) (t:=t) (BinaryCroppedHighBoxes.setup L A).value
      (BinaryCroppedHighEncoder.execute L m t q cap true X)
      (BinaryCroppedHighEncoder.execute L m t q cap false Y)).value=
      (BinaryCroppedHighBoxes.execute L m t q cap A X Y).boxes := rfl

theorem pair_work {L m t q : ℕ} [NeZero q] (cap A : ℕ) (X Y : BinarySourceFormation.RawStore L q)
    (hX : RawBound X A) (hY : RawBound Y A) :
    (pair (L:=L) (m:=m) (t:=t) (BinaryCroppedHighBoxes.setup L A).value
      (BinaryCroppedHighEncoder.execute L m t q cap true X)
      (BinaryCroppedHighEncoder.execute L m t q cap false Y)).work ≤
        BinaryHighTable.preparationBudget L m t q (BinaryCroppedHighBoxes.magnitude L A) := by
  rw [BinaryCroppedHighBoxes.setup_value]
  exact BinaryHighTable.prepare_work _ (BinaryCroppedHighBoxes.magnitude_pos L A) _ _
    (BinaryCroppedHighBoxes.read_bound cap A true X hX) (BinaryCroppedHighBoxes.read_bound cap A false Y hY)

#print axioms side_get
#print axioms side_work
#print axioms prepare_work
#print axioms bank_get
#print axioms bank_work
#print axioms pair_matches
#print axioms pair_work
end ThinMatrix.RetainedHighSources
