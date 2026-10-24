import RetainedHighSources
import GraphHighRun

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000

namespace ThinMatrix.GraphRetainedHigh
open RetainedHighSources ExactHalfSourcePlan

variable {n h r K : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
  (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)

abbrev Sources := Vector (ExactHalfBandSources.Families p.L p.m f.cyclic) K

def Correct (ids : Vector ℕ K) (sources : Sources f p (K:=K)) : Prop :=
  ∀ i,sources.get i=(ExactHalfGraphSources.execute f p block input (ids.get i) (ids.get i)).sources.value

 theorem raw_left (a b : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    raw (ExactHalfGraphSources.execute f p block input a a).sources.value false u v run=
      raw (ExactHalfGraphSources.execute f p block input a b).sources.value false u v run := by
  exact congrArg (fun x => x.get run) (GraphBandSharing.sources_left_independent f p block input a a b u v)

 theorem raw_right (a b : ℕ) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    raw (ExactHalfGraphSources.execute f p block input b b).sources.value true u v run=
      raw (ExactHalfGraphSources.execute f p block input a b).sources.value true u v run := by
  exact congrArg (fun x => x.get run) (GraphBandSharing.sources_right_independent f p block input b a b u v)

 theorem raw_bound (a b : ℕ) (right : Bool) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    BinaryHighExecution.RawBound (raw (ExactHalfGraphSources.execute f p block input a b).sources.value right u v run) (2^(p.L+p.m)) :=
  GraphHighRun.fromInputs_raw_bound f p block input a b 0 u v run right

variable (ids : Vector ℕ K) (sources : Sources f p (K:=K))
  (hc : Correct f p block input ids sources)

include hc

 theorem left_encoder (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (((((bank p.t (p.m/2) sources).value.get a).1.get u).get v).get run)=
      BinaryCroppedHighEncoder.execute p.L p.m p.t f.cyclic (p.m/2) true
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value false u v run) := by
  rw [bank_get]
  change (((prepareSide p.t (p.m/2) false (sources.get a)).value.get u).get v).get run=_
  rw [side_get,hc a,raw_left f p block input (ids.get a) (ids.get b)]
  rfl

 theorem right_encoder (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (((((bank p.t (p.m/2) sources).value.get b).2.get u).get v).get run)=
      BinaryCroppedHighEncoder.execute p.L p.m p.t f.cyclic (p.m/2) false
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value true u v run) := by
  rw [bank_get]
  change (((prepareSide p.t (p.m/2) true (sources.get b)).value.get u).get v).get run=_
  rw [side_get,hc b,raw_right f p block input (ids.get a) (ids.get b)]
  rfl

/-- Pair preparation reads both retained encoders; its parameters do not
contain raw sources and cannot rerun the encoder. -/
def boxes (bank : Vector (Encoded p.L p.m f.cyclic) K) (size : ℕ)
    (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :=
  pair (L:=p.L) (m:=p.m) (t:=p.t) size
    ((((bank.get a).1.get u).get v).get run) ((((bank.get b).2.get u).get v).get run)

 theorem boxes_match (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (boxes f p (bank p.t (p.m/2) sources).value (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).value=
      (BinaryCroppedHighBoxes.execute p.L p.m p.t f.cyclic (p.m/2) (2^(p.L+p.m))
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value false u v run)
        (raw (ExactHalfGraphSources.execute f p block input (ids.get a) (ids.get b)).sources.value true u v run)).boxes := by
  unfold boxes
  rw [left_encoder f p block input ids sources hc a b u v run,right_encoder f p block input ids sources hc a b u v run]
  exact pair_matches _ _ _ _

 theorem boxes_work (a b : Fin K) (u v : Fin (J p.m)) (run : Fin (2*p.m+1)) :
    (boxes f p (bank p.t (p.m/2) sources).value (BinaryCroppedHighBoxes.setup p.L (2^(p.L+p.m))).value a b u v run).work ≤
      BinaryHighTable.preparationBudget p.L p.m p.t f.cyclic (BinaryCroppedHighBoxes.magnitude p.L (2^(p.L+p.m))) := by
  letI : NeZero f.cyclic := ⟨Nat.ne_of_gt f.cyclic_pos⟩
  unfold boxes
  rw [left_encoder f p block input ids sources hc a b u v run,right_encoder f p block input ids sources hc a b u v run]
  exact pair_work _ _ _ _ (raw_bound f p block input _ _ false u v run) (raw_bound f p block input _ _ true u v run)

 theorem bank_work : (bank p.t (p.m/2) sources).operations ≤
    K*(2*sideBudget p.L p.m p.t f.cyclic (p.m/2) (2^(p.L+p.m))+16) := by
  apply RetainedHighSources.bank_work
  · exact Nat.one_le_of_lt f.cyclic_pos
  · intro i right u v run
    rw [hc i]
    exact raw_bound f p block input _ _ right u v run

#print axioms raw_left
#print axioms raw_right
#print axioms raw_bound
#print axioms left_encoder
#print axioms right_encoder
#print axioms boxes_match
#print axioms boxes_work
#print axioms bank_work
end ThinMatrix.GraphRetainedHigh
