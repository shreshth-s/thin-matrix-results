import FoldedBackendExecution
import CountedEndToEndAPSP
import AdaptiveBitBounds
import FactorValidation

/-!
# Concrete aligned integer APSP program

The aligned shape is computed by integer ceiling division. Valid factor
histories use their actual take/drop split, the physical factor three, and
the guarded binary cyclic multiplier. Every producer result is retained once
by the counted controller. The correctness theorem below is unconditional
with respect to running-time claims: it does not assume a fast oracle.

The final complexity theorem must separately connect this same producer to
the proved phase bounds and price the controller and scalar array sites.
-/

namespace ThinMatrix.AlignedAPSP
open StoredMinPlusAPSP ThinMatrixBackend

def shape (h d : ℕ) : FoldedBackendExecution.Shape h d where
  L := ComputableParameters.ordinaryLength (FoldedBackendExecution.middleExponent h d)
  t := ComputableParameters.channelLength (FoldedBackendExecution.middleExponent h d)
  hm := ComputableParameters.ordinaryLength_lower _
  ht := (ComputableParameters.channelLength_upper _).trans (by omega)

theorem shape_length (h d : ℕ) :
    (shape h d).L = Nat.ceil (RealCertificate.c*
      (FoldedBackendExecution.middleExponent h d:ℝ)) :=
  ComputableParameters.ordinaryLength_eq _

theorem shape_cutoff (h d : ℕ) :
    (shape h d).t = Nat.ceil (2*RealCertificate.theta*
      (FoldedBackendExecution.middleExponent h d:ℝ)) :=
  ComputableParameters.channelLength_eq _

def multiplier (h d q : ℕ) [NeZero q] : FullMultiplier q :=
  BinaryMultiplierAdapter.boundedBinaryFullMultiplier q
    (AdaptiveBitBounds.highInputBudget (shape h d).L
      (FoldedBackendExecution.middleExponent h d) 1)
    (AdaptiveBitBounds.highInputBudget_pos _ _ _ (by decide))

abbrev Payload (n h : ℕ) := Option (FoldedBackendExecution.Payload n h)

structure FactorSetup (factors : List ℕ) where
  plan : CompactBlocks.PhysicalFactorization factors.prod
  work : ℕ

/-- Actual one-pass products are stored in the plan. The original
factorization appears only in erased proofs. -/
def prepareFactors (S : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    FactorSetup factors :=
  let split := FactorValidation.splitProducts S factors
  have hfold := congrArg Prod.fst (FactorValidation.splitProducts_value S factors)
  have hring := congrArg Prod.snd (FactorValidation.splitProducts_value S factors)
  let reference := EndToEndAPSP.historyFactorization S factors hv
  { plan :=
      { folded := split.1.1
        cyclic := split.1.2
        folded_pos := by rw [hfold]; exact reference.folded_pos
        cyclic_pos := by rw [hring]; exact reference.cyclic_pos
        coprime := by rw [hfold, hring]; exact reference.coprime
        product := by rw [hfold, hring]; exact reference.product }
    work := split.2 }

theorem prepareFactors_plan (S : ℕ) (factors : List ℕ) (hv : EndToEndAPSP.ValidFactors factors) :
    (prepareFactors S factors hv).plan = EndToEndAPSP.historyFactorization S factors hv := by
  simp only [prepareFactors, FactorValidation.splitProducts_value]
  rfl

def chargeTable {I : ℕ} {P : Type} (work : ℕ) (row : CountedArrayComposite.Table I P) :
    CountedArrayComposite.Table I P := {row with work := row.work+work}

/-- Active flags only mask the already materialized row; they do not trigger
another product preparation or another coefficient query. -/
def maskTable {I : ℕ} {P : Type} (active : ArrayCompositeAlgorithm.Flags I)
    (table : CountedArrayComposite.Table I P) : CountedArrayComposite.Table I (Option P) :=
  ⟨Vector.ofFn (fun i => if active.get i then table.counts.get i else 0),
    some table.payload, table.work+I⟩

noncomputable def physicalProducer {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (A B T : IntTable n) :
    CountedArrayComposite.Table (EndToEndAPSP.incidenceSize n h)
      (FoldedBackendExecution.Payload n h) :=
  FoldedBackendExecution.produce f (shape h (FoldedBackendExecution.physicalFold f))
    (multiplier h (FoldedBackendExecution.physicalFold f) f.cyclic) A B T

/-- A total, reference fallback for the zero-modulus invalid-history branch.
The actual solver's factor-validity theorem excludes this branch. -/
def zeroFallback {n h : ℕ} (A B T : IntTable n)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    CountedArrayComposite.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  ⟨Vector.ofFn (fun i => if active.get i then
      (EndToEndAPSP.flatInstance (h:=h) A B T).modCount 0 i else 0),
    none, (EndToEndAPSP.incidenceSize n h)*(n+1)⟩

noncomputable def table {n h : ℕ} (A B T : IntTable n) (selected : List ℕ)
    (candidate : ℕ) (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h)) :
    CountedArrayComposite.Table (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  let factors := selected++[candidate]
  let validation := FactorValidation.validate factors
  if hb : validation.1 = true then
    let prepared := prepareFactors AlignedCertificate.S factors
      ((FactorValidation.validate_correct factors).mp hb)
    chargeTable (validation.2+prepared.work) (maskTable active (physicalProducer prepared.plan A B T))
  else if hz : factors.prod = 0 then chargeTable validation.2 (zeroFallback A B T active)
  else chargeTable validation.2 (maskTable active (physicalProducer (CompactBlocks.scalarPhysicalPlan factors.prod hz) A B T))

noncomputable def oracle {n h : ℕ} (A B T : IntTable n) :
    CountedArrayComposite.Oracle (EndToEndAPSP.incidenceSize n h) (Payload n h) :=
  ⟨table A B T⟩

theorem oracle_correct {n h : ℕ} (hh : 0 < h) (A B T : IntTable n) :
    (oracle (h:=h) A B T).Correct (EndToEndAPSP.flatInstance (h:=h) A B T) := by
  intro selected candidate active i hi
  change (table (h:=h) A B T selected candidate active).counts.get i = _
  have hp : (selected++[candidate]).prod = selected.prod*candidate := by simp
  unfold table
  dsimp only
  split_ifs with hv hz
  · simp only [chargeTable, maskTable, Vector.get_ofFn, hi, if_true, physicalProducer]
    rw [FoldedBackendExecution.produce_modCount hh, hp]
  · simp only [chargeTable, zeroFallback, Vector.get_ofFn, hi, if_true]
    rw [hp] at hz
    rw [hz]
  · simp only [chargeTable, maskTable, Vector.get_ofFn, hi, if_true, physicalProducer]
    rw [FoldedBackendExecution.produce_modCount hh, hp]

noncomputable def backend (n h : ℕ) (hh : 0 < h) :
    CountedEndToEndAPSP.Backend n h (Payload n h) :=
  ⟨oracle, oracle_correct hh⟩

noncomputable def run {n : ℕ} (w : OptionalTable n) (W : ℕ) :=
  CountedEndToEndAPSP.run
    (backend n (ComputableParameters.block n) (EndToEndAPSP.block_pos n)) w W

theorem run_correct {n : ℕ} (w : OptionalTable n) (W : ℕ)
    (hw : APSPReduction.EdgeBound (decode w) W)
    (hno : APSPReduction.NoNegativeCycles (decode w)) :
    APSPReduction.IsAPSP (decode w) (decode (run w W).value) :=
  CountedEndToEndAPSP.run_correct _ w W hw hno

theorem valid_table_uses_split {n h : ℕ} (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate])) :
    table (h:=h) A B T selected candidate active =
      chargeTable ((FactorValidation.validate (selected++[candidate])).2+
        (FactorValidation.splitProducts AlignedCertificate.S (selected++[candidate])).2)
        (maskTable active (physicalProducer
          (EndToEndAPSP.historyFactorization AlignedCertificate.S (selected++[candidate]) hv) A B T)) := by
  have hb := (FactorValidation.validate_correct (selected++[candidate])).mpr hv
  simp only [table, dif_pos hb]
  rw [prepareFactors_plan]
  rfl

theorem valid_table_retains_producer_work {n h : ℕ} (A B T : IntTable n)
    (selected : List ℕ) (candidate : ℕ)
    (active : ArrayCompositeAlgorithm.Flags (EndToEndAPSP.incidenceSize n h))
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate])) :
    (table (h:=h) A B T selected candidate active).work =
      FoldedBackendExecution.Payload.work
        (physicalProducer (h:=h)
          (EndToEndAPSP.historyFactorization AlignedCertificate.S (selected++[candidate]) hv) A B T).payload +
      EndToEndAPSP.incidenceSize n h +
      ((FactorValidation.validate (selected++[candidate])).2+
        (FactorValidation.splitProducts AlignedCertificate.S (selected++[candidate])).2) := by
  rw [valid_table_uses_split A B T selected candidate active hv]
  rfl

/-- Validation and actual prefix/suffix multiplication are charged against
the literal padded folded dimension, including the final cyclic phase. -/
theorem factor_overhead_budget (selected : List ℕ) (candidate S D : ℕ)
    (hv : EndToEndAPSP.ValidFactors (selected++[candidate]))
    (hd : ((selected++[candidate]).take S).prod ≤ D) :
    (FactorValidation.validate (selected++[candidate])).2 +
      (FactorValidation.splitProducts S (selected++[candidate])).2 ≤
        64*(selected.length+2)^3*D*((selected++[candidate]).drop S).prod := by
  have hvalidate := FactorValidation.validate_history_work selected candidate S D hv hd
  let f := EndToEndAPSP.historyFactorization S (selected++[candidate]) hv
  have hD : 0 < D := f.folded_pos.trans_le hd
  have hq : 0 < ((selected++[candidate]).drop S).prod := f.cyclic_pos
  have hp : selected.length+2 ≤ (selected.length+2)^3 :=
    le_self_pow₀ (by omega) (by decide)
  have hs : (FactorValidation.splitProducts S (selected++[candidate])).2 ≤
      32*(selected.length+2)^3 := by
    rw [FactorValidation.splitProducts_work, List.length_append, List.length_singleton]
    nlinarith
  have hm : 32*(selected.length+2)^3 ≤
      32*(selected.length+2)^3*D*((selected++[candidate]).drop S).prod := by
    have h := Nat.le_mul_of_pos_right (32*(selected.length+2)^3) (Nat.mul_pos hD hq)
    simpa only [Nat.mul_assoc] using h
  have hsum := Nat.add_le_add hvalidate (hs.trans hm)
  convert hsum using 1
  ring

#print axioms shape_length
#print axioms shape_cutoff
#print axioms prepareFactors_plan
#print axioms oracle_correct
#print axioms run_correct
#print axioms valid_table_uses_split
#print axioms valid_table_retains_producer_work
#print axioms factor_overhead_budget

end ThinMatrix.AlignedAPSP
