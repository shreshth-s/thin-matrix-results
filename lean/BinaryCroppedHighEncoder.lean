import ShiftedHighForms

set_option autoImplicit false

/-! Shared, jointly capped HIGH bases for shifted, cropped binary sources.
Root formation is part of execution; all dense intermediate arrays and all
cyclic coefficients persist in the encoder trace. No encoded-base premise
or assumed preparation cost occurs in the public contract. -/
namespace ThinMatrix.BinaryCroppedHighEncoder
open BinaryCell BinaryHighExecution BinaryCroppedHighInput
open SharedEncoder (Coordinates read volume)
open scoped BigOperators

/-- Mathematical target on original raw cells and the literal shifted forms. -/
noncomputable def coefficientValue {L q : ℕ} (b : Bool) (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (word : CacheBounds.Word (2*L)) (r : Fin q) : ℤ :=
  ∑ a : Coordinates (HighBaseEncoder.rootDims L b),
    CroppedSourceContraction.crop cap (fun n o => view (BinarySourceFormation.readRaw raw n o r))
      (decodeSource b a).1 (decodeSource b a).2 *
      ∏ i, ShiftedHighForms.integerForms L b i.val (word i) (a i).val

noncomputable def leafValues {L q : ℕ} (b : Bool) (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L q) (v : HighBoxDP.LeafWord (2*L)) : Vector ℤ q :=
  Vector.ofFn (coefficientValue b cap raw (SourceCoordinates.liftLeaf v))

def execute (L m t q cap : ℕ) (b : Bool) (raw : BinarySourceFormation.RawStore L q) : StoredEncoding q (2*L) :=
  let root := input b cap raw
  let out := encodeStored L m t q b (ShiftedHighForms.forms L b) root.value
  {out with bitSteps := root.bitSteps+out.bitSteps}

theorem tensorValue_get {L q : ℕ} (b : Bool) (cap : ℕ) (raw : BinarySourceFormation.RawStore L q)
    (word : CacheBounds.Word (2*L)) (r : Fin q) :
    (HighBaseEncoder.tensorValue L b (nativeForms (ShiftedHighForms.forms L b) q)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) (input b cap raw).value) word).get r =
        coefficientValue b cap raw word r := by
  rw [ShiftedHighForms.nativeForms_eq,HighBaseEncoder.tensorValue_get]
  unfold SourceCoordinates.vectorTensorValue EncoderCorrectness.tensorSum coefficientValue
  change (∑ a : Coordinates (HighBaseEncoder.rootDims L b),
    (read (2*L) (HighBaseEncoder.rootDims L b)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) (input b cap raw).value) a).get r *
      ∏ i, ShiftedHighForms.integerForms L b i.val (word i) (a i).val) = _
  simp_rw [read_denseView]
  simp only [payloadView,Vector.get_map,input_read]

theorem readBase_correct {L m t q : ℕ} (cap : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (w : HighBoxDP.BaseStates L m t) (r : Fin q) :
    view (((BinaryHighTable.readBase (execute L m t q cap b raw).table w).1).get r) =
      coefficientValue b cap raw w.val r := by
  have h := readBase_view L m t q b (ShiftedHighForms.forms L b) (input b cap raw).value w
  have hh := congrArg (fun v : Vector ℤ q => v.get r) h
  rw [HighBaseEncoder.readBase,HighBaseEncoder.encodeStored_complete,Option.getD_some,tensorValue_get] at hh
  simpa only [execute,BinaryHighTable.readBase,BinaryHighExecution.readBase,payloadView,Vector.get_map] using hh

theorem readBase_values {L m t q : ℕ} (cap : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.vectorView (BinaryHighTable.readBase (execute L m t q cap b raw).table w).1 =
      leafValues b cap raw (HighBoxDP.baseLeaf w.val w.property.2) := by
  apply Vector.ext
  intro r hr
  change (BinaryHighTable.vectorView _).get ⟨r,hr⟩ = (leafValues _ _ _ _).get ⟨r,hr⟩
  rw [BinaryHighTable.vectorView_get]
  change view (((BinaryHighTable.readBase (execute L m t q cap b raw).table w).1).get ⟨r,hr⟩) = _
  rw [readBase_correct,leafValues,Vector.get_ofFn,HighBaseEncoder.lift_baseLeaf]

theorem table_bound {L m t q : ℕ} (cap A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) :
    BinaryHighTable.Bounds.TableBound (8^(2*L)*A) (execute L m t q cap b raw).table :=
  BinaryHighCost.encodeStored_table_bound L m t q A b (ShiftedHighForms.forms L b) (input b cap raw).value
    (ShiftedHighForms.forms_magnitude L b) (input_magnitude b cap raw A hA)

theorem readBase_bound {L m t q : ℕ} (cap A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.VectorBound (8^(2*L)*A) (BinaryHighTable.readBase (execute L m t q cap b raw).table w).1 :=
  BinaryHighTable.Bounds.array_read_bound (table_bound cap A b raw hA) _

def encoderShape (L : ℕ) : ℕ := 70*(2*L+1)+5*(2*L)*(1+4*(2*L))+8*(2*L)+7

theorem native_work {L m t q : ℕ} (b : Bool) (root : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b))
    (hq : 1 ≤ q) :
    let native := HighBaseEncoder.encodeStored L m t q 1 b (nativeForms (ShiftedHighForms.forms L b) q)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) root)
    native.encoding.coefficientWork+native.encoding.capWork+native.trieWork ≤
      encoderShape L*q*HighBaseEncoder.baseCount L m t := by
  simpa only [HighBaseEncoder.encodeVector,encoderShape,ShiftedHighForms.nativeForms_eq] using
    (HighBaseEncoder.encodeVector_work (m:=m) (t:=t) b (ShiftedHighForms.integerForms L b)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) root) hq)

theorem root_volume_le {L m t q : ℕ} (b : Bool)
    (root : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b)) :
    volume (2*L) (HighBaseEncoder.rootDims L b) ≤ HighBaseEncoder.baseCount L m t := by
  have h := HighBaseEncoder.layer_cells_le L m t b 0 (2*L) (HighBaseEncoder.rootDims L b)
    [⟨CappedEnumeration.zeroWord (2*L),root⟩] (HighBaseEncoder.root_shape L b) rfl
  simpa only [List.length_singleton,Nat.one_mul] using h

noncomputable def totalBudget (L m t q cap A : ℕ) : ℕ :=
  10*(cap.size+1)^2+2+
    (payloadBudget L q cap A+4*L+BinaryHighCost.storedFactor L A*encoderShape L*q)*HighBaseEncoder.baseCount L m t

theorem execute_price {L m t q : ℕ} (cap A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) (hq : 1 ≤ q) :
    (execute L m t q cap b raw).bitSteps ≤ totalBudget L m t q cap A := by
  have he := BinaryHighCost.encodeStored_bit_price L m t q A b (ShiftedHighForms.forms L b)
    (input b cap raw).value hq (ShiftedHighForms.forms_magnitude L b) (input_magnitude b cap raw A hA)
  have hn := native_work (m:=m) (t:=t) b (input b cap raw).value hq
  have hm := Nat.mul_le_mul_left (BinaryHighCost.storedFactor L A) hn
  have hi := input_price b cap raw A hA
  have hv := Nat.mul_le_mul_right (payloadBudget L q cap A+4*L)
    (root_volume_le (m:=m) (t:=t) b (input b cap raw).value)
  dsimp only at he hn hm
  simp only [execute,totalBudget,inputBudget] at *
  nlinarith

def allocatedCells {q N : ℕ} (out : StoredEncoding q N) : ℕ :=
  (out.encoding.formed.map (fun s => q*volume s.remaining s.dims)).sum

theorem allocated_cells {L m t q : ℕ} (cap : ℕ) (b : Bool) (raw : BinarySourceFormation.RawStore L q) :
    allocatedCells (execute L m t q cap b raw) ≤ q*(2*L+1)*HighBaseEncoder.baseCount L m t := by
  have h := HighBaseEncoder.encode_cells_le L m t q 1 b (nativeForms (ShiftedHighForms.forms L b) q)
    (denseView (2*L) (HighBaseEncoder.rootDims L b) (input b cap raw).value)
  rw [HighBaseEncoder.encode,HighBaseEncoder.run_cells_eq_formed] at h
  change HighBaseEncoder.formedCells q 1 (HighBaseEncoder.encode L m t q 1 b _ _).formed ≤ _ at h
  rw [←encode_formed_view] at h
  simpa only [HighBaseEncoder.formedCells,List.map_map,Function.comp_def,storedView,Nat.mul_one,
    allocatedCells,execute,encodeStored] using h

theorem leaf_keys {L m t q : ℕ} (cap : ℕ) (b : Bool) (raw : BinarySourceFormation.RawStore L q) :
    ((execute L m t q cap b raw).encoding.leaves.map (fun p => ArrayKeys.toWord p.1)) =
      HighBaseEncoder.generate L m t (2*L) := by
  have h := congrArg (List.map Prod.fst) (encode_leaves_view L m t q b (ShiftedHighForms.forms L b)
    (input b cap raw).value)
  rw [(HighBaseEncoder.encode_correct L m t q 1 b _ _).1] at h
  simpa only [execute,encodeStored,List.map_map,Function.comp_def,leafView] using h

theorem correctness_and_work {L m t q : ℕ} (cap A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) (hq : 1 ≤ q) :
    (∀ w : HighBoxDP.BaseStates L m t, ∀ r : Fin q,
      view (((BinaryHighTable.readBase (execute L m t q cap b raw).table w).1).get r) = coefficientValue b cap raw w.val r) ∧
    allocatedCells (execute L m t q cap b raw) ≤ q*(2*L+1)*HighBaseEncoder.baseCount L m t ∧
    (execute L m t q cap b raw).bitSteps ≤ totalBudget L m t q cap A :=
  ⟨fun w r => readBase_correct cap b raw w r,allocated_cells cap b raw,execute_price cap A b raw hA hq⟩

#print axioms tensorValue_get
#print axioms readBase_correct
#print axioms readBase_values
#print axioms table_bound
#print axioms readBase_bound
#print axioms native_work
#print axioms root_volume_le
#print axioms execute_price
#print axioms allocated_cells
#print axioms leaf_keys
#print axioms correctness_and_work
end ThinMatrix.BinaryCroppedHighEncoder
