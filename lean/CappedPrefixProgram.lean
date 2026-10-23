import RetainedCappedGroups

set_option autoImplicit false

/-! Actual capped binary grouping followed by shared prefix encoding. The
complete tensor-query identity is proved for the retained arrays, with a
redundant-crop corollary when suffix support is supplied by the window program.
No rectangular multiplication or final request scheduler is assumed. -/
namespace ThinMatrix.CappedPrefixProgram
open BinaryCell BinaryGroupedCoordinates CroppedGroupedSuffix CappedBitPreparation GroupedPreparation
open scoped BigOperators

abbrev Traces (P ell r C : ℕ) := Vector (Vector (RetainedPrefixEncoder.Trace C P) (CappedSubsetList.count ell r)) (2^ell)

structure Prepared (P ell r C : ℕ) where
  grouped : RetainedCappedGroups.Prepared P ell r C
  traces : Traces P ell r C

def encode {P ell r C : ℕ} (xs : RetainedCappedGroups.Prepared P ell r C) : Run (Traces P ell r C) :=
  BinaryGroupedPreparation.tabulate xs.groups (fun p => BinaryGroupedPreparation.tabulate (xs.groups.get p)
    (fun j => RetainedPrefixEncoder.run P ((xs.groups.get p).get j)))

def execute {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C) : Run (Prepared P ell r C) :=
  let grouped := RetainedCappedGroups.prepare r X
  let traces := encode grouped.value
  ⟨⟨grouped.value,traces.value⟩,grouped.bitSteps+traces.bitSteps,grouped.control+traces.control+8⟩

theorem execute_get {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (p : Fin (2^ell)) (j : Fin (CappedSubsetList.count ell r)) :
    (((execute r X).value.traces.get p).get j)=
      (RetainedPrefixEncoder.run P (((RetainedCappedGroups.prepare r X).value.groups.get p).get j)).value := by
  simp only [execute,encode,BinaryGroupedPreparation.tabulate_get]

theorem output_value {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (p : Fin (2^ell)) (j : Fin (CappedSubsetList.count ell r)) (q : Fin P → Fin 4) (c : Fin C) :
    view (RetainedPrefixEncoder.output (((execute r X).value.traces.get p).get j) q c)=
      ∑ u : Word P, (signed ((pairKeys ell).get p).get (support ((keyVector ell r).get j))*
        OppositeWindowLayer.value X (Fin.append u (word ((pairKeys ell).get p).get (support ((keyVector ell r).get j)))) c)*
          ∏ i, BinaryPrefixContraction.form (q i) (u i) := by
  rw [execute_get,RetainedPrefixEncoder.run_value]
  simp only [EncoderCorrectness.tensorSum,RetainedCappedGroups.prepare_value]

def bitBudget (P ell r C A : ℕ) : ℕ := RetainedCappedGroups.bitBudget P ell r C A+
  2^ell*(CappedSubsetList.count ell r*RetainedPrefixEncoder.bitBudget P C A)
def controlBudget (P ell r C : ℕ) : ℕ := RetainedCappedGroups.controlBudget P ell r C+
  (2^ell*(CappedSubsetList.count ell r*(RetainedPrefixEncoder.controlBudget P C+32)+40)+8)+8

theorem execute_bits {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) : (execute r X).bitSteps≤bitBudget P ell r C A := by
  have hg := RetainedCappedGroups.prepare_bits r X A ha
  have he := BinaryGroupedPreparation.tabulate_bits (RetainedCappedGroups.prepare r X).value.groups
    (fun p => BinaryGroupedPreparation.tabulate ((RetainedCappedGroups.prepare r X).value.groups.get p)
      (fun j => RetainedPrefixEncoder.run P (((RetainedCappedGroups.prepare r X).value.groups.get p).get j)))
    (fun p => BinaryGroupedPreparation.tabulate_bits _ _ (fun j => RetainedPrefixEncoder.run_bits _ A
      (RetainedCappedGroups.prepare_bound r X A ha p j)))
  exact Nat.add_le_add hg he

theorem execute_control {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C) :
    (execute r X).control≤controlBudget P ell r C := by
  have hg := RetainedCappedGroups.prepare_control r X
  have he := BinaryGroupedPreparation.tabulate_control (RetainedCappedGroups.prepare r X).value.groups
    (fun p => BinaryGroupedPreparation.tabulate ((RetainedCappedGroups.prepare r X).value.groups.get p)
      (fun j => RetainedPrefixEncoder.run P (((RetainedCappedGroups.prepare r X).value.groups.get p).get j)))
    (fun p => BinaryGroupedPreparation.tabulate_control _ _ (fun _ => RetainedPrefixEncoder.run_control _))
  simp only [Nat.add_assoc,show 8+32=40 by decide] at he
  simp only [execute,encode,controlBudget]
  omega

theorem output_bound {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) (p : Fin (2^ell)) (j : Fin (CappedSubsetList.count ell r))
    (q : Fin P → Fin 4) (c : Fin C) :
    (view (RetainedPrefixEncoder.output (((execute r X).value.traces.get p).get j) q c)).natAbs≤2^P*A := by
  rw [execute_get]
  exact RetainedPrefixEncoder.run_bound _ A (RetainedCappedGroups.prepare_bound r X A ha p j) q c

/-- Product decomposition of the full ordinary tensor, with every input word. -/
theorem tensor_append {P ell : ℕ} (f : Fin P → Fin 3 → ℤ) (g : Fin ell → Fin 3 → ℤ)
    (X : Word (P+ell) → ℤ) :
    EncoderCorrectness.tensorSum (fun _ : Fin (P+ell) => 3) (Fin.append f g) X=
      ∑ u : Word P, (∏ i, f i (u i)) * (∑ v : Word ell, (∏ i, g i (v i))*X (Fin.append u v)) := by
  unfold EncoderCorrectness.tensorSum
  rw [← (Fin.appendEquiv P ell).sum_comp (fun w => X w*∏ i, (Fin.append f g) i (w i))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.appendEquiv,Equiv.coe_fn_mk,Fin.prod_univ_add,Fin.append_left,Fin.append_right]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

def cropSuffix {P ell : ℕ} (r : ℕ) (X : Word (P+ell) → ℤ) (w : Word (P+ell)) : ℤ :=
  if (rare (fun i => w (Fin.natAdd P i))).card≤r then X w else 0

noncomputable def query {P ell r C : ℕ} (xs : Prepared P ell r C)
    (p : Fin (2^ell)) (q : Fin P → Fin 4) (active : Finset (Fin ell)) (c : Fin C) : ℤ :=
  ∑ j, if support (xs.grouped.keys.get j)⊆active then
    view (RetainedPrefixEncoder.output ((xs.traces.get p).get j) q c) else 0

theorem query_cropped {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (p : Fin (2^ell)) (q : Fin P → Fin 4) (active : Finset (Fin ell)) (c : Fin C) :
    query (execute r X).value p q active c=
      EncoderCorrectness.tensorSum (fun _ : Fin (P+ell) => 3)
        (Fin.append (fun i => BinaryPrefixContraction.form (q i))
          (fun i => localForm (((pairKeys ell).get p).get i) (decide (i∈active))))
        (cropSuffix r (fun w => OppositeWindowLayer.value X w c)) := by
  have he (j : Fin (CappedSubsetList.count ell r)) :
      (if support ((keyVector ell r).get j)⊆active then
        view (RetainedPrefixEncoder.output (((execute r X).value.traces.get p).get j) q c) else 0)=
      ∑ u : Word P, (∏ i, BinaryPrefixContraction.form (q i) (u i))*
        (if support ((keyVector ell r).get j)⊆active then
          data ((pairKeys ell).get p).get (fun v => OppositeWindowLayer.value X (Fin.append u v) c)
            (support ((keyVector ell r).get j)) else 0) := by
    rw [output_value]
    split_ifs
    · apply Finset.sum_congr rfl
      intro u _
      unfold data
      ring
    · simp
  have hk : (execute r X).value.grouped.keys=keyVector ell r := by
    simp only [execute,RetainedCappedGroups.prepare,storeKeys_value]
  unfold query
  rw [hk]
  simp_rw [he]
  rw [Finset.sum_comm,tensor_append]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.mul_sum]
  have hkeys := GroupedPreparation.sum_keys ell r (fun J => if J⊆active then
    data ((pairKeys ell).get p).get (fun v => OppositeWindowLayer.value X (Fin.append u v) c) J else 0)
  rw [hkeys,← transform_cropped]
  congr 1
  unfold transform kernel crop cropSuffix
  simp only [Fin.append_right]

/-- The actual window adapter discharges this support premise. -/
theorem query_exact {P ell C : ℕ} (r : ℕ) (X : RetainedCappedGroups.Source P ell C)
    (hs : ∀ w c, r<(rare (fun i => w (Fin.natAdd P i))).card → OppositeWindowLayer.value X w c=0)
    (p : Fin (2^ell)) (q : Fin P → Fin 4) (active : Finset (Fin ell)) (c : Fin C) :
    query (execute r X).value p q active c=
      EncoderCorrectness.tensorSum (fun _ : Fin (P+ell) => 3)
        (Fin.append (fun i => BinaryPrefixContraction.form (q i))
          (fun i => localForm (((pairKeys ell).get p).get i) (decide (i∈active))))
        (fun w => OppositeWindowLayer.value X w c) := by
  rw [query_cropped]
  congr 1
  funext w
  unfold cropSuffix
  split
  · rfl
  · exact (hs w c (by omega)).symm

def traceCells {P ell r C : ℕ} (xs : Prepared P ell r C) : ℕ :=
  (xs.traces.toList.map (fun group => (group.toList.map (fun trace => RetainedPrefixEncoder.cells trace)).sum)).sum

/-- All prefix intermediates, including the initial group referenced by each
trace. The separate grouped field shares those initial arrays. -/
theorem traceCells_bound {P ell r C : ℕ} (xs : Prepared P ell r C) :
    traceCells xs≤(P+1)*4^P*(2^ell*CappedSubsetList.count ell r)*C := by
  have hr (group : Vector (RetainedPrefixEncoder.Trace C P) (CappedSubsetList.count ell r)) :
      (group.toList.map (fun trace => RetainedPrefixEncoder.cells trace)).sum≤CappedSubsetList.count ell r*((P+1)*4^P*C) := by
    have h := List.sum_le_card_nsmul (group.toList.map (fun trace => RetainedPrefixEncoder.cells trace)) ((P+1)*4^P*C) (by
      intro v hv; obtain ⟨trace,_,rfl⟩ := List.mem_map.mp hv; exact RetainedPrefixEncoder.cells_bound trace)
    simpa using h
  have h := List.sum_le_card_nsmul (xs.traces.toList.map (fun group => (group.toList.map (fun trace => RetainedPrefixEncoder.cells trace)).sum))
    (CappedSubsetList.count ell r*((P+1)*4^P*C)) (by
      intro v hv; obtain ⟨group,_,rfl⟩ := List.mem_map.mp hv; exact hr group)
  simp only [List.length_map,Vector.length_toList,smul_eq_mul] at h
  unfold traceCells
  calc
    _ ≤ 2^ell*(CappedSubsetList.count ell r*((P+1)*4^P*C)) := h
    _ = _ := by ring

#print axioms traceCells_bound
#print axioms execute_get
#print axioms output_value
#print axioms execute_bits
#print axioms execute_control
#print axioms output_bound
#print axioms tensor_append
#print axioms query_cropped
#print axioms query_exact
end ThinMatrix.CappedPrefixProgram
