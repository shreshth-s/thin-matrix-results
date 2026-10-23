import OppositeTensorBridge

set_option autoImplicit false

/-! Actual retained graph-window permutations to capped shared prefix arrays.
The radius is computed from each original channel count. Input-dependent
budgets sum the actual radii over all occurrences; no batch or desired
asymptotic cost is assumed. -/
namespace ThinMatrix.GraphPrefixProgram
open GoodMapEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation ExactHalfSourcePlan ResidualFamilyKeys
open scoped BigOperators

theorem suffixRare_clamp (k ell : ℕ) (w : CroppedGroupedSuffix.Word (2*k)) :
    RetainedWindowPermutation.suffixRare k (min ell k) w=RetainedWindowPermutation.suffixRare k ell w := by
  let F (len : ℕ) (h : len≤2*k) : ℕ := ∑ j : Fin len, if w (WindowSuffixPermutation.suffixIndex h j)=2 then 1 else 0
  change F _ _=F _ _
  congr 1
  exact min_assoc ell k k |>.trans (by rw [min_self])

abbrev Entry (L m C ell : ℕ) := Vector (WindowPrefixProgram.Prepared (L-m) ell ((m+1)*C))
  (RetainedRootWindows.slots (L-m))
abbrev Family (L m C t ell : ℕ) := Vector (Vector (Vector (Entry L m C ell)
  (channelCount m t)) (goodSlots L m).card) (goodSlots L m).card
abbrev Results (L m C t ell : ℕ) := Vector (Vector (Vector (Family L m C t ell × Family L m C t ell) (2*m+1)) (J m)) (J m)

theorem tabulate_bits_vary {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) (budget : Fin N → ℕ)
    (h : ∀ i, (f i).bitSteps≤budget i) : (tabulate shape f).bitSteps≤∑ i, budget i := by
  rw [tabulate_bits_eq]
  exact Finset.sum_le_sum (fun i _ => h i)

theorem tabulate_control_vary {A B : Type} {N : ℕ} (shape : Vector A N) (f : Fin N → Run B) (budget : Fin N → ℕ)
    (h : ∀ i, (f i).control≤budget i) : (tabulate shape f).control≤(∑ i, (budget i+32))+8 := by
  rw [tabulate_control_eq,Finset.sum_add_distrib]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => h i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

def entry {L m C : ℕ} (ell : ℕ) (window : RetainedRootWindows.Prepared L m C)
    (xs : GraphWindowPermutations.Entry L m C) : Run (Entry L m C ell) :=
  tabulate xs (fun slot => WindowPrefixProgram.execute ell (m/2) window.counts.1 window.counts.2 (xs.get slot).coefficients)

def family {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t)
    (xs : GraphWindowPermutations.Family L m C t) : Run (Family L m C t ell) :=
  tabulate xs (fun i => tabulate (xs.get i) (fun j => tabulate ((xs.get i).get j)
    (fun c => entry ell (((windows.get i).get j).get c) (((xs.get i).get j).get c))))

@[simp] theorem family_get {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t)
    (xs : GraphWindowPermutations.Family L m C t) (i j : Fin (goodSlots L m).card) (c : Fin (channelCount m t)) :
    (((family ell windows xs).value.get i).get j).get c=
      (entry ell (((windows.get i).get j).get c) (((xs.get i).get j).get c)).value := by
  simp only [family,tabulate_get]

def execute {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t)
    (xs : GraphWindowPermutations.Results L m C t) : Run (Results L m C t ell) :=
  tabulate xs (fun u => tabulate (xs.get u) (fun v => tabulate ((xs.get u).get v) (fun run =>
    let a := family ell ((((windows.get u).get v).get run).1) ((((xs.get u).get v).get run).1)
    let b := family ell ((((windows.get u).get v).get run).2) ((((xs.get u).get v).get run).2)
    ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+8⟩)))

@[simp] theorem execute_get {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t)
    (xs : GraphWindowPermutations.Results L m C t) (u v : Fin (J m)) (run : Fin (2*m+1)) :
    (((execute ell windows xs).value.get u).get v).get run=
      ((family ell ((((windows.get u).get v).get run).1) ((((xs.get u).get v).get run).1)).value,
       (family ell ((((windows.get u).get v).get run).2) ((((xs.get u).get v).get run).2)).value) := by
  simp only [execute,tabulate_get]

def EntryBound {L m C : ℕ} (xs : GraphWindowPermutations.Entry L m C) (A : ℕ) : Prop :=
  ∀ slot, OppositeWindowLayer.Bound (xs.get slot).coefficients A

def FamilyBound {L m C t : ℕ} (xs : GraphWindowPermutations.Family L m C t) (A : ℕ) : Prop :=
  ∀ i j c, EntryBound (((xs.get i).get j).get c) A

def PermutedBound {L m C t : ℕ} (xs : GraphWindowPermutations.Results L m C t) (A : ℕ) : Prop :=
  ∀ u v run, FamilyBound ((((xs.get u).get v).get run).1) A ∧ FamilyBound ((((xs.get u).get v).get run).2) A

def entryBitBudget {L m C : ℕ} (ell : ℕ) (window : RetainedRootWindows.Prepared L m C) (A : ℕ) : ℕ :=
  RetainedRootWindows.slots (L-m)*WindowPrefixProgram.bitBudget (L-m) ell (m/2) window.counts.1 window.counts.2 ((m+1)*C) A

def entryControlBudget {L m C : ℕ} (ell : ℕ) (window : RetainedRootWindows.Prepared L m C) : ℕ :=
  RetainedRootWindows.slots (L-m)*(WindowPrefixProgram.controlBudget (L-m) ell (m/2) window.counts.1 window.counts.2 ((m+1)*C)+32)+8

theorem entry_bits {L m C : ℕ} (ell : ℕ) (window : RetainedRootWindows.Prepared L m C)
    (xs : GraphWindowPermutations.Entry L m C) (A : ℕ) (ha : EntryBound xs A) :
    (entry ell window xs).bitSteps≤entryBitBudget ell window A :=
  tabulate_bits _ _ (fun slot => WindowPrefixProgram.execute_bits _ _ _ _ _ A (ha slot))

theorem entry_control {L m C : ℕ} (ell : ℕ) (window : RetainedRootWindows.Prepared L m C)
    (xs : GraphWindowPermutations.Entry L m C) : (entry ell window xs).control≤entryControlBudget ell window :=
  tabulate_control _ _ (fun _ => WindowPrefixProgram.execute_control _ _ _ _ _)

def familyBitBudget {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t) (A : ℕ) : ℕ :=
  ∑ i, ∑ j, ∑ c, entryBitBudget ell (((windows.get i).get j).get c) A

def sumControl {N : ℕ} (budget : Fin N → ℕ) : ℕ := (∑ i, (budget i+32))+8

def familyControlBudget {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t) : ℕ :=
  sumControl (fun i => sumControl (fun j => sumControl (fun c =>
    entryControlBudget ell (((windows.get i).get j).get c))))

theorem family_bits {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t)
    (xs : GraphWindowPermutations.Family L m C t) (A : ℕ) (ha : FamilyBound xs A) :
    (family ell windows xs).bitSteps≤familyBitBudget ell windows A := by
  apply tabulate_bits_vary; intro i
  apply tabulate_bits_vary; intro j
  apply tabulate_bits_vary; intro c
  exact entry_bits _ _ _ A (ha i j c)

theorem family_control {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Family L m C t)
    (xs : GraphWindowPermutations.Family L m C t) :
    (family ell windows xs).control≤familyControlBudget ell windows := by
  apply tabulate_control_vary; intro i
  apply tabulate_control_vary; intro j
  apply tabulate_control_vary; intro c
  exact entry_control _ _ _

def bitBudget {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t) (A : ℕ) : ℕ :=
  ∑ u, ∑ v, ∑ run, (familyBitBudget ell ((((windows.get u).get v).get run).1) A+
    familyBitBudget ell ((((windows.get u).get v).get run).2) A)

def controlBudget {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t) : ℕ :=
  sumControl (fun u => sumControl (fun v => sumControl (fun run =>
    familyControlBudget ell ((((windows.get u).get v).get run).1)+
    familyControlBudget ell ((((windows.get u).get v).get run).2)+8)))

theorem execute_bits {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t)
    (xs : GraphWindowPermutations.Results L m C t) (A : ℕ) (ha : PermutedBound xs A) :
    (execute ell windows xs).bitSteps≤bitBudget ell windows A := by
  apply tabulate_bits_vary; intro u
  apply tabulate_bits_vary; intro v
  apply tabulate_bits_vary; intro run
  exact Nat.add_le_add (family_bits _ _ _ A (ha u v run).1) (family_bits _ _ _ A (ha u v run).2)

theorem execute_control {L m C t : ℕ} (ell : ℕ) (windows : GraphRootWindows.Windows L m C t)
    (xs : GraphWindowPermutations.Results L m C t) : (execute ell windows xs).control≤controlBudget ell windows := by
  apply tabulate_control_vary; intro u
  apply tabulate_control_vary; intro v
  apply tabulate_control_vary; intro run
  exact Nat.add_le_add_right (Nat.add_le_add (family_control _ _ _) (family_control _ _ _)) 8

structure Prepared {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block ell : ℕ) where
  permuted : GraphWindowPermutations.Prepared f p block
  encoded : Run (Results p.L p.m f.cyclic p.t ell)

def fromInputs {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) : Prepared f p block ell :=
  let prior := GraphWindowPermutations.fromInputs f p block input bandL bandR ell
  ⟨prior,execute ell prior.transformed.source.windows.value prior.permuted.value⟩

theorem permuted_bound {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    PermutedBound (GraphWindowPermutations.fromInputs f p block input bandL bandR ell).permuted.value
      (2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))) := by
  intro u v run
  have hs := GraphWindowPermutations.transformed_bound f p block input bandL bandR (min ell (p.L-p.m)) u v run
  constructor <;> intro i j c slot
  · rw [GraphWindowPermutations.fromInputs_left_entry]
    exact RetainedWindowPermutation.prepare_bound _ _ _ _ _ (hs.1 i j c slot)
  · rw [GraphWindowPermutations.fromInputs_right_entry]
    exact RetainedWindowPermutation.prepare_bound _ _ _ _ _ (hs.2 i j c slot)

theorem fromInputs_bits {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).encoded.bitSteps≤bitBudget ell
      (GraphWindowPermutations.fromInputs f p block input bandL bandR ell).transformed.source.windows.value
      (2^(p.L-p.m)*(2^p.m*(4^p.m*2^(p.L+p.m)))) :=
  execute_bits _ _ _ _ (permuted_bound f p block input bandL bandR ell)

theorem fromInputs_control {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ) :
    (fromInputs f p block input bandL bandR ell).encoded.control≤controlBudget ell
      (GraphWindowPermutations.fromInputs f p block input bandL bandR ell).transformed.source.windows.value := execute_control _ _ _

theorem fromInputs_left_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    let prior := GraphWindowPermutations.fromInputs f p block input bandL bandR ell
    let window := (((((((prior.transformed.source.windows.value.get u).get v).get run).1).get i).get j).get c)
    let X := ((((((((prior.permuted.value.get u).get v).get run).1).get i).get j).get c).get slot).coefficients
    (((((((((fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).1).get i).get j).get c).get slot)=
      (WindowPrefixProgram.execute ell (p.m/2) window.counts.1 window.counts.2 X).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_left_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) ell)))
    (q : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell) → Fin 4)
    (active : Finset (Fin (WindowPrefixProgram.length (p.L-p.m) ell))) (col : Fin ((p.m+1)*f.cyclic)) :
    let prior := GraphWindowPermutations.fromInputs f p block input bandL bandR ell
    let X := ((((((((prior.permuted.value.get u).get v).get run).1).get i).get j).get c).get slot).coefficients
    CappedPrefixProgram.query (((((((((fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).1).get i).get j).get c).get slot).encoded pair q active col=
      EncoderCorrectness.tensorSum (fun _ : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell+WindowPrefixProgram.length (p.L-p.m) ell) => 3)
        (Fin.append (fun a => BinaryPrefixContraction.form (q a))
          (fun a => CroppedGroupedSuffix.localForm (((GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell)).get pair).get a) (decide (a∈active))))
        (fun w => OppositeWindowLayer.value X (fun a => w (Fin.cast (WindowPrefixProgram.dimension (p.L-p.m) ell).symm a)) col) := by
  dsimp only
  rw [fromInputs_left_entry]
  apply WindowPrefixProgram.query_exact
  intro word column hw
  have h := GraphWindowPermutations.fromInputs_left_support f p block input bandL bandR ell u v run i j c slot word column
  dsimp only at h
  rw [suffixRare_clamp] at h
  apply h
  simpa only [WindowPrefixProgram.cap,WindowPrefixProgram.length,GraphWindowPermutations.fromInputs,GraphWindowTransforms.fromInputs,RetainedWindowPermutation.suffixRare,min_assoc,min_self] using hw

theorem fromInputs_right_entry {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m))) :
    let prior := GraphWindowPermutations.fromInputs f p block input bandL bandR ell
    let window := (((((((prior.transformed.source.windows.value.get u).get v).get run).2).get i).get j).get c)
    let X := ((((((((prior.permuted.value.get u).get v).get run).2).get i).get j).get c).get slot).coefficients
    (((((((((fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).2).get i).get j).get c).get slot)=
      (WindowPrefixProgram.execute ell (p.m/2) window.counts.1 window.counts.2 X).value := by
  simp only [fromInputs,execute_get,family_get,entry,tabulate_get]

theorem fromInputs_right_query {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f) (block : Fin (CompactBlocks.blockCount n h))
    (input : BinaryFoldedFormation.Inputs n) (bandL bandR ell : ℕ)
    (u v : Fin (J p.m)) (run : Fin (2*p.m+1))
    (i j : Fin (goodSlots p.L p.m).card) (c : Fin (channelCount p.m p.t))
    (slot : Fin (RetainedRootWindows.slots (p.L-p.m)))
    (pair : Fin (2^(WindowPrefixProgram.length (p.L-p.m) ell)))
    (q : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell) → Fin 4)
    (active : Finset (Fin (WindowPrefixProgram.length (p.L-p.m) ell))) (col : Fin ((p.m+1)*f.cyclic)) :
    let prior := GraphWindowPermutations.fromInputs f p block input bandL bandR ell
    let X := ((((((((prior.permuted.value.get u).get v).get run).2).get i).get j).get c).get slot).coefficients
    CappedPrefixProgram.query (((((((((fromInputs f p block input bandL bandR ell).encoded.value.get u).get v).get run).2).get i).get j).get c).get slot).encoded pair q active col=
      EncoderCorrectness.tensorSum (fun _ : Fin (WindowPrefixProgram.prefixLength (p.L-p.m) ell+WindowPrefixProgram.length (p.L-p.m) ell) => 3)
        (Fin.append (fun a => BinaryPrefixContraction.form (q a))
          (fun a => CroppedGroupedSuffix.localForm (((GroupedPreparation.pairKeys (WindowPrefixProgram.length (p.L-p.m) ell)).get pair).get a) (decide (a∈active))))
        (fun w => OppositeWindowLayer.value X (fun a => w (Fin.cast (WindowPrefixProgram.dimension (p.L-p.m) ell).symm a)) col) := by
  dsimp only
  rw [fromInputs_right_entry]
  apply WindowPrefixProgram.query_exact
  intro word column hw
  have h := GraphWindowPermutations.fromInputs_right_support f p block input bandL bandR ell u v run i j c slot word column
  dsimp only at h
  rw [suffixRare_clamp] at h
  apply h
  simpa only [WindowPrefixProgram.cap,WindowPrefixProgram.length,GraphWindowPermutations.fromInputs,GraphWindowTransforms.fromInputs,RetainedWindowPermutation.suffixRare,min_assoc,min_self] using hw

#print axioms suffixRare_clamp
#print axioms tabulate_bits_vary
#print axioms tabulate_control_vary
#print axioms family_get
#print axioms execute_get
#print axioms entry_bits
#print axioms entry_control
#print axioms family_bits
#print axioms family_control
#print axioms execute_bits
#print axioms execute_control
#print axioms permuted_bound
#print axioms fromInputs_bits
#print axioms fromInputs_control
#print axioms fromInputs_left_entry
#print axioms fromInputs_right_entry
#print axioms fromInputs_left_query
#print axioms fromInputs_right_query
end ThinMatrix.GraphPrefixProgram
