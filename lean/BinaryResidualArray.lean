import BinaryResidualRootProgram

set_option autoImplicit false

/-! Complete retained residual-root arrays. Every remaining ternary word is
materialized, including zero rows, and each row holds all F formal degrees
and all C columns. Runtime shape construction grows retained arrays by three;
no unit-cost exponentiation or inverse-equivalence execution is assumed.
Native counters/division/indexing retain their separate control annotation. -/
namespace ThinMatrix.BinaryResidualArray
open WalshEmbedding BinaryGroupedCoordinates BinaryGroupedPreparation BinaryResidualPolynomial
open scoped BigOperators

/-- Actual shape allocation, including intermediate copies from both appends. -/
def slots : (n : ℕ) → GroupedPreparation.Counted (Vector Unit (3^n))
  | 0 => ⟨Vector.singleton (),2⟩
  | n+1 =>
      let previous := slots n
      let out := (previous.value ++ previous.value) ++ previous.value
      ⟨out.cast (by rw [pow_succ]; omega),previous.work+6*previous.value.toArray.size+8⟩

theorem slots_work (n : ℕ) : (slots n).work≤12*3^n := by
  induction n with
  | zero => simp [slots]
  | succ n ih =>
    have hp : 1≤3^n := Nat.one_le_pow _ _ (by decide)
    simp only [slots,Vector.size_toArray,pow_succ]
    omega

def left {a b : ℕ} (w : Vector (Fin 3) (a+b)) : Vector (Fin 3) a :=
  Vector.ofFn (fun i => w.get (Fin.castAdd b i))
def right {a b : ℕ} (w : Vector (Fin 3) (a+b)) : Vector (Fin 3) b :=
  Vector.ofFn (fun i => w.get (Fin.natAdd a i))

def row {L C : ℕ} (F cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (index : ℕ) : Run (Block F C) :=
  let n := (ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length
  let word := WindowSelection.decode n index
  let out := BinaryResidualRootProgram.execute F cap raw maskN maskO cn co (left word.value) (right word.value)
  ⟨out.value,out.bitSteps,out.control+word.work+6*n+8⟩

def execute {L C : ℕ} (F cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    Run (Vector (Block F C) (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length))) :=
  let shape := slots ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)
  let out := tabulate shape.value (fun i => row F cap raw maskN maskO cn co i.val)
  ⟨out.value,out.bitSteps,shape.work+out.control⟩

theorem execute_get {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)) :
    (execute F cap raw maskN maskO cn co).value.get
      (StoredGroupedCompletion.rawIndex _ w) =
    (BinaryResidualRootProgram.execute F cap raw maskN maskO cn co
      (Vector.ofFn (fun i => w (Fin.castAdd _ i)))
      (Vector.ofFn (fun i => w (Fin.natAdd _ i)))).value := by
  simp only [execute,tabulate_get,row,left,right]
  rw [WindowSelection.decode_index,Equiv.symm_apply_apply]

/-- Every retained formal coefficient equals the cropped shifted residual
contraction of the original raw source. The opposite product includes every
channel, and the output index retains every remaining ternary word. -/
theorem execute_coeff {L C F : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (w : CroppedGroupedSuffix.Word ((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length))
    (d : Fin F) (r : Fin C) :
    cellView ((execute F cap raw maskN maskO cn co).value.get (StoredGroupedCompletion.rawIndex _ w)) d r =
      (co.toList.map (fun b => if b then (1:ℤ) else 2)).prod *
      ((DistinguishedResidualRoot.contract cn.get Polynomial.X (fun n => BinaryResidualRootProgram.sourcePolynomial cap raw
        (DistinguishedResidualSupport.assemble (ResidualLayout.equivalence maskN) n
          (fun i => DistinguishedResidualSupport.normalRemaining (w (Fin.castAdd _ i))))
        (DistinguishedResidualSupport.assemble (ResidualLayout.equivalence maskO)
          (fun i => DistinguishedResidualRoot.oppositeLetter (co.get i))
          (fun i => SourceCoordinates.oppositeEquiv (w (Fin.natAdd _ i)))))).coeff d.val) r := by
  rw [execute_get]
  simpa only [Vector.get_ofFn] using BinaryResidualRootProgram.execute_coeff cap raw maskN maskO cn co
    (Vector.ofFn (fun i => w (Fin.castAdd _ i))) (Vector.ofFn (fun i => w (Fin.natAdd _ i))) d r

def bitBudget (L mN mO kN kO C F cap A : ℕ) : ℕ :=
  3^(kN+kO)*BinaryResidualRootProgram.bitBudget L mN mO C F cap A

def controlBudget (L mN mO kN kO C F : ℕ) : ℕ :=
  3^(kN+kO)*(BinaryResidualRootProgram.controlBudget L mN mO C F+
    (kN+kO)*(6*(kN+kO)+16)+6*(kN+kO)+54)+8

theorem execute_bits {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (execute F cap raw maskN maskO cn co).bitSteps≤
      bitBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length
        (ResidualLayout.remaining maskN).length (ResidualLayout.remaining maskO).length C F cap A := by
  apply tabulate_bits
  intro i
  exact BinaryResidualRootProgram.execute_bits cap raw maskN maskO cn co _ _ A ha

theorem execute_control {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    (execute F cap raw maskN maskO cn co).control≤
      controlBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length
        (ResidualLayout.remaining maskN).length (ResidualLayout.remaining maskO).length C F := by
  let n := (ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length
  let B := BinaryResidualRootProgram.controlBudget L (ResidualLayout.selected maskN).length
    (ResidualLayout.selected maskO).length C F
  have hr (i : Fin (3^n)) : (row F cap raw maskN maskO cn co i.val).control≤B+n*(6*n+16)+6*n+10 := by
    have hd := WindowSelection.decode_work n i.val
    have he := BinaryResidualRootProgram.execute_control (F:=F) cap raw maskN maskO cn co
      (left (WindowSelection.decode n i.val).value) (right (WindowSelection.decode n i.val).value)
    change _≤B at he
    simp only [row]
    change _≤_ at hd
    dsimp only [n] at hd he ⊢
    omega
  have ht := tabulate_control (slots n).value (fun i => row F cap raw maskN maskO cn co i.val) hr
  have hs := slots_work n
  simp only [execute]
  change (slots n).work+_≤_
  unfold controlBudget
  change _≤3^n*(B+n*(6*n+16)+6*n+54)+8
  nlinarith

theorem execute_bound {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A)
    (i : Fin (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length))) :
    Bound (2^(ResidualLayout.selected maskO).length*(4^(ResidualLayout.selected maskN).length*A))
      ((execute F cap raw maskN maskO cn co).value.get i) := by
  simp only [execute,tabulate_get,row]
  exact BinaryResidualRootProgram.execute_bound cap raw maskN maskO cn co _ _ A ha

theorem execute_width {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A)
    (i : Fin (3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)))
    (d : Fin F) (r : Fin C) :
    (cellView ((execute F cap raw maskN maskO cn co).value.get i) d r).natAbs.size ≤
      (ResidualLayout.selected maskO).length+2*(ResidualLayout.selected maskN).length+A.size := by
  simp only [execute,tabulate_get,row]
  exact BinaryResidualRootProgram.execute_width cap raw maskN maskO cn co _ _ A ha d r

/-- All rows, degrees and coefficient columns are represented in the output. -/
theorem coefficient_cells {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length) :
    (((execute F cap raw maskN maskO cn co).value.toList.map
      (fun block => (block.toList.map (fun row => row.toArray.size)).sum)).sum) =
      3^((ResidualLayout.remaining maskN).length+(ResidualLayout.remaining maskO).length)*F*C := by
  simp only [Vector.size_toArray,List.map_const',List.sum_const_nat,Vector.length_toList]
  ring

#print axioms slots_work
#print axioms execute_get
#print axioms execute_coeff
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_bound
#print axioms execute_width
#print axioms coefficient_cells
end ThinMatrix.BinaryResidualArray
