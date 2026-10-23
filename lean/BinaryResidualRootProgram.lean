import BinaryResidualContraction

set_option autoImplicit false

/-! Binary residual row construction from actual source arrays and retained
position layouts. Ring-width and arithmetic costs are derived from the raw
input magnitude. Indexed control remains explicitly separate from binary
arithmetic; no whole-program machine bound is asserted. -/
namespace ThinMatrix.BinaryResidualRootProgram
open WalshEmbedding BinaryCell BinaryGroupedCoordinates BinaryResidualPolynomial
open DistinguishedResidualSupport
open scoped BigOperators

def doubleCell (a : Cell) : Run Cell :=
  let sum := add a a
  let out := copy sum.value
  ⟨out.value,sum.bitSteps+out.bitSteps,12⟩

theorem doubleCell_view (a : Cell) : view (doubleCell a).value=2*view a := by simp [doubleCell]; ring

theorem doubleCell_bits (a : Cell) (A : ℕ) (h : (view a).natAbs≤A) :
    (doubleCell a).bitSteps≤2*BackendScalarBits.backendScalarUnit (2*A).size := by
  have hw := Nat.size_le_size (h.trans (by omega : A≤2*A))
  have ha := add_price (2*A).size a a hw hw
  have hb := copy_price (2*A).size (add a a).value (by
    apply Nat.size_le_size
    simpa only [add_view] using (Int.natAbs_add_le (view a) (view a)).trans (by omega : (view a).natAbs+(view a).natAbs≤2*A))
  simp only [doubleCell]
  omega

def double {F C : ℕ} (a : Block F C) : Run (Block F C) := mapBlock a (fun d r => doubleCell ((a.get d).get r))

theorem double_view {F C : ℕ} (a : Block F C) (d : Fin F) (r : Fin C) :
    cellView (double a).value d r=2*cellView a d r := by simp [double,doubleCell_view,cellView,mapBlock]

theorem double_bound {F C : ℕ} (a : Block F C) (A : ℕ) (h : Bound A a) : Bound (2*A) (double a).value := by
  intro d r
  rw [double_view,Int.natAbs_mul]
  simpa using Nat.mul_le_mul_left 2 (h d r)

theorem double_bits {F C : ℕ} (a : Block F C) (A : ℕ) (h : Bound A a) :
    (double a).bitSteps≤F*(C*(2*BackendScalarBits.backendScalarUnit (2*A).size)) := by
  apply mapBlock_bits
  exact fun d r => doubleCell_bits _ A (h d r)

theorem double_control {F C : ℕ} (a : Block F C) :
    (double a).control≤F*(C*44+40)+8 := mapBlock_control _ _ (fun _ _ => le_refl 12)

def scale {F C : ℕ} (channels : List Bool) (a : Block F C) : Run (Block F C) :=
  match channels with
  | [] => ⟨a,0,2⟩
  | b::bs =>
      let rest := scale bs a
      if b then ⟨rest.value,rest.bitSteps,rest.control+4⟩
      else let out := double rest.value
           ⟨out.value,rest.bitSteps+out.bitSteps,rest.control+out.control+4⟩

theorem scale_view {F C : ℕ} (channels : List Bool) (a : Block F C) (d : Fin F) (r : Fin C) :
    cellView (scale channels a).value d r=(channels.map (fun b => if b then (1:ℤ) else 2)).prod*cellView a d r := by
  induction channels with
  | nil => simp [scale]
  | cons b bs ih => cases b <;> simp [scale,double_view,ih,mul_assoc]

theorem scale_bound {F C : ℕ} (channels : List Bool) (a : Block F C) (A : ℕ) (h : Bound A a) :
    Bound (2^channels.length*A) (scale channels a).value := by
  induction channels with
  | nil => simpa [scale] using h
  | cons b bs ih =>
    cases b
    · have hh := double_bound _ (2^bs.length*A) ih
      change Bound (2^(bs.length+1)*A) (double (scale bs a).value).value
      convert hh using 1
      rw [pow_succ]
      ring
    · intro d r
      apply (ih d r).trans
      simp only [List.length_cons,pow_succ]
      nlinarith [Nat.zero_le (2^bs.length*A)]

theorem scale_bits {F C : ℕ} (channels : List Bool) (a : Block F C) (A M : ℕ)
    (hm : channels.length≤M) (ha : Bound A a) :
    (scale channels a).bitSteps≤channels.length*(F*(C*(2*BackendScalarBits.backendScalarUnit (2^M*A).size))) := by
  induction channels with
  | nil => simp [scale]
  | cons b bs ih =>
    have hr := ih (by simp only [List.length_cons] at hm; omega)
    have hh := double_bits _ (2^bs.length*A) (scale_bound bs a A ha)
    have hu : BackendScalarBits.backendScalarUnit (2*(2^bs.length*A)).size≤BackendScalarBits.backendScalarUnit (2^M*A).size := by
      apply BinaryResidualContraction.unit_mono
      apply Nat.size_le_size
      calc
        _ = 2^(bs.length+1)*A := by rw [pow_succ]; ring
        _ ≤ _ := Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by decide) hm)
    have hd : (double (scale bs a).value).bitSteps≤F*(C*(2*BackendScalarBits.backendScalarUnit (2^M*A).size)) :=
      hh.trans (by gcongr)
    cases b <;> simp only [scale,List.length_cons,Bool.false_eq_true,↓reduceIte] <;> nlinarith

theorem scale_control {F C : ℕ} (channels : List Bool) (a : Block F C) :
    (scale channels a).control≤channels.length*(F*(C*44+40)+12)+2 := by
  induction channels with
  | nil => simp [scale]
  | cons b bs ih =>
    have h := double_control (scale bs a).value
    cases b <;> simp only [scale,List.length_cons,Bool.false_eq_true,↓reduceIte] <;> nlinarith

def assembledRead {L m k C : ℕ} (F : ℕ) (layout : ResidualLayout.Stored L)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (word : Vector NormalLetter m) : Run (Block F C) :=
  let physical := ResidualLayout.assembleWord layout word.toArray rest.toArray NormalLetter.x1
  let out := BinaryResidualLeaf.execute F capCell raw physical.value opposite
  ⟨out.value,out.bitSteps,physical.control+out.control+4⟩

theorem assembledRead_bound {L m k C F : ℕ} (layout : ResidualLayout.Stored L)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (word : Vector NormalLetter m) (A : ℕ)
    (ha : BinaryResidualLeaf.RawBound raw A) : Bound A (assembledRead F layout rest capCell raw opposite word).value :=
  BinaryResidualLeaf.execute_bound _ _ _ _ A ha

theorem assembledRead_bits {L m k C F : ℕ} (layout : ResidualLayout.Stored L)
    (rest : Vector NormalLetter k) (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ))
    (raw : BinarySourceFormation.RawStore L C) (opposite : Vector OppositeLetter L)
    (word : Vector NormalLetter m) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (assembledRead F layout rest capCell raw opposite word).bitSteps≤BinaryResidualLeaf.bitBudget L C F cap A :=
  BinaryResidualLeaf.execute_bits cap capCell hc raw _ opposite A ha

theorem assembledRead_control {L m k C F : ℕ} (layout : ResidualLayout.Stored L)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (word : Vector NormalLetter m) :
    (assembledRead F layout rest capCell raw opposite word).control≤
      BinaryResidualLeaf.controlBudget L C F+38*L+12 := by
  have hp := ResidualLayout.assembleWord_control layout word.toArray rest.toArray NormalLetter.x1
  have he := BinaryResidualLeaf.execute_control (F:=F) capCell raw
    (ResidualLayout.assembleWord layout word.toArray rest.toArray NormalLetter.x1).value opposite
  simp only [assembledRead]
  omega

theorem assembledRead_view {L C F : ℕ} (mask : Vector Bool L)
    (rest : Vector NormalLetter (ResidualLayout.remaining mask).length)
    (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ)) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (word : Vector NormalLetter (ResidualLayout.selected mask).length)
    (d : Fin F) (r : Fin C) :
    cellView (assembledRead F (ResidualLayout.build mask).value rest capCell raw opposite word).value d r =
      if d.val=0 then cropBoth cap (fun n o => view (BinarySourceFormation.readRaw raw n o r))
        (assemble (ResidualLayout.equivalence mask) word.get rest.get) opposite.get else 0 := by
  have hw : (ResidualLayout.assembleWord (ResidualLayout.build mask).value word.toArray rest.toArray NormalLetter.x1).value.get =
      assemble (ResidualLayout.equivalence mask) word.get rest.get := by
    funext i
    exact ResidualLayout.assembleWord_value mask word rest NormalLetter.x1 i
  simp only [assembledRead,BinaryResidualLeaf.execute_view cap capCell hc,hw]

def normal {L m k C : ℕ} (F : ℕ) (layout : ResidualLayout.Stored L) (channels : Vector Bool m)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) : Run (Block F C) :=
  BinaryResidualContraction.evaluate m channels (assembledRead F layout rest capCell raw opposite)

theorem normal_bound {L m k C F : ℕ} (layout : ResidualLayout.Stored L) (channels : Vector Bool m)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    Bound (4^m*A) (normal F layout channels rest capCell raw opposite).value :=
  BinaryResidualContraction.evaluate_bound m channels _ A (fun w => assembledRead_bound layout rest capCell raw opposite w A ha)

def normalBits (L m C F cap A : ℕ) : ℕ :=
  3^m*(BinaryResidualLeaf.bitBudget L C F cap A+m*BinaryResidualContraction.nodeBits F C m A)
def normalControl (L m C F : ℕ) : ℕ :=
  3^m*(BinaryResidualLeaf.controlBudget L C F+38*L+14+m*BinaryResidualContraction.nodeControl F C m)

theorem normal_bits {L m k C F : ℕ} (layout : ResidualLayout.Stored L) (channels : Vector Bool m)
    (rest : Vector NormalLetter k) (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ))
    (raw : BinarySourceFormation.RawStore L C) (opposite : Vector OppositeLetter L)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (normal F layout channels rest capCell raw opposite).bitSteps≤normalBits L m C F cap A :=
  BinaryResidualContraction.evaluate_bits m m (le_refl m) channels _ A _
    (fun w => assembledRead_bound layout rest capCell raw opposite w A ha)
    (fun w => assembledRead_bits layout rest cap capCell hc raw opposite w A ha)

theorem normal_control {L m k C F : ℕ} (layout : ResidualLayout.Stored L) (channels : Vector Bool m)
    (rest : Vector NormalLetter k) (capCell : Cell) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) :
    (normal F layout channels rest capCell raw opposite).control≤normalControl L m C F := by
  have h := BinaryResidualContraction.evaluate_control m m (le_refl m) channels _ _
    (fun w => assembledRead_control (F:=F) layout rest capCell raw opposite w)
  convert h using 1
  · rfl
  · unfold normalControl
    ring

noncomputable def sourcePolynomial {L C : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter) : Polynomial (CyclicRing.Cyclic C) :=
  Polynomial.C (fun r => cropBoth cap (fun nn oo => view (BinarySourceFormation.readRaw raw nn oo r)) n o)

theorem normal_coeff {L C F : ℕ} [NeZero C] (mask : Vector Bool L)
    (channels : Vector Bool (ResidualLayout.selected mask).length)
    (rest : Vector NormalLetter (ResidualLayout.remaining mask).length)
    (cap : ℕ) (capCell : Cell) (hc : view capCell=(cap:ℤ)) (raw : BinarySourceFormation.RawStore L C)
    (opposite : Vector OppositeLetter L) (d : Fin F) (r : Fin C) :
    cellView (normal F (ResidualLayout.build mask).value channels rest capCell raw opposite).value d r =
      ((DistinguishedResidualRoot.contract channels.get Polynomial.X
        (fun n => sourcePolynomial cap raw (assemble (ResidualLayout.equivalence mask) n rest.get) opposite.get)).coeff d.val) r := by
  apply BinaryResidualContraction.evaluate_coeff
  intro w dd rr
  rw [assembledRead_view mask rest cap capCell hc raw opposite w dd rr]
  by_cases hd : dd.val=0 <;> simp [sourcePolynomial,Polynomial.coeff_C,hd]

def oppositeWord {L : ℕ} (mask : Vector Bool L)
    (channels : Vector Bool (ResidualLayout.selected mask).length)
    (rest : Vector (Fin 3) (ResidualLayout.remaining mask).length) : Run (Vector OppositeLetter L) :=
  ResidualLayout.assembleWord (ResidualLayout.build mask).value
    (channels.map DistinguishedResidualRoot.oppositeLetter).toArray
    (rest.map SourceCoordinates.oppositeEquiv).toArray OppositeLetter.s

theorem oppositeWord_get {L : ℕ} (mask : Vector Bool L)
    (channels : Vector Bool (ResidualLayout.selected mask).length)
    (rest : Vector (Fin 3) (ResidualLayout.remaining mask).length) :
    (oppositeWord mask channels rest).value.get = assemble (ResidualLayout.equivalence mask)
      (fun i => DistinguishedResidualRoot.oppositeLetter (channels.get i))
      (fun i => SourceCoordinates.oppositeEquiv (rest.get i)) := by
  funext i
  rw [oppositeWord,ResidualLayout.assembleWord_value]
  unfold assemble
  cases ResidualLayout.equivalence mask i <;> simp

/-- One retained F-by-C residual row for a fixed remaining ternary word.
Both layouts and the binary cap are built here from original inputs. -/
def execute {L C : ℕ} (F cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) : Run (Block F C) :=
  let nlayout := ResidualLayout.build maskN
  let olayout := ResidualLayout.build maskO
  let rest := wn.map normalRemaining
  let odist := co.map DistinguishedResidualRoot.oppositeLetter
  let orest := wo.map SourceCoordinates.oppositeEquiv
  let opposite := ResidualLayout.assembleWord olayout.value odist.toArray orest.toArray OppositeLetter.s
  let capCell := BinaryMultiplierAdapter.encodeInteger (cap:ℤ)
  let out := normal F nlayout.value cn rest capCell.value raw opposite.value
  let scaled := scale co.toList out.value
  ⟨scaled.value,nlayout.bitSteps+olayout.bitSteps+capCell.bitSteps+out.bitSteps+scaled.bitSteps,
    nlayout.control+olayout.control+opposite.control+out.control+scaled.control+24*L+24⟩

def bitBudget (L mN mO C F cap A : ℕ) : ℕ :=
  2*(L*ResidualLayout.locateBudget L)+10*(cap.size+1)^2+normalBits L mN C F cap A+
    mO*(F*(C*(2*BackendScalarBits.backendScalarUnit (2^mO*(4^mN*A)).size)))
def controlBudget (L mN mO C F : ℕ) : ℕ :=
  2*(L*(8*L+66)+20)+38*L+8+normalControl L mN C F+
    (mO*(F*(C*44+40)+12)+2)+24*L+24

theorem execute_bound {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    Bound (2^(ResidualLayout.selected maskO).length*(4^(ResidualLayout.selected maskN).length*A))
      (execute F cap raw maskN maskO cn co wn wo).value := by
  have h := normal_bound (F:=F) (ResidualLayout.build maskN).value cn (wn.map normalRemaining)
    (BinaryMultiplierAdapter.encodeInteger (cap:ℤ)).value raw (oppositeWord maskO co wo).value A ha
  simpa only [execute,Vector.length_toList,oppositeWord] using scale_bound co.toList _ _ h

theorem execute_width {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) (d : Fin F) (r : Fin C) :
    (cellView (execute F cap raw maskN maskO cn co wn wo).value d r).natAbs.size≤
      (ResidualLayout.selected maskO).length+2*(ResidualLayout.selected maskN).length+A.size := by
  apply BinaryWalshBounds.natAbs_size_of_le_power_mul
  have h := execute_bound (F:=F) cap raw maskN maskO cn co wn wo A ha d r
  convert h using 1
  rw [pow_add,pow_mul]
  norm_num
  ring

theorem execute_bits {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length)
    (A : ℕ) (ha : BinaryResidualLeaf.RawBound raw A) :
    (execute F cap raw maskN maskO cn co wn wo).bitSteps≤
      bitBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length C F cap A := by
  have hn := ResidualLayout.build_bits maskN
  have ho := ResidualLayout.build_bits maskO
  have hc := BinaryMultiplierAdapter.encodeInteger_cost (cap:ℤ)
  have hr := normal_bits (F:=F) (ResidualLayout.build maskN).value cn (wn.map normalRemaining)
    cap _ (BinaryMultiplierAdapter.encodeInteger_view _) raw (oppositeWord maskO co wo).value A ha
  have hb := normal_bound (F:=F) (ResidualLayout.build maskN).value cn (wn.map normalRemaining)
    (BinaryMultiplierAdapter.encodeInteger (cap:ℤ)).value raw (oppositeWord maskO co wo).value A ha
  have hs := scale_bits co.toList _ _ (ResidualLayout.selected maskO).length (by simp) hb
  simp only [Vector.length_toList,Int.natAbs_natCast,oppositeWord] at hc hr hs
  simp only [execute,bitBudget]
  omega

theorem execute_control {L C F : ℕ} (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) :
    (execute F cap raw maskN maskO cn co wn wo).control≤
      controlBudget L (ResidualLayout.selected maskN).length (ResidualLayout.selected maskO).length C F := by
  have hn := ResidualLayout.build_control maskN
  have ho := ResidualLayout.build_control maskO
  have hp := ResidualLayout.assembleWord_control (ResidualLayout.build maskO).value
    (co.map DistinguishedResidualRoot.oppositeLetter).toArray
    (wo.map SourceCoordinates.oppositeEquiv).toArray OppositeLetter.s
  have hr := normal_control (F:=F) (ResidualLayout.build maskN).value cn (wn.map normalRemaining)
    (BinaryMultiplierAdapter.encodeInteger (cap:ℤ)).value raw (oppositeWord maskO co wo).value
  have hs := scale_control co.toList (normal F (ResidualLayout.build maskN).value cn (wn.map normalRemaining)
    (BinaryMultiplierAdapter.encodeInteger (cap:ℤ)).value raw (oppositeWord maskO co wo).value).value
  simp only [Vector.length_toList,oppositeWord] at hr hs
  simp only [execute,controlBudget]
  omega

theorem execute_coeff {L C F : ℕ} [NeZero C] (cap : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) (d : Fin F) (r : Fin C) :
    cellView (execute F cap raw maskN maskO cn co wn wo).value d r =
      (co.toList.map (fun b => if b then (1:ℤ) else 2)).prod *
      ((DistinguishedResidualRoot.contract cn.get Polynomial.X (fun n => sourcePolynomial cap raw
        (assemble (ResidualLayout.equivalence maskN) n (fun i => normalRemaining (wn.get i)))
        (assemble (ResidualLayout.equivalence maskO)
          (fun i => DistinguishedResidualRoot.oppositeLetter (co.get i))
          (fun i => SourceCoordinates.oppositeEquiv (wo.get i))))).coeff d.val) r := by
  have hw : (wn.map normalRemaining).get=(fun i => normalRemaining (wn.get i)) := by funext i; simp
  simp only [execute,scale_view]
  have h := normal_coeff (F:=F) maskN cn (wn.map normalRemaining) cap _
    (BinaryMultiplierAdapter.encodeInteger_view _) raw (oppositeWord maskO co wo).value d r
  rw [oppositeWord_get,hw] at h
  exact congrArg (fun x => (co.toList.map (fun b => if b then (1:ℤ) else 2)).prod*x) h

#print axioms doubleCell_view
#print axioms doubleCell_bits
#print axioms double_view
#print axioms double_bound
#print axioms double_bits
#print axioms double_control
#print axioms scale_view
#print axioms scale_bound
#print axioms scale_bits
#print axioms scale_control
#print axioms assembledRead_bound
#print axioms assembledRead_bits
#print axioms assembledRead_control
#print axioms assembledRead_view
#print axioms normal_bound
#print axioms normal_bits
#print axioms normal_control
#print axioms normal_coeff
#print axioms oppositeWord_get
#print axioms execute_bound
#print axioms execute_width
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_coeff
end ThinMatrix.BinaryResidualRootProgram
