import BinaryHighExecution

/-!
# Bit costs of the persistent HIGH base encoder

Local costs are derived from the concrete canonical-cell scalar programs,
materialized contractions, key tests, and retained intermediate arrays.
Magnitude bounds propagate from the original raw cells; callers do not
supply a bound on an already-computed output.
-/

namespace ThinMatrix.BinaryHighCost
open scoped BigOperators
open BinaryCell FFTBitCost
open BinaryHighExecution
open SharedEncoder (Dense read volume Coordinates)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def DenseBound {q n : ℕ} {dims : Fin n→ℕ} (input : BinaryDense q n dims) (A : ℕ) : Prop :=
  ∀ c : Coordinates dims,∀r : Fin q,|BinaryCell.view ((read n dims input c).get r)|≤(A:ℤ)

theorem read_materialize_value {q : ℕ} (n : ℕ) (dims : Fin n→ℕ)
    (f : Coordinates dims→Result (Payload q)) (c : Coordinates dims) :
    read n dims (BinaryHighExecution.materialize n dims f).value c=(f c).value := by
  induction n with
  | zero =>
    simp only [BinaryHighExecution.materialize,SharedEncoder.read]
    have hc : (fun i : Fin 0=>Fin.elim0 i)=c := by
      funext i
      exact Fin.elim0 i
    rw [hc]
  | succ n ih =>
    simp only [BinaryHighExecution.materialize,tabulate_value,SharedEncoder.read,Vector.get_ofFn]
    have h:=ih (fun i=>dims i.succ) (fun rest=>f (Fin.cons (c 0) rest)) (fun i=>c i.succ)
    have hc : Fin.cons (c 0) (fun i=>c i.succ)=c := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    rw [hc] at h
    exact h

theorem dotVector_bit_price {q a : ℕ} (weights : Fin a→BinaryCell.Cell)
    (values : Fin a→Payload q) (A : ℕ) (ha : a≤4)
    (hw : ∀i,|BinaryCell.view (weights i)|≤2)
    (hx : ∀i r,|BinaryCell.view ((values i).get r)|≤(A:ℤ)) :
    (dotVector weights values).bitSteps≤q*(21*BackendScalarBits.backendScalarUnit (A.size+5)+2) := by
  unfold dotVector
  apply tabulate_bitSteps_le
  intro r
  have hd:=dot_bit_price
    ((List.finRange a).map (fun i=>(weights i,(values i).get r))) A
    (by simpa using ha)
    (by
      intro z hz
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp hz
      exact hw i)
    (by
      intro z hz
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp hz
      exact hx i r)
  simp only [List.length_map,List.length_finRange] at hd
  exact hd.trans (Nat.mul_le_mul_right _ (by omega))

theorem dotVector_magnitude {q a : ℕ} (weights : Fin a→BinaryCell.Cell)
    (values : Fin a→Payload q) (A : ℕ) (ha : a≤4)
    (hw : ∀i,|BinaryCell.view (weights i)|≤2)
    (hx : ∀i r,|BinaryCell.view ((values i).get r)|≤(A:ℤ)) (r : Fin q) :
    |BinaryCell.view ((dotVector weights values).value.get r)|≤((8*A:ℕ):ℤ) := by
  simp only [dotVector,tabulate_value,Vector.get_ofFn]
  have hm:=dot_magnitude
    ((List.finRange a).map (fun i=>(weights i,(values i).get r))) A
    (by
      intro z hz
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp hz
      exact hw i)
    (by
      intro z hz
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp hz
      exact hx i r)
  simp only [List.length_map,List.length_finRange] at hm
  apply hm.trans
  exact_mod_cast (show 2*a*A≤8*A by nlinarith)

theorem contract_bit_price {q n : ℕ} (dims : Fin (n+1)→ℕ)
    (form : Fin (dims 0)→BinaryCell.Cell) (input : BinaryDense q (n+1) dims)
    (A : ℕ) (hpos : ∀i,0<dims i) (hhead : dims 0≤4)
    (hf : ∀i,|BinaryCell.view (form i)|≤2) (hi : DenseBound input A) :
    (BinaryHighExecution.contract dims form input).bitSteps≤
      volume n (fun i=>dims i.succ)*
        (q*(21*BackendScalarBits.backendScalarUnit (A.size+5)+2)+q*(n+2)*dims 0+2*n) := by
  unfold BinaryHighExecution.contract
  apply materialize_steps_le
  · intro rest
    change (dotVector form (fun a=>read (n+1) dims input (Fin.cons a rest))).bitSteps+
      q*(n+2)*dims 0≤_
    exact Nat.add_le_add_right
      (dotVector_bit_price form _ A hhead hf (fun a r=>hi (Fin.cons a rest) r)) _
  · exact fun i=>hpos i.succ

theorem contract_magnitude {q n : ℕ} (dims : Fin (n+1)→ℕ)
    (form : Fin (dims 0)→BinaryCell.Cell) (input : BinaryDense q (n+1) dims)
    (A : ℕ) (hhead : dims 0≤4)
    (hf : ∀i,|BinaryCell.view (form i)|≤2) (hi : DenseBound input A) :
    DenseBound (BinaryHighExecution.contract dims form input).value (8*A) := by
  intro c r
  unfold BinaryHighExecution.contract
  rw [read_materialize_value]
  exact dotVector_magnitude form _ A hhead hf (fun a r=>hi (Fin.cons a c) r) r

#print axioms contract_bit_price
#print axioms contract_magnitude
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryCell FFTBitCost BinaryHighExecution
open SharedEncoder (Dense read volume Coordinates)

theorem makeChild_steps_le {q : ℕ} (L m t d n : ℕ) (hd : d<2*L)
    (dims : Fin (n+1)→ℕ) (forms : Forms)
    (parent : Node q (2*L) (n+1) dims) (a : Fin 5) (C : ℕ)
    (hc : (contract dims (fun b=>forms d (HighBaseEncoder.baseLabel a) b.val)
      parent.data).bitSteps ≤ C) :
    (makeChild L m t d n hd dims forms parent a).bitSteps ≤ C+10*L+2 := by
  dsimp only [makeChild]
  split <;> simp only [ArrayKeys.baseTest_work] <;> omega

theorem nodeChildren_steps_le {q : ℕ} (L m t d n : ℕ) (hd : d<2*L)
    (dims : Fin (n+1)→ℕ) (forms : Forms)
    (parent : Node q (2*L) (n+1) dims) (C : ℕ)
    (hc : ∀ a : Fin 5,
      (contract dims (fun b=>forms d (HighBaseEncoder.baseLabel a) b.val)
        parent.data).bitSteps ≤ C) :
    (nodeChildren L m t d n hd dims forms parent).bitSteps ≤ 5*C+50*L+25 := by
  have ht := tabulate_bitSteps_le 5 (C+10*L+2)
    (makeChild L m t d n hd dims forms parent)
    (fun a=>makeChild_steps_le L m t d n hd dims forms parent a C (hc a))
  simp only [nodeChildren]
  omega

theorem local_children_arithmetic (L n a q U V : ℕ)
    (hn : n≤2*L) (ha : a≤4) (hapos : 1≤a) (hq : 1≤q)
    (hU : 1≤U) (hV : 1≤V) :
    5*(V*(q*(21*U+2)+q*(n+2)*a+2*n))+50*L+25 ≤
      1000*(2*L+1)*U*q*(a*V) := by
  have hscalar : 21*U+2 ≤ 23*U := by omega
  have hscalarq := Nat.mul_le_mul_left q hscalar
  have hother : (n+2)*a+2*n ≤ 12*L+8 := by
    have := Nat.mul_le_mul_left (n+2) ha
    omega
  have hinner : q*(21*U+2)+q*(n+2)*a+2*n ≤ 23*U*q+q*(12*L+8) := by
    have h:=Nat.mul_le_mul_left q hother
    nlinarith
  have hUq : 1≤U*q := by nlinarith
  have hlinear := Nat.mul_le_mul_left (q*(12*L+8)) hU
  have hcap : 23*U*q+q*(12*L+8) ≤ (12*L+31)*(U*q) := by nlinarith
  have hparent : V≤a*V := by nlinarith
  have hcost : V*(q*(21*U+2)+q*(n+2)*a+2*n) ≤
      (a*V)*((12*L+31)*(U*q)) := by
    exact (Nat.mul_le_mul_left V hinner).trans
      ((Nat.mul_le_mul_left V hcap).trans (Nat.mul_le_mul_right _ hparent))
  have hunit : 1≤(a*V)*(U*q) := by
    have := Nat.mul_le_mul_right (U*q) hparent
    nlinarith
  have hover := Nat.mul_le_mul_left (50*L+25) hunit
  have hfinal : (110*L+180)≤1000*(2*L+1) := by omega
  have hfinal' := Nat.mul_le_mul_right ((a*V)*(U*q)) hfinal
  nlinarith

theorem nodeChildren_bit_price {q : ℕ}
    (L m t d n A : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims)
    (hq : 1≤q) (hn : n≤2*L) (hpos : ∀i,0<dims i) (hhead : dims 0≤4)
    (hf : ∀a : Fin 5,∀b : Fin (dims 0),
      |BinaryCell.view (forms d (HighBaseEncoder.baseLabel a) b.val)|≤2)
    (hi : DenseBound parent.data A) :
    (nodeChildren L m t d n hd dims forms parent).bitSteps ≤
      1000*(2*L+1)*BackendScalarBits.backendScalarUnit (A.size+5)*q*
        volume (n+1) dims := by
  have hv : 1≤volume n (fun i=>dims i.succ) := by
    have hp : 0<volume n (fun i=>dims i.succ) := by
      unfold volume
      exact Finset.prod_pos (fun i _ => hpos i.succ)
    omega
  have hU : 1≤BackendScalarBits.backendScalarUnit (A.size+5) := by
    have hp : 0<(A.size+5+1)^2 := by positivity
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    omega
  have hs : volume (n+1) dims=dims 0*volume n (fun i=>dims i.succ) :=
    Fin.prod_univ_succ dims
  apply (nodeChildren_steps_le L m t d n hd dims forms parent _
    (fun a=>contract_bit_price dims _ parent.data A hpos hhead (hf a) hi)).trans
  rw [hs]
  exact local_children_arithmetic L n (dims 0) q
    (BackendScalarBits.backendScalarUnit (A.size+5)) (volume n (fun i=>dims i.succ))
    hn hhead (by have := hpos 0;omega) hq hU hv

theorem makeChild_some_magnitude {q : ℕ}
    (L m t d n A : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims) (a : Fin 5)
    (child : Node q (2*L) n (fun i=>dims i.succ))
    (hhead : dims 0≤4)
    (hf : ∀b : Fin (dims 0),
      |BinaryCell.view (forms d (HighBaseEncoder.baseLabel a) b.val)|≤2)
    (hi : DenseBound parent.data A)
    (hc : (makeChild L m t d n hd dims forms parent a).value=some child) :
    DenseBound child.data (8*A) := by
  dsimp only [makeChild] at hc
  split at hc
  · simp only [Option.some.injEq] at hc
    cases hc
    exact contract_magnitude dims _ parent.data A hhead hf hi
  · simp at hc

theorem nodeChildren_mem {q : ℕ}
    (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims)
    (child : Node q (2*L) n (fun i=>dims i.succ)) :
    child∈(nodeChildren L m t d n hd dims forms parent).value ↔
      ∃a : Fin 5,(makeChild L m t d n hd dims forms parent a).value=some child := by
  simp only [nodeChildren,tabulate_value,Vector.toList_ofFn,
    List.mem_filterMap,List.mem_ofFn,id_eq]
  aesop

#print axioms nodeChildren_bit_price
#print axioms makeChild_some_magnitude
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost

def commonWidth (L A : ℕ) : ℕ := 6*L+A.size+10
def runFactor (L U : ℕ) : ℕ := 10000*(2*L+1)^2*U

theorem backendUnit_one_le (B : ℕ) : 1≤BackendScalarBits.backendScalarUnit B := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  have h:=Nat.one_le_pow 2 (B+1) (by omega)
  omega

theorem backendUnit_mono {B C : ℕ} (h : B≤C) :
    BackendScalarBits.backendScalarUnit B≤BackendScalarBits.backendScalarUnit C := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

theorem scaled_magnitude_size (d A : ℕ) : (8^d*A).size≤3*d+A.size := by
  apply Nat.size_le.mpr
  calc
    8^d*A <8^d*2^A.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self A) (by positivity)
    _ =2^(3*d+A.size) := by
      rw [show (8:ℕ)=2^3 by norm_num,←pow_mul,←pow_add]

theorem scaled_width_common (L d A : ℕ) (hd : d≤2*L) :
    (8^d*A).size+5≤commonWidth L A := by
  have h:=scaled_magnitude_size d A
  unfold commonWidth
  omega

set_option maxHeartbeats 1000000 in
theorem run_step_arithmetic (L n q U V P : ℕ)
    (hn : n≤2*L) (hq : 1≤q) (hU : 1≤U) (hV : 1≤V) :
    ((1000*(2*L+1)*U*q*V+6)*P+1)+(q+2*L+n+3)*P+1≤
      runFactor L U*(70*q*P*V+1) := by
  calc
    _ ≤ ((1000*(2*L+1)*U*q*V+6)*P+1)+(q+2*L+2*L+3)*P+1 := by gcongr
    _ ≤ _ := by
      obtain ⟨a,rfl⟩ :∃a,q=a+1:=⟨q-1,by omega⟩
      obtain ⟨b,rfl⟩ :∃b,U=b+1:=⟨U-1,by omega⟩
      obtain ⟨c,rfl⟩ :∃c,V=c+1:=⟨V-1,by omega⟩
      unfold runFactor
      ring_nf
      omega

theorem run_metadata_arithmetic (L n q U V P : ℕ)
    (hn : n≤2*L) (hq : 1≤q) (hU : 1≤U) (hV : 1≤V) :
    (q+2*L+n+3)*P+1≤runFactor L U*(70*q*P*V+1) := by
  have h:=run_step_arithmetic L n q U V P hn hq hU hV
  omega

#print axioms scaled_width_common
#print axioms run_step_arithmetic
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryCell FFTBitCost BinaryHighExecution

theorem nodeChildren_length_le {q : ℕ} (L m t d n : ℕ) (hd : d<2*L)
    (dims : Fin (n+1)→ℕ) (forms : Forms)
    (parent : Node q (2*L) (n+1) dims) :
    (nodeChildren L m t d n hd dims forms parent).value.length≤5 := by
  dsimp only [nodeChildren]
  apply (List.length_filterMap_le _ _).trans
  simp

theorem nextLayer_bitSteps_le {q : ℕ} (L m t d n : ℕ) (hd : d<2*L)
    (dims : Fin (n+1)→ℕ) (forms : Forms)
    (parents : List (Node q (2*L) (n+1) dims)) (C : ℕ)
    (hc : ∀parent∈parents,
      (nodeChildren L m t d n hd dims forms parent).bitSteps≤C) :
    (nextLayer L m t d n hd dims forms parents).bitSteps≤
      (C+6)*parents.length+1 := by
  induction parents with
  | nil => simp [nextLayer]
  | cons parent parents ih =>
    have hp:=hc parent (by simp)
    have ht:=ih (fun p hp=>hc p (by simp [hp]))
    have hl:=nodeChildren_length_le L m t d n hd dims forms parent
    simp only [nextLayer,List.length_cons]
    rw [Nat.mul_succ]
    omega

theorem nextLayer_DenseBound {q : ℕ} (L m t d n A : ℕ) (hd : d<2*L)
    (dims : Fin (n+1)→ℕ) (forms : Forms)
    (parents : List (Node q (2*L) (n+1) dims))
    (hhead : dims 0≤4)
    (hf : ∀a : Fin 5,∀b : Fin (dims 0),
      |BinaryCell.view (forms d (HighBaseEncoder.baseLabel a) b.val)|≤2)
    (hi : ∀parent∈parents,DenseBound parent.data A) :
    ∀child∈(nextLayer L m t d n hd dims forms parents).value,
      DenseBound child.data (8*A) := by
  induction parents with
  | nil => simp [nextLayer]
  | cons parent parents ih =>
    intro child hc
    simp only [nextLayer,List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨a,ha⟩ :=
        (nodeChildren_mem L m t d n hd dims forms parent child).mp hc
      exact makeChild_some_magnitude L m t d n A hd dims forms parent a child hhead
        (hf a) (hi parent (by simp)) ha
    · exact ih (fun p hp=>hi p (by simp [hp])) child hc

end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryHighExecution
open SharedEncoder (volume Coordinates)
open scoped BigOperators
noncomputable section

def nativeRun {q : ℕ} (L m t : ℕ) (forms : Forms)
    (n : ℕ) (dims : Fin n→ℕ) (d : ℕ) (parents : List (Node q (2*L) n dims)) :=
  HighBaseEncoder.run L m t q 1 (nativeForms forms q) n dims d (parents.map nodeView)

theorem run_bit_price {q : ℕ} (L m t A : ℕ) (forms : Forms)
    (n : ℕ) (dims : Fin n→ℕ) (d : ℕ) (parents : List (Node q (2*L) n dims))
    (hq : 1≤q) (hdepth : d+n≤2*L)
    (hdims : ∀i,1≤dims i ∧ dims i≤4)
    (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hp : ∀parent∈parents,DenseBound parent.data (8^d*A)) :
    (BinaryHighExecution.run L m t forms n dims d parents).bitSteps≤
      runFactor L (BackendScalarBits.backendScalarUnit (commonWidth L A))*
        ((nativeRun L m t forms n dims d parents).coefficientWork+
          (nativeRun L m t forms n dims d parents).capWork+n+1) := by
  let U:=BackendScalarBits.backendScalarUnit (commonWidth L A)
  have hU : 1≤U:=backendUnit_one_le _
  change _≤runFactor L U*_
  induction n generalizing d with
  | zero =>
    have h:=run_metadata_arithmetic L 0 q U 1 parents.length (by omega) hq hU (by omega)
    simp only [BinaryHighExecution.run,nativeRun,HighBaseEncoder.run,
      List.length_map,volume,Fin.prod_univ_zero,Nat.mul_one,Nat.add_zero]
    nlinarith
  | succ n ih =>
    have hd : d<2*L:=by omega
    let kids:=nextLayer L m t d n hd dims forms parents
    have hkids : ∀child∈kids.value,DenseBound child.data (8^(d+1)*A) := by
      have h:=nextLayer_DenseBound L m t d n (8^d*A) hd dims forms parents
        (hdims 0).2 (fun a b=>hf d _ _) hp
      simpa only [pow_succ',Nat.mul_assoc] using h
    have ht:=ih (fun i=>dims i.succ) (d+1) kids.value
      (by omega) (fun i=>hdims i.succ) hkids
    have hv : 1≤volume (n+1) dims := by
      have hpos :0<volume (n+1) dims := by
        unfold volume
        exact Finset.prod_pos (fun i _=>by have h:=(hdims i).1;omega)
      omega
    have hc : kids.bitSteps≤
        (1000*(2*L+1)*U*q*volume (n+1) dims+6)*parents.length+1 := by
      apply nextLayer_bitSteps_le L m t d n hd dims forms parents
      intro parent hparent
      have h:=nodeChildren_bit_price L m t d n (8^d*A) hd dims forms parent
        hq (by omega) (fun i=>by have h:=(hdims i).1;omega) (hdims 0).2
        (fun a b=>hf d _ _) (hp parent hparent)
      exact h.trans (by
        apply Nat.mul_le_mul_right (volume (n+1) dims)
        apply Nat.mul_le_mul_right q
        apply Nat.mul_le_mul_left (1000*(2*L+1))
        exact backendUnit_mono (scaled_width_common L d A (by omega)))
    have ha:=run_step_arithmetic L n q U (volume (n+1) dims) parents.length
      (by omega) hq hU hv
    simp only [BinaryHighExecution.run,nativeRun,HighBaseEncoder.run,
      dif_pos hd,List.length_map,Nat.mul_one]
    rw [←nextLayer_view L m t d n hd dims forms parents]
    change kids.bitSteps+
        (BinaryHighExecution.run L m t forms n (fun i=>dims i.succ) (d+1) kids.value).bitSteps+
        (q+2*L+n+3)*parents.length+1≤
      runFactor L U*
        ((70*q*parents.length*volume (n+1) dims+
          (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).coefficientWork)+
         (5*parents.length*(1+4*(2*L))+
          (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).capWork)+(n+1)+1)
    calc
      _ ≤ ((1000*(2*L+1)*U*q*volume (n+1) dims+6)*parents.length+1)+
          (runFactor L U*((nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).coefficientWork+
            (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).capWork+n+1))+
          (q+2*L+n+3)*parents.length+1 := by gcongr
      _ = (((1000*(2*L+1)*U*q*volume (n+1) dims+6)*parents.length+1)+
          (q+2*L+n+3)*parents.length+1)+
          runFactor L U*((nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).coefficientWork+
            (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).capWork+n+1) := by ring
      _ ≤ runFactor L U*(70*q*parents.length*volume (n+1) dims+1)+
          runFactor L U*((nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).coefficientWork+
            (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).capWork+n+1) :=
        Nat.add_le_add_right ha _
      _ = runFactor L U*(70*q*parents.length*volume (n+1) dims+
          (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).coefficientWork+
          (nativeRun L m t forms n (fun i=>dims i.succ) (d+1) kids.value).capWork+n+2) := by ring
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        omega

#print axioms run_bit_price
end
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryHighExecution
open SharedEncoder (volume)
noncomputable section

def encoderFactor (L A : ℕ) : ℕ :=
  runFactor L (BackendScalarBits.backendScalarUnit (commonWidth L A))*(2*L+2)

theorem nativeRun_encode (L m t q : ℕ) (b : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b)) :
    nativeRun L m t forms (2*L) (HighBaseEncoder.rootDims L b) 0
      [⟨ArrayKeys.zero (2*L),input⟩]=
    HighBaseEncoder.encode L m t q 1 b (nativeForms forms q)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) input) := by
  simp only [nativeRun,HighBaseEncoder.encode,List.map_cons,List.map_nil,
    nodeView,ArrayKeys.toWord_zero]

theorem encode_coefficientWork_pos (L m t q : ℕ) (b : Bool)
    (forms : SharedEncoder.LocalForms (Vector ℤ q))
    (input : SharedEncoder.Dense (R:=Vector ℤ q) (2*L) (HighBaseEncoder.rootDims L b))
    (hq : 1≤q) :
    1≤(HighBaseEncoder.encode L m t q 1 b forms input).coefficientWork := by
  have hr:=native_run_root_work_le L m t q forms (2*L)
    (HighBaseEncoder.rootDims L b) 0 [⟨CappedEnumeration.zeroWord (2*L),input⟩]
  have hv : 1≤volume (2*L) (HighBaseEncoder.rootDims L b) := by
    apply Nat.one_le_iff_ne_zero.mpr
    unfold volume
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>by
      have h:=(shape_dims_bounds L b 0 (2*L) _ (HighBaseEncoder.root_shape L b) i).1
      omega)
  simp only [List.length_singleton,Nat.mul_one] at hr
  change 70*q*volume (2*L) (HighBaseEncoder.rootDims L b)≤
    (HighBaseEncoder.encode L m t q 1 b forms input).coefficientWork at hr
  nlinarith

theorem encode_bit_price (L m t q A : ℕ) (b : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b))
    (hq : 1≤q) (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hi : DenseBound input A) :
    (BinaryHighExecution.encode L m t q b forms input).bitSteps≤
      encoderFactor L A*
        ((HighBaseEncoder.encode L m t q 1 b (nativeForms forms q)
          (denseView (2*L) (HighBaseEncoder.rootDims L b) input)).coefficientWork+
         (HighBaseEncoder.encode L m t q 1 b (nativeForms forms q)
          (denseView (2*L) (HighBaseEncoder.rootDims L b) input)).capWork) := by
  have h:=run_bit_price L m t A forms (2*L) (HighBaseEncoder.rootDims L b) 0
    [⟨ArrayKeys.zero (2*L),input⟩] hq (by omega)
    (shape_dims_bounds L b 0 (2*L) _ (HighBaseEncoder.root_shape L b)) hf
    (by simpa only [List.mem_singleton,pow_zero,Nat.one_mul,forall_eq] using hi)
  rw [nativeRun_encode] at h
  have hp:=encode_coefficientWork_pos L m t q b (nativeForms forms q)
    (denseView (2*L) (HighBaseEncoder.rootDims L b) input) hq
  apply h.trans
  unfold encoderFactor
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

theorem copyPayload_bit_price {q : ℕ} (a : Payload q) (W : ℕ)
    (h : ∀r,(BinaryCell.view (a.get r)).natAbs.size≤W) :
    (copyPayload a).bitSteps≤q*(BackendScalarBits.backendScalarUnit W+2) := by
  apply tabulate_bitSteps_le
  intro r
  exact BinaryCell.copy_price W (a.get r) (h r)

theorem storeRows_bit_price {q N : ℕ} (rows : List (ArrayKeys.Key N×Payload q))
    (table : StoredHighDP.Trie (Payload q)) (W : ℕ)
    (h : ∀row∈rows,∀r,(BinaryCell.view (row.2.get r)).natAbs.size≤W) :
    (storeRows table rows).bitSteps≤
      rows.length*(q*(BackendScalarBits.backendScalarUnit W+2)+9*N+8)+1 := by
  induction rows generalizing table with
  | nil => simp only [storeRows,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons row rows ih =>
    have hc:=copyPayload_bit_price row.2 W (h row (by simp))
    have ht:=ih (ArrayKeys.write table row.1 (copyPayload row.2).value).1
      (fun a ha=>h a (by simp [ha]))
    simp only [storeRows,ArrayKeys.write_work,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

#print axioms encode_bit_price
#print axioms storeRows_bit_price
end
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryHighExecution
noncomputable section

theorem run_leaves_bound {q : ℕ} (L m t A : ℕ) (forms : Forms)
    (n : ℕ) (dims : Fin n→ℕ) (d : ℕ) (parents : List (Node q (2*L) n dims))
    (hdepth : d+n≤2*L) (hdims : ∀i,1≤dims i ∧ dims i≤4)
    (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hp : ∀parent∈parents,DenseBound parent.data (8^d*A)) :
    ∀row∈(BinaryHighExecution.run L m t forms n dims d parents).leaves,
      ∀r : Fin q,|BinaryCell.view (row.2.get r)|≤((8^(d+n)*A:ℕ):ℤ) := by
  induction n generalizing d with
  | zero =>
    intro row hrow r
    simp only [BinaryHighExecution.run] at hrow
    obtain ⟨parent,hparent,rfl⟩:=List.mem_map.mp hrow
    simpa only [Nat.add_zero,SharedEncoder.read] using
      hp parent hparent (fun i=>Fin.elim0 i) r
  | succ n ih =>
    have hd : d<2*L:=by omega
    have hk : ∀child∈(nextLayer L m t d n hd dims forms parents).value,
        DenseBound child.data (8^(d+1)*A) := by
      have h:=nextLayer_DenseBound L m t d n (8^d*A) hd dims forms parents
        (hdims 0).2 (fun a b=>hf d _ _) hp
      simpa only [pow_succ',Nat.mul_assoc] using h
    have ht:=ih (fun i=>dims i.succ) (d+1)
      (nextLayer L m t d n hd dims forms parents).value
      (by omega) (fun i=>hdims i.succ) hk
    simp only [BinaryHighExecution.run,dif_pos hd]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem encode_leaves_bound (L m t q A : ℕ) (b : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b))
    (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hi : DenseBound input A) :
    ∀row∈(BinaryHighExecution.encode L m t q b forms input).leaves,
      ∀r : Fin q,|BinaryCell.view (row.2.get r)|≤((8^(2*L)*A:ℕ):ℤ) := by
  have h:=run_leaves_bound L m t A forms (2*L) (HighBaseEncoder.rootDims L b) 0
    [⟨ArrayKeys.zero (2*L),input⟩] (by omega)
    (shape_dims_bounds L b 0 (2*L) _ (HighBaseEncoder.root_shape L b)) hf
    (by simpa only [List.mem_singleton,pow_zero,Nat.one_mul,forall_eq] using hi)
  simpa only [BinaryHighExecution.encode,Nat.zero_add] using h

def storedFactor (L A : ℕ) : ℕ :=
  encoderFactor L A+BackendScalarBits.backendScalarUnit (commonWidth L A)+5

theorem encodeStored_bit_price (L m t q A : ℕ) (b : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b))
    (hq : 1≤q) (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hi : DenseBound input A) :
    let native:=HighBaseEncoder.encodeStored L m t q 1 b (nativeForms forms q)
      (denseView (2*L) (HighBaseEncoder.rootDims L b) input)
    (BinaryHighExecution.encodeStored L m t q b forms input).bitSteps≤
      storedFactor L A*(native.encoding.coefficientWork+native.encoding.capWork+native.trieWork) := by
  let native:=HighBaseEncoder.encode L m t q 1 b (nativeForms forms q)
    (denseView (2*L) (HighBaseEncoder.rootDims L b) input)
  let rows:=(BinaryHighExecution.encode L m t q b forms input).leaves
  let U:=BackendScalarBits.backendScalarUnit (commonWidth L A)
  have he:=encode_bit_price L m t q A b forms input hq hf hi
  have hp : 1≤native.coefficientWork:=encode_coefficientWork_pos L m t q b _ _ hq
  have hl : q*rows.length≤native.coefficientWork := by
    have h:=native_run_leaves_work_le L m t q (nativeForms forms q) (2*L)
      (HighBaseEncoder.rootDims L b) 0
      [⟨CappedEnumeration.zeroWord (2*L),denseView (2*L) (HighBaseEncoder.rootDims L b) input⟩]
    have hv:=encode_leaves_view L m t q b forms input
    have hlen:=congrArg List.length hv
    simp only [List.length_map] at hlen
    change rows.length=native.leaves.length at hlen
    change q*native.leaves.length≤native.coefficientWork at h
    simpa only [←hlen] using h
  have hs : (storeRows .empty rows).bitSteps≤rows.length*(q*(U+2)+18*L+8)+1 := by
    have hcap:=encode_leaves_bound L m t q A b forms input hf hi
    have h:=storeRows_bit_price rows .empty (commonWidth L A) (by
      intro row hrow r
      exact (view_bits_of_abs_le _ _ (hcap row hrow r)).trans
        (by have h:=scaled_width_common L (2*L) A (by omega);omega))
    simpa only [show 9*(2*L)=18*L by omega] using h
  have hcopy : rows.length*(q*(U+2))≤(U+2)*native.coefficientWork := by
    calc
      _=(U+2)*(q*rows.length) := by ring
      _≤_ := Nat.mul_le_mul_left _ hl
  have htrie : rows.length*(18*L+8)≤2*((16*L+7)*rows.length) := by nlinarith
  have hstore : (storeRows .empty rows).bitSteps≤
      (U+3)*native.coefficientWork+2*((16*L+7)*rows.length) := by
    rw [Nat.mul_add] at hs
    nlinarith
  dsimp only [HighBaseEncoder.encodeStored]
  rw [HighBaseEncoder.storeRowsCounted_work]
  have hv:=encode_leaves_view L m t q b forms input
  have hlen:=congrArg List.length hv
  simp only [List.length_map] at hlen
  change rows.length=native.leaves.length at hlen
  change (BinaryHighExecution.encode L m t q b forms input).bitSteps+
      (storeRows .empty rows).bitSteps≤
    storedFactor L A*(native.coefficientWork+native.capWork+(8*(2*L)+7)*native.leaves.length)
  rw [←hlen,show 8*(2*L)=16*L by omega]
  change _≤(encoderFactor L A+U+5)*(native.coefficientWork+native.capWork+(16*L+7)*rows.length)
  nlinarith [Nat.zero_le native.capWork]

#print axioms run_leaves_bound
#print axioms encodeStored_bit_price
end
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryHighExecution
noncomputable section

def rawStoredFactor (L A : ℕ) : ℕ :=
  storedFactor L A+BackendScalarBits.backendScalarUnit A.size+6*L+3

theorem encodeRawSource_bit_price (L m t q A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) (hq : 1≤q) :
    let native:=if b then HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
      else HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
    (encodeRawSource L m t q b raw).bitSteps≤
      rawStoredFactor L A*(native.encoding.coefficientWork+native.encoding.capWork+native.trieWork) := by
  have hstored:=encodeStored_bit_price L m t q A b (sourceForms L b)
    (rawInput b raw).value hq (sourceForms_magnitude L b) (rawInput_magnitude b raw A hA)
  have hraw:=rawInput_bit_price_le_root_work b raw A hA hq m t (nativeForms (sourceForms L b) q)
  rw [←rawInput_view] at hraw
  have htotal : (encodeRawSource L m t q b raw).bitSteps≤
      rawStoredFactor L A*
        ((HighBaseEncoder.encodeStored L m t q 1 b (nativeForms (sourceForms L b) q)
          (denseView (2*L) (HighBaseEncoder.rootDims L b) (rawInput b raw).value)).encoding.coefficientWork+
         (HighBaseEncoder.encodeStored L m t q 1 b (nativeForms (sourceForms L b) q)
          (denseView (2*L) (HighBaseEncoder.rootDims L b) (rawInput b raw).value)).encoding.capWork+
         (HighBaseEncoder.encodeStored L m t q 1 b (nativeForms (sourceForms L b) q)
          (denseView (2*L) (HighBaseEncoder.rootDims L b) (rawInput b raw).value)).trieWork) := by
    change (rawInput b raw).bitSteps+
      (BinaryHighExecution.encodeStored L m t q b (sourceForms L b) (rawInput b raw).value).bitSteps≤_
    dsimp only [HighBaseEncoder.encodeStored] at hstored ⊢
    unfold rawStoredFactor
    nlinarith
  have hf : nativeForms (sourceForms L b) q=
      (fun d row col=>((if b then SourceCoordinates.leftForms (R:=ℤ) L d row col
        else SourceCoordinates.rightForms (R:=ℤ) L d row col):Vector ℤ q)) := by
    funext d row col
    cases b <;> exact congrArg (fun z:ℤ=>(z:Vector ℤ q)) (sourceForms_view L _ d row col)
  rw [hf,rawInput_view] at htotal
  cases b <;> exact htotal

#print axioms encodeRawSource_bit_price
end
end ThinMatrix.BinaryHighCost

namespace ThinMatrix.BinaryHighCost
open BinaryHighExecution

theorem copyPayload_vector_bound {q A : ℕ} (a : Payload q)
    (ha : BinaryHighTable.Bounds.VectorBound A a) :
    BinaryHighTable.Bounds.VectorBound A (copyPayload a).value := by
  intro j
  simpa only [copyPayload,tabulate_value,Vector.get_ofFn,BinaryCell.view] using
    (show (BinaryCell.view (BinaryCell.copy (a.get j)).value).natAbs≤A by
      rw [BinaryCell.copy_view]
      exact ha j)

theorem storeRows_table_bound {q N A : ℕ}
    (table : StoredHighDP.Trie (Payload q)) (rows : List (ArrayKeys.Key N×Payload q))
    (ht : BinaryHighTable.Bounds.TableBound A table)
    (hr : ∀row∈rows,BinaryHighTable.Bounds.VectorBound A row.2) :
    BinaryHighTable.Bounds.TableBound A (storeRows table rows).value := by
  induction rows generalizing table with
  | nil => exact ht
  | cons row rows ih =>
    simp only [storeRows]
    apply ih
    · exact BinaryHighTable.Bounds.array_write_bound ht row.1 _
        (copyPayload_vector_bound row.2 (hr row (by simp)))
    · intro r hmem
      exact hr r (by simp [hmem])

theorem encodeStored_table_bound (L m t q A : ℕ) (b : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L b))
    (hf : ∀d row raw,|BinaryCell.view (forms d row raw)|≤2)
    (hi : DenseBound input A) :
    BinaryHighTable.Bounds.TableBound (8^(2*L)*A)
      (BinaryHighExecution.encodeStored L m t q b forms input).table := by
  apply storeRows_table_bound
  · exact BinaryHighTable.Bounds.empty _ _
  · intro row hrow j
    have h:=encode_leaves_bound L m t q A b forms input hf hi row hrow j
    have h' : (((row.2.get j).view.natAbs:ℕ):ℤ)≤((8^(2*L)*A:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs,BinaryCell.view] using h
    exact_mod_cast h'

theorem encodeRawSource_table_bound (L m t q A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A) :
    BinaryHighTable.Bounds.TableBound (8^(2*L)*A) (encodeRawSource L m t q b raw).table :=
  encodeStored_table_bound L m t q A b (sourceForms L b) (rawInput b raw).value
    (sourceForms_magnitude L b) (rawInput_magnitude b raw A hA)

theorem encodeRawSource_readBase_bound (L m t q A : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (hA : RawBound raw A)
    (w : HighBoxDP.BaseStates L m t) :
    BinaryHighTable.VectorBound (8^(2*L)*A)
      (BinaryHighTable.readBase (encodeRawSource L m t q b raw).table w).1 := by
  change BinaryHighTable.Bounds.VectorBound (8^(2*L)*A)
    ((ArrayKeys.read (encodeRawSource L m t q b raw).table
      (ArrayKeys.materialize w.val)).1.getD (BinaryHighTable.Bounds.zeroVector q))
  exact BinaryHighTable.Bounds.array_read_bound (encodeRawSource_table_bound L m t q A b raw hA) _

#print axioms encodeRawSource_table_bound
#print axioms encodeRawSource_readBase_bound
end ThinMatrix.BinaryHighCost
