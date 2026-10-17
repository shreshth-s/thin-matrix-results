import BinaryCell
import BinarySourceFormation
import BinaryHighTable
import HighBaseEncoder
import ArrayKeys

/-! Persistent binary-cell execution of the retained HIGH base encoder.
Integer projections below are proof views; executable contraction consumes
only the canonical bits in stored coefficient cells and fixed coefficient ROM.
-/
namespace ThinMatrix.BinaryHighExecution
open scoped BigOperators
open BinaryCell FFTBitCost
open SharedEncoder (Dense read volume Coordinates)
open CacheBounds CappedEnumeration
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Payload (q : ℕ) := Vector BinaryCell.Cell q
abbrev BinaryDense (q n : ℕ) (dims : Fin n → ℕ) := Dense (R:=Payload q) n dims
abbrev Forms := ℕ → Label → ℕ → BinaryCell.Cell

def payloadView {q : ℕ} (a : Payload q) : Vector ℤ q := a.map BinaryCell.view

def denseView {q : ℕ} : (n : ℕ) → (dims : Fin n → ℕ) → BinaryDense q n dims → Dense (R:=Vector ℤ q) n dims
  | 0,_,a => payloadView a
  | n+1,dims,a => a.map (denseView n (fun i=>dims i.succ))

theorem read_denseView {q : ℕ} (n : ℕ) (dims : Fin n → ℕ) (a : BinaryDense q n dims)
    (c : Coordinates dims) :
    read n dims (denseView n dims a) c=payloadView (read n dims a c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [denseView,SharedEncoder.read,Vector.get_map,ih]

/-- Each callback executes once and its result is retained before the two
field traversals. Allocation and writes are part of the returned counter. -/
def tabulate {α : Type} (n : ℕ) (f : Fin n→Result α) : Result (Vector α n) :=
  let rows:=Vector.ofFn f
  ⟨rows.map (fun r=>r.value),(rows.toList.map (fun r=>r.bitSteps)).sum+2*n⟩

theorem tabulate_value {α : Type} (n : ℕ) (f : Fin n→Result α) :
    (tabulate n f).value=Vector.ofFn (fun i=>(f i).value) := by
  simp only [tabulate,Vector.map_ofFn,Function.comp_def]

theorem tabulate_steps {α : Type} (n : ℕ) (f : Fin n→Result α) :
    (tabulate n f).bitSteps=(∑i,(f i).bitSteps)+2*n := by
  simp [tabulate,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]

def materialize {q : ℕ} : (n : ℕ) → (dims : Fin n→ℕ) →
    (Coordinates dims→Result (Payload q)) → Result (BinaryDense q n dims)
  | 0,_,f => f (fun i=>Fin.elim0 i)
  | n+1,dims,f => tabulate (dims 0) (fun a=>
      materialize n (fun i=>dims i.succ) (fun rest=>f (Fin.cons a rest)))

/-- Literal scalar-register dot loop; copied inputs, multiplication,
accumulated tail, and final addition all return their actual bit counters. -/
def dot : List (BinaryCell.Cell×BinaryCell.Cell) → Result BinaryCell.Cell
  | [] => ⟨BinaryCell.zero,1⟩
  | (w,x)::xs =>
      let cw:=BinaryCell.copy w
      let cx:=BinaryCell.copy x
      let product:=BinaryCell.mul cw.value cx.value
      let tail:=dot xs
      let output:=BinaryCell.add product.value tail.value
      ⟨output.value,cw.bitSteps+cx.bitSteps+product.bitSteps+tail.bitSteps+output.bitSteps+1⟩

theorem dot_view (xs : List (BinaryCell.Cell×BinaryCell.Cell)) :
    BinaryCell.view (dot xs).value=(xs.map (fun z=>BinaryCell.view z.1*BinaryCell.view z.2)).sum := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
      simp only [dot,BinaryCell.add_view,BinaryCell.mul_view,BinaryCell.copy_view,
        ih,List.map_cons,List.sum_cons]

theorem view_bits_of_abs_le (z : ℤ) (A : ℕ) (hz : |z|≤(A:ℤ)) :
    z.natAbs.size≤A.size := by
  apply Nat.size_le_size
  exact_mod_cast (show (z.natAbs:ℤ)≤(A:ℤ) by
    simpa only [Int.natCast_natAbs] using hz)

theorem view_bits_of_abs_le_eight (z : ℤ) (A : ℕ) (hz : |z|≤((8*A:ℕ):ℤ)) :
    z.natAbs.size≤A.size+5 := by
  have hn : z.natAbs≤8*A := by
    exact_mod_cast (show (z.natAbs:ℤ)≤((8*A:ℕ):ℤ) by
      simpa only [Int.natCast_natAbs] using hz)
  have hb : z.natAbs<2^(A.size+3) := by
    calc
      _ ≤ 8*A := hn
      _ < 8*2^A.size := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self A) (by decide)
      _ = _ := by rw [pow_add];norm_num;ring
  have hsize:=Nat.size_le.mpr hb
  omega

theorem dot_magnitude (xs : List (BinaryCell.Cell×BinaryCell.Cell)) (A : ℕ)
    (hw : ∀z∈xs,|BinaryCell.view z.1|≤2)
    (hx : ∀z∈xs,|BinaryCell.view z.2|≤(A:ℤ)) :
    |BinaryCell.view (dot xs).value|≤((2*xs.length*A:ℕ):ℤ) := by
  induction xs with
  | nil => simp [dot]
  | cons z xs ih =>
    have hwi:=hw z (by simp)
    have hxi:=hx z (by simp)
    have ht : |BinaryCell.view z.1*BinaryCell.view z.2|≤((2*A:ℕ):ℤ) := by
      rw [abs_mul,Nat.cast_mul,Nat.cast_ofNat]
      exact mul_le_mul hwi hxi (abs_nonneg _) (by norm_num)
    have hi:=ih (fun y hy=>hw y (by simp [hy]))
      (fun y hy=>hx y (by simp [hy]))
    simp only [dot,BinaryCell.add_view,BinaryCell.mul_view,BinaryCell.copy_view,
      List.length_cons]
    calc
      _ ≤ |BinaryCell.view z.1*BinaryCell.view z.2|+
          |BinaryCell.view (dot xs).value| := abs_add_le _ _
      _ ≤ ((2*A:ℕ):ℤ)+((2*xs.length*A:ℕ):ℤ) := add_le_add ht hi
      _ = _ := by push_cast;ring

theorem dot_width (xs : List (BinaryCell.Cell×BinaryCell.Cell)) (A : ℕ)
    (hlen : xs.length≤4) (hw : ∀z∈xs,|BinaryCell.view z.1|≤2)
    (hx : ∀z∈xs,|BinaryCell.view z.2|≤(A:ℤ)) :
    (BinaryCell.view (dot xs).value).natAbs.size≤A.size+5 := by
  apply view_bits_of_abs_le_eight _ A
  have h:=dot_magnitude xs A hw hx
  have hn : 2*xs.length*A≤8*A := by nlinarith
  exact h.trans (by exact_mod_cast hn)

theorem dot_suffix_width (xs ys : List (BinaryCell.Cell×BinaryCell.Cell)) (A : ℕ)
    (hlen : xs.length≤4) (hw : ∀z∈xs,|BinaryCell.view z.1|≤2)
    (hx : ∀z∈xs,|BinaryCell.view z.2|≤(A:ℤ)) (hy : ys<:+xs) :
    (BinaryCell.view (dot ys).value).natAbs.size≤A.size+5 :=
  dot_width ys A (hy.sublist.length_le.trans hlen)
    (fun z hz=>hw z (hy.mem hz)) (fun z hz=>hx z (hy.mem hz))

theorem row_product_width (w x : BinaryCell.Cell) (A : ℕ)
    (hw : |BinaryCell.view w|≤2) (hx : |BinaryCell.view x|≤(A:ℤ)) :
    (BinaryCell.view (BinaryCell.mul (BinaryCell.copy w).value
      (BinaryCell.copy x).value).value).natAbs.size≤A.size+5 := by
  simp only [BinaryCell.mul_view,BinaryCell.copy_view]
  apply view_bits_of_abs_le_eight _ A
  rw [abs_mul]
  have hp:=mul_le_mul hw hx (abs_nonneg _) (by norm_num : (0:ℤ)≤2)
  push_cast
  nlinarith

theorem dot_bit_price (xs : List (BinaryCell.Cell×BinaryCell.Cell)) (A : ℕ)
    (hlen : xs.length≤4) (hw : ∀z∈xs,|BinaryCell.view z.1|≤2)
    (hx : ∀z∈xs,|BinaryCell.view z.2|≤(A:ℤ)) :
    (dot xs).bitSteps≤(xs.length*5+1)*BackendScalarBits.backendScalarUnit (A.size+5) := by
  have hu : 1≤BackendScalarBits.backendScalarUnit (A.size+5) := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    have h:=Nat.one_le_pow 2 (A.size+5+1) (by omega)
    omega
  induction xs with
  | nil => simpa only [dot,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.one_mul] using hu
  | cons z xs ih =>
    have hwi:=hw z (by simp)
    have hxi:=hx z (by simp)
    have hwb : (BinaryCell.view z.1).natAbs.size≤A.size+5 := by
      have h:=view_bits_of_abs_le _ 2 hwi
      rw [show (2:ℕ).size=2 by decide] at h
      omega
    have hxb : (BinaryCell.view z.2).natAbs.size≤A.size+5 :=
      (view_bits_of_abs_le _ A hxi).trans (by omega)
    have hc1:=BinaryCell.copy_price (A.size+5) z.1 hwb
    have hc2:=BinaryCell.copy_price (A.size+5) z.2 hxb
    have hm:=BinaryCell.mul_price (A.size+5)
      (BinaryCell.copy z.1).value (BinaryCell.copy z.2).value
      (by simpa only [BinaryCell.copy_view] using hwb)
      (by simpa only [BinaryCell.copy_view] using hxb)
    have hlen':xs.length≤4 := by
      have h:=hlen
      simp only [List.length_cons] at h
      omega
    have hw':∀y∈xs,|BinaryCell.view y.1|≤2 := fun y hy=>hw y (by simp [hy])
    have hx':∀y∈xs,|BinaryCell.view y.2|≤(A:ℤ) := fun y hy=>hx y (by simp [hy])
    have ht:=dot_width xs A hlen' hw' hx'
    have hp:=row_product_width z.1 z.2 A hwi hxi
    have ha:=BinaryCell.add_price (A.size+5) _ _ hp ht
    have hi:=ih hlen' hw' hx'
    simp only [dot,List.length_cons]
    nlinarith

theorem tabulate_bitSteps_le {α : Type} (n C : ℕ) (f : Fin n → Result α)
    (hf : ∀ i, (f i).bitSteps ≤ C) :
    (tabulate n f).bitSteps ≤ n*(C+2) := by
  rw [tabulate_steps]
  calc
    (∑ i, (f i).bitSteps)+2*n ≤ (∑ _i : Fin n, C)+2*n :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun i _ => hf i)) _
    _ = n*(C+2) := by simp;ring

theorem materialize_steps_le {q : ℕ} (n : ℕ) (dims : Fin n → ℕ)
    (f : Coordinates dims → Result (Payload q)) (C : ℕ)
    (hC : ∀ c, (f c).bitSteps ≤ C)
    (hpos : ∀ i, 0 < dims i) :
    (materialize n dims f).bitSteps ≤ volume n dims * (C+2*n) := by
  induction n with
  | zero =>
    simpa [materialize, volume] using hC (fun i => Fin.elim0 i)
  | succ n ih =>
    have hv : 1 ≤ volume n (fun i => dims i.succ) := by
      have hp : 0 < volume n (fun i => dims i.succ) := by
        unfold volume
        exact Finset.prod_pos (fun i _ => hpos i.succ)
      omega
    simp only [materialize, tabulate_steps]
    calc
      (∑ a : Fin (dims 0),
          (materialize n (fun i => dims i.succ)
            (fun rest => f (Fin.cons a rest))).bitSteps) + 2*dims 0 ≤
          (∑ _a : Fin (dims 0),
            volume n (fun i => dims i.succ)*(C+2*n)) + 2*dims 0 := by
        apply Nat.add_le_add_right
        apply Finset.sum_le_sum
        intro a _
        exact ih (fun i => dims i.succ) (fun rest => f (Fin.cons a rest))
          (fun rest => hC (Fin.cons a rest)) (fun i => hpos i.succ)
      _ = dims 0 * (volume n (fun i => dims i.succ)*(C+2*n)) +
          2*dims 0 := by simp
      _ ≤ (dims 0 * volume n (fun i => dims i.succ))*
          (C+2*(n+1)) := by nlinarith
      _ = volume (n+1) dims*(C+2*(n+1)) := by
        have hs : volume (n+1) dims =
            dims 0 * volume n (fun i => dims i.succ) :=
          Fin.prod_univ_succ dims
        rw [hs]


def dotVector {q a : ℕ} (weights : Fin a→BinaryCell.Cell) (values : Fin a→Payload q) : Result (Payload q) :=
  tabulate q (fun r=>dot ((List.finRange a).map (fun i=>(weights i,(values i).get r))))

theorem dotVector_view {q a : ℕ} (weights : Fin a→BinaryCell.Cell) (values : Fin a→Payload q)
    (r : Fin q) :
    BinaryCell.view ((dotVector weights values).value.get r)=
      ∑i : Fin a,BinaryCell.view (weights i)*BinaryCell.view ((values i).get r) := by
  simp only [dotVector,tabulate_value,Vector.get_ofFn,dot_view,List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map,List.sum_ofFn]

/-- Dense contraction performs only pointwise small-coefficient binary
operations. It does not call a full cyclic multiplier. -/
def contract {q n : ℕ} (dims : Fin (n+1)→ℕ) (form : Fin (dims 0)→BinaryCell.Cell)
    (input : BinaryDense q (n+1) dims) : Result (BinaryDense q n (fun i=>dims i.succ)) :=
  materialize n (fun i=>dims i.succ) (fun rest=>
    let result:=dotVector form (fun a=>read (n+1) dims input (Fin.cons a rest))
    ⟨result.value,result.bitSteps+q*(n+2)*(dims 0)⟩)

 theorem materialize_view {q : ℕ} (n : ℕ) (dims : Fin n → ℕ)
    (f : Coordinates dims → Result (Payload q)) :
    denseView n dims (materialize n dims f).value =
      SharedEncoder.materialize n dims (fun c => payloadView (f c).value) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [materialize, tabulate_value, denseView, Vector.map_ofFn,
        Function.comp_def, SharedEncoder.materialize]
      congr 1
      funext a
      exact ih (fun i => dims i.succ) (fun rest => f (Fin.cons a rest))

 theorem contract_view {q n : ℕ} (dims : Fin (n+1) → ℕ)
    (form : Fin (dims 0) → BinaryCell.Cell) (input : BinaryDense q (n+1) dims) :
    denseView n (fun i => dims i.succ) (contract dims form input).value =
      SharedEncoder.contract dims
        (fun a => (BinaryCell.view (form a) : Vector ℤ q)) (denseView (n+1) dims input) := by
  unfold contract SharedEncoder.contract
  rw [materialize_view]
  congr 1
  funext rest
  apply (HighBaseEncoder.vectorEquiv q).injective
  funext r
  change (payloadView _).get r = _
  simp only [payloadView, Vector.get_map]
  change BinaryCell.view ((dotVector form
      (fun a => read (n+1) dims input (Fin.cons a rest))).value.get r) =
    HighBaseEncoder.eval q r _
  rw [dotVector_view, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_mul, HighBaseEncoder.get_intCast,
    HighBaseEncoder.eval_apply, read_denseView, payloadView, Vector.get_map]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- HIGH evaluates the private normal form at auxiliary degree zero. -/
def highCoefficient (normal : Bool) (row : Fin 6) (col : Fin 4) : BinaryCell.Cell :=
  if normal && decide (row=4 ∧ col=2) then BinaryCell.zero else BinaryCell.coefficient normal row col

theorem highCoefficient_view (normal : Bool) (row : Fin 6) (col : Fin 4) :
    BinaryCell.view (highCoefficient normal row col)=HighBaseEncoder.baseCoefficient normal row col := by
  cases normal <;> fin_cases row <;> fin_cases col <;> rfl

/-- Coefficient ROM for the actual normal/opposite physical order. -/
def sourceForms (L : ℕ) (firstNormal : Bool) : Forms := fun d row raw=>
  if hc : raw<4 then
    if row.val<5 then highCoefficient (if d<L then firstNormal else !firstNormal) row ⟨raw,hc⟩
    else BinaryCell.zero
  else BinaryCell.zero

theorem sourceForms_view (L : ℕ) (firstNormal : Bool) (d : ℕ) (row : Label) (raw : ℕ) :
    BinaryCell.view (sourceForms L firstNormal d row raw) =
      if firstNormal then SourceCoordinates.leftForms (R := ℤ) L d row raw
      else SourceCoordinates.rightForms (R := ℤ) L d row raw := by
  cases firstNormal <;> by_cases hd : d < L <;> by_cases hr : raw < 4
  all_goals try (have hr3 : ¬raw < 3 := by omega
                 simp [sourceForms, SourceCoordinates.leftForms, SourceCoordinates.rightForms, hd, hr, hr3])
  all_goals interval_cases raw <;> fin_cases row <;>
    simp only [sourceForms, SourceCoordinates.leftForms, SourceCoordinates.rightForms,
      hd, if_true, if_false]
  all_goals rfl


structure Node (q N n : ℕ) (dims : Fin n→ℕ) where
  key : ArrayKeys.Key N
  data : BinaryDense q n dims

def nodeView {q N n : ℕ} {dims : Fin n→ℕ} (a : Node q N n dims) :
    SharedEncoder.Node (R:=Vector ℤ q) N n dims :=
  ⟨ArrayKeys.toWord a.key,denseView n dims a.data⟩

def nativeForms (forms : Forms) (q : ℕ) : SharedEncoder.LocalForms (Vector ℤ q) :=
  fun d row col=>(BinaryCell.view (forms d row col):Vector ℤ q)

theorem baseTest_refines (L m t : ℕ) (key : ArrayKeys.Key (2*L)) :
    (ArrayKeys.baseTest L m t key).1=HighBaseEncoder.baseTest L m t (ArrayKeys.toWord key) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ArrayKeys.baseTest_value,HighBaseEncoder.baseTest_eq_true,HighBaseEncoder.Admissible]

/-- Rejected children allocate no coefficient array. Accepted children run
one literal binary dense contraction and retain the resulting array. -/
def makeChild {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims) (a : Fin 5) :
    Result (Option (Node q (2*L) n (fun i=>dims i.succ))) :=
  let key:=ArrayKeys.put parent.key ⟨d,hd⟩ (HighBaseEncoder.baseLabel a)
  let test:=ArrayKeys.baseTest L m t key
  if test.1 then
    let child:=contract dims (fun b=>forms d (HighBaseEncoder.baseLabel a) b.val) parent.data
    ⟨some ⟨key,child.value⟩,test.2+child.bitSteps+2*L+2⟩
  else ⟨none,test.2+2*L+1⟩

def nodeChildren {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims) :
    Result (List (Node q (2*L) n (fun i=>dims i.succ))) :=
  let candidates:=tabulate 5 (makeChild L m t d n hd dims forms parent)
  ⟨candidates.value.toList.filterMap id,candidates.bitSteps+5⟩

def nextLayer {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) : List (Node q (2*L) (n+1) dims)→
      Result (List (Node q (2*L) n (fun i=>dims i.succ)))
  | [] => ⟨[],1⟩
  | parent::parents =>
      let children:=nodeChildren L m t d n hd dims forms parent
      let tail:=nextLayer L m t d n hd dims forms parents
      ⟨children.value++tail.value,children.bitSteps+tail.bitSteps+children.value.length+1⟩

theorem makeChild_view {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims) (a : Fin 5) :
    ((makeChild L m t d n hd dims forms parent a).value).map nodeView=
      if HighBaseEncoder.baseTest L m t (put d hd (ArrayKeys.toWord parent.key)
        (HighBaseEncoder.baseLabel a)) then
        some (⟨put d hd (ArrayKeys.toWord parent.key) (HighBaseEncoder.baseLabel a),
          SharedEncoder.contract dims (fun b=>nativeForms forms q d (HighBaseEncoder.baseLabel a) b.val)
            (denseView (n+1) dims parent.data)⟩ : SharedEncoder.Node (R:=Vector ℤ q)
              (2*L) n (fun i=>dims i.succ)) else none := by
  unfold makeChild
  simp only [baseTest_refines,ArrayKeys.toWord_put,put]
  split <;> simp only [Option.map_some,Option.map_none,nodeView,ArrayKeys.toWord_put,
    contract_view,nativeForms]

theorem nodeChildren_view {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parent : Node q (2*L) (n+1) dims) :
    (nodeChildren L m t d n hd dims forms parent).value.map nodeView=
      HighBaseEncoder.nodeChildren L m t d n hd dims (nativeForms forms q) (nodeView parent) := by
  simp only [nodeChildren,tabulate_value,Vector.toList_ofFn,List.ofFn_eq_map,
    List.filterMap_map,List.map_filterMap,Function.comp_def,id_eq,makeChild_view,
    HighBaseEncoder.nodeChildren,nodeView]

theorem nextLayer_view {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parents : List (Node q (2*L) (n+1) dims)) :
    (nextLayer L m t d n hd dims forms parents).value.map nodeView=
      HighBaseEncoder.nextLayer L m t d n hd dims (nativeForms forms q) (parents.map nodeView) := by
  induction parents with
  | nil => rfl
  | cons p ps ih =>
    simp only [nextLayer,List.map_append,nodeChildren_view,ih,List.map_cons,
      HighBaseEncoder.nextLayer,List.flatMap_cons]

theorem nextLayer_words {q : ℕ} (L m t d n : ℕ) (hd : d<2*L) (dims : Fin (n+1)→ℕ)
    (forms : Forms) (parents : List (Node q (2*L) (n+1) dims))
    (hwords : parents.map (fun p=>ArrayKeys.toWord p.key)=HighBaseEncoder.generate L m t d) :
    (nextLayer L m t d n hd dims forms parents).value.map (fun p=>ArrayKeys.toWord p.key)=
      HighBaseEncoder.generate L m t (d+1) := by
  have hp:=congrArg (List.map SharedEncoder.Node.word)
    (nextLayer_view L m t d n hd dims forms parents)
  have hw : (parents.map nodeView).map SharedEncoder.Node.word=HighBaseEncoder.generate L m t d := by
    simpa only [List.map_map,Function.comp_def,nodeView] using hwords
  rw [HighBaseEncoder.nextLayer_words L m t d n hd dims (nativeForms forms q) _ hw] at hp
  simpa only [List.map_map,Function.comp_def,nodeView] using hp

theorem parents_nonempty {q n : ℕ} (L m t d : ℕ) (hd : d≤2*L) (dims : Fin n→ℕ)
    (parents : List (Node q (2*L) n dims))
    (hwords : parents.map (fun p=>ArrayKeys.toWord p.key)=HighBaseEncoder.generate L m t d) :
    parents≠[] := by
  have hz : zeroWord (2*L)∈HighBaseEncoder.generate L m t d :=
    (HighBaseEncoder.mem_generate L m t d hd (zeroWord (2*L))).mpr
      ⟨by intro i hi;rfl,HighBaseEncoder.zero_admissible L m t⟩
  intro he
  rw [he] at hwords
  simp only [List.map_nil] at hwords
  rw [←hwords] at hz
  exact List.not_mem_nil hz

structure Stored (q N : ℕ) where
  depth : ℕ
  remaining : ℕ
  dims : Fin remaining→ℕ
  node : Node q N remaining dims

structure Execution (q N : ℕ) where
  leaves : List (ArrayKeys.Key N×Payload q)
  formed : List (Stored q N)
  bitSteps : ℕ

/-- All dense arrays are retained in the trace. Parent arrays are shared
between sibling contractions, and each child is materialized once. -/
def run {q : ℕ} (L m t : ℕ) (forms : Forms) :
    (n : ℕ)→(dims : Fin n→ℕ)→ℕ→List (Node q (2*L) n dims)→Execution q (2*L)
  | 0,dims,d,parents =>
      ⟨parents.map (fun a=>(a.key,a.data)),parents.map (fun a=>⟨d,0,dims,a⟩),
        (q+2*L+2)*parents.length+1⟩
  | n+1,dims,d,parents =>
      if hd : d<2*L then
        let children:=nextLayer L m t d n hd dims forms parents
        let tail:=run L m t forms n (fun i=>dims i.succ) (d+1) children.value
        ⟨tail.leaves,parents.map (fun a=>⟨d,n+1,dims,a⟩)++tail.formed,
          children.bitSteps+tail.bitSteps+(q+2*L+n+3)*parents.length+1⟩
      else
        ⟨[],parents.map (fun a=>⟨d,n+1,dims,a⟩),
          (q+2*L+n+3)*parents.length+1⟩

def encode (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal)) : Execution q (2*L) :=
  run L m t forms (2*L) (HighBaseEncoder.rootDims L firstNormal) 0
    [⟨ArrayKeys.zero (2*L),input⟩]

def storedView {q N : ℕ} (s : Stored q N) : HighBaseEncoder.Stored (Vector ℤ q) N :=
  ⟨s.depth,s.remaining,s.dims,nodeView s.node⟩

def leafView {q N : ℕ} (a : ArrayKeys.Key N×Payload q) : Word N×Vector ℤ q :=
  (ArrayKeys.toWord a.1,payloadView a.2)

theorem run_leaves_view {q : ℕ} (L m t : ℕ) (forms : Forms) (n : ℕ)
    (dims : Fin n→ℕ) (d : ℕ) (parents : List (Node q (2*L) n dims)) :
    (run L m t forms n dims d parents).leaves.map leafView=
      (HighBaseEncoder.run L m t q 1 (nativeForms forms q) n dims d (parents.map nodeView)).leaves := by
  induction n generalizing d with
  | zero => simp only [run,HighBaseEncoder.run,List.map_map,Function.comp_def,leafView,nodeView,denseView]
  | succ n ih =>
      simp only [run,HighBaseEncoder.run]
      split
      · rw [ih,nextLayer_view]
      · rfl

theorem run_formed_view {q : ℕ} (L m t : ℕ) (forms : Forms) (n : ℕ)
    (dims : Fin n→ℕ) (d : ℕ) (parents : List (Node q (2*L) n dims)) :
    (run L m t forms n dims d parents).formed.map storedView=
      (HighBaseEncoder.run L m t q 1 (nativeForms forms q) n dims d (parents.map nodeView)).formed := by
  induction n generalizing d with
  | zero => simp only [run,HighBaseEncoder.run,List.map_map,Function.comp_def,storedView,nodeView,denseView]
  | succ n ih =>
      simp only [run,HighBaseEncoder.run]
      split
      · simp only [List.map_append,List.map_map,Function.comp_def,storedView]
        rw [ih,nextLayer_view]
      · simp only [List.map_map,Function.comp_def,storedView]

theorem encode_leaves_view (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal)) :
    (encode L m t q firstNormal forms input).leaves.map leafView=
      (HighBaseEncoder.encode L m t q 1 firstNormal (nativeForms forms q)
        (denseView (2*L) (HighBaseEncoder.rootDims L firstNormal) input)).leaves := by
  unfold encode HighBaseEncoder.encode
  rw [run_leaves_view]
  simp only [List.map_cons,List.map_nil,nodeView,ArrayKeys.toWord_zero]

theorem encode_formed_view (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal)) :
    (encode L m t q firstNormal forms input).formed.map storedView=
      (HighBaseEncoder.encode L m t q 1 firstNormal (nativeForms forms q)
        (denseView (2*L) (HighBaseEncoder.rootDims L firstNormal) input)).formed := by
  unfold encode HighBaseEncoder.encode
  rw [run_formed_view]
  simp only [List.map_cons,List.map_nil,nodeView,ArrayKeys.toWord_zero]

/-- Copy each stored output cell using its actual binary primitive. -/
def copyPayload {q : ℕ} (a : Payload q) : Result (Payload q) :=
  tabulate q (fun r=>BinaryCell.copy (a.get r))

theorem copyPayload_view {q : ℕ} (a : Payload q) :
    payloadView (copyPayload a).value=payloadView a := by
  apply Vector.ext
  intro i hi
  simp only [payloadView,copyPayload,tabulate_value,Vector.getElem_map,
    Vector.getElem_ofFn,BinaryCell.copy_view]
  rfl

def storeRows {q N : ℕ} : StoredHighDP.Trie (Payload q)→
    List (ArrayKeys.Key N×Payload q)→Result (StoredHighDP.Trie (Payload q))
  | table,[] => ⟨table,1⟩
  | table,row::rows =>
      let copied:=copyPayload row.2
      let written:=ArrayKeys.write table row.1 copied.value
      let tail:=storeRows written.1 rows
      ⟨tail.value,copied.bitSteps+written.2+tail.bitSteps+1⟩

/-- Projection is a read relation between persistent stores; no native
coefficient trie is constructed by the executable binary program. -/
theorem storeRows_view {q N : ℕ} (rows : List (ArrayKeys.Key N×Payload q))
    (binary : StoredHighDP.Trie (Payload q)) (native : StoredHighDP.Trie (Vector ℤ q))
    (h : BinaryHighTable.Projection.TrieRel payloadView binary native) :
    BinaryHighTable.Projection.TrieRel payloadView (storeRows binary rows).value
      (HighBaseEncoder.storeRows native (rows.map leafView)) := by
  induction rows generalizing binary native with
  | nil => exact h
  | cons row rows ih =>
      simp only [storeRows,List.map_cons,HighBaseEncoder.storeRows,leafView]
      apply ih
      simp only [ArrayKeys.write_value]
      apply BinaryHighTable.Projection.write_of_eq h
      exact (copyPayload_view row.2).symm

structure StoredEncoding (q N : ℕ) where
  encoding : Execution q N
  table : StoredHighDP.Trie (Payload q)
  bitSteps : ℕ

/-- Encoding and insertion are each run once, and return the same binary
payloads that are subsequently read by the HIGH leaf multiplier. -/
def encodeStored (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal)) : StoredEncoding q (2*L) :=
  let encoded:=encode L m t q firstNormal forms input
  let stored:=storeRows .empty encoded.leaves
  ⟨encoded,stored.value,encoded.bitSteps+stored.bitSteps⟩

theorem encodeStored_view (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal)) :
    BinaryHighTable.Projection.TrieRel payloadView
      (encodeStored L m t q firstNormal forms input).table
      (HighBaseEncoder.encodeStored L m t q 1 firstNormal (nativeForms forms q)
        (denseView (2*L) (HighBaseEncoder.rootDims L firstNormal) input)).table := by
  have h:=storeRows_view (encode L m t q firstNormal forms input).leaves
    .empty .empty (BinaryHighTable.Projection.empty payloadView)
  rw [encode_leaves_view] at h
  simpa only [encodeStored,HighBaseEncoder.encodeStored,HighBaseEncoder.storeRowsCounted_value] using h

def readBase {q N : ℕ} (stored : StoredEncoding q N) (key : ArrayKeys.Key N) : Result (Payload q) :=
  let found:=ArrayKeys.read stored.table key
  ⟨found.1.getD (BinaryCell.vectorZero q),found.2+1⟩

theorem highCoefficient_magnitude (normal : Bool) (row : Fin 6) (col : Fin 4) :
    |BinaryCell.view (highCoefficient normal row col)|≤2 := by
  cases normal <;> fin_cases row <;> fin_cases col <;> decide

theorem sourceForms_magnitude (L : ℕ) (firstNormal : Bool) (d : ℕ) (row : Label) (raw : ℕ) :
    |BinaryCell.view (sourceForms L firstNormal d row raw)|≤2 := by
  unfold sourceForms
  split_ifs <;> first | exact highCoefficient_magnitude _ _ _ | decide

theorem shape_dims_bounds (L : ℕ) (firstNormal : Bool) (d n : ℕ) (dims : Fin n→ℕ)
    (hs : HighBaseEncoder.Shape L firstNormal d n dims) (i : Fin n) :
    1≤dims i ∧ dims i≤4 := by
  rw [hs.2 i]
  unfold CacheBounds.rawDim
  split_ifs <;> decide

theorem payloadView_zero (q : ℕ) :
    payloadView (BinaryCell.vectorZero q)=Vector.replicate q (0:ℤ) := by
  simp only [payloadView,BinaryCell.vectorZero,Vector.map_replicate,BinaryCell.zero_view]

/-- Stored base reads project directly; no coefficient or full source sweep
is reconstructed when the persistent binary table is read. -/
theorem readBase_view (L m t q : ℕ) (firstNormal : Bool) (forms : Forms)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal))
    (w : HighBoxDP.BaseStates L m t) :
    payloadView (readBase (encodeStored L m t q firstNormal forms input)
      (ArrayKeys.materialize w.val)).value=
      HighBaseEncoder.readBase
        (HighBaseEncoder.encodeStored L m t q 1 firstNormal (nativeForms forms q)
          (denseView (2*L) (HighBaseEncoder.rootDims L firstNormal) input)) w := by
  have h:=BinaryHighTable.Projection.read_getD
    (encodeStored_view L m t q firstNormal forms input) (StoredHighDP.key w.val) (BinaryCell.vectorZero q)
  rw [payloadView_zero] at h
  simpa only [readBase,ArrayKeys.read_value,ArrayKeys.toWord_materialize,
    HighBaseEncoder.readBase] using h.symm

/-- The public binary source encoder and the old native vector encoder have
identical stored reads; native forms are used only in this proof statement. -/
theorem source_readBase_view (L m t q : ℕ) (firstNormal : Bool)
    (input : BinaryDense q (2*L) (HighBaseEncoder.rootDims L firstNormal))
    (w : HighBoxDP.BaseStates L m t) :
    payloadView (readBase (encodeStored L m t q firstNormal (sourceForms L firstNormal) input)
      (ArrayKeys.materialize w.val)).value=
      HighBaseEncoder.readBase (HighBaseEncoder.encodeVector L m t q firstNormal
        (if firstNormal then SourceCoordinates.leftForms L else SourceCoordinates.rightForms L)
        (denseView (2*L) (HighBaseEncoder.rootDims L firstNormal) input)) w := by
  have h:=readBase_view L m t q firstNormal (sourceForms L firstNormal) input w
  have hf : nativeForms (sourceForms L firstNormal) q=
      (fun d row col=>((if firstNormal then SourceCoordinates.leftForms (R:=ℤ) L d row col
        else SourceCoordinates.rightForms (R:=ℤ) L d row col):Vector ℤ q)) := by
    funext d row col
    cases firstNormal <;> exact congrArg (fun z:ℤ=>(z:Vector ℤ q)) (sourceForms_view L _ d row col)
  rw [hf] at h
  cases firstNormal <;> exact h


/-- Every leaf has a charged native coefficient slot in the same execution. -/
theorem native_run_leaves_work_le {R : Type*} [CommSemiring R]
    (L m t q : ℕ) (forms : SharedEncoder.LocalForms R)
    (n : ℕ) (dims : Fin n→ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R:=R) (2*L) n dims)) :
    q*(HighBaseEncoder.run L m t q 1 forms n dims d parents).leaves.length≤
      (HighBaseEncoder.run L m t q 1 forms n dims d parents).coefficientWork := by
  induction n generalizing d with
  | zero => simp [HighBaseEncoder.run,SharedEncoder.volume];nlinarith
  | succ n ih =>
    simp only [HighBaseEncoder.run]
    split
    · exact (ih (fun i=>dims i.succ) (d+1) _).trans (Nat.le_add_left _ _)
    · simp only [List.length_nil,Nat.mul_zero];exact Nat.zero_le _

/-- The native ledger includes the full input layer before any child is made. -/
theorem native_run_root_work_le {R : Type*} [CommSemiring R]
    (L m t q : ℕ) (forms : SharedEncoder.LocalForms R)
    (n : ℕ) (dims : Fin n→ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R:=R) (2*L) n dims)) :
    70*q*parents.length*volume n dims≤
      (HighBaseEncoder.run L m t q 1 forms n dims d parents).coefficientWork := by
  cases n with
  | zero => simp only [HighBaseEncoder.run,Nat.mul_one];exact le_refl _
  | succ n => simp only [HighBaseEncoder.run];split <;> simp only [Nat.mul_one];exact Nat.le_add_right _ _;exact le_refl _

/-- Literal source-letter decoding; the noncomputable semantic equivalences
are used only by the projection lemmas. -/
def decodeSource {L : ℕ} : (b : Bool) → Coordinates (HighBaseEncoder.rootDims L b) → CompleteThinProduct.SourceWord L
  | true,a =>
    (fun j=>SourceCoordinates.normalEquiv (Fin.cast (by exact SourceCoordinates.rootDims_left L true j) (a (CompleteThinProduct.physicalLeft j))),
     fun j=>SourceCoordinates.oppositeEquiv (Fin.cast (by exact SourceCoordinates.rootDims_right L true j) (a (CompleteThinProduct.physicalRight j))))
  | false,a =>
    (fun j=>SourceCoordinates.normalEquiv (Fin.cast (by exact SourceCoordinates.rootDims_right L false j) (a (CompleteThinProduct.physicalRight j))),
     fun j=>SourceCoordinates.oppositeEquiv (Fin.cast (by exact SourceCoordinates.rootDims_left L false j) (a (CompleteThinProduct.physicalLeft j))))

@[simp] theorem decodeSource_true {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L true)) :
    decodeSource true a=SourceCoordinates.toSourceTrue a := rfl
@[simp] theorem decodeSource_false {L : ℕ} (a : Coordinates (HighBaseEncoder.rootDims L false)) :
    decodeSource false a=SourceCoordinates.toSourceFalse a := rfl

/-- Each dense root cell is read from the already formed Walsh source and
copied as canonical bits. The two raw-trie paths are charged for every read. -/
def rawPayload {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) : Result (Payload q) :=
  let word:=decodeSource b a
  tabulate q (fun r=>
    let copied:=BinaryCell.copy (BinarySourceFormation.readRaw raw word.1 word.2 r)
    ⟨copied.value,copied.bitSteps+2*L+1⟩)

/-- The source is materialized once in physical normal/opposite order. -/
def rawInput {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q) :
    Result (BinaryDense q (2*L) (HighBaseEncoder.rootDims L b)) :=
  materialize (2*L) (HighBaseEncoder.rootDims L b) (rawPayload b raw)

/-- Joint execution from an actual binary Walsh source to the stored HIGH
encoder table. Initial input copies are included in the returned bit counter. -/
def encodeRawSource (L m t q : ℕ) (b : Bool) (raw : BinarySourceFormation.RawStore L q) :
    StoredEncoding q (2*L) :=
  let input:=rawInput b raw
  let encoded:=encodeStored L m t q b (sourceForms L b) input.value
  { encoded with bitSteps:=input.bitSteps+encoded.bitSteps }

@[simp] theorem rawPayload_view {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) :
    payloadView (rawPayload b raw a).value=
      Vector.ofFn (fun r=>SourceFormation.readRaw (BinarySourceFormation.viewRaw raw)
        (decodeSource b a).1 (decodeSource b a).2 r) := by
  apply Vector.ext
  intro i hi
  simp only [payloadView,rawPayload,tabulate_value,Vector.getElem_map,Vector.getElem_ofFn,
    BinaryCell.copy_view,BinarySourceFormation.readRaw_view]
  rfl

/-- Semantic native source input, erased from the actual binary wrapper. -/
noncomputable def nativeRawInput {L q : ℕ} : (b : Bool) → BinarySourceFormation.RawStore L q →
    Dense (R:=Vector ℤ q) (2*L) (HighBaseEncoder.rootDims L b)
  | true,raw => SourceCoordinates.leftVectorInput
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
  | false,raw => SourceCoordinates.rightVectorInput
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))

/-- The materialized binary root is exactly the source-coordinate root of
its integer view, including the swapped orientation on the right. -/
theorem rawInput_view {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q) :
    denseView (2*L) (HighBaseEncoder.rootDims L b) (rawInput b raw).value=
      nativeRawInput b raw := by
  rw [rawInput,materialize_view]
  cases b <;> simp only [nativeRawInput,SourceCoordinates.leftVectorInput,
    SourceCoordinates.rightVectorInput,rawPayload_view,decodeSource_true,decodeSource_false,
    ThinMatrixBackend.sourceValue] <;> rfl

/-- Public source-read correctness, with native source materialization
appearing only in the semantic theorem. -/
theorem encodeRawSource_readBase_view (L m t q : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (w : HighBoxDP.BaseStates L m t) :
    payloadView (readBase (encodeRawSource L m t q b raw) (ArrayKeys.materialize w.val)).value=
      HighBaseEncoder.readBase
        (if b then HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
        else HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))) w := by
  have h:=source_readBase_view L m t q b (rawInput b raw).value w
  rw [rawInput_view] at h
  cases b <;> exact h


/-- Original raw source magnitude cap, before any HIGH contraction. -/
def RawBound {L q : ℕ} (raw : BinarySourceFormation.RawStore L q) (A : ℕ) : Prop :=
  ∀ normal opposite r,|BinaryCell.view (BinarySourceFormation.readRaw raw normal opposite r)|≤(A:ℤ)

@[simp] theorem rawPayload_get_view {L q : ℕ} (b : Bool)
    (raw : BinarySourceFormation.RawStore L q)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) (r : Fin q) :
    BinaryCell.view ((rawPayload b raw a).value.get r)=
      BinaryCell.view (BinarySourceFormation.readRaw raw (decodeSource b a).1 (decodeSource b a).2 r) := by
  simp only [rawPayload,tabulate_value,Vector.get_ofFn,BinaryCell.copy_view]

/-- Reads of the concrete materialized root use the stored callback result. -/
theorem read_materialize_value {q : ℕ} (n : ℕ) (dims : Fin n→ℕ)
    (f : Coordinates dims→Result (Payload q)) (c : Coordinates dims) :
    read n dims (materialize n dims f).value c=(f c).value := by
  induction n with
  | zero =>
    simp only [materialize,SharedEncoder.read]
    have hc : (fun i : Fin 0=>Fin.elim0 i)=c := by funext i;exact Fin.elim0 i
    rw [hc]
  | succ n ih =>
    simp only [materialize,tabulate_value,SharedEncoder.read,Vector.get_ofFn]
    have h:=ih (fun i=>dims i.succ) (fun rest=>f (Fin.cons (c 0) rest)) (fun i=>c i.succ)
    have hc : Fin.cons (c 0) (fun i=>c i.succ)=c := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    rw [hc] at h
    exact h

/-- Input copying preserves the original cap, with no intermediate premise. -/
theorem rawInput_magnitude {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q)
    (A : ℕ) (hA : RawBound raw A)
    (a : Coordinates (HighBaseEncoder.rootDims L b)) (r : Fin q) :
    |BinaryCell.view ((read (2*L) (HighBaseEncoder.rootDims L b) (rawInput b raw).value a).get r)|≤(A:ℤ) := by
  rw [rawInput,read_materialize_value,rawPayload_get_view]
  exact hA _ _ _

/-- A complete raw q-vector is copied; raw-trie path reads and allocation
are charged in addition to the actual scalar bit-copy circuit. -/
theorem rawPayload_bit_price {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q)
    (A : ℕ) (hA : RawBound raw A) (a : Coordinates (HighBaseEncoder.rootDims L b)) :
    (rawPayload b raw a).bitSteps≤q*(BackendScalarBits.backendScalarUnit A.size+2*L+3) := by
  let word:=decodeSource b a
  have h:=tabulate_bitSteps_le q (BackendScalarBits.backendScalarUnit A.size+2*L+1)
    (fun r=>
      let copied:=BinaryCell.copy (BinarySourceFormation.readRaw raw word.1 word.2 r)
      ⟨copied.value,copied.bitSteps+2*L+1⟩) (by
        intro r
        have hc:=BinaryCell.copy_price A.size
          (BinarySourceFormation.readRaw raw word.1 word.2 r)
          (view_bits_of_abs_le _ A (hA _ _ _))
        dsimp only
        omega)
  simpa only [rawPayload,Nat.add_assoc] using h

/-- Total initial-source materialization has the exact physical root
volume; it does not enumerate source leaves independently. -/
theorem rawInput_bit_price {L q : ℕ} (b : Bool) (raw : BinarySourceFormation.RawStore L q)
    (A : ℕ) (hA : RawBound raw A) :
    (rawInput b raw).bitSteps≤volume (2*L) (HighBaseEncoder.rootDims L b)*
      (q*(BackendScalarBits.backendScalarUnit A.size+2*L+3)+4*L) := by
  have hp : ∀i,0<HighBaseEncoder.rootDims L b i := by
    intro i
    exact (shape_dims_bounds L b 0 (2*L) _ (HighBaseEncoder.root_shape L b) i).1
  have h:=materialize_steps_le (2*L) (HighBaseEncoder.rootDims L b) (rawPayload b raw)
    (q*(BackendScalarBits.backendScalarUnit A.size+2*L+3)) (rawPayload_bit_price b raw A hA) hp
  simpa only [rawInput,show 2*(2*L)=4*L by omega] using h

/-- Physical raw input copies are absorbed by the already charged native
input layer with a polynomial factor in the input width and tensor depth. -/
theorem rawInput_bit_price_le_root_work {L q : ℕ} (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) (A : ℕ) (hA : RawBound raw A) (hq : 1≤q)
    (m t : ℕ) (forms : SharedEncoder.LocalForms (Vector ℤ q)) :
    (rawInput b raw).bitSteps≤
      (BackendScalarBits.backendScalarUnit A.size+6*L+3)*
        (HighBaseEncoder.encode L m t q 1 b forms (nativeRawInput b raw)).coefficientWork := by
  have h:=rawInput_bit_price b raw A hA
  have hroot:=native_run_root_work_le L m t q forms (2*L) (HighBaseEncoder.rootDims L b) 0
    [⟨CappedEnumeration.zeroWord (2*L),nativeRawInput b raw⟩]
  simp only [List.length_singleton,Nat.mul_one] at hroot
  change 70*q*volume (2*L) (HighBaseEncoder.rootDims L b)≤
    (HighBaseEncoder.encode L m t q 1 b forms (nativeRawInput b raw)).coefficientWork at hroot
  have hc : q*(BackendScalarBits.backendScalarUnit A.size+2*L+3)+4*L≤
      q*(BackendScalarBits.backendScalarUnit A.size+6*L+3) := by nlinarith
  apply h.trans
  apply (Nat.mul_le_mul_left _ hc).trans
  calc
    volume (2*L) (HighBaseEncoder.rootDims L b)*(q*(BackendScalarBits.backendScalarUnit A.size+6*L+3))=
      (BackendScalarBits.backendScalarUnit A.size+6*L+3)*(q*volume (2*L) (HighBaseEncoder.rootDims L b)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

/-- Persistent store projection for the complete raw-source wrapper. -/
theorem encodeRawSource_view (L m t q : ℕ) (b : Bool)
    (raw : BinarySourceFormation.RawStore L q) :
    BinaryHighTable.Projection.TrieRel payloadView (encodeRawSource L m t q b raw).table
      (if b then HighBaseEncoder.encodeLeftSource (m:=m) (t:=t)
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))
        else HighBaseEncoder.encodeRightSource (m:=m) (t:=t)
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).table := by
  have h:=encodeStored_view L m t q b (sourceForms L b) (rawInput b raw).value
  have hf : nativeForms (sourceForms L b) q=
      (fun d row col=>((if b then SourceCoordinates.leftForms (R:=ℤ) L d row col
        else SourceCoordinates.rightForms (R:=ℤ) L d row col):Vector ℤ q)) := by
    funext d row col
    cases b <;> exact congrArg (fun z:ℤ=>(z:Vector ℤ q)) (sourceForms_view L _ d row col)
  rw [hf,rawInput_view] at h
  cases b <;> exact h

#print axioms rawInput_magnitude
#print axioms rawPayload_bit_price
#print axioms rawInput_bit_price
#print axioms rawInput_bit_price_le_root_work
#print axioms encodeRawSource_view

#print axioms native_run_leaves_work_le
#print axioms native_run_root_work_le
#print axioms rawPayload_view
#print axioms rawInput_view
#print axioms encodeRawSource_readBase_view

#print axioms highCoefficient_magnitude
#print axioms sourceForms_magnitude
#print axioms shape_dims_bounds
#print axioms readBase_view
#print axioms source_readBase_view

#print axioms materialize_view
#print axioms contract_view
#print axioms sourceForms_view
#print axioms nextLayer_words
#print axioms parents_nonempty
#print axioms copyPayload_view
#print axioms storeRows_view
#print axioms encodeStored_view

#print axioms makeChild_view
#print axioms nodeChildren_view
#print axioms nextLayer_view
#print axioms run_leaves_view
#print axioms run_formed_view
#print axioms encode_leaves_view
#print axioms encode_formed_view

#print axioms highCoefficient_view
#print axioms baseTest_refines

#print axioms read_denseView
#print axioms tabulate_steps
#print axioms dot_view
#print axioms dotVector_view
end ThinMatrix.BinaryHighExecution
