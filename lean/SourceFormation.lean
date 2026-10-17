import WalshEmbedding
import CyclicRing
import RealCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Stored raw-source formation by direct Walsh summation

The source tables below store every normal/opposite word and every cyclic
coefficient. Direct Walsh summation is deliberately used: it visits `2^k`
terms per coefficient. At the aligned witness this larger formation cost
still fits strictly below the complete high-box exponent `2T-G`.

Finite read/write/arithmetic sites and their address depths are counted.
These counters are not a claim about the runtime of Lean's evaluator or an
implementation of arbitrary integer operations on a fixed-size machine.
-/

namespace ThinMatrix.SourceFormation

universe u
open scoped BigOperators
open WalshEmbedding CyclicRing
open Filter Asymptotics

structure Program (α : Type*) where
  value : α
  operations : ℕ

/-- A stored radix tree, with actual backing vectors at every level. -/
def Table (α : Type u) (radix : ℕ) : ℕ → Type u
  | 0 => α
  | n+1 => Vector (Table α radix n) radix

def tableRead {α : Type*} (radix : ℕ) :
    (n : ℕ) → Table α radix n → (Fin n → Fin radix) → α
  | 0, data, _ => data
  | n+1, data, key => tableRead radix n (data.get (key 0)) (fun i => key i.succ)

def tableReadProgram {α : Type*} (radix : ℕ) :
    (n : ℕ) → Table α radix n → (Fin n → Fin radix) → Program α
  | 0, data, _ => {value := data, operations := 1}
  | n+1, data, key =>
    let child := tableReadProgram radix n (data.get (key 0)) (fun i => key i.succ)
    { value := child.value, operations := child.operations+2 }

theorem tableReadProgram_value {α : Type*} (radix n : ℕ)
    (data : Table α radix n) (key : Fin n → Fin radix) :
    (tableReadProgram radix n data key).value = tableRead radix n data key := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tableReadProgram, tableRead, ih]

theorem tableReadProgram_cost {α : Type*} (radix n : ℕ)
    (data : Table α radix n) (key : Fin n → Fin radix) :
    (tableReadProgram radix n data key).operations = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tableReadProgram, ih]; omega

/-- Each child is evaluated once, stored, and then read for its value and
counter. Eight sites per branch cover allocation, reads, and accounting. -/
def tableBuild {α : Type*} (radix : ℕ) :
    (n : ℕ) → ((Fin n → Fin radix) → Program α) → Program (Table α radix n)
  | 0, f => f (fun i => Fin.elim0 i)
  | n+1, f =>
    let children := Vector.ofFn fun a =>
      tableBuild radix n (fun rest => f (Fin.cons a rest))
    { value := children.map (fun child => child.value)
      operations := (∑ a : Fin radix, (children.get a).operations) + 8*radix }

theorem tableRead_build {α : Type*} (radix n : ℕ)
    (f : (Fin n → Fin radix) → Program α) (key : Fin n → Fin radix) :
    tableRead radix n (tableBuild radix n f).value key = (f key).value := by
  induction n with
  | zero =>
    simp only [tableRead, tableBuild]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [tableBuild, tableRead, Vector.get_map, Vector.get_ofFn, ih]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem tableBuild_cost {α : Type*} (radix n B : ℕ)
    (f : (Fin n → Fin radix) → Program α)
    (hf : ∀ key, (f key).operations ≤ B) :
    (tableBuild radix n f).operations ≤ (B+8*radix*n)*radix^n := by
  induction n with
  | zero => simpa [tableBuild] using hf (fun i => Fin.elim0 i)
  | succ n ih =>
    simp only [tableBuild, Vector.get_ofFn]
    have hc : (∑ a : Fin radix,
        (tableBuild radix n (fun rest => f (Fin.cons a rest))).operations) ≤
        radix*((B+8*radix*n)*radix^n) := by
      calc
        _ ≤ ∑ _a : Fin radix, (B+8*radix*n)*radix^n :=
          Finset.sum_le_sum (fun a _ => ih _ (fun rest => hf _))
        _ = _ := by simp
    by_cases hr : radix = 0
    · subst radix
      simp
    · have hp : 1 ≤ radix^n := Nat.one_le_pow n radix (Nat.one_le_iff_ne_zero.mpr hr)
      have hm : 8*radix ≤ 8*radix*radix*radix^n := by
        have h1 : 1 ≤ radix*radix^n := by
          have hh : 1 ≤ radix := Nat.one_le_iff_ne_zero.mpr hr
          nlinarith
        simpa only [mul_one, Nat.mul_assoc] using Nat.mul_le_mul_left (8*radix) h1
      calc
        _ ≤ radix*((B+8*radix*n)*radix^n)+8*radix := Nat.add_le_add_right hc _
        _ ≤ (B+8*radix*(n+1))*radix^(n+1) := by
          rw [pow_succ]
          nlinarith

def boolIndex (b : Bool) : Fin 2 := if b then 1 else 0
def indexBool (i : Fin 2) : Bool := decide (i = 1)

theorem indexBool_boolIndex (b : Bool) : indexBool (boolIndex b) = b := by
  cases b <;> rfl

def cubeKey {n : ℕ} (b : Cube n) : Fin n → Fin 2 := fun i => boolIndex (b i)
def keyCube {n : ℕ} (b : Fin n → Fin 2) : Cube n := fun i => indexBool (b i)

theorem keyCube_cubeKey {n : ℕ} (b : Cube n) : keyCube (cubeKey b) = b := by
  funext i
  exact indexBool_boolIndex (b i)

def cubeList : (n : ℕ) → List (Cube n)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (cubeList n).map (Fin.cons false) ++ (cubeList n).map (Fin.cons true)

theorem cubeList_length (n : ℕ) : (cubeList n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cubeList, ih, pow_succ]; omega

theorem cubeList_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Cube n → R) :
    ((cubeList n).map f).sum = ∑ a, f a := by
  classical
  induction n with
  | zero =>
    simp only [cubeList, List.map_singleton, List.sum_singleton, Fintype.sum_unique]
    congr 1
  | succ n ih =>
    simp only [cubeList, List.map_append, List.map_map, List.sum_append]
    rw [ih, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,
      Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Fin.consEquiv, Equiv.coe_fn_mk]
    exact add_comm _ _

def vectorBuild {α : Type*} (n : ℕ) (f : Fin n → Program α) : Program (Vector α n) :=
  let children := Vector.ofFn f
  { value := children.map (fun child => child.value)
    operations := (∑ i : Fin n, (children.get i).operations)+8*n }

@[simp] theorem vectorBuild_get {α : Type*} (n : ℕ) (f : Fin n → Program α)
    (i : Fin n) : (vectorBuild n f).value.get i = (f i).value := by
  simp [vectorBuild]

theorem vectorBuild_cost {α : Type*} (n B : ℕ) (f : Fin n → Program α)
    (hf : ∀ i, (f i).operations ≤ B) :
    (vectorBuild n f).operations ≤ (B+8)*n := by
  simp only [vectorBuild, Vector.get_ofFn]
  have h : (∑ i : Fin n, (f i).operations) ≤ n*B := by
    calc
      _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp
  nlinarith

private theorem listCost_bound {α : Type*} (xs : List α) (cost : α → ℕ)
    (B : ℕ) (hc : ∀ a ∈ xs, cost a ≤ B) :
    (xs.map cost).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := hc a (by simp)
    have ht := ih (fun b hb => hc b (by simp [hb]))
    nlinarith

def walshTerm {k : ℕ} (read : Cube k → Program ℤ) (frequency outer : Cube k) : Program ℤ :=
  let value := read outer
  { value := if dotBits frequency outer then -value.value else value.value
    operations := value.operations+8*(k+1) }

/-- The list of all terms is evaluated once. Summation then reads the
stored term values; the counter also charges list allocation and traversal. -/
def walshProgram {k : ℕ} (read : Cube k → Program ℤ) (frequency : Cube k) : Program ℤ :=
  let terms := (cubeList k).map (walshTerm read frequency)
  { value := (terms.map (fun term => term.value)).sum
    operations := (terms.map (fun term => term.operations)).sum+8*terms.length+1 }

theorem walshProgram_cost {k B : ℕ} (read : Cube k → Program ℤ)
    (frequency : Cube k) (hr : ∀ outer, (read outer).operations ≤ B) :
    (walshProgram read frequency).operations ≤ (B+8*(k+1)+9)*2^k := by
  have h := listCost_bound (cubeList k) (fun outer => (walshTerm read frequency outer).operations)
    (B+8*(k+1)) (fun outer _ => Nat.add_le_add_right (hr outer) _)
  have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  simp only [walshProgram, List.map_map, List.length_map, cubeList_length]
  simp only [Function.comp_def]
  rw [cubeList_length] at h
  nlinarith

theorem walshProgram_correct {q k : ℕ} [NeZero q] (f : Cube k → Cyclic q)
    (read : Cube k → Program ℤ) (frequency : Cube k) (residue : Fin q)
    (hr : ∀ outer, (read outer).value = f outer residue) :
    (walshProgram read frequency).value = walsh f frequency residue := by
  classical
  simp only [walshProgram, List.map_map, walshTerm, Function.comp_def]
  simp_rw [hr]
  rw [cubeList_sum]
  unfold walsh
  rw [CyclicRing.sum_coeff]
  apply Finset.sum_congr rfl
  intro outer _
  rw [character_eq_sign_dot]
  by_cases hd : dotBits frequency outer = true <;>
    simp [bitSign, hd]

def normalIndex : NormalLetter → Fin 4
  | .x1 => 0 | .x2 => 1 | .p1 => 2 | .p2 => 3

def indexNormal (i : Fin 4) : NormalLetter :=
  if i = 0 then .x1 else if i = 1 then .x2 else if i = 2 then .p1 else .p2

def oppositeIndex : OppositeLetter → Fin 3
  | .s => 0 | .v => 1 | .w => 2

def indexOpposite (i : Fin 3) : OppositeLetter :=
  if i = 0 then .s else if i = 1 then .v else .w

theorem indexNormal_normalIndex (n : NormalLetter) : indexNormal (normalIndex n) = n := by
  cases n <;> rfl

theorem indexOpposite_oppositeIndex (n : OppositeLetter) : indexOpposite (oppositeIndex n) = n := by
  cases n <;> rfl

abbrev RawStore (L q : ℕ) := Table (Table (Vector ℤ q) 3 L) 4 L

def readRaw {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) : ℤ :=
  (tableRead 3 L (tableRead 4 L store (fun i => normalIndex (normal i)))
    (fun i => oppositeIndex (opposite i))).get residue

def readRawProgram {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (residue : Fin q) : Program ℤ :=
  let first := tableReadProgram 4 L store (fun i => normalIndex (normal i))
  let second := tableReadProgram 3 L first.value (fun i => oppositeIndex (opposite i))
  { value := second.value.get residue
    operations := first.operations+second.operations+1 }

theorem readRawProgram_value {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    (readRawProgram store normal opposite residue).value = readRaw store normal opposite residue := by
  simp only [readRawProgram, tableReadProgram_value, readRaw]

theorem readRawProgram_cost {L q : ℕ} (store : RawStore L q)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    (readRawProgram store normal opposite residue).operations = 4*L+3 := by
  simp only [readRawProgram, tableReadProgram_cost]
  omega

def rawBuild {L q : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector ℤ q)) :
    Program (RawStore L q) :=
  tableBuild 4 L fun normal => tableBuild 3 L fun opposite =>
    f (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i))

theorem readRaw_build {L q : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector ℤ q))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    readRaw (rawBuild f).value normal opposite residue = (f normal opposite).value.get residue := by
  unfold readRaw rawBuild
  rw [tableRead_build, tableRead_build]
  simp only [indexNormal_normalIndex, indexOpposite_oppositeIndex]

theorem rawBuild_cost {L q B : ℕ}
    (f : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Program (Vector ℤ q))
    (hf : ∀ normal opposite, (f normal opposite).operations ≤ B) :
    (rawBuild f).operations ≤ (B+56*L)*12^L := by
  have ho (normal : Fin L → Fin 4) :
      (tableBuild 3 L (fun opposite =>
        f (fun i => indexNormal (normal i)) (fun i => indexOpposite (opposite i)))).operations ≤
        (B+24*L)*3^L := by
    simpa using tableBuild_cost 3 L B _ (fun opposite => hf _ _)
  have hn := tableBuild_cost 4 L ((B+24*L)*3^L) _ ho
  have hp : 1 ≤ 3^L := Nat.one_le_pow L 3 (by norm_num)
  unfold rawBuild
  calc
    _ ≤ ((B+24*L)*3^L+32*L)*4^L := by simpa using hn
    _ ≤ (B+56*L)*12^L := by
      have hh : 32*L ≤ 32*L*3^L := by nlinarith
      rw [show (12:ℕ) = 3*4 by norm_num, mul_pow]
      calc
        _ ≤ ((B+56*L)*3^L)*4^L := Nat.mul_le_mul_right _ (by nlinarith)
        _ = _ := by ring

def cubeSupport {L : ℕ} (mask : Cube L) : Finset (Fin L) :=
  Finset.univ.filter fun i => mask i

theorem cubeSupport_injective {L : ℕ} : Function.Injective (@cubeSupport L) := by
  intro a b h
  funext i
  have hi := Finset.ext_iff.mp h i
  apply Bool.eq_iff_iff.mpr
  simpa [cubeSupport] using hi

def maskEqual {L : ℕ} (a b : Cube L) : Bool :=
  (List.finRange L).all fun i => decide (a i = b i)

theorem maskEqual_true {L : ℕ} (a b : Cube L) : maskEqual a b = true ↔ a = b := by
  simp [maskEqual, funext_iff]

def maskSlots {L : ℕ} (masks : List (Cube L)) : Finset (Finset (Fin L)) :=
  (masks.map cubeSupport).toFinset

def goodMaskProgram {L : ℕ} (masks : List (Cube L)) (mask : Cube L) : Program Bool :=
  { value := masks.any (maskEqual mask)
    operations := 8*(L+1)^2*(masks.length+1) }

theorem goodMaskProgram_correct {L : ℕ} (masks : List (Cube L)) (mask : Cube L) :
    (goodMaskProgram masks mask).value = decide (cubeSupport mask ∈ maskSlots masks) := by
  apply Bool.eq_iff_iff.mpr
  simp only [goodMaskProgram, List.any_eq_true, maskEqual_true, decide_eq_true_eq,
    maskSlots, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨other, hm, heq⟩
    exact ⟨other, hm, congrArg cubeSupport heq.symm⟩
  · rintro ⟨other, hm, heq⟩
    exact ⟨other, hm, (cubeSupport_injective heq).symm⟩

abbrev GoodStore (L : ℕ) := Table Bool 2 L

def prepareGood {L : ℕ} (masks : List (Cube L)) : Program (GoodStore L) :=
  tableBuild 2 L fun key => goodMaskProgram masks (keyCube key)

def readGood {L : ℕ} (store : GoodStore L) (normal : Fin L → NormalLetter) : Bool :=
  tableRead 2 L store (cubeKey (fun i => decide (normalIsP (normal i))))

theorem readGood_prepare {L : ℕ} (masks : List (Cube L))
    (normal : Fin L → NormalLetter) :
    readGood (prepareGood masks).value normal = decide (normalSupport normal ∈ maskSlots masks) := by
  unfold readGood prepareGood
  rw [tableRead_build, keyCube_cubeKey, goodMaskProgram_correct]
  simp only [cubeSupport, normalSupport, decide_eq_true_eq]
  rfl

/-- Even a direct scan of the supplied good-mask list is performed only
while preparing the small table, and never for each raw word. -/
theorem prepareGood_cost {L : ℕ} (masks : List (Cube L)) (hn : masks.Nodup) :
    (prepareGood masks).operations ≤ 32*(L+1)^2*4^L := by
  have hc : masks.length ≤ 2^L := by
    simpa [Cube, Fintype.card_fun] using hn.length_le_card
  have h := tableBuild_cost 2 L (8*(L+1)^2*(masks.length+1))
    (fun key => goodMaskProgram masks (keyCube key)) (fun _ => le_rfl)
  have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by norm_num)
  unfold prepareGood
  calc
    _ ≤ (8*(L+1)^2*(masks.length+1)+16*L)*2^L := by simpa using h
    _ ≤ 32*(L+1)^2*4^L := by
      rw [show (4:ℕ) = 2*2 by norm_num, mul_pow]
      rw [← Nat.mul_assoc]
      apply Nat.mul_le_mul_right
      nlinarith

def columnFunction {L d : ℕ} (columns : Vector (Vector Bool d) L) : Fin L → Cube d :=
  fun j i => (columns.get j).get i

def asCube {d : ℕ} (bits : Vector Bool d) : Cube d := fun i => bits.get i

theorem asCube_ofFn {d : ℕ} (bits : Cube d) : asCube (Vector.ofFn bits) = bits := by
  funext i
  simp [asCube]

def powerTwo : ℕ → ℤ
  | 0 => 1
  | h+1 => 2*powerTwo h

theorem powerTwo_eq (h : ℕ) : powerTwo h = (2:ℤ)^h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [powerTwo, ih, pow_succ, mul_comm]

abbrev LeftRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube k → Cube m → Cube m → Fin q → Program ℤ

abbrev RightRead (L m k q : ℕ) :=
  Finset (Fin L) → Cube L → Cube m → Cube m → Cube k → Fin q → Program ℤ

/-- The maps are genuine stored binary columns. Only the good-mask table
is read during formation; no linear-independence test occurs here. -/
structure Environment (L m k : ℕ) where
  good : GoodStore L
  gammaColumns : Vector (Vector Bool m) L
  deltaColumns : Vector (Vector Bool k) L

def Environment.gamma {L m k : ℕ} (env : Environment L m k) : Cube L → Cube m :=
  columnMap (columnFunction env.gammaColumns)

def Environment.delta {L m k : ℕ} (env : Environment L m k) : Cube L → Cube k :=
  columnMap (columnFunction env.deltaColumns)

/-- Metadata is shared by all cyclic coefficients and Walsh terms of one
word. In particular the mapped middle indices and frequency are stored
vectors before the summation loops begin. -/
structure Metadata (L m k : ℕ) where
  support : Finset (Fin L)
  outer : Vector Bool L
  normalWeight : ℕ
  oppositeWeight : ℕ
  gammaNormal : Vector Bool m
  gammaOpposite : Vector Bool m
  frequency : Vector Bool k
  good : Bool

def metadata {L m k : ℕ} (env : Environment L m k)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : Metadata L m k :=
  let p2 := Vector.ofFn (normalP2Bits normal)
  let w := Vector.ofFn (oppositeWBits opposite)
  let v := Vector.ofFn (oppositeVBits opposite)
  { support := normalSupport normal
    outer := Vector.ofFn (normalOuterBits normal)
    normalWeight := ones (asCube p2)
    oppositeWeight := ones (asCube w)
    gammaNormal := Vector.ofFn (env.gamma (asCube p2))
    gammaOpposite := Vector.ofFn (env.gamma (asCube w))
    frequency := Vector.ofFn (env.delta (asCube v))
    good := readGood env.good normal }

def metadataCost (L m k : ℕ) : ℕ := 100*(L+m+k+1)^2

def leftWordProgram {L m k q : ℕ} (env : Environment L m k)
    (read : LeftRead L m k q) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : Program (Vector ℤ q) :=
  let entry := metadata env normal opposite
  let weight := powerTwo entry.normalWeight
  let coefficients := if entry.good ∧
      (entry.oppositeWeight:ℤ)-(entry.normalWeight:ℤ) = run then
    vectorBuild q fun residue =>
      let sum := walshProgram
        (fun outer => read entry.support (asCube entry.outer) outer
          (asCube entry.gammaNormal) (asCube entry.gammaOpposite) residue)
        (asCube entry.frequency)
      { value := weight * sum.value
        operations := sum.operations+2 }
  else vectorBuild q fun _ => {value := 0, operations := 1}
  { value := coefficients.value
    operations := coefficients.operations+metadataCost L m k }

def rightWordProgram {L m k q : ℕ} (env : Environment L m k)
    (read : RightRead L m k q) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) : Program (Vector ℤ q) :=
  let entry := metadata env normal opposite
  let weight := powerTwo entry.normalWeight
  let coefficients := if entry.good ∧
      (entry.normalWeight:ℤ)-(entry.oppositeWeight:ℤ) = run then
    vectorBuild q fun residue =>
      let sum := walshProgram
        (fun outer => read entry.support (asCube entry.outer)
          (asCube entry.gammaOpposite) (asCube entry.gammaNormal) outer residue)
        (asCube entry.frequency)
      { value := weight * sum.value
        operations := sum.operations+2 }
  else vectorBuild q fun _ => {value := 0, operations := 1}
  { value := coefficients.value
    operations := coefficients.operations+metadataCost L m k }

def formLeftSource {L m k q : ℕ} (env : Environment L m k)
    (read : LeftRead L m k q) (run : ℤ) : Program (RawStore L q) :=
  rawBuild (leftWordProgram env read run)

def formRightSource {L m k q : ℕ} (env : Environment L m k)
    (read : RightRead L m k q) (run : ℤ) : Program (RawStore L q) :=
  rawBuild (rightWordProgram env read run)

theorem weighted_coeff {q : ℕ} [NeZero q] (h : ℕ) (a : Cyclic q) (residue : Fin q) :
    ((2:Cyclic q)^h*a) residue = powerTwo h * a residue := by
  rw [powerTwo_eq]
  simpa only [Int.cast_pow, Int.cast_ofNat] using
    intCast_mul_coeff ((2:ℤ)^h) a residue

theorem leftWordProgram_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : LeftRead L m k q)
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).value =
      X Q bits outer r s residue)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (residue : Fin q) :
    (leftWordProgram env read run normal opposite).value.get residue =
      rawLeftSource X good env.gamma env.delta run normal opposite residue := by
  simp only [leftWordProgram, metadata, asCube_ofFn, hg, decide_eq_true_eq]
  unfold rawLeftSource
  split_ifs with h
  · rw [vectorBuild_get]
    change powerTwo _ * (walshProgram _ _).value = _
    rw [walshProgram_correct _ _ _ residue (fun outer => hr _ _ _ _ _ _), weighted_coeff]
  · rw [vectorBuild_get]
    rfl

theorem rightWordProgram_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : RightRead L m k q)
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).value =
      Y Q bits r s outer residue)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (residue : Fin q) :
    (rightWordProgram env read run normal opposite).value.get residue =
      rawRightSource Y good env.gamma env.delta run normal opposite residue := by
  simp only [rightWordProgram, metadata, asCube_ofFn, hg, decide_eq_true_eq]
  unfold rawRightSource
  split_ifs with h
  · rw [vectorBuild_get]
    change powerTwo _ * (walshProgram _ _).value = _
    rw [walshProgram_correct _ _ _ residue (fun outer => hr _ _ _ _ _ _), weighted_coeff]
  · rw [vectorBuild_get]
    rfl

theorem formLeftSource_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : LeftRead L m k q)
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).value =
      X Q bits outer r s residue)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (residue : Fin q) :
    readRaw (formLeftSource env read run).value normal opposite residue =
      rawLeftSource X good env.gamma env.delta run normal opposite residue := by
  rw [formLeftSource, readRaw_build]
  exact leftWordProgram_correct env read X good hg hr run normal opposite residue

theorem formRightSource_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : RightRead L m k q)
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).value =
      Y Q bits r s outer residue)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter)
    (residue : Fin q) :
    readRaw (formRightSource env read run).value normal opposite residue =
      rawRightSource Y good env.gamma env.delta run normal opposite residue := by
  rw [formRightSource, readRaw_build]
  exact rightWordProgram_correct env read Y good hg hr run normal opposite residue

def wordCoefficientBudget (k B : ℕ) : ℕ := (B+8*(k+1)+19)*2^k
def wordBudget (L m k q B : ℕ) : ℕ := metadataCost L m k+wordCoefficientBudget k B*q
def sourceBudget (L m k q B : ℕ) : ℕ := (wordBudget L m k q B+56*L)*12^L

private theorem walshCell_cost {k B : ℕ} (read : Cube k → Program ℤ)
    (frequency : Cube k) (hr : ∀ outer, (read outer).operations ≤ B) :
    (walshProgram read frequency).operations+2+8 ≤ wordCoefficientBudget k B := by
  have h := walshProgram_cost read frequency hr
  have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  unfold wordCoefficientBudget
  nlinarith

theorem leftWordProgram_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : LeftRead L m k q)
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).operations ≤ B)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    (leftWordProgram env read run normal opposite).operations ≤ wordBudget L m k q B := by
  unfold leftWordProgram wordBudget
  dsimp only
  split_ifs
  · have h := vectorBuild_cost q (wordCoefficientBudget k B-8)
      (fun residue =>
        { value := powerTwo (metadata env normal opposite).normalWeight *
            (walshProgram
              (fun outer => read (metadata env normal opposite).support
                (asCube (metadata env normal opposite).outer) outer
                (asCube (metadata env normal opposite).gammaNormal)
                (asCube (metadata env normal opposite).gammaOpposite) residue)
              (asCube (metadata env normal opposite).frequency)).value
          operations := (walshProgram
              (fun outer => read (metadata env normal opposite).support
                (asCube (metadata env normal opposite).outer) outer
                (asCube (metadata env normal opposite).gammaNormal)
                (asCube (metadata env normal opposite).gammaOpposite) residue)
              (asCube (metadata env normal opposite).frequency)).operations+2 })
      (fun residue => by
        dsimp only
        apply Nat.le_sub_of_add_le
        apply walshCell_cost
        intro outer
        exact hr _ _ outer _ _ residue)
    have hb : 8 ≤ wordCoefficientBudget k B := by
      have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
      unfold wordCoefficientBudget
      nlinarith
    simpa [Nat.sub_add_cancel hb, Nat.add_comm] using
      Nat.add_le_add_right h (metadataCost L m k)
  · have h := vectorBuild_cost q 1 (fun _ => {value := (0:ℤ), operations := 1})
      (fun _ => le_rfl)
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
    have hb : 9 ≤ wordCoefficientBudget k B := by unfold wordCoefficientBudget; nlinarith
    have hh := Nat.mul_le_mul_right q hb
    omega

theorem rightWordProgram_eq_left {L m k q : ℕ} (env : Environment L m k)
    (read : RightRead L m k q) (run : ℤ)
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    rightWordProgram env read run normal opposite =
      leftWordProgram env (fun Q bits outer r s residue => read Q bits s r outer residue)
        (-run) normal opposite := by
  unfold rightWordProgram leftWordProgram
  dsimp only
  have hh : ((metadata env normal opposite).good = true ∧
      ((metadata env normal opposite).normalWeight:ℤ)-
        ((metadata env normal opposite).oppositeWeight:ℤ) = run) ↔
      ((metadata env normal opposite).good = true ∧
      ((metadata env normal opposite).oppositeWeight:ℤ)-
        ((metadata env normal opposite).normalWeight:ℤ) = -run) := by
    constructor <;> rintro ⟨hg, heq⟩ <;> exact ⟨hg, by linarith⟩
  simp only [hh]

theorem rightWordProgram_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : RightRead L m k q)
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).operations ≤ B)
    (run : ℤ) (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) :
    (rightWordProgram env read run normal opposite).operations ≤ wordBudget L m k q B := by
  rw [rightWordProgram_eq_left]
  exact leftWordProgram_cost env _ (fun Q bits outer r s residue => hr Q bits s r outer residue)
    (-run) normal opposite

theorem formLeftSource_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : LeftRead L m k q)
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).operations ≤ B)
    (run : ℤ) :
    (formLeftSource env read run).operations ≤ sourceBudget L m k q B := by
  exact rawBuild_cost _ (fun normal opposite => leftWordProgram_cost env read hr run normal opposite)

theorem formRightSource_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : RightRead L m k q)
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).operations ≤ B)
    (run : ℤ) :
    (formRightSource env read run).operations ≤ sourceBudget L m k q B := by
  exact rawBuild_cost _ (fun normal opposite => rightWordProgram_cost env read hr run normal opposite)

def runValue (m : ℕ) (i : Fin (2*m+1)) : ℤ := (i.val:ℤ)-(m:ℤ)

theorem runValue_mem (m : ℕ) (i : Fin (2*m+1)) :
    -(m:ℤ) ≤ runValue m i ∧ runValue m i ≤ (m:ℤ) := by
  unfold runValue
  have hi := i.isLt
  omega

def runIndex (m : ℕ) (run : ℤ) (h : -(m:ℤ) ≤ run ∧ run ≤ (m:ℤ)) : Fin (2*m+1) :=
  ⟨(run+(m:ℤ)).toNat, by omega⟩

theorem runValue_runIndex (m : ℕ) (run : ℤ)
    (h : -(m:ℤ) ≤ run ∧ run ≤ (m:ℤ)) : runValue m (runIndex m run h) = run := by
  unfold runValue runIndex
  change (((run+(m:ℤ)).toNat:ℤ)-(m:ℤ)) = run
  omega

def formLeftRuns {L m k q : ℕ} (env : Environment L m k) (read : LeftRead L m k q) :
    Program (Vector (RawStore L q) (2*m+1)) :=
  vectorBuild (2*m+1) fun i => formLeftSource env read (runValue m i)

def formRightRuns {L m k q : ℕ} (env : Environment L m k) (read : RightRead L m k q) :
    Program (Vector (RawStore L q) (2*m+1)) :=
  vectorBuild (2*m+1) fun i => formRightSource env read (runValue m i)

theorem formLeftRuns_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : LeftRead L m k q)
    (X : RawLeftInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).value =
      X Q bits outer r s residue)
    (run : ℤ) (h : -(m:ℤ) ≤ run ∧ run ≤ (m:ℤ))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    readRaw ((formLeftRuns env read).value.get (runIndex m run h)) normal opposite residue =
      rawLeftSource X good env.gamma env.delta run normal opposite residue := by
  rw [formLeftRuns, vectorBuild_get]
  rw [runValue_runIndex]
  exact formLeftSource_correct env read X good hg hr run normal opposite residue

theorem formRightRuns_correct {L m k q : ℕ} [NeZero q]
    (env : Environment L m k) (read : RightRead L m k q)
    (Y : RawRightInput L m k (Cyclic q)) (good : Finset (Finset (Fin L)))
    (hg : ∀ normal, readGood env.good normal = decide (normalSupport normal ∈ good))
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).value =
      Y Q bits r s outer residue)
    (run : ℤ) (h : -(m:ℤ) ≤ run ∧ run ≤ (m:ℤ))
    (normal : Fin L → NormalLetter) (opposite : Fin L → OppositeLetter) (residue : Fin q) :
    readRaw ((formRightRuns env read).value.get (runIndex m run h)) normal opposite residue =
      rawRightSource Y good env.gamma env.delta run normal opposite residue := by
  rw [formRightRuns, vectorBuild_get]
  rw [runValue_runIndex]
  exact formRightSource_correct env read Y good hg hr run normal opposite residue

theorem formLeftRuns_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : LeftRead L m k q)
    (hr : ∀ Q bits outer r s residue, (read Q bits outer r s residue).operations ≤ B) :
    (formLeftRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1) := by
  exact vectorBuild_cost _ _ _ (fun i => formLeftSource_cost env read hr (runValue m i))

theorem formRightRuns_cost {L m k q B : ℕ} (env : Environment L m k)
    (read : RightRead L m k q)
    (hr : ∀ Q bits r s outer residue, (read Q bits r s outer residue).operations ≤ B) :
    (formRightRuns env read).operations ≤ (sourceBudget L m k q B+8)*(2*m+1) := by
  exact vectorBuild_cost _ _ _ (fun i => formRightSource_cost env read hr (runValue m i))

theorem sourceBudget_polynomial (L m k q B : ℕ) (hq : 1 ≤ q) :
    sourceBudget L m k q B ≤ 200*(B+1)*(L+m+k+1)^2*q*12^L*2^k := by
  let P := L+m+k+1
  have hP : 1 ≤ P := by omega
  have hP2 : 1 ≤ P^2 := by nlinarith
  have hPP : P ≤ P^2 := by nlinarith
  have hL : L ≤ P^2 := by omega
  have hk : k+1 ≤ P^2 := by omega
  have hB : B ≤ B*P^2 := by nlinarith
  have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  have hF : 1 ≤ q*2^k := by nlinarith
  have hpoly : 100*P^2+B+8*(k+1)+19+56*L ≤ 200*(B+1)*P^2 := by nlinarith
  have hmeta : 100*P^2 ≤ 100*P^2*(q*2^k) := Nat.le_mul_of_pos_right _ (by omega)
  have hlast : 56*L ≤ 56*L*(q*2^k) := Nat.le_mul_of_pos_right _ (by omega)
  unfold sourceBudget wordBudget wordCoefficientBudget metadataCost
  change (100*P^2+(B+8*(k+1)+19)*2^k*q+56*L)*12^L ≤ _
  calc
    _ ≤ ((100*P^2+B+8*(k+1)+19+56*L)*(q*2^k))*12^L := by
      apply Nat.mul_le_mul_right
      nlinarith
    _ ≤ (200*(B+1)*P^2*(q*2^k))*12^L :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpoly)
    _ = _ := by dsimp [P]; ring

theorem logTwelve : Real.log 12 < (9/5 : ℝ)*Real.log 4 := by
  have h := Real.log_lt_log (by norm_num : 0 < (12:ℝ)^5)
    (by norm_num : (12:ℝ)^5 < (4:ℝ)^9)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

noncomputable def directSourceExponent : ℝ := (23/10 : ℝ)*RealCertificate.c-1/2

theorem directSource_gap : directSourceExponent + 1/1000 <
    2*RealCertificate.T-RealCertificate.G := by
  have ht := RealCertificate.TEnclosure.1
  have hg := RealCertificate.GEnclosure.2
  norm_num [directSourceExponent, RealCertificate.c] at ht hg ⊢
  linarith

theorem rounded_raw_cost (m : ℕ) :
    (12:ℝ)^(Nat.ceil (RealCertificate.c*(m:ℝ))) *
      (2:ℝ)^(Nat.ceil (RealCertificate.c*(m:ℝ))-m) ≤
      64 * (((4:ℝ)^m)^directSourceExponent) := by
  open RealCertificate in
  let L := Nat.ceil (c*(m:ℝ))
  change (12:ℝ)^L * (2:ℝ)^(L-m) ≤ 64 * (((4:ℝ)^m)^directSourceExponent)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hc : 1 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have hceil : RealCertificate.c*(m:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hml : m ≤ L := by exact_mod_cast (show (m:ℝ) ≤ (L:ℝ) by nlinarith)
  have hL : (L:ℝ) ≤ RealCertificate.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ RealCertificate.c*(m:ℝ) by positivity)).le
  have h4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 = Real.log 4/2 := by linarith [RealCertificate.logFour]
  have h64 : Real.log 64 = 3 * Real.log 4 := by
    convert Real.log_pow (4:ℝ) 3 using 1 <;> norm_num
  have h12L := mul_le_mul_of_nonneg_left logTwelve.le (Nat.cast_nonneg L)
  have hceil4 := mul_le_mul_of_nonneg_right hL h4pos.le
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num : (64:ℝ) ≠ 0) (by positivity),
    Real.log_rpow (by positivity), Real.log_pow, h64, Nat.cast_sub hml, h2]
  norm_num [directSourceExponent, RealCertificate.c] at hceil4 ⊢
  nlinarith

private theorem dimension_exp (m : ℕ) (a : ℝ) :
    (((4:ℝ)^m)^a) = Real.exp ((a*Real.log 4)*(m:ℝ)) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  ring

/-- Every fixed polynomial overhead in the logarithmic dimension fits
inside the proved strict source-versus-box gap, with constant one
eventually. This includes metadata, all matching degree runs, direct
good-table preparation, and a polynomially bounded input-address routine. -/
theorem eventual_polynomial_source_fit (degree : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in Filter.atTop,
      C*((m:ℝ)+1)^degree *
        (12:ℝ)^(Nat.ceil (RealCertificate.c*(m:ℝ))) *
        (2:ℝ)^(Nat.ceil (RealCertificate.c*(m:ℝ))-m) ≤
      (((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  have hgap : directSourceExponent*Real.log 4 <
      (2*RealCertificate.T-RealCertificate.G)*Real.log 4 := by
    apply mul_lt_mul_of_pos_right _ (Real.log_pos (by norm_num))
    linarith [directSource_gap]
  have hsmall := (isLittleO_exp_mul_rpow_of_lt (degree:ℝ) hgap).natCast_atTop
  have hscaled := hsmall.const_mul_left (C*64*2^degree)
  have hb := hscaled.bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [hb, Filter.eventually_ge_atTop (1:ℕ)] with m hm hmn
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hmn
  have hpow : ((m:ℝ)+1)^degree ≤ (2:ℝ)^degree*(m:ℝ)^degree := by
    rw [← mul_pow]
    gcongr
    linarith
  have hraw := rounded_raw_cost m
  have hCm : 0 ≤ C*((m:ℝ)+1)^degree := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hraw hCm
  have hsecond := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ C*(64*((4:ℝ)^m)^directSourceExponent) by positivity)
  have hbound : (C*64*2^degree)*
      (Real.exp ((directSourceExponent*Real.log 4)*(m:ℝ))*(m:ℝ)^degree) ≤
      Real.exp (((2*RealCertificate.T-RealCertificate.G)*Real.log 4)*(m:ℝ)) := by
    simpa only [Real.rpow_natCast, Real.norm_of_nonneg (by positivity :
      0 ≤ (C*64*2^degree)*(Real.exp ((directSourceExponent*Real.log 4)*(m:ℝ))*
        (m:ℝ)^degree)), Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] using hm
  rw [dimension_exp] at hfirst hsecond
  rw [dimension_exp]
  nlinarith

/-- Instantiation for the actual finite source counter. The address
routine may take any fixed polynomial number of sites in `m`; every
complete cyclic coefficient is still charged by the displayed `q`. -/
theorem eventual_sourceBudget_fit (degree C : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ q B : ℕ, 1 ≤ q → B ≤ C*(m+1)^degree →
      (sourceBudget (Nat.ceil (RealCertificate.c*(m:ℝ))) m
        (Nat.ceil (RealCertificate.c*(m:ℝ))-m) q B : ℝ) ≤
        (q:ℝ)*(((4:ℝ)^m)^(2*RealCertificate.T-RealCertificate.G)) := by
  let A : ℝ := 2*RealCertificate.c+3
  let constant : ℝ := 200*((C:ℝ)+1)*A^2
  have hA : 0 < A := by norm_num [A, RealCertificate.c]
  have hconstant : 0 ≤ constant := by positivity
  have hfit := eventual_polynomial_source_fit (degree+2) constant hconstant
  filter_upwards [hfit] with m hm
  intro q B hq hB
  let L := Nat.ceil (RealCertificate.c*(m:ℝ))
  let k := L-m
  have hL : (L:ℝ) ≤ RealCertificate.c*(m:ℝ)+1 :=
    (Nat.ceil_lt_add_one (by unfold RealCertificate.c; positivity :
      0 ≤ RealCertificate.c*(m:ℝ))).le
  have hk : (k:ℝ) ≤ L := by exact_mod_cast (Nat.sub_le L m)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hP : ((L:ℝ)+(m:ℝ)+(k:ℝ)+1) ≤ A*((m:ℝ)+1) := by
    norm_num [A, RealCertificate.c] at hL ⊢
    nlinarith
  have hp : 1 ≤ ((m:ℝ)+1)^degree := one_le_pow₀ (by linarith : (1:ℝ) ≤ m+1)
  have hBc : (B:ℝ) ≤ (C:ℝ)*((m:ℝ)+1)^degree := by exact_mod_cast hB
  have hB' : (B:ℝ)+1 ≤ ((C:ℝ)+1)*((m:ℝ)+1)^degree := by nlinarith
  have hc : 200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2 ≤
      constant*((m:ℝ)+1)^(degree+2) := by
    calc
      _ ≤ 200*(((C:ℝ)+1)*((m:ℝ)+1)^degree)*(A*((m:ℝ)+1))^2 := by gcongr
      _ = _ := by unfold constant; rw [pow_add]; ring
  have hs := sourceBudget_polynomial L m k q B hq
  have hsR : (sourceBudget L m k q B:ℝ) ≤
      200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := by
    exact_mod_cast hs
  change (sourceBudget L m k q B:ℝ) ≤ _
  calc
    _ ≤ 200*((B:ℝ)+1)*((L:ℝ)+(m:ℝ)+(k:ℝ)+1)^2*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := hsR
    _ ≤ constant*((m:ℝ)+1)^(degree+2)*(q:ℝ)*(12:ℝ)^L*(2:ℝ)^k := by gcongr
    _ = (q:ℝ)*(constant*((m:ℝ)+1)^(degree+2)*(12:ℝ)^L*(2:ℝ)^k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q)

end ThinMatrix.SourceFormation

#print axioms ThinMatrix.SourceFormation.tableRead_build
#print axioms ThinMatrix.SourceFormation.tableReadProgram_cost
#print axioms ThinMatrix.SourceFormation.readRawProgram_cost
#print axioms ThinMatrix.SourceFormation.tableBuild_cost
#print axioms ThinMatrix.SourceFormation.cubeList_sum
#print axioms ThinMatrix.SourceFormation.directSource_gap
#print axioms ThinMatrix.SourceFormation.rounded_raw_cost
#print axioms ThinMatrix.SourceFormation.prepareGood_cost
#print axioms ThinMatrix.SourceFormation.formLeftSource_correct
#print axioms ThinMatrix.SourceFormation.formRightSource_correct
#print axioms ThinMatrix.SourceFormation.formLeftSource_cost
#print axioms ThinMatrix.SourceFormation.formRightSource_cost
#print axioms ThinMatrix.SourceFormation.formLeftRuns_cost
#print axioms ThinMatrix.SourceFormation.formLeftRuns_correct
#print axioms ThinMatrix.SourceFormation.formRightRuns_correct
#print axioms ThinMatrix.SourceFormation.sourceBudget_polynomial
#print axioms ThinMatrix.SourceFormation.eventual_polynomial_source_fit
#print axioms ThinMatrix.SourceFormation.eventual_sourceBudget_fit
