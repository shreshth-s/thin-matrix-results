import ComputableParameters
import BackendScalarBits
import ToomExecutionBound
import BinaryMultiplierAdapter

/-! Counted binary execution of the uniform parameter selector. Natural values
are semantic projections of canonical stored words. Power, comparison and
remainder operations execute the proved bit-list programs. -/
namespace ThinMatrix.ParameterExecution
open IntegerArithmetic BackendScalarBits ComputableParameters
open scoped BigOperators
open Filter Asymptotics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

structure Word where
  bits : List Bool
  canonical : bits.length = (value bits).size

def Word.view (x : Word) : ℕ := value x.bits

def input (x : ℕ) : Word := ⟨x.bits, by simp only [Nat.size_eq_bits_len,value_bits]⟩
@[simp] theorem input_view (x : ℕ) : (input x).view = x := value_bits x
@[simp] theorem word_width (x : Word) : x.bits.length = x.view.size := x.canonical

structure Run (A : Type) where
  value : A
  bitSteps : ℕ

/-- Input serialization is the proved bit extraction/shift loop. -/
def serialize (n : ℕ) : Run Word :=
  let out := BinaryMultiplierAdapter.encodeNat n
  ⟨⟨out.value,by rw [BinaryMultiplierAdapter.encodeNat_value];simp only [Nat.size_eq_bits_len,value_bits]⟩,
    out.bitSteps⟩
theorem serialize_eq_input (n : ℕ) : (serialize n).value = input n := by
  dsimp only [serialize,input]
  congr 1
  exact BinaryMultiplierAdapter.encodeNat_value n

/-- Public natural metadata is decoded by an actual charged traversal. -/
def decode (x : Word) : Run ℕ :=
  let out := BinaryMultiplierAdapter.decodeNat x.bits
  ⟨out.value,out.bitSteps⟩
@[simp] theorem decode_value (x : Word) : (decode x).value = x.view :=
  BinaryMultiplierAdapter.decodeNat_value x.bits

def normalize (bs : List Bool) : Run Word :=
  let out := trimCounted bs
  ⟨⟨out.1, by dsimp [out]; rw [trimCounted_value]; exact trimCounted_length bs⟩, out.2⟩
@[simp] theorem normalize_view (bs : List Bool) : (normalize bs).value.view = value bs :=
  trimCounted_value bs

def copy (x : Word) : Run Word :=
  let out := copyBits x.bits
  ⟨⟨out.1, by dsimp [out]; rw [copyBits_value]; exact x.canonical⟩,out.2⟩
@[simp] theorem copy_view (x : Word) : (copy x).value.view = x.view := by
  simp only [copy, Word.view, copyBits_value]

def add (x y : Word) : Run Word :=
  let raw := addCounted x.bits y.bits false
  let out := normalize raw.1
  ⟨out.value,raw.2+out.bitSteps+1⟩
@[simp] theorem add_view (x y : Word) : (add x y).value.view = x.view+y.view := by
  change (normalize (addCounted x.bits y.bits false).1).value.view = _
  rw [normalize_view,(addCounted_projections _ _ _).1,addBits_correct]
  simp only [digit_false,add_zero,Word.view]

def mul (x y : Word) : Run Word :=
  let raw := mulCounted x.bits y.bits
  let out := normalize raw.1
  ⟨out.value,raw.2+out.bitSteps+1⟩
@[simp] theorem mul_view (x y : Word) : (mul x y).value.view = x.view*y.view := by
  change (normalize (mulCounted x.bits y.bits).1).value.view = _
  rw [normalize_view,(mulCounted_projections _ _).1,mulBits_correct]
  rfl

def less (x y : Word) : Run Bool :=
  let out := unsignedLessCounted x.bits y.bits
  ⟨out.1,out.2+1⟩
@[simp] theorem less_view (x y : Word) : (less x y).value = true ↔ x.view < y.view :=
  unsignedLess_correct x.bits y.bits

def isZero : List Bool → Run Bool
  | [] => ⟨true,1⟩
  | b::bs => let out := isZero bs; ⟨(!b)&&out.value,out.bitSteps+2⟩
@[simp] theorem isZero_view (bs : List Bool) : (isZero bs).value = true ↔ value bs = 0 := by
  induction bs with
  | nil => simp [isZero,value]
  | cons b bs ih => cases b <;> simp [isZero,value,ih]
@[simp] theorem isZero_steps (bs : List Bool) : (isZero bs).bitSteps = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [isZero,List.length_cons,ih]; omega

/-- The divisor is positive at every trial site. -/
def nondivisor (p d : Word) : Run Bool :=
  let raw := divideCounted d.bits p.bits
  let zero := isZero raw.1.2
  ⟨!zero.value,raw.2+zero.bitSteps+1⟩
theorem nondivisor_view (p d : Word) (hd : 0 < d.view) :
    (nondivisor p d).value = true ↔ ¬ d.view ∣ p.view := by
  have h := (unsigned_divide_correct d.bits p.bits hd).2
  change (!(isZero _).value) = true ↔ _
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  apply not_congr
  rw [isZero_view,h]
  exact (Nat.dvd_iff_mod_eq_zero).symm

def unit (B : ℕ) : ℕ := 1000*(B+1)^2

theorem copy_price (B : ℕ) (x : Word) (hx : x.view.size ≤ B) : (copy x).bitSteps ≤ unit B := by
  simp only [copy,copyBits_work,word_width]
  unfold unit
  nlinarith

theorem add_price (B : ℕ) (x y : Word) (hx : x.view.size ≤ B) (hy : y.view.size ≤ B) :
    (add x y).bitSteps ≤ unit B := by
  have hx' : x.bits.length ≤ B := x.canonical.trans_le hx
  have hy' : y.bits.length ≤ B := y.canonical.trans_le hy
  have hlen := addBits_length x.bits y.bits false
  have hm : max x.bits.length y.bits.length ≤ B := max_le hx' hy'
  simp only [add,normalize,trimCounted_work,(addCounted_projections _ _ _).1,
    (addCounted_projections _ _ _).2,columnSteps_eq]
  unfold unit
  nlinarith

theorem mul_price (B : ℕ) (x y : Word) (hx : x.view.size ≤ B) (hy : y.view.size ≤ B) :
    (mul x y).bitSteps ≤ unit B := by
  have hx' : x.bits.length ≤ B := x.canonical.trans_le hx
  have hy' : y.bits.length ≤ B := y.canonical.trans_le hy
  have hlen := mulBits_length x.bits y.bits
  have hsteps := mulSteps_bound x.bits y.bits
  have hm : 40*(x.bits.length+1)*(x.bits.length+y.bits.length+2) ≤ 40*(B+1)*(2*B+2) := by
    gcongr <;> omega
  simp only [mul,normalize,trimCounted_work,(mulCounted_projections _ _).1,
    (mulCounted_projections _ _).2]
  unfold unit
  nlinarith

theorem less_price (B : ℕ) (x y : Word) (hx : x.view.size ≤ B) (hy : y.view.size ≤ B) :
    (less x y).bitSteps ≤ unit B := by
  have h := unsignedLess_price B x.bits y.bits (x.canonical.trans_le hx) (y.canonical.trans_le hy)
  change (unsignedLessCounted x.bits y.bits).2+1 ≤ _
  unfold unit scalarUnit at *
  nlinarith

theorem nondivisor_price (B : ℕ) (p d : Word)
    (hp : p.view.size ≤ B) (hd : d.view.size ≤ B) :
    (nondivisor p d).bitSteps ≤ unit B := by
  have hp' : p.bits.length ≤ B := p.canonical.trans_le hp
  have hd' : d.bits.length ≤ B := d.canonical.trans_le hd
  have h := unsigned_divide_price B d.bits p.bits hp' hd'
  have hr := divideBits_remainder_length d.bits p.bits
  simp only [nondivisor,isZero_steps,(divideCounted_projections _ _).1]
  rw [(divideCounted_projections _ _).2] at h ⊢
  unfold unit scalarUnit at *
  nlinarith

/-- Every multiplication retains its normalized binary result. -/
def power (x : Word) : ℕ → Run Word
  | 0 => ⟨input 1,1⟩
  | e+1 =>
      let previous := power x e
      let out := mul previous.value x
      ⟨out.value,previous.bitSteps+out.bitSteps+1⟩
@[simp] theorem power_view (x : Word) (e : ℕ) : (power x e).value.view = x.view^e := by
  induction e with
  | zero => simp [power]
  | succ e ih => simp [power,ih,pow_succ]

theorem power_price (B : ℕ) (x : Word) (e : ℕ) (hx : x.view.size ≤ B)
    (hp : ∀ j ≤ e, (x.view^j).size ≤ B) :
    (power x e).bitSteps ≤ e*(unit B+1)+1 := by
  induction e with
  | zero => simp [power]
  | succ e ih =>
      have hprev := hp e (by omega)
      have hm := mul_price B (power x e).value x (by simpa only [power_view] using hprev) hx
      have hi := ih (fun j hj => hp j (by omega))
      simp only [power]
      nlinarith

/-- The scan's candidate word is incremented by binary addition. -/
def rootLoop (p q : ℕ) (n : Word) : ℕ → Word → Run Word
  | 0,_ => ⟨input 0,1⟩
  | fuel+1,x =>
      let left := power x q
      let right := power n p
      let reject := less right.value left.value
      let selected := if reject.value then input 0 else x
      let next := add x (input 1)
      let tail := rootLoop p q n fuel next.value
      let larger := less selected tail.value
      let kept := copy (if larger.value then tail.value else selected)
      ⟨kept.value,left.bitSteps+right.bitSteps+reject.bitSteps+next.bitSteps+
        tail.bitSteps+larger.bitSteps+kept.bitSteps+1⟩

def rootSpec (p q n : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | fuel+1,x => max (if x^q ≤ n^p then x else 0) (rootSpec p q n fuel (x+1))

theorem less_bool (x y : Word) : (less x y).value = decide (x.view < y.view) := by
  apply Bool.eq_iff_iff.mpr
  simp only [less_view,decide_eq_true_eq]

lemma max_view (x y : Word) :
    (if (less x y).value then y else x).view = max x.view y.view := by
  rw [less_bool]
  by_cases h : x.view < y.view
  · simp only [h,decide_true,ite_true,max_eq_right h.le]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,max_eq_left (by omega : y.view ≤ x.view)]

theorem rootLoop_view (p q : ℕ) (n : Word) (fuel : ℕ) (x : Word) :
    (rootLoop p q n fuel x).value.view = rootSpec p q n.view fuel x.view := by
  induction fuel generalizing x with
  | zero => simp [rootLoop,rootSpec]
  | succ fuel ih =>
      simp only [rootLoop,copy_view,max_view,ih,add_view,input_view]
      rw [less_bool]
      simp only [power_view]
      by_cases h : x.view^q ≤ n.view^p
      · simp only [not_lt.mpr h,decide_false,Bool.false_eq_true,ite_false,rootSpec,if_pos h]
      · simp only [show n.view^p < x.view^q by omega,decide_true,ite_true,input_view,
          rootSpec,if_neg h]

theorem rootSpec_scan (p q n fuel x : ℕ) :
    rootSpec p q n fuel x = (scanCounted p q n (List.range' x fuel)).1 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih => simp [rootSpec,List.range'_succ,scanCounted,powerCounted_value,ih]

def root (p q n : ℕ) : Run Word := rootLoop p q (input n) (n+1) (input 0)
@[simp] theorem root_view (p q n : ℕ) : (root p q n).value.view = rootScan p q n := by
  rw [root,rootLoop_view,input_view,input_view,rootSpec_scan,←List.range_eq_range']
  exact rootProgram_value p q n

lemma rootSpec_le (p q n fuel x : ℕ) : rootSpec p q n fuel x ≤ x+fuel := by
  induction fuel generalizing x with
  | zero => simp [rootSpec]
  | succ fuel ih =>
      simp only [rootSpec,max_le_iff]
      constructor
      · split_ifs <;> omega
      · have := ih (x+1); omega

lemma size_pow (x e : ℕ) : (x^e).size ≤ e*x.size+1 := by
  simpa [Nat.mul_comm] using ToomCook.size_powerProduct_bound x 1 1 e 0 0
lemma size_mul (x y : ℕ) : (x*y).size ≤ x.size+y.size :=
  ToomExecutionBound.size_mul_le x y
lemma size_succ (n : ℕ) : (n+1).size ≤ n.size+1 := by
  apply Nat.size_le.mpr
  have h : n+1 ≤ 2^n.size := by have := Nat.lt_size_self n; omega
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
lemma size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- Truncated subtraction uses binary comparison and borrow propagation. -/
def subtract (x y : Word) : Run Word :=
  let cmp := less x y
  let raw := subCounted x.bits y.bits false
  let out := normalize raw.1.1
  ⟨if cmp.value then input 0 else out.value,cmp.bitSteps+raw.2+out.bitSteps+1⟩
@[simp] theorem subtract_view (x y : Word) : (subtract x y).value.view = x.view-y.view := by
  simp only [subtract,less_bool]
  by_cases h : x.view < y.view
  · simp [h, Nat.sub_eq_zero_of_le h.le]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,normalize_view,
      (subCounted_projections _ _ _).1]
    exact subBits_value x.bits y.bits (show value y.bits ≤ value x.bits from Nat.le_of_not_gt h)

/-- Bit length is obtained by traversing the stored word; each visited bit
increments a retained binary length register. -/
def lengthWord {A : Type} : List A → Run Word
  | [] => ⟨input 0,1⟩
  | _::xs => let tail := lengthWord xs; let out := add tail.value (input 1)
             ⟨out.value,tail.bitSteps+out.bitSteps+1⟩
@[simp] theorem lengthWord_view {A : Type} (xs : List A) : (lengthWord xs).value.view = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [lengthWord,ih]

def width (x : Word) : Run Word := lengthWord x.bits
@[simp] theorem width_view (x : Word) : (width x).value.view = x.view.size := by
  rw [width,lengthWord_view,word_width]

/-- The divisor counter is an incremented stored word. -/
def divisors (p : Word) : ℕ → Word → Run Bool
  | 0,_ => ⟨true,1⟩
  | fuel+1,d =>
      let test := nondivisor p d
      let next := add d (input 1)
      let tail := divisors p fuel next.value
      ⟨test.value && tail.value,test.bitSteps+next.bitSteps+tail.bitSteps+1⟩

def divisorSpec (p : ℕ) : ℕ → ℕ → Bool
  | 0,_ => true
  | fuel+1,d => decide (¬d∣p) && divisorSpec p fuel (d+1)

theorem divisors_view (p : Word) (fuel : ℕ) (d : Word) (hd : 0 < d.view) :
    (divisors p fuel d).value = divisorSpec p.view fuel d.view := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
      have htest : (nondivisor p d).value = decide (¬d.view∣p.view) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using nondivisor_view p d hd
      simp only [divisors,htest,ih (add d (input 1)).value (by simp),
        add_view,input_view,divisorSpec]

theorem divisorSpec_true (p fuel d : ℕ) :
    divisorSpec p fuel d = true ↔ ∀ x ∈ List.range' d fuel, ¬x∣p := by
  induction fuel generalizing d with
  | zero => simp [divisorSpec]
  | succ fuel ih => simp [divisorSpec,List.range'_succ,ih]

def trial (p : Word) : Run Bool :=
  let bound := subtract p (input 2)
  let limit := decode bound.value
  let ds := divisors p limit.value (input 2)
  let ge := less (input 1) p
  ⟨ge.value && ds.value,bound.bitSteps+limit.bitSteps+ds.bitSteps+ge.bitSteps+1⟩

theorem trial_view (p : Word) : (trial p).value = true ↔ Nat.Prime p.view := by
  have hdiv := divisors_view p ((subtract p (input 2)).value.view) (input 2) (by decide)
  simp only [trial,decode_value,Bool.and_eq_true,less_view,input_view]
  rw [hdiv,subtract_view,input_view,divisorSpec_true,Nat.prime_def_lt']
  have hmem (x : ℕ) : x∈List.range' 2 (p.view-2) ↔ 2≤x ∧ x<p.view := by
    rw [List.mem_range']
    constructor
    · rintro ⟨i,hi,rfl⟩; omega
    · rintro ⟨h2,hp⟩; exact ⟨x-2,by omega,by omega⟩
  simp only [hmem,and_imp]
  constructor
  · rintro ⟨hp,hds⟩; exact ⟨by omega,hds⟩
  · rintro ⟨hp,hds⟩; exact ⟨by omega,hds⟩

/-- Candidate decisions execute and retain all binary trial results before
filtering. Each counter word is advanced once, even on rejected candidates. -/
def poolLoop (P : Word) : ℕ → Word → Run (List Word)
  | 0,_ => ⟨[],1⟩
  | fuel+1,p =>
      let primality := trial p
      let lower := less P p
      let belowThree := less p (input 3)
      let aboveThree := less (input 3) p
      let next := add p (input 1)
      let tail := poolLoop P fuel next.value
      let keep := lower.value && (belowThree.value || aboveThree.value) && primality.value
      let retained := copy p
      ⟨if keep then retained.value::tail.value else tail.value,
        primality.bitSteps+lower.bitSteps+belowThree.bitSteps+aboveThree.bitSteps+
        next.bitSteps+tail.bitSteps+retained.bitSteps+1⟩

def poolSpec (P : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | fuel+1,p =>
      let tail := poolSpec P fuel (p+1)
      if P<p ∧ p≠3 ∧ Nat.Prime p then p::tail else tail

theorem poolLoop_view (P : Word) (fuel : ℕ) (p : Word) :
    (poolLoop P fuel p).value.map Word.view = poolSpec P.view fuel p.view := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
      have hk : ((less P p).value &&
          ((less p (input 3)).value || (less (input 3) p).value) && (trial p).value) =
          decide (P.view<p.view ∧ p.view≠3 ∧ Nat.Prime p.view) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,Bool.or_eq_true,less_view,input_view,trial_view,decide_eq_true_eq]
        have hiff : (p.view<3 ∨ 3<p.view) ↔ p.view≠3 := by omega
        rw [hiff]
        tauto
      simp only [poolLoop,hk,poolSpec,decide_eq_true_eq]
      split_ifs <;> simp only [List.map_cons,copy_view,ih,add_view,input_view]

/-- The candidate interval is the executable integer range, with 3 excluded. -/
def pool (P : Word) : Run (List Word) :=
  let limit := mul (input 8) P
  let size := decode limit.value
  let rows := poolLoop P size.value (input 0)
  ⟨rows.value,limit.bitSteps+size.bitSteps+rows.bitSteps+1⟩

theorem poolSpec_mem (P fuel start p : ℕ) : p∈poolSpec P fuel start ↔
    p∈List.range' start fuel ∧ P<p ∧ p≠3 ∧ Nat.Prime p := by
  induction fuel generalizing start with
  | zero => simp [poolSpec]
  | succ fuel ih =>
      simp only [poolSpec,List.range'_succ,List.mem_cons,ih]
      split_ifs <;> simp_all <;> aesop

theorem pool_view (P : Word) : ((pool P).value.map Word.view).toFinset =
    PrimePool.enumeratedCandidates P.view \ {3} := by
  simp only [pool,decode_value,poolLoop_view,mul_view,input_view]
  ext p
  rw [List.mem_toFinset,poolSpec_mem]
  simp only [←List.range_eq_range',List.mem_range,PrimePool.enumeratedCandidates,
    Finset.mem_sdiff,Finset.mem_filter,Finset.mem_range,Finset.mem_singleton,
    PrimePool.trialPrime_iff]
  tauto

lemma poolSpec_filter (P fuel start : ℕ) : poolSpec P fuel start =
    (List.range' start fuel).filter (fun p => decide (P<p ∧ p≠3 ∧ Nat.Prime p)) := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      simp only [poolSpec,List.range'_succ,List.filter_cons,ih,decide_eq_true_eq]

lemma pool_nodup (P : Word) : ((pool P).value.map Word.view).Nodup := by
  simp only [pool,decode_value,poolLoop_view,mul_view,input_view,poolSpec_filter]
  exact List.Nodup.filter _ (List.nodup_range' (s:=0) (n:=8*P.view))

lemma pool_card (P : Word) : (pool P).value.length =
    (PrimePool.enumeratedCandidates P.view \ {3}).card := by
  rw [←pool_view P, List.toFinset_card_of_nodup (pool_nodup P),List.length_map]

attribute [irreducible] power rootLoop root mul add less copy subtract lengthWord width divisors trial poolLoop pool
attribute [local irreducible] ComputableParameters.rootScan Nat.pow

structure Data where
  block : Word
  scale : Word
  lam : Word
  reserve : Word
  stages : Word
  pool : List Word

def prepareWith (p q R n U : ℕ) : Run Data :=
  let nr := input n
  let ur := input U
  let nc := copy nr
  let uc := copy ur
  let br := root p q n
  let block := add br.value (input 1)
  let pr := root p (q*R) n
  let rounded := add pr.value (input 1)
  let ns := width nc.value
  let np := power ns.value 4
  let scale := mul rounded.value np.value
  let pool := pool scale.value
  let card := lengthWord pool.value
  let reserve := subtract card.value (input R)
  let lam := width uc.value
  let twice := mul (input 2) nc.value
  let stages := width twice.value
  ⟨⟨block.value,scale.value,lam.value,reserve.value,stages.value,pool.value⟩,
    nc.bitSteps+uc.bitSteps+br.bitSteps+block.bitSteps+pr.bitSteps+rounded.bitSteps+
    ns.bitSteps+np.bitSteps+scale.bitSteps+pool.bitSteps+card.bitSteps+reserve.bitSteps+
    lam.bitSteps+twice.bitSteps+stages.bitSteps+1⟩

def prepare (n U : ℕ) : Run Data :=
  prepareWith bNumerator bDenominator factorCount n U

def Data.Correct (n U : ℕ) (d : Data) : Prop :=
  d.block.view = ComputableParameters.block n ∧
  d.scale.view = ComputableParameters.scale n ∧ d.lam.view = U.size ∧
  d.reserve.view = ComputableParameters.reserve n ∧ d.stages.view = (2*n).size ∧
  (d.pool.map Word.view).toFinset = computedPool n ∧ (d.pool.map Word.view).Nodup

def Data.CorrectWith (p q R n U : ℕ) (d : Data) : Prop :=
  d.block.view = rootScan p q n+1 ∧
  d.scale.view = (rootScan p (q*R) n+1)*n.size^4 ∧ d.lam.view = U.size ∧
  d.reserve.view = (PrimePool.enumeratedCandidates ((rootScan p (q*R) n+1)*n.size^4) \ {3}).card-R ∧
  d.stages.view = (2*n).size ∧
  (d.pool.map Word.view).toFinset = PrimePool.enumeratedCandidates ((rootScan p (q*R) n+1)*n.size^4) \ {3} ∧
  (d.pool.map Word.view).Nodup

theorem prepareWith_correct (p q R n U : ℕ) : (prepareWith p q R n U).value.CorrectWith p q R n U := by
  let sc := (mul (add (root p (q*R) n).value (input 1)).value
      (power (width (copy (input n)).value).value 4).value).value
  have hs : sc.view = (rootScan p (q*R) n+1)*n.size^4 := by
    simp only [sc,mul_view,add_view,root_view,input_view,power_view,width_view,copy_view]
  have hp := pool_view sc
  have hc := pool_card sc
  have hd := pool_nodup sc
  rw [hs] at hp hc
  dsimp only [prepareWith,Data.CorrectWith]
  refine ⟨?_,hs,?_,?_,?_,hp,hd⟩
  · rw [add_view,root_view,input_view]
  · rw [width_view,copy_view,input_view]
  · rw [subtract_view,lengthWord_view,input_view,hc]
  · rw [width_view,mul_view,input_view,copy_view,input_view]

theorem prepare_correct (n U : ℕ) : (prepare n U).value.Correct n U := by
  have h := prepareWith_correct bNumerator bDenominator factorCount n U
  simpa only [prepare,Data.Correct,Data.CorrectWith,ComputableParameters.block,
    ComputableParameters.scale,roundedPower,ComputableParameters.reserve,computedPool] using h

attribute [irreducible] prepare prepareWith

def validate (d : Data) : Run Bool :=
  let scale := less (input 1) d.scale
  let positive := less (input 0) d.reserve
  let twice := mul (input 2) d.lam
  let half := less d.reserve twice.value
  let lambdaPower := power d.lam factorCount
  let fourBlock := mul (input 4) d.block
  let numerator := mul fourBlock.value lambdaPower.value
  let denominator := power d.reserve factorCount
  let rate := less denominator.value numerator.value
  ⟨scale.value && positive.value && !half.value && !rate.value,
    scale.bitSteps+positive.bitSteps+twice.bitSteps+half.bitSteps+lambdaPower.bitSteps+
    fourBlock.bitSteps+numerator.bitSteps+denominator.bitSteps+rate.bitSteps+3⟩

theorem validate_correct (n U : ℕ) (d : Data) (hd : d.Correct n U) :
    (validate d).value = true ↔ Good n U := by
  have hl : ∀ x y : Word, (less x y).value = false ↔ y.view ≤ x.view := by
    intro x y
    rw [Bool.eq_false_iff]
    exact not_congr (less_view x y) |>.trans not_lt
  simp only [validate,Bool.and_eq_true,Bool.not_eq_true',less_view,input_view,
    mul_view,power_view,hl,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1]
  unfold Good
  omega
attribute [irreducible] validate

/-- The real entry point uses its two serialized input words throughout the
root scans and field preparation. -/
def prepareWordsWith (p q R n U : ℕ) (nr ur : Word) : Run Data :=
  let nc := copy nr
  let uc := copy ur
  let br := rootLoop p q nr (n+1) (input 0)
  let block := add br.value (input 1)
  let pr := rootLoop p (q*R) nr (n+1) (input 0)
  let rounded := add pr.value (input 1)
  let ns := width nc.value
  let np := power ns.value 4
  let scale := mul rounded.value np.value
  let pool := pool scale.value
  let card := lengthWord pool.value
  let reserve := subtract card.value (input R)
  let lam := width uc.value
  let twice := mul (input 2) nc.value
  let stages := width twice.value
  ⟨⟨block.value,scale.value,lam.value,reserve.value,stages.value,pool.value⟩,
    nc.bitSteps+uc.bitSteps+br.bitSteps+block.bitSteps+pr.bitSteps+rounded.bitSteps+
    ns.bitSteps+np.bitSteps+scale.bitSteps+pool.bitSteps+card.bitSteps+reserve.bitSteps+
    lam.bitSteps+twice.bitSteps+stages.bitSteps+1⟩

theorem prepareWords_eq (p q R n U : ℕ) (nr ur : Word)
    (hn : nr=input n) (hU : ur=input U) :
    prepareWordsWith p q R n U nr ur = prepareWith p q R n U := by
  subst nr;subst ur
  unfold prepareWordsWith prepareWith root
  rfl

def prepareEncoded (n U : ℕ) : Run Data :=
  let nr := serialize n
  let ur := serialize U
  let out := prepareWordsWith bNumerator bDenominator factorCount n U nr.value ur.value
  ⟨out.value,nr.bitSteps+ur.bitSteps+out.bitSteps+1⟩

theorem prepareEncoded_value (n U : ℕ) : (prepareEncoded n U).value=(prepare n U).value := by
  simp only [prepareEncoded,prepareWords_eq _ _ _ _ _ _ _ (serialize_eq_input n) (serialize_eq_input U),prepare]

theorem prepareEncoded_steps (n U : ℕ) : (prepareEncoded n U).bitSteps =
    (BinaryMultiplierAdapter.encodeNat n).bitSteps+(BinaryMultiplierAdapter.encodeNat U).bitSteps+
      (prepare n U).bitSteps+1 := by
  simp only [prepareEncoded,prepareWords_eq _ _ _ _ _ _ _ (serialize_eq_input n) (serialize_eq_input U),prepare]
  rfl

structure Decoded where
  block : ℕ
  scale : ℕ
  lam : ℕ
  reserve : ℕ
  stages : ℕ
  pool : List ℕ

def decodeList : List Word → Run (List ℕ)
  | [] => ⟨[],1⟩
  | x::xs => let head := decode x;let tail := decodeList xs
             ⟨head.value::tail.value,head.bitSteps+tail.bitSteps+1⟩
@[simp] theorem decodeList_value (xs : List Word) : (decodeList xs).value=xs.map Word.view := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [decodeList,decode_value,ih,List.map_cons]

def decodeData (d : Data) : Run Decoded :=
  let block := decode d.block
  let scale := decode d.scale
  let lam := decode d.lam
  let reserve := decode d.reserve
  let stages := decode d.stages
  let pool := decodeList d.pool
  ⟨⟨block.value,scale.value,lam.value,reserve.value,stages.value,pool.value⟩,
    block.bitSteps+scale.bitSteps+lam.bitSteps+reserve.bitSteps+stages.bitSteps+pool.bitSteps+1⟩

def Decoded.Correct (d : Data) (m : Decoded) : Prop :=
  m.block=d.block.view ∧ m.scale=d.scale.view ∧ m.lam=d.lam.view ∧
  m.reserve=d.reserve.view ∧ m.stages=d.stages.view ∧ m.pool=d.pool.map Word.view

theorem decodeData_correct (d : Data) : (decodeData d).value.Correct d := by
  simp only [decodeData,Decoded.Correct,decode_value,decodeList_value,and_self]

/-- A duplicate-free retained word list is installed directly as the pool;
there is no repeated primality call or uncharged deduplication pass. -/
def storedPool (d : Data) (h : (d.pool.map Word.view).Nodup) : Finset ℕ :=
  ⟨(d.pool.map Word.view : Multiset ℕ),by simpa only [Multiset.coe_nodup] using h⟩

theorem storedPool_eq (d : Data) (h : (d.pool.map Word.view).Nodup) :
    storedPool d h = (d.pool.map Word.view).toFinset := by
  ext p
  simp [storedPool]

/-- Only the retained binary results supply the configuration's data fields.
The finite proof fields are erased. -/
def configuration (n U : ℕ) (d : Data) (hd : d.Correct n U) (h : Good n U) :
    CompleteAPSP.Parameters (ComputableParameters.block n) U where
  pool := storedPool d hd.2.2.2.2.2.2
  P := d.scale.view
  lam := d.lam.view
  k := factorCount-1
  M := d.reserve.view
  stages := d.stages.view
  prime := by
    intro p hp
    rw [storedPool_eq,hd.2.2.2.2.2.1] at hp
    exact (finiteComputedParameters n U h).prime p hp
  lower := by
    intro p hp
    rw [storedPool_eq,hd.2.2.2.2.2.1] at hp
    simpa only [hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).lower p hp
  P_pos := by simpa only [hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).P_pos
  power := by simpa only [hd.2.1,hd.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).power
  threshold := by
    simpa only [hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).threshold
  size := by
    rw [storedPool_eq,hd.2.2.2.2.2.1]
    simpa only [hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).size
  rate := by
    simpa only [hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).rate

theorem configuration_eq (n U : ℕ) (d : Data) (hd : d.Correct n U) (h : Good n U) :
    configuration n U d hd h = finiteComputedParameters n U h := by
  unfold configuration finiteComputedParameters
  rw [CompleteAPSP.Parameters.mk.injEq]
  exact ⟨(storedPool_eq _ _).trans hd.2.2.2.2.2.1,hd.2.1,hd.2.2.1,rfl,
    hd.2.2.2.1,hd.2.2.2.2.1⟩

def nativePool (m : Decoded) (h : m.pool.Nodup) : Finset ℕ :=
  ⟨(m.pool:Multiset ℕ),by simpa only [Multiset.coe_nodup] using h⟩

def configurationDecoded (n U : ℕ) (d : Data) (hd : d.Correct n U)
    (m : Decoded) (hm : m.Correct d) (h : Good n U) :
    CompleteAPSP.Parameters (ComputableParameters.block n) U where
  pool := nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2)
  P := m.scale
  lam := m.lam
  k := factorCount-1
  M := m.reserve
  stages := m.stages
  prime := by
    intro p hp
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he] at hp
    exact (finiteComputedParameters n U h).prime p hp
  lower := by
    intro p hp
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he] at hp
    simpa only [hm.2.1,hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).lower p hp
  P_pos := by simpa only [hm.2.1,hd.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).P_pos
  power := by simpa only [hm.2.1,hm.2.2.1,hd.2.1,hd.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).power
  threshold := by simpa only [hm.2.2.1,hm.2.2.2.1,hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).threshold
  size := by
    have he : nativePool m (hm.2.2.2.2.2 ▸ hd.2.2.2.2.2.2) = computedPool n := by
      ext x
      simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
      rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]
    rw [he]
    simpa only [hm.2.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).size
  rate := by simpa only [hm.2.2.1,hm.2.2.2.1,hd.2.2.1,hd.2.2.2.1,finiteComputedParameters] using (finiteComputedParameters n U h).rate

theorem configurationDecoded_eq (n U : ℕ) (d : Data) (hd : d.Correct n U)
    (m : Decoded) (hm : m.Correct d) (h : Good n U) :
    configurationDecoded n U d hd m hm h = finiteComputedParameters n U h := by
  unfold configurationDecoded finiteComputedParameters
  rw [CompleteAPSP.Parameters.mk.injEq]
  refine ⟨?_,hm.2.1.trans hd.2.1,hm.2.2.1.trans hd.2.2.1,rfl,
    hm.2.2.2.1.trans hd.2.2.2.1,hm.2.2.2.2.1.trans hd.2.2.2.2.1⟩
  ext x
  simp only [nativePool,Finset.mem_mk,Multiset.mem_coe]
  rw [hm.2.2.2.2.2,←List.mem_toFinset,hd.2.2.2.2.2.1]

structure Execution (n U : ℕ) where
  value : Option (CompleteAPSP.Parameters (ComputableParameters.block n) U)
  metadata : Decoded
  bitSteps : ℕ

/-- Input words, all binary setup results, and the decoded public metadata are
retained once. The implementation never calls the reference program. -/
def execute (n U : ℕ) : Execution n U :=
  let prepared := prepareEncoded n U
  have hd : prepared.value.Correct n U := prepareEncoded_value n U ▸ prepare_correct n U
  let checked := validate prepared.value
  let metadata := decodeData prepared.value
  if h : checked.value = true then
    ⟨some (configurationDecoded n U prepared.value hd metadata.value (decodeData_correct prepared.value)
      ((validate_correct n U prepared.value hd).mp h)),metadata.value,
      prepared.bitSteps+checked.bitSteps+metadata.bitSteps+1⟩
  else ⟨none,metadata.value,prepared.bitSteps+checked.bitSteps+metadata.bitSteps+1⟩

theorem execute_value (n U : ℕ) : (execute n U).value = program n U := by
  have hd : (prepareEncoded n U).value.Correct n U := prepareEncoded_value n U ▸ prepare_correct n U
  by_cases hg : Good n U
  · have hc := (validate_correct n U _ hd).mpr hg
    simp only [execute,hc,dif_pos,program,hg,configurationDecoded_eq]
  · have hc : ¬(validate (prepareEncoded n U).value).value = true :=
      fun h => hg ((validate_correct n U _ hd).mp h)
    simp only [execute,hc,dif_neg,program,hg,Bool.false_eq_true,if_false,dif_neg,not_false_eq_true]

theorem execute_steps (n U : ℕ) : (execute n U).bitSteps =
    (prepareEncoded n U).bitSteps+(validate (prepareEncoded n U).value).bitSteps+
      (decodeData (prepareEncoded n U).value).bitSteps+1 := by
  dsimp only [execute]
  split_ifs <;> rfl

theorem execute_metadata (n U : ℕ) : (execute n U).metadata=(decodeData (prepare n U).value).value := by
  dsimp only [execute]
  split_ifs
  all_goals change (decodeData (prepareEncoded n U).value).value = _
  all_goals rw [prepareEncoded_value]

theorem rootLoop_price (B H p q fuel : ℕ) (n x : Word)
    (hH : 1 ≤ H) (hn : n.view ≤ H) (hx : x.view+fuel ≤ H)
    (hf : ∀ z ≤ H, z.size ≤ B)
    (hp : ∀ z ≤ H, ∀ j ≤ p+q+1, (z^j).size ≤ B) :
    (rootLoop p q n fuel x).bitSteps ≤ (fuel+1)*(p+q+10)*(unit B+1) := by
  induction fuel generalizing x with
  | zero => simp only [rootLoop]; nlinarith
  | succ fuel ih =>
      let sel := if (less (power n p).value (power x q).value).value then input 0 else x
      let nxt := (add x (input 1)).value
      let tail := rootLoop p q n fuel nxt
      have hxH : x.view ≤ H := by omega
      have hsel : sel.view ≤ H := by
        dsimp only [sel]
        split_ifs
        · change 0 ≤ H; omega
        · exact hxH
      have hnxt : nxt.view+fuel ≤ H := by simp only [nxt,add_view,input_view]; omega
      have htail : tail.value.view ≤ H := by
        rw [show tail.value.view = rootSpec p q n.view fuel nxt.view by exact rootLoop_view _ _ _ _ _]
        exact (rootSpec_le _ _ _ _ _).trans hnxt
      have hl := power_price B x q (hf _ hxH) (fun j hj => hp _ hxH j (by omega))
      have hr := power_price B n p (hf _ hn) (fun j hj => hp _ hn j (by omega))
      have hre := less_price B (power n p).value (power x q).value
        (by rw [power_view];exact hp _ hn p (by omega))
        (by rw [power_view];exact hp _ hxH q (by omega))
      have ha := add_price B x (input 1) (hf _ hxH) (by rw [input_view];exact hf 1 hH)
      have ht := ih nxt hnxt
      have hc := less_price B sel tail.value (hf _ hsel) (hf _ htail)
      have hk := copy_price B (if (less sel tail.value).value then tail.value else sel) (by
        split_ifs <;> exact hf _ (by assumption))
      rw [rootLoop]
      change (power x q).bitSteps+(power n p).bitSteps+
        (less (power n p).value (power x q).value).bitSteps+(add x (input 1)).bitSteps+
        tail.bitSteps+(less sel tail.value).bitSteps+
        (copy (if (less sel tail.value).value then tail.value else sel)).bitSteps+1 ≤ _
      nlinarith

theorem subtract_price (B : ℕ) (x y : Word)
    (hx : x.view.size ≤ B) (hy : y.view.size ≤ B) : (subtract x y).bitSteps ≤ unit B := by
  have hx' : x.bits.length ≤ B := x.canonical.trans_le hx
  have hy' : y.bits.length ≤ B := y.canonical.trans_le hy
  have hless := unsignedLess_price B x.bits y.bits hx' hy'
  have hlen := subBits_length x.bits y.bits false
  have hm : max x.bits.length y.bits.length ≤ B := max_le hx' hy'
  simp only [subtract,less,normalize,trimCounted_work,(subCounted_projections _ _ _).1,
    (subCounted_projections _ _ _).2,columnSteps_eq]
  unfold unit scalarUnit at *
  nlinarith

theorem lengthWord_price {A : Type} (B : ℕ) (xs : List A)
    (h : ∀ j ≤ xs.length, j.size ≤ B) :
    (lengthWord xs).bitSteps ≤ (xs.length+1)*(unit B+1) := by
  induction xs with
  | nil => simp only [lengthWord,List.length_nil]; nlinarith
  | cons a xs ih =>
      have ht := ih (fun j hj => h j (by simp only [List.length_cons];omega))
      have hp := add_price B (lengthWord xs).value (input 1)
        (by rw [lengthWord_view];exact h xs.length (by simp))
        (by rw [input_view];exact h 1 (by simp))
      simp only [lengthWord,List.length_cons]
      nlinarith

theorem divisors_price (B H fuel : ℕ) (p d : Word)
    (hp : p.view.size ≤ B) (hd : d.view+fuel ≤ H) (hH : 1 ≤ H)
    (hf : ∀ z ≤ H, z.size ≤ B) :
    (divisors p fuel d).bitSteps ≤ (2*fuel+1)*(unit B+1) := by
  induction fuel generalizing d with
  | zero => simp only [divisors]; nlinarith
  | succ fuel ih =>
      have hdH : d.view ≤ H := by omega
      have ht := ih (add d (input 1)).value (by simp only [add_view,input_view];omega)
      have hm := nondivisor_price B p d hp (hf _ hdH)
      have ha := add_price B d (input 1) (hf _ hdH) (by rw [input_view];exact hf 1 hH)
      simp only [divisors]
      nlinarith

theorem trial_price (B H : ℕ) (p : Word) (hp : p.view ≤ H)
    (hH : 2 ≤ H) (hf : ∀ z ≤ H, z.size ≤ B) :
    (trial p).bitSteps ≤ (2*p.view+5)*(unit B+1) := by
  have hs := subtract_price B p (input 2) (hf _ hp) (by rw [input_view];exact hf 2 hH)
  have hd := divisors_price B H ((decode (subtract p (input 2)).value).value) p (input 2)
    (hf _ hp) (by rw [input_view,decode_value,subtract_view,input_view];omega) (by omega) hf
  have hl := less_price B (input 1) p (by rw [input_view];exact hf 1 (by omega)) (hf _ hp)
  simp only [trial,decode_value,subtract_view,input_view] at hd ⊢
  have hdec := BinaryMultiplierAdapter.decodeNat_cost (subtract p (input 2)).value.bits
  rw [word_width,subtract_view,input_view] at hdec
  have hds : (p.view-2).size ≤ B := (Nat.size_le_size (Nat.sub_le _ _)).trans (hf _ hp)
  have hdc : (decode (subtract p (input 2)).value).bitSteps ≤ unit B := by
    change (BinaryMultiplierAdapter.decodeNat _).bitSteps ≤ _
    unfold unit
    nlinarith
  nlinarith [Nat.sub_le p.view 2]

theorem poolLoop_price (B H fuel : ℕ) (P p : Word)
    (hP : P.view ≤ H) (hp : p.view+fuel ≤ H)
    (hH : 3 ≤ H) (hf : ∀ z ≤ H, z.size ≤ B) :
    (poolLoop P fuel p).bitSteps ≤ (fuel+1)*(2*H+12)*(unit B+1) := by
  induction fuel generalizing p with
  | zero => simp only [poolLoop]; nlinarith
  | succ fuel ih =>
      have hpH : p.view ≤ H := by omega
      have ht := ih (add p (input 1)).value (by simp only [add_view,input_view];omega)
      have htrial := trial_price B H p hpH (by omega) hf
      have hlow := less_price B P p (hf _ hP) (hf _ hpH)
      have hbelow := less_price B p (input 3) (hf _ hpH) (by rw [input_view];exact hf 3 hH)
      have habove := less_price B (input 3) p (by rw [input_view];exact hf 3 hH) (hf _ hpH)
      have ha := add_price B p (input 1) (hf _ hpH) (by rw [input_view];exact hf 1 (by omega))
      have hc := copy_price B p (hf _ hpH)
      simp only [poolLoop]
      have hm : (2*p.view+5)*(unit B+1) ≤ (2*H+5)*(unit B+1) := by gcongr
      nlinarith

theorem pool_price (B H : ℕ) (P : Word) (hH : 8*P.view+8 ≤ H)
    (hf : ∀ z ≤ H, z.size ≤ B) :
    (pool P).bitSteps ≤ (8*P.view+2)*(2*H+12)*(unit B+1) := by
  have hm := mul_price B (input 8) P (by rw [input_view];exact hf 8 (by omega))
    (hf P.view (by omega))
  have ht := poolLoop_price B H ((mul (input 8) P).value.view) P (input 0)
    (by omega) (by simp only [input_view,mul_view];omega) (by omega) hf
  simp only [pool,decode_value,mul_view,input_view] at ht ⊢
  have hdec := BinaryMultiplierAdapter.decodeNat_cost (mul (input 8) P).value.bits
  rw [word_width,mul_view,input_view] at hdec
  have hds : (8*P.view).size ≤ B := hf _ (by omega)
  have hdc : (decode (mul (input 8) P).value).bitSteps ≤ unit B := by
    change (BinaryMultiplierAdapter.decodeNat _).bitSteps ≤ _
    unfold unit
    nlinarith
  nlinarith

theorem pool_length (P : Word) : (pool P).value.length ≤ 8*P.view := by
  have h := List.length_filter_le (fun p => decide (P.view<p ∧ p≠3 ∧ Nat.Prime p))
    (List.range' 0 (8*P.view))
  rw [←List.length_map (f:=Word.view) (as:=(pool P).value)]
  simpa only [pool,decode_value,poolLoop_view,mul_view,input_view,poolSpec_filter,List.length_range'] using h

theorem validate_price (B : ℕ) (d : Data) (h8 : (8:ℕ).size ≤ B)
    (hs : d.scale.view.size ≤ B) (hm : d.reserve.view.size ≤ B)
    (hl : d.lam.view.size ≤ B) (hb : d.block.view.size ≤ B)
    (ht : (2*d.lam.view).size ≤ B) (hf : (4*d.block.view).size ≤ B)
    (hn : (4*d.block.view*d.lam.view^factorCount).size ≤ B)
    (hlp : ∀ j ≤ factorCount, (d.lam.view^j).size ≤ B)
    (hmp : ∀ j ≤ factorCount, (d.reserve.view^j).size ≤ B) :
    (validate d).bitSteps ≤ (2*factorCount+12)*(unit B+1) := by
  have hc (z : ℕ) (hz : z ≤ 8) : (input z).view.size ≤ B := by
    rw [input_view]
    exact (Nat.size_le_size hz).trans h8
  have hsc := less_price B (input 1) d.scale (hc 1 (by omega)) hs
  have hpo := less_price B (input 0) d.reserve (hc 0 (by omega)) hm
  have htw := mul_price B (input 2) d.lam (hc 2 (by omega)) hl
  have hha := less_price B d.reserve (mul (input 2) d.lam).value hm
    (by rw [mul_view,input_view];exact ht)
  have hlpow := power_price B d.lam factorCount hl hlp
  have hfour := mul_price B (input 4) d.block (hc 4 (by omega)) hb
  have hnum := mul_price B (mul (input 4) d.block).value (power d.lam factorCount).value
    (by rw [mul_view,input_view];exact hf) (by rw [power_view];exact hlp _ le_rfl)
  have hden := power_price B d.reserve factorCount hm hmp
  have hra := less_price B (power d.reserve factorCount).value
    (mul (mul (input 4) d.block).value (power d.lam factorCount).value).value
    (by rw [power_view];exact hmp _ le_rfl)
    (by rw [mul_view,mul_view,input_view,power_view];exact hn)
  simp only [validate]
  nlinarith

lemma rootScan_le (p q n : ℕ) : rootScan p q n ≤ n := by
  unfold rootScan
  apply Finset.sup_le
  intro x hx
  split_ifs
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  · exact Nat.zero_le _
lemma roundedPower_le (p q n : ℕ) : roundedPower p q n ≤ n+1 :=
  Nat.add_le_add_right (rootScan_le p q n) 1
lemma scale_width (n : ℕ) : (scale n).size ≤ 5*(n.size+1) := by
  unfold scale
  have hr := (Nat.size_le_size (roundedPower_le bNumerator (bDenominator*factorCount) n)).trans (size_succ n)
  have hp : (n.size^4).size ≤ 4*n.size+1 :=
    (size_pow _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (size_le_self _)) 1)
  exact (size_mul _ _).trans (by nlinarith)
lemma block_width (n : ℕ) : (ComputableParameters.block n).size ≤ n.size+1 := by
  unfold ComputableParameters.block
  exact (Nat.size_le_size (roundedPower_le _ _ n)).trans (size_succ n)
lemma pool_card_le (P : ℕ) : (PrimePool.enumeratedCandidates P \ {3}).card ≤ 8*P := by
  calc
    _ ≤ (PrimePool.enumeratedCandidates P).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (Finset.range (8*P)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = _ := Finset.card_range _
lemma reserve_le (n : ℕ) : ComputableParameters.reserve n ≤ 8*scale n :=
  (Nat.sub_le _ _).trans (pool_card_le _)
lemma size_eight_mul (P : ℕ) : (8*P).size ≤ P.size+4 := by
  have h := size_mul 8 P
  have h8 : (8:ℕ).size=4 := by decide
  omega
lemma input_size_of_real_power (n U : ℕ) (κ : ℝ) (hn : 1≤n)
    (hU : (U:ℝ)≤(n:ℝ)^κ) : U.size≤Nat.ceil κ*n.size+1 := by
  have hpow : U≤n^(Nat.ceil κ) := by
    have hcast : (U:ℝ)≤((n^(Nat.ceil κ):ℕ):ℝ) := by
      calc
        (U:ℝ)≤(n:ℝ)^κ := hU
        _≤(n:ℝ)^(Nat.ceil κ:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (Nat.le_ceil κ)
        _=((n^(Nat.ceil κ):ℕ):ℝ) := by rw [Real.rpow_natCast,Nat.cast_pow]
    exact_mod_cast hcast
  exact (Nat.size_le_size hpow).trans (size_pow n (Nat.ceil κ))

/-- A single register-width bound covers root powers, candidate arithmetic,
and both fixed-depth validation powers. -/
def registerWidth (n U : ℕ) : ℕ :=
  (bNumerator+bDenominator*factorCount+10*factorCount+100)*(n.size+2)+(factorCount+1)*U.size

lemma validate_registers (n U : ℕ) :
    (validate (prepare n U).value).bitSteps ≤ (2*factorCount+12)*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  let d := (prepare n U).value
  have hd := prepare_correct n U
  have hR : factorCount = 1000000000 := rfl
  have h8 : (8:ℕ).size ≤ B := by change 4 ≤ B; dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]; omega
  have hsc : (scale n).size ≤ B := (scale_width n).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];omega)
  have hres : (ComputableParameters.reserve n).size ≤ 9*(n.size+1) :=
    (Nat.size_le_size (reserve_le n)).trans ((size_eight_mul _).trans (by nlinarith [scale_width n]))
  have hm : (ComputableParameters.reserve n).size ≤ B := hres.trans (by dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];omega)
  have hl : U.size.size ≤ B := (size_le_self _).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];nlinarith)
  have hb : (ComputableParameters.block n).size ≤ B := (block_width n).trans (by dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];omega)
  have hlp : ∀ j ≤ factorCount, (U.size^j).size ≤ B := by
    intro j hj
    have h := size_pow U.size j
    have hs := size_le_self U.size
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    nlinarith
  have hmp : ∀ j ≤ factorCount, (ComputableParameters.reserve n^j).size ≤ B := by
    intro j hj
    have h := size_pow (ComputableParameters.reserve n) j
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    nlinarith
  have ht : (2*U.size).size ≤ B := (size_mul _ _).trans (by
    have h2 : (2:ℕ).size=2 := by decide
    rw [h2];dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];nlinarith [size_le_self U.size])
  have hf : (4*ComputableParameters.block n).size ≤ B := (size_mul _ _).trans (by
    have h4 : (4:ℕ).size=3 := by decide
    rw [h4];dsimp [B,registerWidth,bNumerator,bDenominator,factorCount];nlinarith [block_width n])
  have hn : (4*ComputableParameters.block n*U.size^factorCount).size ≤ B := by
    have h1 := size_mul (4*ComputableParameters.block n) (U.size^factorCount)
    have h2 := size_mul 4 (ComputableParameters.block n)
    have h3 := size_pow U.size factorCount
    have h4 : (4:ℕ).size=3 := by decide
    rw [h4] at h2
    rw [hR] at h1 h3
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    nlinarith [block_width n,size_le_self U.size]
  apply validate_price B d h8
  all_goals simp only [d,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1]
  · exact hsc
  · exact hm
  · exact hl
  · exact hb
  · exact ht
  · exact hf
  · exact hn
  · exact hlp
  · exact hmp

theorem decode_price (B : ℕ) (x : Word) (hx : x.view.size ≤ B) : (decode x).bitSteps ≤ unit B := by
  have h := BinaryMultiplierAdapter.decodeNat_cost x.bits
  rw [word_width] at h
  have hh : 8*(x.view.size+1)^2 ≤ 8*(B+1)^2 := by gcongr
  change (BinaryMultiplierAdapter.decodeNat x.bits).bitSteps ≤ _
  unfold unit
  nlinarith

theorem serialize_price (B n : ℕ) (hn : n.size ≤ B) : (serialize n).bitSteps ≤ unit B := by
  have h := BinaryMultiplierAdapter.encodeNat_cost n
  have hh : 8*(n.size+1)^2 ≤ 8*(B+1)^2 := by gcongr
  change (BinaryMultiplierAdapter.encodeNat n).bitSteps ≤ _
  unfold unit
  nlinarith

theorem decodeList_price (B : ℕ) (xs : List Word)
    (hx : ∀ x∈xs,x.view.size≤B) :
    (decodeList xs).bitSteps ≤ (xs.length+1)*(unit B+1) := by
  induction xs with
  | nil => simp only [decodeList,List.length_nil];nlinarith
  | cons x xs ih =>
      have hh := decode_price B x (hx x (by simp))
      have ht := ih (fun y hy => hx y (by simp [hy]))
      simp only [decodeList,List.length_cons]
      nlinarith

theorem decodeData_price (B : ℕ) (d : Data)
    (hb : d.block.view.size≤B) (hs : d.scale.view.size≤B) (hl : d.lam.view.size≤B)
    (hm : d.reserve.view.size≤B) (ht : d.stages.view.size≤B)
    (hp : ∀ x∈d.pool,x.view.size≤B) :
    (decodeData d).bitSteps ≤ (d.pool.length+6)*(unit B+1) := by
  have h1 := decode_price B d.block hb
  have h2 := decode_price B d.scale hs
  have h3 := decode_price B d.lam hl
  have h4 := decode_price B d.reserve hm
  have h5 := decode_price B d.stages ht
  have h6 := decodeList_price B d.pool hp
  simp only [decodeData]
  nlinarith

lemma decodePrepared_price (n U : ℕ) :
    (decodeData (prepare n U).value).bitSteps ≤ (8*scale n+6)*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  let d := (prepare n U).value
  have hd := prepare_correct n U
  have hbound : 9*(n.size+1)+U.size ≤ B := by
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    omega
  have hb : d.block.view.size≤B := by rw [show d.block.view=ComputableParameters.block n from hd.1]; nlinarith [block_width n]
  have hs : d.scale.view.size≤B := by rw [show d.scale.view=scale n from hd.2.1];nlinarith [scale_width n]
  have hl : d.lam.view.size≤B := by rw [show d.lam.view=U.size from hd.2.2.1];nlinarith [size_le_self U.size]
  have hm : d.reserve.view.size≤B := by
    rw [show d.reserve.view=ComputableParameters.reserve n from hd.2.2.2.1]
    have h := (Nat.size_le_size (reserve_le n)).trans (size_eight_mul (scale n))
    nlinarith [scale_width n]
  have ht : d.stages.view.size≤B := by
    rw [show d.stages.view=(2*n).size from hd.2.2.2.2.1]
    have h := size_mul 2 n
    have h2 : (2:ℕ).size=2 := by decide
    rw [h2] at h
    nlinarith [size_le_self ((2*n).size)]
  have hp : ∀ x∈d.pool,x.view.size≤B := by
    intro x hx
    have hmem : x.view∈computedPool n := by
      rw [←hd.2.2.2.2.2.1]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩)
    have hxle : x.view ≤ 8*scale n := by
      have hmem' := (Finset.mem_sdiff.mp hmem).1
      exact (Finset.mem_range.mp (Finset.mem_filter.mp hmem').1).le
    have h := (Nat.size_le_size hxle).trans (size_eight_mul (scale n))
    nlinarith [scale_width n]
  have hlen : d.pool.length ≤ 8*scale n := by
    rw [←List.length_map (f:=Word.view) (as:=d.pool),←List.toFinset_card_of_nodup hd.2.2.2.2.2.2,
      hd.2.2.2.2.2.1]
    exact pool_card_le _
  exact (decodeData_price B d hb hs hl hm ht hp).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 6))

def rootWidth (p q n : ℕ) : ℕ := (p+q+2)*(n.size+2)+1

theorem root_price (p q n : ℕ) :
    (root p q n).bitSteps ≤ (n+2)*(p+q+10)*(unit (rootWidth p q n)+1) := by
  have hf : ∀ z ≤ n+1, z.size ≤ rootWidth p q n := by
    intro z hz
    have h := (Nat.size_le_size hz).trans (size_succ n)
    unfold rootWidth
    nlinarith
  have hp : ∀ z ≤ n+1, ∀ j ≤ p+q+1, (z^j).size ≤ rootWidth p q n := by
    intro z hz j hj
    have hzsize := (Nat.size_le_size hz).trans (size_succ n)
    have h := size_pow z j
    have hm := Nat.mul_le_mul hj hzsize
    unfold rootWidth
    nlinarith
  have h := rootLoop_price (rootWidth p q n) (n+1) p q (n+1) (input n) (input 0)
    (by omega) (by simp) (by simp) hf hp
  simpa only [root,Nat.add_assoc] using h

theorem root_output_size (p q n : ℕ) : (root p q n).value.view.size ≤ n.size+1 := by
  have h := rootSpec_le p q n (n+1) 0
  have hview : (root p q n).value.view ≤ n+1 := by
    rw [root,rootLoop_view,input_view,input_view]
    simpa only [Nat.zero_add] using h
  exact (Nat.size_le_size hview).trans (size_succ n)


theorem unit_mono {A B : ℕ} (h : A ≤ B) : unit A ≤ unit B := by
  unfold unit
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)

theorem root_price_common (B p q n : ℕ) (hB : rootWidth p q n ≤ B) :
    (root p q n).bitSteps ≤ (n+2)*(p+q+10)*(unit B+1) :=
  (root_price p q n).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (unit_mono hB) 1))

theorem root_output_le (p q n : ℕ) : (root p q n).value.view ≤ n+1 := by
  rw [root,rootLoop_view,input_view,input_view]
  simpa only [Nat.zero_add] using rootSpec_le p q n (n+1) 0


/-- Finite composition of the exact prepared selector; assumptions concern
stored operand widths, not an assumed cost of the complete selector. -/
theorem prepareWith_price (p q R n U B H : ℕ)
    (hn : n+2 ≤ H) (h2n : 2*n ≤ H) (hU : U.size ≤ B) (hUs : U.size ≤ H)
    (hR : R ≤ H)
    (hP : 8*((ComputableParameters.rootScan p (q*R) n+1)*n.size^4)+8 ≤ H)
    (hf : ∀ z ≤ H, z.size ≤ B)
    (hr1 : rootWidth p q n ≤ B) (hr2 : rootWidth p (q*R) n ≤ B)
    (hpow : ∀ j ≤ 4, (n.size^j).size ≤ B) :
    let P := (ComputableParameters.rootScan p (q*R) n+1)*n.size^4
    (prepareWith p q R n U).bitSteps ≤
      ((n+2)*(p+q+10)+(n+2)*(p+q*R+10)+(8*P+2)*(2*H+12)+
        8*P+2*n.size+U.size+30)*(unit B+1) := by
  let P := (ComputableParameters.rootScan p (q*R) n+1)*n.size^4
  let nr := input n
  let ur := input U
  let nc := copy nr
  let uc := copy ur
  let br := root p q n
  let block := add br.value (input 1)
  let pr := root p (q*R) n
  let rounded := add pr.value (input 1)
  let ns := width nc.value
  let np := power ns.value 4
  let sc := mul rounded.value np.value
  let ps := pool sc.value
  let card := lengthWord ps.value
  let reserve := subtract card.value (input R)
  let lam := width uc.value
  let twice := mul (input 2) nc.value
  let stages := width twice.value
  have h1 : 1 ≤ H := by omega
  have hnc := copy_price B nr (by rw [input_view]; exact hf n (by omega))
  have huc := copy_price B ur (by rw [input_view]; exact hU)
  have hbr := root_price_common B p q n hr1
  have hpr := root_price_common B p (q*R) n hr2
  have hnb : n.size+1 ≤ B := by unfold rootWidth at hr1; nlinarith
  have hblock := add_price B br.value (input 1)
    ((root_output_size p q n).trans hnb)
    (by rw [input_view]; exact hf 1 h1)
  have hrounded := add_price B pr.value (input 1)
    ((root_output_size p (q*R) n).trans (by unfold rootWidth at hr2; nlinarith))
    (by rw [input_view]; exact hf 1 h1)
  have hns := lengthWord_price B nc.value.bits (fun j hj => hf j (by
    rw [word_width,copy_view,input_view] at hj
    exact hj.trans ((size_le_self n).trans (by omega))))
  have hns' : ns.bitSteps ≤ (n.size+1)*(unit B+1) := by
    simpa only [ns,width,word_width,nc,nr,copy_view,input_view] using hns
  have hnp := power_price B ns.value 4
    (by rw [width_view,copy_view,input_view]; exact hf n.size ((size_le_self n).trans (by omega)))
    (by intro j hj; rw [width_view,copy_view,input_view]; exact hpow j hj)
  have hroundvalue : rounded.value.view ≤ H := by
    rw [add_view,input_view]
    exact (Nat.add_le_add_right (root_output_le p (q*R) n) 1).trans hn
  have hsc := mul_price B rounded.value np.value
    (hf _ hroundvalue) (by rw [power_view,width_view,copy_view,input_view]; exact hpow 4 le_rfl)
  have hscview : sc.value.view = P := by
    simp only [sc,P,rounded,pr,np,ns,nc,nr,mul_view,add_view,root_view,input_view,power_view,width_view,copy_view]
  have hps := pool_price B H sc.value (by rw [hscview]; exact hP) hf
  have hpslen : ps.value.length ≤ 8*P := by
    simpa only [ps,hscview] using pool_length sc.value
  have hcard := lengthWord_price B ps.value (fun j hj => hf j (by
    have hj' := hj.trans hpslen
    dsimp only [P] at hj' hP
    omega))
  have hreserve := subtract_price B card.value (input R)
    (by rw [lengthWord_view]; exact hf _ (by have hh := hpslen; dsimp only [P] at hh hP; omega))
    (by rw [input_view]; exact hf R hR)
  have hlam := lengthWord_price B uc.value.bits (fun j hj => hf j (by
    rw [word_width,copy_view,input_view] at hj
    exact hj.trans hUs))
  have hlam' : lam.bitSteps ≤ (U.size+1)*(unit B+1) := by
    simpa only [lam,width,word_width,uc,ur,copy_view,input_view] using hlam
  have htwice := mul_price B (input 2) nc.value
    (by rw [input_view]; exact hf 2 (by omega))
    (by rw [copy_view,input_view]; exact hf n (by omega))
  have hstages := lengthWord_price B twice.value.bits (fun j hj => hf j (by
    rw [word_width,mul_view,input_view,copy_view,input_view] at hj
    exact hj.trans ((size_le_self (2*n)).trans h2n)))
  have h2size : (2*n).size ≤ n.size+2 := by
    have hh := size_mul 2 n
    rw [show (2:ℕ).size=2 by decide] at hh
    omega
  have hstages' : stages.bitSteps ≤ (n.size+3)*(unit B+1) := by
    have hh : stages.bitSteps ≤ ((2*n).size+1)*(unit B+1) := by
      simpa only [stages,width,word_width,twice,nc,nr,mul_view,input_view,copy_view,input_view] using hstages
    exact hh.trans (Nat.mul_le_mul_right _ (by omega))
  have hcard' : card.bitSteps ≤ (8*P+1)*(unit B+1) :=
    hcard.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hpslen 1))
  have hps' : ps.bitSteps ≤ (8*P+2)*(2*H+12)*(unit B+1) := by
    simpa only [ps,hscview] using hps
  rw [prepareWith]
  change nc.bitSteps+uc.bitSteps+br.bitSteps+block.bitSteps+pr.bitSteps+rounded.bitSteps+
    ns.bitSteps+np.bitSteps+sc.bitSteps+ps.bitSteps+card.bitSteps+reserve.bitSteps+
    lam.bitSteps+twice.bitSteps+stages.bitSteps+1 ≤ _
  have htotal := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hnc huc) hbr) hblock) hpr) hrounded) hns') hnp) hsc) hps') hcard') hreserve) hlam') htwice) hstages') 1
  apply htotal.trans
  dsimp only [P]
  nlinarith


noncomputable def widthCoefficient (κ : ℝ) : ℝ :=
  6*(bNumerator+bDenominator*factorCount+10*factorCount+100:ℕ)+
    (factorCount+1:ℕ)*(4*(Nat.ceil κ:ℝ)+1)

lemma widthCoefficient_nonneg (κ : ℝ) : 0 ≤ widthCoefficient κ := by
  unfold widthCoefficient
  positivity

lemma registerWidth_le_log (n U : ℕ) (κ : ℝ) (hn : 3≤n)
    (hU : (U:ℝ)≤(n:ℝ)^κ) :
    (registerWidth n U:ℝ) ≤ widthCoefficient κ*Real.log (n:ℝ) := by
  have hs := size_le_four_log n hn
  have hu := input_size_of_real_power n U κ (by omega) hU
  have huR : (U.size:ℝ) ≤ (Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := by exact_mod_cast hu
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hUs : (U.size:ℝ) ≤ (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) := by
    nlinarith [(show (0:ℝ)≤(Nat.ceil κ:ℝ) by positivity)]
  unfold registerWidth widthCoefficient
  push_cast
  have hc : (0:ℝ) ≤ (bNumerator:ℝ)+(bDenominator:ℝ)*factorCount+10*factorCount+100 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (show (n.size:ℝ)+2 ≤ 6*Real.log (n:ℝ) by linarith) hc
  have h2 := mul_le_mul_of_nonneg_left hUs (show (0:ℝ)≤(factorCount:ℝ)+1 by positivity)
  nlinarith

noncomputable def unitCoefficient (κ : ℝ) : ℝ := 1000*(widthCoefficient κ+1)^2+1
lemma unitCoefficient_pos (κ : ℝ) : 0 < unitCoefficient κ := by unfold unitCoefficient;positivity

lemma unit_le_log_square (n U : ℕ) (κ : ℝ) (hn : 3≤n)
    (hU : (U:ℝ)≤(n:ℝ)^κ) :
    (unit (registerWidth n U)+1:ℝ) ≤ unitCoefficient κ*(Real.log (n:ℝ))^2 := by
  have hw := registerWidth_le_log n U κ hn hU
  have hl := PhaseGeometry.one_le_log_nat n hn
  have hc := widthCoefficient_nonneg κ
  have h : (registerWidth n U:ℝ)+1 ≤ (widthCoefficient κ+1)*Real.log (n:ℝ) := by nlinarith
  have hh : ((registerWidth n U:ℝ)+1)^2 ≤ ((widthCoefficient κ+1)*Real.log (n:ℝ))^2 := by gcongr
  unfold unit unitCoefficient
  push_cast
  nlinarith [sq_nonneg (Real.log (n:ℝ)-1)]

lemma eventually_scale_le_n : ∀ᶠ n : ℕ in atTop, scale n ≤ n := by
  have h := AsymptoticCosts.eventualPowerFit (show AsymptoticCosts.eta<1 by
    norm_num [AsymptoticCosts.eta,AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.R]) 4 512
  filter_upwards [h,eventually_ge_atTop (3:ℕ)] with n hn hn3
  have hs := (scale_bounds n hn3).2
  have hn' : (scale n:ℝ)≤n := by
    apply hs.trans
    simpa only [Real.rpow_one,mul_comm,mul_left_comm,mul_assoc] using hn
  exact_mod_cast hn'

lemma eventually_input_size_le_n (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ)≤(n:ℝ)^κ → U.size ≤ n := by
  have h := AsymptoticCosts.eventualPowerFit (show (0:ℝ)<1 by norm_num) 1
    (4*(Nat.ceil κ:ℝ)+1)
  filter_upwards [h,eventually_ge_atTop (3:ℕ)] with n hn hn3
  intro U hU
  have hu := input_size_of_real_power n U κ (by omega) hU
  have hs := size_le_four_log n hn3
  have hl := PhaseGeometry.one_le_log_nat n hn3
  have huR : (U.size:ℝ)≤(Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := by exact_mod_cast hu
  have hmul := mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤(Nat.ceil κ:ℝ) by positivity)
  have hf : (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) ≤ n := by
    simpa only [Real.rpow_zero,Real.rpow_one,pow_one,mul_one] using hn
  have hbound : (U.size:ℝ)≤n := by
    calc
      (U.size:ℝ) ≤ (Nat.ceil κ:ℝ)*(n.size:ℝ)+1 := huR
      _ ≤ (Nat.ceil κ:ℝ)*(4*Real.log (n:ℝ))+1 := by
        simpa only [add_comm] using add_le_add_right hmul 1
      _ ≤ (4*(Nat.ceil κ:ℝ)+1)*Real.log (n:ℝ) := by nlinarith
      _ ≤ n := hf
  exact_mod_cast hbound

lemma scale_add_one_upper (n : ℕ) (hn : 3≤n) :
    (scale n+1:ℝ) ≤ 513*(Real.log (n:ℝ))^4*(n:ℝ)^AsymptoticCosts.eta := by
  have hs := (scale_bounds n hn).2
  have hl := one_le_pow₀ (PhaseGeometry.one_le_log_nat n hn) (n:=4)
  have he : 0≤AsymptoticCosts.eta := by
    norm_num [AsymptoticCosts.eta,AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.R]
  have hx := Real.one_le_rpow (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)) he
  have hm := one_le_mul_of_one_le_of_one_le hl hx
  nlinarith

/-- A fixed coefficient absorbs the finite root degrees and validation depth;
no parameter-sized power is normalized to establish the time estimate. -/
def executionCoefficient : ℕ := 1000000000000000000000000000000

theorem execute_finite_price (n U : ℕ) (hn : 4≤n) (hR : factorCount≤n)
    (hP : scale n≤n) (hU : U.size≤n) :
    (execute n U).bitSteps ≤ executionCoefficient*(scale n+1)*n*(unit (registerWidth n U)+1) := by
  let B := registerWidth n U
  have hbase : n.size+10+U.size ≤ B := by
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    omega
  have hf : ∀ z≤10*n,z.size≤B := by
    intro z hz
    have h1 := (Nat.size_le_size hz).trans (size_mul 10 n)
    have h10 : (10:ℕ).size=4 := by decide
    rw [h10] at h1
    omega
  have hr1 : rootWidth bNumerator bDenominator n ≤ B := by
    dsimp [rootWidth,B,registerWidth,bNumerator,bDenominator,factorCount]
    omega
  have hr2 : rootWidth bNumerator (bDenominator*factorCount) n ≤ B := by
    dsimp [rootWidth,B,registerWidth,bNumerator,bDenominator,factorCount]
    omega
  have hpw : ∀ j≤4,(n.size^j).size≤B := by
    intro j hj
    have h := size_pow n.size j
    have hm := Nat.mul_le_mul hj (size_le_self n.size)
    dsimp [B,registerWidth,bNumerator,bDenominator,factorCount]
    nlinarith
  have hprep := prepareWith_price bNumerator bDenominator factorCount n U B (10*n)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by change 8*scale n+8≤10*n;omega) hf hr1 hr2 hpw
  have hprep' : (prepare n U).bitSteps ≤
    ((n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*factorCount+10)+
      (8*scale n+2)*(2*(10*n)+12)+8*scale n+2*n.size+U.size+30)*(unit B+1) := by
    simpa only [prepare,ComputableParameters.scale,roundedPower] using hprep
  clear hprep
  have hencn := serialize_price B n (by omega)
  have hencU := serialize_price B U (by omega)
  change (BinaryMultiplierAdapter.encodeNat n).bitSteps ≤ unit B at hencn
  change (BinaryMultiplierAdapter.encodeNat U).bitSteps ≤ unit B at hencU
  have hval := validate_registers n U
  have hdec := decodePrepared_price n U
  have hcoef :
    (n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*factorCount+10)+
      (8*scale n+2)*(2*(10*n)+12)+16*scale n+2*n.size+U.size+2*factorCount+52 ≤
      executionCoefficient*(scale n+1)*n := by
    have hs := size_le_self n
    dsimp [bNumerator,bDenominator,factorCount,executionCoefficient]
    nlinarith
  rw [execute_steps,prepareEncoded_steps,prepareEncoded_value]
  have htotal :
      (BinaryMultiplierAdapter.encodeNat n).bitSteps+(BinaryMultiplierAdapter.encodeNat U).bitSteps+
        (prepare n U).bitSteps+1+(validate (prepare n U).value).bitSteps+
        (decodeData (prepare n U).value).bitSteps+1 ≤
      ((n+2)*(bNumerator+bDenominator+10)+(n+2)*(bNumerator+bDenominator*factorCount+10)+
        (8*scale n+2)*(2*(10*n)+12)+16*scale n+2*n.size+U.size+2*factorCount+52)*(unit B+1) := by
    nlinarith
  exact htotal.trans (Nat.mul_le_mul_right _ hcoef)

/-- Uniform setup bound for the actual selector, including input encoding,
trial division, all finite validation, and public metadata decoding. -/
theorem execute_bitSteps_eventually (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, (U:ℝ)≤(n:ℝ)^κ → (execute n U).bitSteps≤(n:ℝ)^2 := by
  let C : ℝ := (executionCoefficient:ℝ)*513*unitCoefficient κ
  have hfit := AsymptoticCosts.eventualPowerFit (show (1+AsymptoticCosts.eta:ℝ)<2 by
    norm_num [AsymptoticCosts.eta,AlignedCertificate.eta,AlignedCertificate.b,AlignedCertificate.R]) 6 C
  filter_upwards [hfit,eventually_scale_le_n,eventually_input_size_le_n κ,
    eventually_ge_atTop (max 4 factorCount)] with n hn hP hU hnlarge
  intro U hbound
  have hn4 : 4≤n := (le_max_left _ _).trans hnlarge
  have hnR : factorCount≤n := (le_max_right _ _).trans hnlarge
  have hn3 : 3≤n := by omega
  have hfinite := execute_finite_price n U hn4 hnR hP (hU U hbound)
  have hfiniteR : ((execute n U).bitSteps:ℝ) ≤
      (executionCoefficient:ℝ)*(scale n+1:ℝ)*(n:ℝ)*(unit (registerWidth n U)+1:ℝ) := by exact_mod_cast hfinite
  have hs := scale_add_one_upper n hn3
  have hu := unit_le_log_square n U κ hn3 hbound
  have hc := unitCoefficient_pos κ
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  calc
    ((execute n U).bitSteps:ℝ) ≤
        (executionCoefficient:ℝ)*(scale n+1:ℝ)*(n:ℝ)*(unit (registerWidth n U)+1:ℝ) := hfiniteR
    _ ≤ (executionCoefficient:ℝ)*(513*(Real.log (n:ℝ))^4*(n:ℝ)^AsymptoticCosts.eta)*
        (n:ℝ)*(unitCoefficient κ*(Real.log (n:ℝ))^2) := by gcongr
    _ = C*(Real.log (n:ℝ))^6*(n:ℝ)^(1+AsymptoticCosts.eta) := by
      rw [Real.rpow_add hnpos,Real.rpow_one,show (6:ℕ)=4+2 by rfl,pow_add]
      dsimp [C]
      ring
    _ ≤ (n:ℝ)^2 := by simpa only [Real.rpow_two] using hn

/-- The actual adaptive APSP cap satisfies the same uniform selector bound. -/
theorem execute_apspCap_eventually (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W≤n^degree →
      (execute n (192*n*W+40)).bitSteps≤(n:ℝ)^2 := by
  filter_upwards [execute_bitSteps_eventually (degree+2:ℕ),eventually_ge_atTop (232:ℕ)] with n hn hn232
  intro W hW
  apply hn
  have hcap := apspCap_polynomial degree n W (by omega) hW
  have hpoly : 192*n*W+40 ≤ n^(degree+2) := by
    calc
      _ ≤ 232*n^(degree+1) := hcap
      _ ≤ n*n^(degree+1) := Nat.mul_le_mul_right _ hn232
      _ = n^(degree+2) := by rw [show degree+2=(degree+1)+1 by omega,pow_succ];ring
  exact_mod_cast hpoly

end ThinMatrix.ParameterExecution
#print axioms ThinMatrix.ParameterExecution.execute_value
#print axioms ThinMatrix.ParameterExecution.execute_finite_price
#print axioms ThinMatrix.ParameterExecution.execute_bitSteps_eventually
#print axioms ThinMatrix.ParameterExecution.execute_apspCap_eventually
