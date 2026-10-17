import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Finite directed integer APSP reduction

Edges are optional integer weights; `none` means absent. Walks contain only
present directed edges. No-negative-cycles is stated as nonnegativity of every
closed walk, including the empty closed walk. No nonnegative-edge assumption
is made. This module concerns the reduction to exact min-plus multiplication,
not the implementation or exponent of that multiplication oracle.
-/
namespace ThinMatrix.APSPReduction
universe u
variable {V : Type u}

abbrev Graph (V : Type u) := V → V → Option ℤ

inductive Walk (w : Graph V) : V → V → Type u where
  | nil (a : V) : Walk w a a
  | cons (a b : V) {c : V} (cost : ℤ) (edge : w a b = some cost)
      (tail : Walk w b c) : Walk w a c

namespace Walk
variable {w : Graph V}

def length {a b : V} : Walk w a b → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ p => p.length + 1

def weight {a b : V} : Walk w a b → ℤ
  | .nil _ => 0
  | .cons _ _ cost _ p => cost + p.weight

def vertices {a b : V} : Walk w a b → List V
  | .nil a => [a]
  | .cons a _ _ _ p => a :: p.vertices

def append {a b c : V} (p : Walk w a b) (q : Walk w b c) : Walk w a c :=
  match p with
  | .nil _ => q
  | .cons a next cost edge tail => .cons a next cost edge (tail.append q)

@[simp] theorem append_length {a b c : V} (p : Walk w a b) (q : Walk w b c) :
    (p.append q).length = p.length + q.length := by
  induction p <;> simp_all [append, length]
  omega

@[simp] theorem append_weight {a b c : V} (p : Walk w a b) (q : Walk w b c) :
    (p.append q).weight = p.weight + q.weight := by
  induction p <;> simp_all [append, weight]
  omega

@[simp] theorem vertices_length {a b : V} (p : Walk w a b) :
    p.vertices.length = p.length + 1 := by
  induction p <;> simp_all [vertices, length]

/-- Splitting a simple walk at a vertex preserves a simple suffix. -/
theorem split_nodup {a b z : V} (p : Walk w a b)
    (hn : p.vertices.Nodup) (hz : z ∈ p.vertices) :
    ∃ pre : Walk w a z, ∃ suffix : Walk w z b,
      suffix.vertices.Nodup ∧ p.weight = pre.weight + suffix.weight := by
  induction p with
  | nil a =>
      simp only [vertices, List.mem_singleton] at hz
      subst z
      exact ⟨.nil a, .nil a, by simp [vertices], by simp [weight]⟩
  | cons a next cost edge tail ih =>
      simp only [vertices, List.mem_cons] at hz
      rcases hz with hz | hz
      · subst z
        exact ⟨.nil a, .cons a next cost edge tail, hn, by simp [weight]⟩
      · have ht : tail.vertices.Nodup := (List.nodup_cons.mp hn).2
        obtain ⟨pre, suffix, hs, heq⟩ := ih ht hz
        refine ⟨.cons a next cost edge pre, suffix, hs, ?_⟩
        simp only [weight]
        omega

end Walk

/-- Standard no-negative-cycle condition in its equivalent closed-walk form. -/
def NoNegativeCycles (w : Graph V) : Prop :=
  ∀ a (p : Walk w a a), 0 ≤ p.weight

/-- Genuine cycle removal: every walk has a simple walk with no larger weight. -/
theorem exists_simple_le {w : Graph V} (hno : NoNegativeCycles w)
    {a b : V} (p : Walk w a b) :
    ∃ q : Walk w a b, q.vertices.Nodup ∧ q.weight ≤ p.weight := by
  induction p with
  | nil a => exact ⟨.nil a, by simp [Walk.vertices], by simp [Walk.weight]⟩
  | cons a next cost edge tail ih =>
      obtain ⟨q, hn, hw⟩ := ih
      by_cases ha : a ∈ q.vertices
      · obtain ⟨pre, suffix, hs, heq⟩ := Walk.split_nodup q hn ha
        have hc := hno a (.cons a next cost edge pre)
        refine ⟨suffix, hs, ?_⟩
        simp only [Walk.weight] at hc ⊢
        omega
      · refine ⟨.cons a next cost edge q, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨ha, hn⟩
        · simp only [Walk.weight]
          omega

/-- The finite n-1 edge bound is proved, not assumed as an oracle contract. -/
theorem exists_short_le [Fintype V] {w : Graph V} (hno : NoNegativeCycles w)
    {a b : V} (p : Walk w a b) :
    ∃ q : Walk w a b, q.length ≤ Fintype.card V - 1 ∧ q.weight ≤ p.weight := by
  obtain ⟨q, hn, hw⟩ := exists_simple_le hno p
  have hc : q.vertices.length ≤ Fintype.card V := hn.length_le_card
  rw [Walk.vertices_length] at hc
  exact ⟨q, by omega, hw⟩

namespace Walk
variable {w : Graph V}

theorem length_zero {a b : V} (p : Walk w a b) (h : p.length = 0) :
    a = b ∧ p.weight = 0 := by
  cases p with
  | nil a => simp [weight]
  | cons a next cost edge tail => simp only [length] at h; omega

/-- Split any walk at a length budget; no graph or cycle hypothesis is used. -/
theorem split_length {a b : V} (p : Walk w a b) (cut : ℕ) :
    ∃ middle : V, ∃ pre : Walk w a middle, ∃ suf : Walk w middle b,
      p.weight = pre.weight + suf.weight ∧
      pre.length ≤ cut ∧ suf.length = p.length - cut := by
  induction cut generalizing a b with
  | zero => exact ⟨a, .nil a, p, by simp [weight], by simp [length], by simp⟩
  | succ cut ih =>
      cases p with
      | nil a => exact ⟨a, .nil a, .nil a, by simp [weight], by simp [length], by simp [length]⟩
      | cons a next cost edge tail =>
          obtain ⟨middle, pre, suf, hw, hp, hs⟩ := ih tail
          refine ⟨middle, .cons a next cost edge pre, suf, ?_, ?_, ?_⟩
          · simp only [weight]; omega
          · simp only [length]; omega
          · simp only [length]; omega

end Walk

abbrev Distance := WithTop ℤ
abbrev Matrix (V : Type u) := V → V → Distance

def edgeValue (value : Option ℤ) : Distance :=
  match value with
  | none => ⊤
  | some z => (z : Distance)

/-- Zero diagonal accounts for empty walks, including when an edge is absent. -/
noncomputable def initial (w : Graph V) (a b : V) : Distance :=
  by classical exact min (if a = b then 0 else ⊤) (edgeValue (w a b))

noncomputable def minPlus [Fintype V] (A B : Matrix V) (a b : V) : Distance :=
  Finset.univ.inf (fun middle => A a middle + B middle b)

/-- A bounded walk minimum, with attainment of every finite value. -/
def BoundedSpec (w : Graph V) (A : Matrix V) (limit : ℕ) : Prop :=
  ∀ a b, (∀ p : Walk w a b, p.length ≤ limit → A a b ≤ (p.weight : Distance)) ∧
    (A a b = ⊤ ∨ ∃ p : Walk w a b, p.length ≤ limit ∧ A a b = (p.weight : Distance))

/-- APSP means the minimum over every finite directed walk, not just a bounded
enumeration; unreachable entries are infinity. -/
def IsAPSP (w : Graph V) (A : Matrix V) : Prop :=
  ∀ a b, (∀ p : Walk w a b, A a b ≤ (p.weight : Distance)) ∧
    (A a b = ⊤ ∨ ∃ p : Walk w a b, A a b = (p.weight : Distance))

theorem initial_spec (w : Graph V) : BoundedSpec w (initial w) 1 := by
  classical
  intro a b
  constructor
  · intro p hp
    cases p with
    | nil a => simp [initial, Walk.weight]
    | cons a next cost edge tail =>
        have ht : tail.length = 0 := by simp only [Walk.length] at hp; omega
        obtain ⟨he, hw⟩ := Walk.length_zero tail ht
        subst b
        have h := min_le_right (if a = next then (0 : Distance) else ⊤)
          (edgeValue (w a next))
        simp [initial, edgeValue, edge, Walk.weight, hw]
  · cases he : w a b with
    | none =>
        by_cases hab : a = b
        · subst b
          right
          exact ⟨.nil a, by simp [Walk.length], by simp [initial, edgeValue, he, Walk.weight]⟩
        · left
          simp [initial, edgeValue, he, hab]
    | some z =>
        by_cases hab : a = b
        · subst b
          by_cases hz : (0 : ℤ) ≤ z
          · right
            refine ⟨.nil a, by simp [Walk.length], ?_⟩
            have hz' : (0 : Distance) ≤ (z : Distance) := by exact_mod_cast hz
            simp [initial, edgeValue, he, Walk.weight, min_eq_left hz']
          · right
            refine ⟨.cons a a z he (.nil a), by simp [Walk.length], ?_⟩
            have hz' : (z : Distance) ≤ 0 := by exact_mod_cast (show z ≤ 0 by omega)
            simp [initial, edgeValue, he, Walk.weight, min_eq_right hz']
        · right
          exact ⟨.cons a b z he (.nil b), by simp [Walk.length],
            by simp [initial, edgeValue, he, hab, Walk.weight]⟩

/-- One exact min-plus product composes two bounded walk minima. -/
theorem minPlus_spec [Fintype V] {w : Graph V} {A B : Matrix V} {L M : ℕ}
    (hA : BoundedSpec w A L) (hB : BoundedSpec w B M) :
    BoundedSpec w (minPlus A B) (L+M) := by
  classical
  intro a b
  constructor
  · intro p hp
    obtain ⟨middle, pre, suf, hw, hpre, hsuf⟩ := Walk.split_length p L
    have hs : suf.length ≤ M := by omega
    have ha := (hA a middle).1 pre hpre
    have hb := (hB middle b).1 suf hs
    calc
      minPlus A B a b ≤ A a middle + B middle b := Finset.inf_le (by simp)
      _ ≤ (pre.weight : Distance) + (suf.weight : Distance) := add_le_add ha hb
      _ = (p.weight : Distance) := by rw [← WithTop.coe_add, hw]
  · obtain ⟨middle, _, hm⟩ := Finset.exists_mem_eq_inf
      (Finset.univ : Finset V) ⟨a, by simp⟩ (fun k => A a k + B k b)
    rcases (hA a middle).2 with ha | ⟨pre, hp, ha⟩
    · left
      simpa [minPlus, ha] using hm
    · rcases (hB middle b).2 with hb | ⟨suf, hs, hb⟩
      · left
        simpa [minPlus, hb] using hm
      · right
        refine ⟨pre.append suf, ?_, ?_⟩
        · simp only [Walk.append_length]
          omega
        · calc
            minPlus A B a b = A a middle + B middle b := hm
            _ = (pre.weight : Distance) + (suf.weight : Distance) := by rw [ha, hb]
            _ = ((pre.append suf).weight : Distance) := by simp

/-- Each stage binds the previous matrix once and performs one product. -/
noncomputable def squared [Fintype V] (w : Graph V) : ℕ → Matrix V
  | 0 => initial w
  | k+1 => let previous := squared w k; minPlus previous previous

theorem squared_spec [Fintype V] (w : Graph V) (k : ℕ) :
    BoundedSpec w (squared w k) (2^k) := by
  induction k with
  | zero => simpa [squared] using initial_spec w
  | succ k ih =>
      have h := minPlus_spec ih ih
      simpa [squared, Nat.pow_succ, Nat.mul_two] using h

/-- A sufficiently long bounded minimum is the all-walk minimum because
cycle removal supplies a no-heavier walk of length at most n-1. -/
theorem boundedSpec_isAPSP [Fintype V] {w : Graph V} {A : Matrix V} {L : ℕ}
    (hno : NoNegativeCycles w) (hA : BoundedSpec w A L)
    (hL : Fintype.card V - 1 ≤ L) : IsAPSP w A := by
  intro a b
  constructor
  · intro p
    obtain ⟨q, hq, hw⟩ := exists_short_le hno p
    exact ((hA a b).1 q (hq.trans hL)).trans (by exact_mod_cast hw)
  · rcases (hA a b).2 with htop | ⟨p, _, hp⟩
    · exact Or.inl htop
    · exact Or.inr ⟨p, hp⟩

def rounds (n : ℕ) : ℕ := Nat.log2 n + 1

theorem length_budget (n : ℕ) : n - 1 ≤ 2 ^ rounds n := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  rw [← Nat.log2_eq_log_two] at h
  unfold rounds
  omega

noncomputable def apsp [Fintype V] (w : Graph V) : Matrix V :=
  squared w (rounds (Fintype.card V))

/-- Exact directed integer APSP from logarithmically many min-plus products. -/
theorem apsp_correct [Fintype V] (w : Graph V) (hno : NoNegativeCycles w) :
    IsAPSP w (apsp w) :=
  boundedSpec_isAPSP hno (squared_spec w _) (length_budget _)

theorem IsAPSP.unique {w : Graph V} {A B : Matrix V}
    (hA : IsAPSP w A) (hB : IsAPSP w B) : A = B := by
  funext a b
  apply le_antisymm
  · rcases (hB a b).2 with htop | ⟨p, hp⟩
    · simp [htop]
    · rw [hp]
      exact (hA a b).1 p
  · rcases (hA a b).2 with htop | ⟨p, hp⟩
    · simp [htop]
    · rw [hp]
      exact (hB a b).1 p

theorem IsAPSP.unreachable {w : Graph V} {A : Matrix V}
    (hA : IsAPSP w A) (a b : V) :
    A a b = ⊤ ↔ ¬ Nonempty (Walk w a b) := by
  constructor
  · intro ht ⟨p⟩
    have h := (hA a b).1 p
    simp [ht] at h
  · intro hn
    rcases (hA a b).2 with htop | ⟨p, _⟩
    · exact htop
    · exact (hn ⟨p⟩).elim

/-- Input magnitude bound in integers; absent edges impose no condition. -/
def EdgeBound (w : Graph V) (W : ℕ) : Prop :=
  ∀ a b z, w a b = some z → z.natAbs ≤ W

theorem Walk.weight_bound {w : Graph V} {W : ℕ} (hb : EdgeBound w W)
    {a b : V} (p : Walk w a b) : p.weight.natAbs ≤ p.length * W := by
  induction p with
  | nil a => simp [Walk.weight, Walk.length]
  | cons a next cost edge tail ih =>
      simp only [Walk.weight, Walk.length]
      calc
        (cost+tail.weight).natAbs ≤ cost.natAbs+tail.weight.natAbs := Int.natAbs_add_le _ _
        _ ≤ W+tail.length*W := Nat.add_le_add (hb a next cost edge) ih
        _ = (tail.length+1)*W := by ring

theorem BoundedSpec.entry_bound {w : Graph V} {A : Matrix V} {L W : ℕ}
    (hA : BoundedSpec w A L) (hb : EdgeBound w W) {a b : V} {z : ℤ}
    (hz : A a b = (z : Distance)) : z.natAbs ≤ L*W := by
  rcases (hA a b).2 with ht | ⟨p, hp, hv⟩
  · rw [hz] at ht
    simp at ht
  · have he : p.weight = z := by simpa using hv.symm.trans hz
    calc
      z.natAbs = p.weight.natAbs := by rw [he]
      _ ≤ p.length*W := p.weight_bound hb
      _ ≤ L*W := Nat.mul_le_mul_right W hp

theorem budget_upper {n : ℕ} (hn : n ≠ 0) : 2^rounds n ≤ 2*n := by
  have h := Nat.pow_log_le_self 2 hn
  rw [← Nat.log2_eq_log_two] at h
  rw [rounds, Nat.pow_succ]
  omega

/-- Every finite intermediate matrix entry has magnitude at most 2^k W.
This bound holds even before imposing the no-negative-cycle hypothesis. -/
theorem squared_entry_bound [Fintype V] {w : Graph V} {W : ℕ}
    (hb : EdgeBound w W) (k : ℕ) {a b : V} {z : ℤ}
    (hz : squared w k a b = (z : Distance)) : z.natAbs ≤ 2^k*W :=
  (squared_spec w k).entry_bound hb hz

/-- At the chosen logarithmic stopping point, finite values grow by ≤2n. -/
theorem apsp_entry_bound [Fintype V] {w : Graph V} {W : ℕ}
    (hb : EdgeBound w W) {a b : V} {z : ℤ}
    (hz : apsp w a b = (z : Distance)) : z.natAbs ≤ 2*Fintype.card V*W := by
  let : Nonempty V := ⟨a⟩
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  exact (squared_entry_bound hb _ hz).trans (Nat.mul_le_mul_right W (budget_upper hn))

/-- Polynomially bounded input integers remain polynomially bounded. -/
theorem apsp_polynomial_magnitude [Fintype V] {w : Graph V} {degree : ℕ}
    (hb : EdgeBound w ((Fintype.card V)^degree)) {a b : V} {z : ℤ}
    (hz : apsp w a b = (z : Distance)) :
    z.natAbs ≤ 2*(Fintype.card V)^(degree+1) := by
  calc
    z.natAbs ≤ 2*Fintype.card V*(Fintype.card V)^degree := apsp_entry_bound hb hz
    _ = 2*(Fintype.card V)^(degree+1) := by rw [Nat.pow_succ]; ring

/-- The cost model counts one min-plus call for each let-bound squaring stage. -/
def productCalls : ℕ → ℕ
  | 0 => 0
  | k+1 => productCalls k+1

theorem productCalls_eq (k : ℕ) : productCalls k = k := by
  induction k <;> simp_all [productCalls]

/-- Joint value/count execution model: one oracle call is charged at exactly
the same let-bound stage that computes its min-plus square. Matrix formation
and the implementation cost of an individual oracle are separate obligations.
-/
noncomputable def execution [Fintype V] (w : Graph V) : ℕ → Matrix V × ℕ
  | 0 => (initial w, 0)
  | k+1 =>
      let previous := execution w k
      (minPlus previous.1 previous.1, previous.2+1)

theorem execution_value [Fintype V] (w : Graph V) (k : ℕ) :
    (execution w k).1 = squared w k := by
  induction k <;> simp_all [execution, squared]

theorem execution_calls [Fintype V] (w : Graph V) (k : ℕ) :
    (execution w k).2 = k := by
  induction k <;> simp_all [execution]

/-- Exact count is log2 n+1, in particular O(log n) for n≥2. -/
theorem apsp_product_count (n : ℕ) : productCalls (rounds n) = Nat.log2 n+1 := by
  simp [productCalls_eq, rounds]

/-- Correctness and charged oracle calls for the same execution. -/
theorem apsp_execution [Fintype V] (w : Graph V) (hno : NoNegativeCycles w) :
    IsAPSP w ((execution w (rounds (Fintype.card V))).1) ∧
      (execution w (rounds (Fintype.card V))).2 = Nat.log2 (Fintype.card V)+1 := by
  constructor
  · rw [execution_value]
    exact apsp_correct w hno
  · simp [execution_calls, rounds]

#print axioms exists_simple_le
#print axioms exists_short_le
#print axioms minPlus_spec
#print axioms squared_spec
#print axioms apsp_correct
#print axioms apsp_polynomial_magnitude
#print axioms apsp_product_count
#print axioms apsp_execution

end ThinMatrix.APSPReduction
