import SourceCoordinates
import LightSourceIdentities
import CyclicLightWindow

set_option autoImplicit false

/-! Distinguished LOW contraction with the shifted private row. The recursive
scalar evaluator reads at most three children per normal nonchannel and one
per channel. Its lookup/ring-operation counts do not price word construction,
coefficient arrays, binary arithmetic, or indexing. -/
namespace ThinMatrix.DistinguishedResidualRoot
open WalshEmbedding
open scoped BigOperators
variable {R : Type*} [CommRing R]

def normalFactor (channel : Bool) (z : R) : NormalLetter → R
  | .x1 | .x2 => if channel then 0 else -1
  | .p1 => if channel then 0 else 1+z
  | .p2 => if channel then 1 else 0

def oppositeLetter (channel : Bool) : OppositeLetter := if channel then .w else .s

def oppositeScale (channel : Bool) : R := if channel then 1 else 2

def oppositeFactor (channel : Bool) (o : OppositeLetter) : R :=
  if o=oppositeLetter channel then oppositeScale channel else 0

theorem opposite_contract {m : ℕ} (channels : Cube m)
    (read : (Fin m → OppositeLetter) → R) :
    (∑ o, (∏ i, oppositeFactor (channels i) (o i))*read o) =
      (∏ i, oppositeScale (R:=R) (channels i))*read (fun i => oppositeLetter (channels i)) := by
  classical
  rw [Fintype.sum_eq_single (fun i => oppositeLetter (channels i))]
  · simp [oppositeFactor]
  · intro o ho
    have hex : ∃ i, o i≠oppositeLetter (channels i) := by
      by_contra! h
      exact ho (funext h)
    obtain ⟨i,hi⟩ := hex
    have hz : (∏ j, oppositeFactor (R:=R) (channels j) (o j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [oppositeFactor,hi])
    simp [hz]

theorem normalFactor_sum (channel : Bool) (z : R) (f : NormalLetter → R) :
    (∑ n, normalFactor channel z n*f n) =
      if channel then f .p2 else -f .x1-f .x2+(1+z)*f .p1 := by
  rw [← Equiv.sum_comp SourceCoordinates.normalEquiv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change normalFactor channel z .x1*f .x1 + (normalFactor channel z .x2*f .x2 +
    (normalFactor channel z .p1*f .p1 + normalFactor channel z .p2*f .p2)) = _
  cases channel <;> simp [normalFactor]
  ring

theorem shifted_private_sum (z : R) (f : NormalLetter → R) :
    (∑ n, normalFactor false z n*f n) =
      LightSourceIdentities.sharedNormal (f .x1) (f .x2) (f .p1) z := by
  simp [normalFactor_sum,LightSourceIdentities.sharedNormal]

def kernel {m : ℕ} (channels : Cube m) (z : R) (n : Fin m → NormalLetter) : R :=
  ∏ i, normalFactor (channels i) z (n i)

noncomputable def contract {m : ℕ} (channels : Cube m) (z : R)
    (read : (Fin m → NormalLetter) → R) : R := ∑ n, kernel channels z n*read n

theorem sum_words_succ {A : Type*} [Fintype A] (m : ℕ) (f : (Fin (m+1) → A) → R) :
    (∑ w, f w) = ∑ a, ∑ tail, f (Fin.cons a tail) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => A)),Fintype.sum_prod_type]
  rfl

theorem contract_succ {m : ℕ} (channels : Cube (m+1)) (z : R)
    (read : (Fin (m+1) → NormalLetter) → R) :
    contract channels z read = if channels 0 then
      contract (fun i => channels i.succ) z (fun w => read (Fin.cons .p2 w))
    else -contract (fun i => channels i.succ) z (fun w => read (Fin.cons .x1 w)) -
      contract (fun i => channels i.succ) z (fun w => read (Fin.cons .x2 w)) +
      (1+z)*contract (fun i => channels i.succ) z (fun w => read (Fin.cons .p1 w)) := by
  unfold contract kernel
  rw [sum_words_succ]
  simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_assoc,← Finset.mul_sum]
  exact normalFactor_sum (channels 0) z _

structure Evaluation (R : Type*) where
  value : R
  lookups : ℕ
  ringOps : ℕ

def evaluate : (m : ℕ) → Cube m → R → ((Fin m → NormalLetter) → R) → Evaluation R
  | 0, _, _, read => ⟨read Fin.elim0,1,0⟩
  | m+1, channels, z, read =>
      if channels 0 then evaluate m (fun i => channels i.succ) z (fun w => read (Fin.cons .p2 w))
      else
        let a := evaluate m (fun i => channels i.succ) z (fun w => read (Fin.cons .x1 w))
        let b := evaluate m (fun i => channels i.succ) z (fun w => read (Fin.cons .x2 w))
        let c := evaluate m (fun i => channels i.succ) z (fun w => read (Fin.cons .p1 w))
        ⟨-a.value-b.value+(1+z)*c.value,a.lookups+b.lookups+c.lookups,a.ringOps+b.ringOps+c.ringOps+5⟩

theorem evaluate_value (m : ℕ) (channels : Cube m) (z : R) (read : (Fin m → NormalLetter) → R) :
    (evaluate m channels z read).value = contract channels z read := by
  induction m with
  | zero =>
    simp only [evaluate,contract,kernel,Fintype.prod_empty,one_mul,Fintype.sum_unique]
    exact congrArg read (Subsingleton.elim _ _)
  | succ m ih => rw [contract_succ]; simp only [evaluate]; split <;> simp_all only

theorem evaluate_lookups (m : ℕ) (channels : Cube m) (z : R) (read : (Fin m → NormalLetter) → R) :
    (evaluate m channels z read).lookups ≤ 3^m := by
  induction m with
  | zero => simp [evaluate]
  | succ m ih =>
    have ha := ih (fun i => channels i.succ) (fun w => read (Fin.cons .x1 w))
    have hb := ih (fun i => channels i.succ) (fun w => read (Fin.cons .x2 w))
    have hc := ih (fun i => channels i.succ) (fun w => read (Fin.cons .p1 w))
    have hd := ih (fun i => channels i.succ) (fun w => read (Fin.cons .p2 w))
    simp only [evaluate,pow_succ]
    split <;> (try dsimp only) <;> omega

theorem evaluate_ringOps (m : ℕ) (channels : Cube m) (z : R) (read : (Fin m → NormalLetter) → R) :
    2*(evaluate m channels z read).ringOps ≤ 5*(3^m-1) := by
  induction m with
  | zero => simp [evaluate]
  | succ m ih =>
    have ha := ih (fun i => channels i.succ) (fun w => read (Fin.cons .x1 w))
    have hb := ih (fun i => channels i.succ) (fun w => read (Fin.cons .x2 w))
    have hc := ih (fun i => channels i.succ) (fun w => read (Fin.cons .p1 w))
    have hd := ih (fun i => channels i.succ) (fun w => read (Fin.cons .p2 w))
    have hp : 0<3^m := by positivity
    simp only [evaluate,pow_succ]
    split <;> (try dsimp only) <;> omega

theorem kernel_support {m : ℕ} (channels : Cube m) (z : R) (n : Fin m → NormalLetter)
    (h : kernel channels z n ≠ 0) : normalP2Bits n = channels := by
  funext i
  have hn : normalFactor (channels i) z (n i) ≠ 0 := by
    intro hz
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  cases hc : channels i <;> cases hw : n i <;> simp_all [normalFactor,normalP2Bits]

#print axioms opposite_contract
#print axioms normalFactor_sum
#print axioms shifted_private_sum
#print axioms sum_words_succ
#print axioms contract_succ
#print axioms evaluate_value
#print axioms evaluate_lookups
#print axioms evaluate_ringOps
#print axioms kernel_support
end ThinMatrix.DistinguishedResidualRoot
