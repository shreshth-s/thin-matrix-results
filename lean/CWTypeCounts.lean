import CWBlockWords

set_option autoImplicit false

namespace ThinMatrix.CWTypeCounts
open scoped BigOperators
open PolynomialDegeneration CWSixBlocks CWBlockWords

def count {A : Type*} [DecidableEq A] (a : A) : (n : ℕ) → PowerIndex A n → ℕ
  | 0 => fun _ => 0
  | n+1 => fun w => (if w.1=a then 1 else 0)+count a n w.2

theorem marginal_counts (n : ℕ) (w : Word n) :
    count (2:Fin 3) n (wx n w)=count Block.b200 n w ∧
    count (2:Fin 3) n (wy n w)=count Block.b020 n w ∧
    count (2:Fin 3) n (wz n w)=count Block.b002 n w ∧
    count (1:Fin 3) n (wx n w)=count Block.b101 n w+count Block.b110 n w ∧
    count (1:Fin 3) n (wy n w)=count Block.b011 n w+count Block.b110 n w ∧
    count (1:Fin 3) n (wz n w)=count Block.b011 n w+count Block.b101 n w := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have ht := ih w.2
      obtain ⟨b,w⟩ := w
      cases b <;> simp_all [count,wx,wy,wz,mapWord,cx,cy,cz] <;> omega

theorem joint_counts_unique (n : ℕ) (u v : Word n)
    (hx : ∀ a : Fin 3,count a n (wx n u)=count a n (wx n v))
    (hy : ∀ a : Fin 3,count a n (wy n u)=count a n (wy n v))
    (hz : ∀ a : Fin 3,count a n (wz n u)=count a n (wz n v)) :
    ∀ b : Block,count b n u=count b n v := by
  have hu := marginal_counts n u
  have hv := marginal_counts n v
  have hx1 := hx 1;have hy1 := hy 1;have hz1 := hz 1
  have hx2 := hx 2;have hy2 := hy 2;have hz2 := hz 2
  intro b
  cases b <;> omega

theorem rows_card (q n : ℕ) (w : Word n) : Fintype.card (Rows q n w)=q^count Block.b101 n w := by
  induction n with
  | zero => simp [Rows,count]
  | succ n ih =>
      calc
        _ = Fintype.card (Row q w.1×Rows q n w.2) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by
          rw [Fintype.card_prod,ih]
          obtain ⟨b,w⟩ := w
          cases b <;> simp [Row,count,Fintype.card_eq_nat_card,-Nat.card_eq_fintype_card,Nat.card_fin,pow_add]

theorem inners_card (q n : ℕ) (w : Word n) : Fintype.card (Inners q n w)=q^count Block.b110 n w := by
  induction n with
  | zero => simp [Inners,count]
  | succ n ih =>
      calc
        _ = Fintype.card (Inner q w.1×Inners q n w.2) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by
          rw [Fintype.card_prod,ih]
          obtain ⟨b,w⟩ := w
          cases b <;> simp [CWSixBlocks.Inner,count,Fintype.card_eq_nat_card,-Nat.card_eq_fintype_card,Nat.card_fin,pow_add]

theorem cols_card (q n : ℕ) (w : Word n) : Fintype.card (Cols q n w)=q^count Block.b011 n w := by
  induction n with
  | zero => simp [Cols,count]
  | succ n ih =>
      calc
        _ = Fintype.card (Col q w.1×Cols q n w.2) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by
          rw [Fintype.card_prod,ih]
          obtain ⟨b,w⟩ := w
          cases b <;> simp [Col,count,Fintype.card_eq_nat_card,-Nat.card_eq_fintype_card,Nat.card_fin,pow_add]

#print axioms marginal_counts
#print axioms joint_counts_unique
#print axioms rows_card
#print axioms inners_card
#print axioms cols_card
end ThinMatrix.CWTypeCounts
