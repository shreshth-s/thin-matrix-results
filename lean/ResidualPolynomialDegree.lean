import BinaryResidualArray
import ExactHalfResidualWindow

set_option autoImplicit false

/-! Formal-degree space for the actual residual polynomial, over the cyclic
ring (which may have zero divisors). These bounds are applied to the binary
array program in CompleteResidualArray; they are not operation-cost bounds. -/
namespace ThinMatrix.ResidualPolynomialDegree
open WalshEmbedding DistinguishedResidualSupport DistinguishedResidualRoot
open BinaryResidualPolynomial
open scoped BigOperators

/-- Each distinguished normal position increases degree by at most one.
No integral-domain or nonzero-leading-coefficient premise is needed. -/
theorem contract_degree {R : Type*} [CommRing R] (m D : ℕ) (channels : Cube m)
    (read : (Fin m → NormalLetter) → Polynomial R)
    (h : ∀ w, (read w).natDegree ≤ D) :
    (contract channels Polynomial.X read).natDegree ≤ m+D := by
  induction m with
  | zero =>
    simpa only [contract,kernel,Fintype.prod_empty,one_mul,Fintype.sum_unique,Nat.zero_add] using h default
  | succ m ih =>
    have ht (a : NormalLetter) := ih (fun i => channels i.succ) (fun w => read (Fin.cons a w))
      (fun w => h (Fin.cons a w))
    have hx : (1+Polynomial.X : Polynomial R).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le (by simp) Polynomial.natDegree_X_le
    rw [contract_succ]
    split
    · exact (ht .p2).trans (by omega)
    · apply Polynomial.natDegree_add_le_of_degree_le
      · apply (Polynomial.natDegree_sub_le _ _).trans
        simp only [Polynomial.natDegree_neg]
        exact max_le ((ht .x1).trans (by omega)) ((ht .x2).trans (by omega))
      · exact Polynomial.natDegree_mul_le.trans (by have hp := ht .p1; omega)

def integerScale {m : ℕ} (co : Vector Bool m) : ℤ :=
  (co.toList.map (fun b => if b then (1:ℤ) else 2)).prod

/-- Exact polynomial specified by the already implemented binary root row. -/
noncomputable def polynomial {L C : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) : Polynomial (CyclicRing.Cyclic C) :=
  (integerScale co : Polynomial (CyclicRing.Cyclic C))*
    contract cn.get Polynomial.X (fun n => BinaryResidualRootProgram.sourcePolynomial cap raw
      (assemble (ResidualLayout.equivalence maskN) n (fun i => normalRemaining (wn.get i)))
      (assemble (ResidualLayout.equivalence maskO) (fun i => oppositeLetter (co.get i))
        (fun i => SourceCoordinates.oppositeEquiv (wo.get i))))

theorem polynomial_degree {L C : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) :
    (polynomial cap raw maskN maskO cn co wn wo).natDegree ≤ (ResidualLayout.selected maskN).length := by
  have h := contract_degree (ResidualLayout.selected maskN).length 0 cn.get
    (fun n => BinaryResidualRootProgram.sourcePolynomial cap raw
      (assemble (ResidualLayout.equivalence maskN) n (fun i => normalRemaining (wn.get i)))
      (assemble (ResidualLayout.equivalence maskO) (fun i => oppositeLetter (co.get i))
        (fun i => SourceCoordinates.oppositeEquiv (wo.get i))))
    (by intro w; simp [BinaryResidualRootProgram.sourcePolynomial])
  exact Polynomial.natDegree_mul_le.trans (by simpa [Polynomial.natDegree_intCast] using h)

theorem row_coeff {L C F : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length) (d : Fin F) (r : Fin C) :
    cellView (BinaryResidualRootProgram.execute F cap raw maskN maskO cn co wn wo).value d r =
      ((polynomial cap raw maskN maskO cn co wn wo).coeff d.val) r := by
  rw [polynomial,Polynomial.coeff_intCast_mul,CyclicRing.intCast_mul_coeff]
  exact BinaryResidualRootProgram.execute_coeff cap raw maskN maskO cn co wn wo d r

/-- Semantic view of every coefficient, including the zero tail beyond storage.
It is not an additional runtime polynomial reconstruction. -/
noncomputable def decode {F C : ℕ} [NeZero C] (block : Block F C) : Polynomial (CyclicRing.Cyclic C) :=
  ∑ d : Fin F, Polynomial.monomial d.val (fun r => cellView block d r)

theorem decode_coeff {F C : ℕ} [NeZero C] (block : Block F C) (n : ℕ) (r : Fin C) :
    ((decode block).coeff n) r = if h : n<F then cellView block ⟨n,h⟩ r else 0 := by
  classical
  simp only [decode,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,CyclicRing.sum_coeff]
  by_cases hn : n<F
  · rw [Finset.sum_eq_single ⟨n,hn⟩]
    · simp [hn]
    · intro i _ hi
      have hv : i.val≠n := by intro h; exact hi (Fin.ext h)
      simp [hv]
    · simp
  · have hz (d : Fin F) : d.val≠n := by intro h; have := d.isLt; omega
    simp [hn,hz]

/-- A full polynomial equality, not just equality on supplied coefficients. -/
theorem row_complete {L C F : ℕ} [NeZero C] (cap : ℕ)
    (raw : BinarySourceFormation.RawStore L C) (maskN maskO : Vector Bool L)
    (cn : Vector Bool (ResidualLayout.selected maskN).length)
    (co : Vector Bool (ResidualLayout.selected maskO).length)
    (wn : Vector (Fin 3) (ResidualLayout.remaining maskN).length)
    (wo : Vector (Fin 3) (ResidualLayout.remaining maskO).length)
    (hf : (ResidualLayout.selected maskN).length < F) :
    decode (BinaryResidualRootProgram.execute F cap raw maskN maskO cn co wn wo).value =
      polynomial cap raw maskN maskO cn co wn wo := by
  apply Polynomial.ext
  intro n
  funext r
  rw [decode_coeff]
  split
  · exact row_coeff cap raw maskN maskO cn co wn wo _ r
  · rename_i hn
    have hd := polynomial_degree cap raw maskN maskO cn co wn wo
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    rfl

#print axioms contract_degree
#print axioms polynomial_degree
#print axioms row_coeff
#print axioms decode_coeff
#print axioms row_complete
end ThinMatrix.ResidualPolynomialDegree
