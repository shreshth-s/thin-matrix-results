import Lean

/-!
# Limited verification of the aligned local algebra

This file proves only the commutative-ring identities (A1) and (A7) in
`outputs/exponent-improvement.tex`, plus their local residual rearrangement.
It does not formalize the source/Walsh embedding, exact division of complete
outputs, tensor powers, cache construction, complexity bounds, numerical
certificates, reductions, or the APSP theorem.

It uses the commutative-ring class and proof-producing algebra solver shipped
with Lean 4.31.0. There is no Mathlib or other package dependency. The
variable `z` is an arbitrary ring element; these equalities can therefore
also be instantiated in a commutative polynomial or quotient ring once its
ring structure is supplied. No inversion or division is assumed.

Reproduce with the `lean` executable from Lean 4.31.0:
`lean lean/LocalIdentities.lean`.
-/

namespace ThinMatrix.LocalIdentities

universe u

variable {R : Type u} [Lean.Grind.CommRing R]

/-- The normal-side private factor from the aligned identity. -/
def privateNormal (x₁ x₂ : R) : R := -x₁ - x₂

/-- The opposite-side private factor. -/
def privateOpposite (s : R) : R := 2 * s

/-- The private bilinear term `P`. -/
def privateKernel (x₁ x₂ s : R) : R :=
  privateNormal x₁ x₂ * privateOpposite s

/-- The aligned inner bilinear term `I`. -/
def innerKernel (p₁ p₂ s w : R) : R := 2 * p₁ * s + p₂ * w

/-- The shared polynomial normal factor `H(z)`. -/
def sharedNormal (x₁ x₂ p₁ z : R) : R := -x₁ - x₂ + z * p₁

/-- The four ordinary bilinear terms in the aligned identity. -/
def ordinarySum (x₁ x₂ p₁ p₂ s v w : R) : R :=
  (x₁ + p₁ + p₂) * (s + v) +
  (x₁ + p₁) * (s - v) +
  (x₂ - p₂) * (s + v - w) +
  x₂ * (s - v + w)

/-- Equation (A1), with all five terms written explicitly. -/
theorem aligned_five_term (x₁ x₂ p₁ p₂ s v w : R) :
    (x₁ + p₁ + p₂) * (s + v) +
      (x₁ + p₁) * (s - v) +
      (x₂ - p₂) * (s + v - w) +
      x₂ * (s - v + w) +
      (-x₁ - x₂) * (2 * s) =
    2 * p₁ * s + p₂ * w := by
  grind

/-- The same identity using the named ordinary, private, and inner terms. -/
theorem ordinary_plus_private (x₁ x₂ p₁ p₂ s v w : R) :
    ordinarySum x₁ x₂ p₁ p₂ s v w + privateKernel x₁ x₂ s =
      innerKernel p₁ p₂ s w := by
  exact aligned_five_term x₁ x₂ p₁ p₂ s v w

/-- The local residual rearrangement; it is not the global residual formula. -/
theorem ordinary_eq_inner_sub_private (x₁ x₂ p₁ p₂ s v w : R) :
    ordinarySum x₁ x₂ p₁ p₂ s v w =
      innerKernel p₁ p₂ s w - privateKernel x₁ x₂ s := by
  have h := ordinary_plus_private x₁ x₂ p₁ p₂ s v w
  grind

/-- Equation (A7), with every factor written explicitly. -/
theorem aligned_pencil (x₁ x₂ p₁ p₂ s w z : R) :
    (-x₁ - x₂) * (2 * s) + z * (2 * p₁ * s + p₂ * w) =
      (-x₁ - x₂ + z * p₁) * (2 * s) + z * p₂ * w := by
  grind

/-- The shared-factor pencil using the named `P`, `I`, and `H(z)`. -/
theorem private_plus_scaled_inner (x₁ x₂ p₁ p₂ s w z : R) :
    privateKernel x₁ x₂ s + z * innerKernel p₁ p₂ s w =
      sharedNormal x₁ x₂ p₁ z * privateOpposite s + z * p₂ * w := by
  exact aligned_pencil x₁ x₂ p₁ p₂ s w z

/-- The private box base uses the constant specialization `H(0)`. -/
theorem shared_normal_at_zero (x₁ x₂ p₁ : R) :
    sharedNormal x₁ x₂ p₁ 0 = privateNormal x₁ x₂ := by
  unfold sharedNormal privateNormal
  grind

end ThinMatrix.LocalIdentities

#print axioms ThinMatrix.LocalIdentities.aligned_five_term
#print axioms ThinMatrix.LocalIdentities.ordinary_plus_private
#print axioms ThinMatrix.LocalIdentities.ordinary_eq_inner_sub_private
#print axioms ThinMatrix.LocalIdentities.aligned_pencil
#print axioms ThinMatrix.LocalIdentities.private_plus_scaled_inner
#print axioms ThinMatrix.LocalIdentities.shared_normal_at_zero
