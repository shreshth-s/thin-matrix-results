import LocalIdentities

set_option autoImplicit false

/-!
# Shifted local identity for the light-source and exact-half constructions

The ordinary normal forms have no p1 term.  The private factor absorbs that
term, and its polynomial baseline is H(z) = -x1-x2+(1+z)p1.  These are finite
ring identities; source masks, cropping, shared completion and execution
costs are separate obligations.  The aligned identity remains unchanged.
-/

namespace ThinMatrix.LightSourceIdentities

universe u
variable {R : Type u} [Lean.Grind.CommRing R]

def privateNormal (x₁ x₂ p₁ : R) : R := -x₁-x₂+p₁

def sharedNormal (x₁ x₂ p₁ z : R) : R := -x₁-x₂+(1+z)*p₁

def ordinarySum (x₁ x₂ p₂ s v w : R) : R :=
  (x₁+p₂)*(s+v) + x₁*(s-v) +
    (x₂-p₂)*(s+v-w) + x₂*(s-v+w)

theorem shifted_five_term (x₁ x₂ p₁ p₂ s v w : R) :
    ordinarySum x₁ x₂ p₂ s v w + privateNormal x₁ x₂ p₁*(2*s) =
      LocalIdentities.innerKernel p₁ p₂ s w := by
  unfold ordinarySum privateNormal LocalIdentities.innerKernel
  grind

theorem shifted_pencil (x₁ x₂ p₁ p₂ s w z : R) :
    privateNormal x₁ x₂ p₁*(2*s) + z*LocalIdentities.innerKernel p₁ p₂ s w =
      sharedNormal x₁ x₂ p₁ z*(2*s) + z*p₂*w := by
  unfold privateNormal sharedNormal LocalIdentities.innerKernel
  grind

theorem box_base (x₁ x₂ p₁ : R) :
    sharedNormal x₁ x₂ p₁ 0 = privateNormal x₁ x₂ p₁ := by
  unfold sharedNormal privateNormal
  grind

theorem aligned_change_of_variables (x₁ x₂ p₁ p₂ s v w : R) :
    LocalIdentities.ordinarySum (x₁-p₁) x₂ p₁ p₂ s v w =
      ordinarySum x₁ x₂ p₂ s v w ∧
    LocalIdentities.privateNormal (x₁-p₁) x₂ = privateNormal x₁ x₂ p₁ := by
  unfold LocalIdentities.ordinarySum LocalIdentities.privateNormal ordinarySum privateNormal
  constructor <;> grind

#print axioms shifted_five_term
#print axioms shifted_pencil
#print axioms box_base
#print axioms aligned_change_of_variables

end ThinMatrix.LightSourceIdentities
