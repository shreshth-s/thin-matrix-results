import RecursiveTable
import FiniteDirectSum

set_option autoImplicit false

namespace ThinMatrix.RecursiveBilinearStep
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum RecursiveTable
variable {I J K A B C S R : Type} [CommRing R]

def dotList : List (R×R) → Run R
  | [] => ⟨0,0,2⟩
  | p::ps =>
      let tail := dotList ps
      ⟨p.1*p.2+tail.value,tail.arithmetic+2,tail.control+12⟩

theorem dotList_value (ps : List (R×R)) :
    (dotList ps).value=(ps.map (fun p => p.1*p.2)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [dotList,ih]

theorem dotList_arithmetic (ps : List (R×R)) : (dotList ps).arithmetic=2*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [dotList,ih];omega

theorem dotList_control (ps : List (R×R)) : (dotList ps).control=12*ps.length+2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [dotList,ih];omega

def dot (a : Layout I) (f g : I → R) : Run R :=
  let inputs := store a (fun i => (f i,g i))
  let out := dotList inputs.toList
  ⟨out.value,out.arithmetic,out.control+8*a.size+2⟩

theorem dot_value [Fintype I] (a : Layout I) (f g : I → R) :
    (dot a f g).value=∑ i,f i*g i := by
  simp only [dot,dotList_value,store,Vector.toList_ofFn,List.map_ofFn,
    Function.comp_apply,List.sum_ofFn]
  exact a.index.symm.sum_comp (fun i => f i*g i)

theorem dot_arithmetic (a : Layout I) (f g : I → R) : (dot a f g).arithmetic=2*a.size := by
  simp [dot,dotList_arithmetic]

theorem dot_control (a : Layout I) (f g : I → R) : (dot a f g).control=20*a.size+4 := by
  simp [dot,dotList_control];omega

theorem diagonal_bilinear [Fintype S] [DecidableEq S] [Fintype I] [Fintype J]
    (u : Tensor I J K R) (x : S×I → R) (y : S×J → R) (z : S×K) :
    bilinear (diagonal S u) x y z=bilinear u (fun i => x (z.1,i)) (fun j => y (z.1,j)) z.2 := by
  simp [bilinear,diagonal,Fintype.sum_prod_type,ite_and,ite_mul]

/-- One recursive level: form each upper linear combination once for every
suffix coordinate, multiply the suffix tensors, then recombine. -/
theorem step [Fintype S] [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    (a : S → Term I J K R) (v : Tensor A B C R)
    (x : I×A → R) (y : J×B → R) (z : K×C) :
    (∑ s,(a s).right z.1 * bilinear v
      (fun p => ∑ i,(a s).left i*x (i,p))
      (fun q => ∑ j,(a s).middle j*y (j,q)) z.2)=
      bilinear (product (total a) v) x y z := by
  symm
  calc
    _ = ∑ p, ∑ q, v p q z.2 * bilinear (total a)
        (fun i => x (i,p)) (fun j => y (j,q)) z.1 := by
      simp only [bilinear,product,Fintype.sum_prod_type,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro p _
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro q _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      ring
    _ = ∑ p, ∑ q, ∑ s, v p q z.2 * ((a s).right z.1 *
        (∑ i,(a s).left i*x (i,p)) * (∑ j,(a s).middle j*y (j,q))) := by
      simp only [total_bilinear,Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro s _
      rw [Finset.sum_comm]
      simp only [bilinear]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro p _
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro q _
      ring

#print axioms dotList_value
#print axioms dotList_arithmetic
#print axioms dotList_control
#print axioms dot_value
#print axioms dot_arithmetic
#print axioms dot_control
#print axioms diagonal_bilinear
#print axioms step
end ThinMatrix.RecursiveBilinearStep
