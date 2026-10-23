import Mathlib

set_option autoImplicit false

/-! Finite coefficient tensors and explicit sums of separated products.
The index types distinguish the three variable spaces. A decomposition is
finite data, not an assumed rank bound. Its bilinear interpretation and
coordinate restriction/product laws are the interfaces needed by extraction.
No asymptotic rank or matrix-multiplication exponent is defined here. -/
namespace ThinMatrix.FiniteTrilinear
open scoped BigOperators

universe u v w x
abbrev Tensor (I J K : Type*) (R : Type*) := I → J → K → R

structure Term (I J K : Type*) (R : Type*) where
  left : I → R
  middle : J → R
  right : K → R

variable {I J K I' J' K' S T R : Type*} [CommRing R]

def Term.tensor (a : Term I J K R) : Tensor I J K R :=
  fun i j k => a.left i*a.middle j*a.right k

def total [Fintype S] (terms : S → Term I J K R) : Tensor I J K R :=
  fun i j k => ∑ s, (terms s).tensor i j k

def bilinear [Fintype I] [Fintype J] (t : Tensor I J K R) (x : I → R) (y : J → R) : K → R :=
  fun k => ∑ i, ∑ j, t i j k*x i*y j

theorem term_bilinear [Fintype I] [Fintype J] (a : Term I J K R) (x : I → R) (y : J → R) (k : K) :
    bilinear a.tensor x y k = a.right k*(∑ i,a.left i*x i)*(∑ j,a.middle j*y j) := by
  simp only [bilinear,Term.tensor,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm (f:=fun j i => a.right k*(a.left i*x i)*(a.middle j*y j))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem total_bilinear [Fintype I] [Fintype J] [Fintype S]
    (a : S → Term I J K R) (x : I → R) (y : J → R) (k : K) :
    bilinear (total a) x y k = ∑ s,(a s).right k*(∑ i,(a s).left i*x i)*(∑ j,(a s).middle j*y j) := by
  calc
    _ = ∑ i, ∑ j, ∑ s, (a s).tensor i j k*x i*y j := by
      simp only [bilinear,total,Finset.sum_mul]
    _ = ∑ i, ∑ s, ∑ j, (a s).tensor i j k*x i*y j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ j, (a s).tensor i j k*x i*y j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun s _ => term_bilinear (a s) x y k)

theorem total_reindex [Fintype S] [Fintype T] (e : S ≃ T) (a : S → Term I J K R) :
    total (fun t => a (e.symm t))=total a := by
  funext i j k
  exact e.symm.sum_comp (fun s => (a s).tensor i j k)

def restrict (t : Tensor I J K R) (f : I' → I) (g : J' → J) (h : K' → K) : Tensor I' J' K' R :=
  fun i j k => t (f i) (g j) (h k)

def Term.restrict (a : Term I J K R) (f : I' → I) (g : J' → J) (h : K' → K) : Term I' J' K' R :=
  ⟨a.left ∘ f,a.middle ∘ g,a.right ∘ h⟩

theorem total_restrict [Fintype S] (a : S → Term I J K R) (f : I' → I) (g : J' → J) (h : K' → K) :
    total (fun s => (a s).restrict f g h)=restrict (total a) f g h := rfl

def product (a : Tensor I J K R) (b : Tensor I' J' K' R) : Tensor (I×I') (J×J') (K×K') R :=
  fun i j k => a i.1 j.1 k.1*b i.2 j.2 k.2

def Term.product (a : Term I J K R) (b : Term I' J' K' R) : Term (I×I') (J×J') (K×K') R :=
  ⟨fun i => a.left i.1*b.left i.2,fun j => a.middle j.1*b.middle j.2,fun k => a.right k.1*b.right k.2⟩

theorem term_product (a : Term I J K R) (b : Term I' J' K' R) :
    (a.product b).tensor=product a.tensor b.tensor := by
  funext i j k
  simp only [Term.product,Term.tensor,product]
  ring

theorem total_product [Fintype S] [Fintype T] (a : S → Term I J K R) (b : T → Term I' J' K' R) :
    total (fun s : S×T => (a s.1).product (b s.2))=product (total a) (total b) := by
  funext i j k
  simp only [total,term_product,product,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

def Term.map {A : Type*} [CommRing A] (f : R →+* A) (a : Term I J K R) : Term I J K A :=
  ⟨fun i => f (a.left i),fun j => f (a.middle j),fun k => f (a.right k)⟩

theorem total_map {A : Type*} [CommRing A] [Fintype S] (f : R →+* A) (a : S → Term I J K R) :
    total (fun s => (a s).map f)=fun i j k => f (total a i j k) := by
  funext i j k
  simp only [total,Term.map,Term.tensor,map_sum,map_mul]

#print axioms term_bilinear
#print axioms total_bilinear
#print axioms total_reindex
#print axioms total_restrict
#print axioms term_product
#print axioms total_product
#print axioms total_map
end ThinMatrix.FiniteTrilinear
