import RecursiveBilinearStep
import EqualCopyRecursion

set_option autoImplicit false
set_option maxRecDepth 3000

/-! Stored recursive evaluation. Upper forms, padded child inputs, recursive
outputs and recombination outputs are vectors evaluated once, not closures
that rerun the recursive computation at each lookup. -/
namespace ThinMatrix.RetainedEqualCopy
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum PolynomialDegeneration RecursiveTable RecursiveBilinearStep
variable {I J K R : Type} [CommRing R] {r t : ℕ}

def copies {I : Type} (t : ℕ) (a : Layout I) (k : ℕ) : Layout (Fin t×PowerIndex I k) :=
  prod (fin t) (power a k)

structure Base (r t : ℕ) (a : Layout I) (b : Layout J) (c : Layout K) (R : Type) where
  left : Table (prod (fin r) (prod (fin t) a)) R
  middle : Table (prod (fin r) (prod (fin t) b)) R
  right : Table (prod (fin r) (prod (fin t) c)) R

def Base.terms {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c R)
    (s : Fin r) : Term (Fin t×I) (Fin t×J) (Fin t×K) R :=
  ⟨fun i => read d.left (s,i),fun j => read d.middle (s,j),fun k => read d.right (s,k)⟩

def padded {A : Type} (a : Layout A) (g : ℕ) (x : Table (prod (fin r) a) R) :
    Run (Table (prod (fin t) a) R) :=
  tabulate (prod (fin t) a) (fun i =>
    if h : g*t+i.1.val<r then ⟨read x (⟨g*t+i.1.val,h⟩,i.2),0,8⟩ else ⟨0,0,8⟩)

theorem padded_slot {A : Type} (a : Layout A) (ht : 0<t)
    (x : Table (prod (fin r) a) R) (s : Fin r) (p : A) :
    read (padded (t:=t) a (slot r t ht s).1.val x).value ((slot r t ht s).2,p)=read x (s,p) := by
  have hs : s.val/t*t+s.val%t=s.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod s.val t
  simp only [padded,tabulate_read,slot]
  simp only [hs,s.isLt,↓reduceDIte]

def forms {A : Type} (a : Layout I) (tail : Layout A)
    (coeff : Table (prod (fin r) (prod (fin t) a)) R)
    (x : Fin t×(I×A) → R) : Run (Table (prod (fin r) tail) R) :=
  tabulate (prod (fin r) tail) (fun sp =>
    dot (prod (fin t) a) (fun i => read coeff (sp.1,i)) (fun i => x (i.1,(i.2,sp.2))))

def run (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c R) : (k : ℕ) → Table (copies t a k) R →
      Table (copies t b k) R → Run (Table (copies t c k) R)
  | 0,x,y => tabulate (copies t c 0) (fun z =>
      ⟨read x (z.1,PUnit.unit)*read y (z.1,PUnit.unit),1,8⟩)
  | k+1,x,y =>
      let left := forms a (power a k) d.left (read x)
      let right := forms b (power b k) d.middle (read y)
      let children := tabulate (fin ((r+t-1)/t)) (fun g =>
        let px := padded (t:=t) (power a k) g.val left.value
        let py := padded (t:=t) (power b k) g.val right.value
        let child := run a b c ht d k px.value py.value
        ⟨child.value,px.arithmetic+py.arithmetic+child.arithmetic,
          px.control+py.control+child.control+8⟩)
      let output := tabulate (copies t c (k+1)) (fun z =>
        dot (fin r) (fun s => read d.right (s,(z.1,z.2.1)))
          (fun s => read (read children.value (slot r t ht s).1) ((slot r t ht s).2,z.2.2)))
      ⟨output.value,left.arithmetic+right.arithmetic+children.arithmetic+output.arithmetic,
        left.control+right.control+children.control+output.control+16⟩

theorem diagonal_product_bilinear [Fintype I] [Fintype J]
    {A B C : Type} [Fintype A] [Fintype B]
    (u : Tensor I J K R) (v : Tensor A B C R)
    (x : Fin t×(I×A) → R) (y : Fin t×(J×B) → R) (z : Fin t×(K×C)) :
    bilinear (product (diagonal (Fin t) u) v)
      (fun i => x (i.1.1,(i.1.2,i.2))) (fun j => y (j.1.1,(j.1.2,j.2))) ((z.1,z.2.1),z.2.2)=
      bilinear (product u v) (fun i => x (z.1,i)) (fun j => y (z.1,j)) z.2 := by
  simp [bilinear,product,diagonal,Fintype.sum_prod_type,ite_and,ite_mul]

set_option backward.isDefEq.respectTransparency false in
theorem run_correct [Fintype I] [Fintype J] [Fintype K]
    (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c R) (u : Tensor I J K R)
    (hd : total d.terms=diagonal (Fin t) u) (k : ℕ)
    (x : Table (copies t a k) R) (y : Table (copies t b k) R) (z : Fin t×PowerIndex K k) :
    read (run a b c ht d k x y).value z=
      bilinear (tensorPower u k) (fun i => read x (z.1,i)) (fun j => read y (z.1,j)) z.2 := by
  induction k with
  | zero => simp [run,tabulate_read,bilinear,tensorPower,PowerIndex]
  | succ k ih =>
    simp only [run,tabulate_read,dot_value]
    simp only [ih]
    have hx (s : Fin r) (p : PowerIndex I k) := padded_slot (power a k) ht
      (forms a (power a k) d.left (read x)).value s p
    have hy (s : Fin r) (p : PowerIndex J k) := padded_slot (power b k) ht
      (forms b (power b k) d.middle (read y)).value s p
    simp only [hx,hy]
    simp only [forms,tabulate_read,dot_value]
    have h := step d.terms (tensorPower u k)
      (fun i => read x (i.1.1,(i.1.2,i.2)))
      (fun j => read y (j.1.1,(j.1.2,j.2))) ((z.1,z.2.1),z.2.2)
    rw [hd] at h
    exact h.trans (diagonal_product_bilinear u (tensorPower u k) (read x) (read y) z)

#print axioms padded_slot
#print axioms diagonal_product_bilinear
#print axioms run_correct
end ThinMatrix.RetainedEqualCopy
