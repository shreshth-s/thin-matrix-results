import BinaryRecursiveDot
import RetainedEqualCopyCosts

set_option autoImplicit false
set_option maxRecDepth 3000

/-! Binary recursive execution on stored signed cells. Integer projections
occur only in theorem statements. Every actual multiplication/addition reads
the stored bit lists; child outputs are shared vectors. -/
namespace ThinMatrix.BinaryRetainedEqualCopy
open scoped BigOperators
open FiniteTrilinear FiniteDirectSum PolynomialDegeneration
open RecursiveTable (Layout Table prod fin power read store)
open RetainedEqualCopy (Base copies)
open BinaryCell BinaryRecursiveDot
variable {I J K : Type} {r t : ℕ}

def denoteBase {a : Layout I} {b : Layout J} {c : Layout K} (d : Base r t a b c Cell) : Base r t a b c ℤ :=
  ⟨d.left.map view,d.middle.map view,d.right.map view⟩

@[simp] theorem read_map_view {A : Type} (a : Layout A) (v : Table a Cell) (i : A) :
    read (v.map view) i=view (read v i) := by simp [RecursiveTable.read]

def padded {A : Type} (a : Layout A) (g : ℕ) (x : Table (prod (fin r) a) Cell) :
    Run (Table (prod (fin t) a) Cell) :=
  tabulate (prod (fin t) a) (fun i =>
    if h : g*t+i.1.val<r then ⟨read x (⟨g*t+i.1.val,h⟩,i.2),0,8⟩ else ⟨zero,0,8⟩)

theorem padded_slot {A : Type} (a : Layout A) (ht : 0<t)
    (x : Table (prod (fin r) a) Cell) (s : Fin r) (p : A) :
    read (padded (t:=t) a (slot r t ht s).1.val x).value ((slot r t ht s).2,p)=read x (s,p) := by
  have hs : s.val/t*t+s.val%t=s.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod s.val t
  simp only [padded,tabulate_read,slot]
  simp only [hs,s.isLt,↓reduceDIte]

def forms {A : Type} (a : Layout I) (tail : Layout A)
    (coeff : Table (prod (fin r) (prod (fin t) a)) Cell)
    (x : Fin t×(I×A) → Cell) : Run (Table (prod (fin r) tail) Cell) :=
  tabulate (prod (fin r) tail) (fun sp =>
    dot (prod (fin t) a) (fun i => read coeff (sp.1,i)) (fun i => x (i.1,(i.2,sp.2))))

def run (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c Cell) : (k : ℕ) → Table (copies t a k) Cell →
      Table (copies t b k) Cell → Run (Table (copies t c k) Cell)
  | 0,x,y => tabulate (copies t c 0) (fun z =>
      let product := mul (read x (z.1,PUnit.unit)) (read y (z.1,PUnit.unit))
      ⟨product.value,product.bitSteps,8⟩)
  | k+1,x,y =>
      let left := forms a (power a k) d.left (read x)
      let right := forms b (power b k) d.middle (read y)
      let children := tabulate (fin ((r+t-1)/t)) (fun g =>
        let px := padded (t:=t) (power a k) g.val left.value
        let py := padded (t:=t) (power b k) g.val right.value
        let child := run a b c ht d k px.value py.value
        ⟨child.value,px.bitSteps+py.bitSteps+child.bitSteps,
          px.control+py.control+child.control+8⟩)
      let output := tabulate (copies t c (k+1)) (fun z =>
        dot (fin r) (fun s => read d.right (s,(z.1,z.2.1)))
          (fun s => read (read children.value (slot r t ht s).1) ((slot r t ht s).2,z.2.2)))
      ⟨output.value,left.bitSteps+right.bitSteps+children.bitSteps+output.bitSteps,
        left.control+right.control+children.control+output.control+16⟩

set_option backward.isDefEq.respectTransparency false in
theorem run_correct [Fintype I] [Fintype J] [Fintype K]
    (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c Cell) (u : Tensor I J K ℤ)
    (hd : total (denoteBase d).terms=diagonal (Fin t) u) (k : ℕ)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell) (z : Fin t×PowerIndex K k) :
    view (read (run a b c ht d k x y).value z)=
      bilinear (tensorPower u k) (fun i => view (read x (z.1,i))) (fun j => view (read y (z.1,j))) z.2 := by
  induction k with
  | zero => simp [run,tabulate_read,bilinear,tensorPower,PowerIndex]
  | succ k ih =>
    simp only [run,tabulate_read,dot_view,ih]
    have hx (s : Fin r) (p : PowerIndex I k) := padded_slot (power a k) ht
      (forms a (power a k) d.left (read x)).value s p
    have hy (s : Fin r) (p : PowerIndex J k) := padded_slot (power b k) ht
      (forms b (power b k) d.middle (read y)).value s p
    simp only [hx,hy]
    simp only [forms,tabulate_read,dot_view]
    have h := RecursiveBilinearStep.step (denoteBase d).terms (tensorPower u k)
      (fun i => view (read x (i.1.1,(i.1.2,i.2))))
      (fun j => view (read y (j.1.1,(j.1.2,j.2)))) ((z.1,z.2.1),z.2.2)
    rw [hd] at h
    have hh := h.trans (RetainedEqualCopy.diagonal_product_bilinear u (tensorPower u k)
        (fun i => view (read x i)) (fun j => view (read y j)) z)
    simp only [Base.terms,denoteBase,read_map_view] at hh
    exact hh

theorem run_control [Fintype I] [Fintype J] [Fintype K]
    (a : Layout I) (b : Layout J) (c : Layout K) (ht : 0<t)
    (d : Base r t a b c Cell) (k : ℕ)
    (x : Table (copies t a k) Cell) (y : Table (copies t b k) Cell) :
    (run a b c ht d k x y).control=RetainedEqualCopyCosts.control r t a.size b.size c.size k := by
  have hp {A : Type} [Fintype A] (q : Layout A) (g : ℕ) (v : Table (prod (fin r) q) Cell) :
      (padded (t:=t) q g v).control=40*t*q.size+8 := by
    rw [padded,tabulate_control]
    have hv (i : Fin t×A) :
        (if h : g*t+i.1.val<r then (⟨read v (⟨g*t+i.1.val,h⟩,i.2),0,8⟩ : Run Cell)
          else ⟨zero,0,8⟩).control=8 := by split_ifs <;> rfl
    simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
    rw [← RecursiveTable.size_eq_card q]
    simp only [prod,fin];ring
  have hf {A B : Type} [Fintype B] (q : Layout A) (tail : Layout B)
      (coeff : Table (prod (fin r) (prod (fin t) q)) Cell) (v : Fin t×(A×B) → Cell) :
      (forms q tail coeff v).control=r*tail.size*(20*t*q.size+36)+8 := by
    rw [forms,tabulate_control]
    simp only [dot_control,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
    rw [← RecursiveTable.size_eq_card tail]
    simp only [prod,fin];ring
  induction k with
  | zero => simp [run,tabulate_control,RetainedEqualCopyCosts.control,copies,power,RecursiveTable.unit,prod,fin,
      PowerIndex];ring
  | succ k ih =>
    simp only [run,tabulate_control,hf,hp,ih,dot_control,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,
      powerIndex_card,smul_eq_mul,RecursiveTable.power_size,fin]
    rw [← RecursiveTable.size_eq_card c]
    simp only [copies,prod,fin,RecursiveTable.power_size,RetainedEqualCopyCosts.control]
    ring

#print axioms read_map_view
#print axioms padded_slot
#print axioms run_correct
#print axioms run_control
end ThinMatrix.BinaryRetainedEqualCopy
