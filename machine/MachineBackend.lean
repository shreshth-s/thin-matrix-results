import ThreeSumApsp.Lang.Lib.Copy
import ThreeSumApsp.Lang.Lib.ArrayAt
import ThreeSumApsp.Lang.PolyBounded

/-!
# Initial concrete Light backend routines

These finite imperative programs perform coefficient reads and pointwise
integer array operations. Their specifications are proved from Light's
execution rules, with explicit word/address promises and memory framing.
They do not claim to implement cyclic convolution or the full thin oracle.

The pass proof uses the upstream `Ends.pass` API; the separation and read
invariants follow the pattern documented by its copy routine. The upstream
library is the pinned Apache-2.0 Lake dependency, not vendored source.
-/

namespace Light.ThinMatrixBackend

variable {lim : Limits} {P : Program} {d : Nat}

/-- Read one stored coefficient. Arguments are the base address and offset. -/
def indexedReadBody : Stmt := .set 0 (M (v 0 +' v 1))

/-- The read takes five source-language steps and changes no memory cell.
A caller additionally pays its own argument-evaluation/call overhead. -/
theorem indexedRead_meets {p : Nat} (hp : P[p]? = some indexedReadBody)
    {μ : Nat → Int} {src i : Nat}
    (hw : (lim.space : Int) ≤ lim.word) (hi : src + i < lim.space) :
    Meets lim P p d [(src : Int), i] μ 5
      (fun r μ' => r = μ (src + i) ∧ μ' = μ) := by
  apply Meets.of_body hp
  unfold indexedReadBody
  exact Ends.setLast (by simp) (by light_side) (by light_time)

/-- Pointwise array operation, with the arithmetic operation fixed in the
finite program text. Inputs may alias each other; the output is separate. -/
def pointwiseBody (o : Op) : Stmt :=
  pass 4 (v 3) (v 2) (.op o (M (v 0 +' v 4)) (M (v 1 +' v 4)))

@[simp] def pointwiseTime (n : Nat) : Nat := 21 * n + 6

theorem pointwise_meets {o : Op} {p : Nat}
    (hp : P[p]? = some (pointwiseBody o))
    {μ : Nat → Int} {a b dst n : Nat}
    (hw : (lim.space : Int) ≤ lim.word)
    (ha : a + n ≤ lim.space) (hb : b + n ≤ lim.space)
    (hdst : dst + n ≤ lim.space)
    (hsepA : Apart a n dst n) (hsepB : Apart b n dst n)
    (hval : ∀ i < n, |o.eval (μ (a+i)) (μ (b+i))| ≤ lim.word) :
    Meets lim P p d [(a : Int), b, dst, n] μ (pointwiseTime n) fun _ μ' =>
      (∀ i < n, μ' (dst+i) = o.eval (μ (a+i)) (μ (b+i))) ∧
      SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass
    (fun i => o.eval (μ (a+i)) (μ (b+i))) (fun i hi => ?_)
    ⟨fun i hi => wrote_done
      (f := fun i => o.eval (μ (a+i)) (μ (b+i))) hi, by light_keep⟩
    hw hdst rfl rfl (hT := by light_time [pointwiseTime]))
  have hreadA (f : Nat → Int) : wrote μ dst f i (a+i) = μ (a+i) :=
    wrote_rest (by omega)
  have hreadB (f : Nat → Int) : wrote μ dst f i (b+i) = μ (b+i) :=
    wrote_rest (by omega)
  have hv := abs_le.mp (hval i hi)
  cases o <;> simp only [Op.eval] at hv <;> light_side [hreadA, hreadB]

/-- A single finite program containing the initial backend routines. -/
def program : Program :=
  [indexedReadBody, pointwiseBody .add, pointwiseBody .sub, pointwiseBody .mul]

theorem read_in_program : program[0]? = some indexedReadBody := rfl

theorem add_in_program : program[1]? = some (pointwiseBody .add) := rfl

theorem sub_in_program : program[2]? = some (pointwiseBody .sub) := rfl

theorem mul_in_program : program[3]? = some (pointwiseBody .mul) := rfl

/-- Concrete memory-level instance for reading a stored coefficient. -/
structure ReadInstance where
  src : Nat
  offset : Nat
  length : Nat
  bound : Nat
  coefficients : List Int

def readTask : Task where
  Inst := ReadInstance
  size x := x.length
  bound x := x.bound
  args x := [x.src, x.offset]
  Pre x μ fr := ArrayAt μ x.src x.coefficients x.length x.bound fr ∧
    x.offset < x.length
  Post x μ _ r μ' := r = x.coefficients.getD x.offset 0 ∧ μ' = μ

def readNeed (_n U : Nat) : Need where
  word := U
  cells := 0
  depth := 0

/-- A closed execution proof for an actual routine of the finite backend
program, stable under arbitrary appended procedures and memory frames. -/
theorem readTask_solved : Solves readTask program 0 (fun _ _ => 5) readNeed := by
  refine ⟨indexedReadBody, read_in_program, ?_⟩
  intro R lim d x μ fr hpre hok
  obtain ⟨harray, hoff⟩ := hpre
  have hspace : x.src + x.offset < lim.space := by
    have hb := harray.below
    have hc := hok.cells
    simp only [readNeed, add_zero] at hc
    omega
  have hread : μ (x.src + x.offset) = x.coefficients.getD x.offset 0 :=
    harray.read hoff
  change Ends lim (program ++ R) d indexedReadBody
    ⟨frame [x.src, x.offset, fr], μ⟩ 5 _
  unfold indexedReadBody
  exact Ends.setLast (by simp [readTask, hread])
    (by have hw := hok.space; light_side) (by light_time)

theorem readNeed_polynomial : PolyNeed readNeed := by
  unfold readNeed
  poly_need []

theorem storedCoefficientRead_solvedIn : SolvedIn readTask (fun _ _ => 5) :=
  ⟨program, 0, (fun _ _ => 5), readNeed, readNeed_polynomial,
    readTask_solved, by intros; norm_num⟩

#print axioms indexedRead_meets
#print axioms pointwise_meets
#print axioms readTask_solved
#print axioms storedCoefficientRead_solvedIn

end Light.ThinMatrixBackend

