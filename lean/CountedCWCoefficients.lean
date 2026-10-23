import CWPowerSpecialization

set_option autoImplicit false

/-! Integer arithmetic schedules for the coefficients actually used by the
CW interpolation program. Counts are integer-register operations, not Lean
runtime or a binary machine refinement. The powers use retained recursion. -/
namespace ThinMatrix.CountedCWCoefficients
open scoped BigOperators
open FiniteTrilinear CWPolynomialCertificate PolynomialDegeneration CWPowerSpecialization
abbrev Scalar := ℤ×ℕ

def lit (z : ℤ) : Scalar := (z,0)
def add (a b : Scalar) : Scalar := (a.1+b.1,a.2+b.2+1)
def sub (a b : Scalar) : Scalar := (a.1-b.1,a.2+b.2+1)
def mul (a b : Scalar) : Scalar := (a.1*b.1,a.2+b.2+1)
def neg (a : Scalar) : Scalar := sub (lit 0) a

def power (t : ℤ) : ℕ → Scalar
  | 0 => lit 1
  | n+1 => let child := power t n;mul child (lit t)

def sum : List Scalar → Scalar
  | [] => lit 0
  | a::xs => let child := sum xs;add a child

theorem power_value (t : ℤ) (n : ℕ) : (power t n).1=t^n := by
  induction n with
  | zero => simp [power,lit]
  | succ n ih => simp [power,mul,lit,ih,pow_succ]

theorem power_work (t : ℤ) (n : ℕ) : (power t n).2=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power,mul,lit,ih]

theorem sum_value (xs : List Scalar) : (sum xs).1=(xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sum,add,ih]

theorem sum_work (xs : List Scalar) : (sum xs).2=(xs.map Prod.snd).sum+xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sum,add,ih];omega

def privateCell (t : ℤ) (a : Fin 16) (i : Axis 16) : Scalar :=
  add (lit (basis origin i)) (mul (lit t) (lit (basis (privateLabel a) i)))

def sumCell (t : ℤ) (i : Axis 16) : Scalar :=
  add (lit (basis origin i)) (mul (power t 2)
    (sum (List.ofFn (fun a : Fin 16 => lit (basis (privateLabel a) i)))))

def terminalCell (t : ℤ) (i : Axis 16) : Scalar :=
  add (lit (basis origin i)) (mul (power t 3) (lit (basis terminal i)))

def base (t : ℤ) : Fin 18 → Term (Axis 16) (Axis 16) (Axis 16) Scalar :=
  Fin.addCases (m:=16) (n:=2) (motive:=fun _ => Term (Axis 16) (Axis 16) (Axis 16) Scalar) (fun a : Fin 16 => ⟨fun i => mul (lit t) (privateCell t a i),privateCell t a,privateCell t a⟩)
    (Fin.cons ⟨fun i => neg (sumCell t i),sumCell t,sumCell t⟩
      (Fin.cons ⟨fun i => mul (sub (lit 1) (mul (lit 16) (lit t))) (terminalCell t i),
        terminalCell t,terminalCell t⟩ (fun i : Fin 0 => Fin.elim0 i)))

/-- All three axes have the same label type, but remain separate variables. -/
def component {A D : Type*} (a : Term A A A D) (side : Fin 3) : A → D :=
  if side.val=0 then a.left else if side.val=1 then a.middle else a.right

theorem privateCell_value (t : ℤ) (a : Fin 16) (i : Axis 16) :
    (privateCell t a i).1=privateAt a t i := rfl

theorem sumCell_value (t : ℤ) (i : Axis 16) : (sumCell t i).1=sumAt t i := by
  simp only [sumCell,add,mul,lit,power_value,sum_value,List.map_ofFn,Function.comp_def,List.sum_ofFn,sumAt]

theorem terminalCell_value (t : ℤ) (i : Axis 16) : (terminalCell t i).1=terminalAt t i := by
  simp only [terminalCell,add,mul,lit,power_value,terminalAt]

theorem sumCell_work (t : ℤ) (i : Axis 16) : (sumCell t i).2=20 := by
  simp only [sumCell,add,mul,lit,power_work,sum_work,List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn]
  norm_num

def values {A : Type*} (a : Term A A A Scalar) : Term A A A ℤ :=
  ⟨fun i => (a.left i).1,fun i => (a.middle i).1,fun i => (a.right i).1⟩

theorem base_values (t : ℤ) (s : Fin 18) : values (base t s)=termsAt 16 t s := by
  refine Fin.addCases (m:=16) (n:=2) (motive:=fun s => values (base t s)=termsAt 16 t s)
    (fun a => ?_) (fun a => ?_) s
  · simp only [base,termsAt,Fin.addCases_left,values,mainAt,mul,lit,privateCell_value]
  · simp only [base,termsAt,Fin.addCases_right]
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero,values,negativeAt,neg,sub,lit,sumCell_value,zero_sub]
    · have hb : b=0 := Fin.eq_zero b
      subst b
      simp only [Fin.cons_succ,Fin.cons_zero,values,terminalTermAt,mul,sub,lit,terminalCell_value,Nat.cast_ofNat]

theorem base_value (t : ℤ) (s : Fin 18) (side : Fin 3) (i : Axis 16) :
    (component (base t s) side i).1=component (termsAt 16 t s) side i := by
  rw [← base_values]
  unfold component values
  split_ifs <;> rfl

theorem base_works (t : ℤ) (s : Fin 18) (i : Axis 16) :
    ((base t s).left i).2≤24 ∧ ((base t s).middle i).2≤24 ∧ ((base t s).right i).2≤24 := by
  refine Fin.addCases (m:=16) (n:=2) (motive:=fun s =>
    ((base t s).left i).2≤24 ∧ ((base t s).middle i).2≤24 ∧ ((base t s).right i).2≤24)
    (fun a => ?_) (fun a => ?_) s
  · simp only [base,Fin.addCases_left,privateCell,mul,add,lit];norm_num
  · simp only [base,Fin.addCases_right]
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero,neg,sub,lit,sumCell_work];norm_num
    · have hb : b=0 := Fin.eq_zero b
      subst b
      simp only [Fin.cons_succ,Fin.cons_zero,terminalCell,mul,sub,add,lit,power_work];norm_num

theorem base_work (t : ℤ) (s : Fin 18) (side : Fin 3) (i : Axis 16) :
    (component (base t s) side i).2≤24 := by
  have h := base_works t s i
  unfold component
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

def evaluate (side : Fin 3) (t : ℤ) : (n : ℕ) → TermIndex n → Index n → Scalar
  | 0 => fun _ _ => lit 1
  | n+1 => fun s i =>
    let child := evaluate side t n s.2 i.2
    let first := component (base t s.1) side i.1
    mul first child

theorem evaluate_value (side : Fin 3) (t : ℤ) (n : ℕ) (s : TermIndex n) (i : Index n) :
    (evaluate side t n s i).1=component (atInteger n t s) side i := by
  induction n with
  | zero => fin_cases side <;> rfl
  | succ n ih =>
      simp only [evaluate,mul,base_value,ih,atInteger,powerTerms,Term.product]
      fin_cases side <;> rfl

theorem evaluate_work (side : Fin 3) (t : ℤ) (n : ℕ) (s : TermIndex n) (i : Index n) :
    (evaluate side t n s i).2≤25*n := by
  induction n with
  | zero => simp [evaluate,lit]
  | succ n ih =>
      simp only [evaluate,mul]
      have := base_work t s.1 side i.1
      have := ih s.2 i.2
      omega

#print axioms power_value
#print axioms power_work
#print axioms sum_value
#print axioms sum_work
#print axioms privateCell_value
#print axioms sumCell_value
#print axioms terminalCell_value
#print axioms sumCell_work
#print axioms base_values
#print axioms base_works
#print axioms base_value
#print axioms base_work
#print axioms evaluate_value
#print axioms evaluate_work
end ThinMatrix.CountedCWCoefficients
