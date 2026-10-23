import BinaryResidualLeaf

set_option autoImplicit false

/-! Recursive retained binary normal contraction. The public relative bounds
expose every leaf call; they do not supply a fast source oracle. Leaf assembly
must instantiate these bounds with BinaryResidualLeaf and retained layouts.
Intermediate coefficient widths follow from the original leaf magnitude.
Every formal degree and full coefficient column is processed at each node. -/
namespace ThinMatrix.BinaryResidualContraction
open WalshEmbedding BinaryCell BinaryGroupedCoordinates BinaryResidualPolynomial
open scoped BigOperators

def push {m : ℕ} (a : NormalLetter) (w : Vector NormalLetter m) : Vector NormalLetter (m+1) :=
  Vector.ofFn (Fin.cons a w.get)

theorem push_get {m : ℕ} (a : NormalLetter) (w : Vector NormalLetter m) :
    (push a w).get=Fin.cons a w.get := by funext i; simp [push]

def pushRead {m F C : ℕ} (a : NormalLetter) (read : Vector NormalLetter (m+1) → Run (Block F C))
    (w : Vector NormalLetter m) : Run (Block F C) :=
  let word := push a w
  let out := read word
  ⟨out.value,out.bitSteps,out.control+6*(m+1)+4⟩

def tail {m : ℕ} (channels : Vector Bool (m+1)) : Vector Bool m := Vector.ofFn (fun i => channels.get i.succ)

theorem tail_get {m : ℕ} (channels : Vector Bool (m+1)) : (tail channels).get=(fun i => channels.get i.succ) := by
  funext i; simp [tail]

def evaluate {F C : ℕ} : (m : ℕ) → Vector Bool m → (Vector NormalLetter m → Run (Block F C)) → Run (Block F C)
  | 0, _, read => let out := read (Vector.ofFn Fin.elim0); ⟨out.value,out.bitSteps,out.control+2⟩
  | m+1, channels, read =>
      let next := tail channels
      if channels.get 0 then
        let out := evaluate m next (pushRead .p2 read)
        ⟨out.value,out.bitSteps,out.control+6*m+12⟩
      else
        let a := evaluate m next (pushRead .x1 read)
        let b := evaluate m next (pushRead .x2 read)
        let c := evaluate m next (pushRead .p1 read)
        let out := privateRow a.value b.value c.value
        ⟨out.value,a.bitSteps+b.bitSteps+c.bitSteps+out.bitSteps,a.control+b.control+c.control+out.control+6*m+16⟩

theorem evaluate_bound {F C : ℕ} (m : ℕ) (channels : Vector Bool m)
    (read : Vector NormalLetter m → Run (Block F C)) (A : ℕ) (h : ∀ w, Bound A (read w).value) :
    Bound (4^m*A) (evaluate m channels read).value := by
  induction m with
  | zero => simpa [evaluate] using h (Vector.ofFn Fin.elim0)
  | succ m ih =>
    have hh (a : NormalLetter) := ih (tail channels) (pushRead a read) (fun w => h (push a w))
    simp only [evaluate]
    split
    · intro d r
      apply (hh .p2 d r).trans
      calc
        _ ≤ (4^m*A)*4 := Nat.le_mul_of_pos_right _ (by decide)
        _ = _ := by rw [pow_succ]; ring
    · have ho := privateRow_magnitude _ _ _ (4^m*A) (hh .x1) (hh .x2) (hh .p1)
      convert ho using 1
      rw [pow_succ]
      ring

theorem unit_mono {a b : ℕ} (h : a≤b) :
    BackendScalarBits.backendScalarUnit a≤BackendScalarBits.backendScalarUnit b := by
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

def nodeBits (F C M A : ℕ) : ℕ := F*(C*(9*BackendScalarBits.backendScalarUnit (4^M*A).size))

theorem evaluate_bits {F C : ℕ} (m M : ℕ) (hm : m≤M) (channels : Vector Bool m)
    (read : Vector NormalLetter m → Run (Block F C)) (A W : ℕ)
    (ha : ∀ w, Bound A (read w).value) (hw : ∀ w, (read w).bitSteps≤W) :
    (evaluate m channels read).bitSteps≤3^m*(W+m*nodeBits F C M A) := by
  induction m with
  | zero => simpa [evaluate] using hw (Vector.ofFn Fin.elim0)
  | succ m ih =>
    have hh (a : NormalLetter) := ih (by omega) (tail channels) (pushRead a read)
      (fun w => ha (push a w)) (fun w => hw (push a w))
    have hb (a : NormalLetter) := evaluate_bound m (tail channels) (pushRead a read) A (fun w => ha (push a w))
    have hp := privateRow_bits _ _ _ (4^m*A) (hb .x1) (hb .x2) (hb .p1)
    have hu : BackendScalarBits.backendScalarUnit (4*(4^m*A)).size≤BackendScalarBits.backendScalarUnit (4^M*A).size := by
      apply unit_mono
      apply Nat.size_le_size
      calc
        _ = 4^(m+1)*A := by rw [pow_succ]; ring
        _ ≤ _ := Nat.mul_le_mul_right A (Nat.pow_le_pow_right (by decide) hm)
    have hn : (privateRow (evaluate m (tail channels) (pushRead .x1 read)).value
      (evaluate m (tail channels) (pushRead .x2 read)).value
      (evaluate m (tail channels) (pushRead .p1 read)).value).bitSteps≤nodeBits F C M A :=
      hp.trans (by unfold nodeBits; gcongr)
    have h3 : 1≤3^m := Nat.one_le_pow _ _ (by decide)
    have h0 := hh .x1
    have h1 := hh .x2
    have h2 := hh .p1
    have h4 := hh .p2
    simp only [evaluate,pow_succ]
    split <;> dsimp only <;> nlinarith

def nodeControl (F C M : ℕ) : ℕ := 2*(6*(M+1)+4)+(F*(C*116+40)+8)+20

theorem evaluate_control {F C : ℕ} (m M : ℕ) (hm : m≤M) (channels : Vector Bool m)
    (read : Vector NormalLetter m → Run (Block F C)) (W : ℕ) (hw : ∀ w, (read w).control≤W) :
    (evaluate m channels read).control≤3^m*(W+2+m*nodeControl F C M) := by
  induction m generalizing W with
  | zero => simpa [evaluate] using Nat.add_le_add_right (hw (Vector.ofFn Fin.elim0)) 2
  | succ m ih =>
    have hh (a : NormalLetter) := ih (by omega) (tail channels) (pushRead a read) (W+6*(m+1)+4) (by
      intro w
      exact Nat.add_le_add_right (Nat.add_le_add_right (hw (push a w)) (6*(m+1))) 4)
    have hp := privateRow_control (evaluate m (tail channels) (pushRead .x1 read)).value
      (evaluate m (tail channels) (pushRead .x2 read)).value
      (evaluate m (tail channels) (pushRead .p1 read)).value
    have h3 : 1≤3^m := Nat.one_le_pow _ _ (by decide)
    have h0 := hh .x1
    have h1 := hh .x2
    have h2 := hh .p1
    have h4 := hh .p2
    simp only [evaluate,pow_succ,nodeControl]
    simp only [nodeControl] at h0 h1 h2 h4
    split <;> dsimp only <;> nlinarith

/-- The coefficient recursion is the previously proved scalar tensor
contraction at z=X, with arbitrary entangled polynomial leaves. -/
theorem evaluate_coeff {F q : ℕ} [NeZero q] (m : ℕ) (channels : Vector Bool m)
    (read : Vector NormalLetter m → Run (Block F q))
    (p : (Fin m → NormalLetter) → Polynomial (CyclicRing.Cyclic q))
    (h : ∀ w d r, cellView (read w).value d r=((p w.get).coeff d.val) r) (d : Fin F) (r : Fin q) :
    cellView (evaluate m channels read).value d r =
      ((DistinguishedResidualRoot.contract channels.get Polynomial.X p).coeff d.val) r := by
  induction m generalizing d r with
  | zero =>
    have he : (Vector.ofFn (Fin.elim0 : Fin 0 → NormalLetter)).get=(default : Fin 0 → NormalLetter) := Subsingleton.elim _ _
    simpa only [evaluate,DistinguishedResidualRoot.contract,DistinguishedResidualRoot.kernel,
      Fintype.prod_empty,one_mul,Fintype.sum_unique,he] using h (Vector.ofFn Fin.elim0) d r
  | succ m ih =>
    have hh (a : NormalLetter) (dd : Fin F) (rr : Fin q) :=
      ih (tail channels) (pushRead a read) (fun w => p (Fin.cons a w))
        (fun w d r => by simpa only [pushRead,push_get] using h (push a w) d r) dd rr
    rw [DistinguishedResidualRoot.contract_succ]
    simp only [evaluate]
    split
    · simpa only [tail_get] using hh .p2 d r
    · have hv := privateRow_extract _ _ _
        (DistinguishedResidualRoot.contract (tail channels).get Polynomial.X (fun w => p (Fin.cons .x1 w)))
        (DistinguishedResidualRoot.contract (tail channels).get Polynomial.X (fun w => p (Fin.cons .x2 w)))
        (DistinguishedResidualRoot.contract (tail channels).get Polynomial.X (fun w => p (Fin.cons .p1 w)))
        (hh .x1) (hh .x2) (hh .p1) d r
      simpa only [tail_get] using hv

#print axioms push_get
#print axioms tail_get
#print axioms evaluate_bound
#print axioms unit_mono
#print axioms evaluate_bits
#print axioms evaluate_control
#print axioms evaluate_coeff
end ThinMatrix.BinaryResidualContraction
