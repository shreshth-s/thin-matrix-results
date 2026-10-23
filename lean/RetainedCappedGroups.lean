import RetainedPrefixEncoder

set_option autoImplicit false

/-! Capped suffix grouping directly from retained binary cells. Each group
contains a retained ternary prefix tree. No intermediate integer is serialized.
Repeated pair/support occurrences and every coefficient column are retained. -/
namespace ThinMatrix.RetainedCappedGroups
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix CappedBitPreparation
open GroupedPreparation
open scoped BigOperators

abbrev Source (P ell C : ℕ) := OppositeWindowLayer.Source (P+ell) C

def suffix {ell : ℕ} (p k : Key ell) : Vector (Fin 3) ell :=
  ofStoredFn p (fun i => if k.get i then 2 else pairLetter (p.get i))

theorem suffix_get {ell : ℕ} (p k : Key ell) : (suffix p k).get=word p.get (support k) := by
  funext i
  simp [suffix,ofStoredFn_eq,word,support]

def datum {P ell C : ℕ} (X : Source P ell C) (p k : Key ell) (u : Word P) : Run (Vector Cell C) :=
  let signInfo := locate p k
  let w := Vector.ofFn (Fin.append u (suffix p k).get)
  let address := TernaryWindowAddress.encode w
  let out := BinaryGroupedPreparation.tabulate (X.get address.value) (fun c =>
    let copied := signedCopy signInfo.value.negative ((X.get address.value).get c)
    ⟨copied.value,copied.bitSteps,8⟩)
  ⟨out.value,signInfo.bitSteps+address.bitSteps+out.bitSteps,
    signInfo.control+address.control+out.control+16*(P+ell+1)^2+16⟩

theorem datum_value {P ell C : ℕ} (X : Source P ell C) (p k : Key ell) (u : Word P) (c : Fin C) :
    view ((datum X p k u).value.get c)=signed p.get (support k)*
      OppositeWindowLayer.value X (Fin.append u (word p.get (support k))) c := by
  have hv (f : Word (P+ell)) : (Vector.ofFn f).get=f := by
    funext i; exact Vector.get_ofFn _ _
  simp only [datum,BinaryGroupedPreparation.tabulate_get,signedCopy_view,locate_negative,
    GroupedCoordinates.coordinates_sign,TernaryWindowAddress.encode_value,hv,suffix_get,OppositeWindowLayer.value]

theorem datum_bound {P ell C : ℕ} (X : Source P ell C) (p k : Key ell) (u : Word P)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) (c : Fin C) :
    (view ((datum X p k u).value.get c)).natAbs≤A := by
  simp only [datum,BinaryGroupedPreparation.tabulate_get,signedCopy_abs]
  exact ha _ c

def datumBitBudget (P ell C A : ℕ) : ℕ := addressBudget ell+addressBudget (P+ell)+C*BackendScalarBits.backendScalarUnit A.size
def datumControlBudget (P ell C : ℕ) : ℕ := 28*ell+10+(40*(P+ell)+18)+(40*C+8)+16*(P+ell+1)^2+16

theorem datum_bits {P ell C : ℕ} (X : Source P ell C) (p k : Key ell) (u : Word P)
    (A : ℕ) (ha : OppositeWindowLayer.Bound X A) : (datum X p k u).bitSteps≤datumBitBudget P ell C A := by
  have hs := locate_bits p k
  have hw := TernaryWindowAddress.encode_bits (Vector.ofFn (Fin.append u (suffix p k).get))
  have hc := BinaryGroupedPreparation.tabulate_bits (X.get (TernaryWindowAddress.encode (Vector.ofFn (Fin.append u (suffix p k).get))).value)
    (fun c => let copied := signedCopy (locate p k).value.negative ((X.get (TernaryWindowAddress.encode (Vector.ofFn (Fin.append u (suffix p k).get))).value).get c)
      (⟨copied.value,copied.bitSteps,8⟩ : Run Cell))
    (fun c => signedCopy_bits A _ _ (ha _ c))
  dsimp only at hc
  simp only [datum,datumBitBudget]
  omega

theorem datum_control {P ell C : ℕ} (X : Source P ell C) (p k : Key ell) (u : Word P) :
    (datum X p k u).control≤datumControlBudget P ell C := by
  have hc := BinaryGroupedPreparation.tabulate_control (X.get (TernaryWindowAddress.encode (Vector.ofFn (Fin.append u (suffix p k).get))).value)
    (fun c => let copied := signedCopy (locate p k).value.negative ((X.get (TernaryWindowAddress.encode (Vector.ofFn (Fin.append u (suffix p k).get))).value).get c)
      (⟨copied.value,copied.bitSteps,8⟩ : Run Cell)) (W:=8) (by intro c; rfl)
  dsimp only at hc
  simp only [datum,datumControlBudget,locate_control,TernaryWindowAddress.encode_control]
  omega

structure Prepared (P ell r C : ℕ) where
  keys : Vector (Key ell) (CappedSubsetList.count ell r)
  pairs : Vector (Key ell) (2^ell)
  groups : Vector (Vector (PrefixCellTree.Data C P) (CappedSubsetList.count ell r)) (2^ell)

def prepare {P ell C : ℕ} (r : ℕ) (X : Source P ell C) : Run (Prepared P ell r C) :=
  let keys := storeKeys ell r
  let pairs := storePairs ell
  let out := BinaryGroupedPreparation.tabulate pairs.value (fun p => BinaryGroupedPreparation.tabulate keys.value
    (fun j => PrefixCellTree.build P (datum X (pairs.value.get p) (keys.value.get j))))
  ⟨⟨keys.value,pairs.value,out.value⟩,out.bitSteps,keys.work+pairs.work+out.control+12⟩

theorem prepare_value {P ell C : ℕ} (r : ℕ) (X : Source P ell C) (p : Fin (2^ell))
    (j : Fin (CappedSubsetList.count ell r)) (u : Word P) (c : Fin C) :
    view (PrefixCellTree.read ((((prepare r X).value.groups.get p).get j)) u c)=
      signed ((pairKeys ell).get p).get (support ((keyVector ell r).get j))*
        OppositeWindowLayer.value X (Fin.append u (word ((pairKeys ell).get p).get (support ((keyVector ell r).get j)))) c := by
  simp only [prepare,BinaryGroupedPreparation.tabulate_get,PrefixCellTree.build_read,
    datum_value,storeKeys_value,storePairs_value]

theorem prepare_bound {P ell C : ℕ} (r : ℕ) (X : Source P ell C) (A : ℕ) (ha : OppositeWindowLayer.Bound X A)
    (p : Fin (2^ell)) (j : Fin (CappedSubsetList.count ell r)) :
    PrefixCellTree.Bound (((prepare r X).value.groups.get p).get j) A := by
  simp only [prepare,BinaryGroupedPreparation.tabulate_get]
  exact PrefixCellTree.build_bound _ (fun u c => datum_bound _ _ _ u A ha c)

def bitBudget (P ell r C A : ℕ) : ℕ := 2^ell*(CappedSubsetList.count ell r*(3^P*datumBitBudget P ell C A))
def controlBudget (P ell r C : ℕ) : ℕ := keyBudget ell r+(keyBudget ell ell+2)+
  (2^ell*(CappedSubsetList.count ell r*(3^P*(datumControlBudget P ell C+200*(P+1))+32)+40)+8)+12

theorem prepare_bits {P ell C : ℕ} (r : ℕ) (X : Source P ell C) (A : ℕ) (ha : OppositeWindowLayer.Bound X A) :
    (prepare r X).bitSteps≤bitBudget P ell r C A := by
  apply BinaryGroupedPreparation.tabulate_bits; intro p
  apply BinaryGroupedPreparation.tabulate_bits; intro j
  exact PrefixCellTree.build_bits _ (datum_bits _ _ _ · A ha)

theorem prepare_control {P ell C : ℕ} (r : ℕ) (X : Source P ell C) :
    (prepare r X).control≤controlBudget P ell r C := by
  have hk := storeKeys_work ell r
  have hp := storePairs_work ell
  have hg := BinaryGroupedPreparation.tabulate_control (storePairs ell).value
    (fun p => BinaryGroupedPreparation.tabulate (storeKeys ell r).value
      (fun j => PrefixCellTree.build P (datum X ((storePairs ell).value.get p) ((storeKeys ell r).value.get j))))
    (fun p => BinaryGroupedPreparation.tabulate_control _ _ (fun j => PrefixCellTree.build_control _ (datum_control _ _ _)))
  simp only [Nat.add_assoc,show 8+32=40 by decide] at hg
  simp only [prepare,controlBudget]
  omega

def cells {P ell r C : ℕ} (xs : Prepared P ell r C) : ℕ :=
  (xs.groups.toList.map (fun group => (group.toList.map (fun tree => PrefixCellTree.cells tree)).sum)).sum

theorem cells_eq {P ell r C : ℕ} (xs : Prepared P ell r C) :
    cells xs=2^ell*CappedSubsetList.count ell r*3^P*C := by
  simp only [cells,PrefixCellTree.cells_eq,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

#print axioms suffix_get
#print axioms datum_value
#print axioms datum_bound
#print axioms datum_bits
#print axioms datum_control
#print axioms prepare_value
#print axioms prepare_bound
#print axioms prepare_bits
#print axioms prepare_control
#print axioms cells_eq
end ThinMatrix.RetainedCappedGroups
