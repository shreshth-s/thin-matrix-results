import BinaryRecursiveAddress

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Stored recursive tables whose actual reads and enumeration use binary
copy/word addresses. Vector access itself is a bounded indexed primitive;
word/product flattening, splitting, stride formation and decoding are charged
binary computations and their computed results are consumed by the lookup. -/
namespace ThinMatrix.BinaryRecursiveTable
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open PolynomialDegeneration
open RecursiveTable (Table Layout prod fin power power_size)
open RetainedEqualCopy (copies)
variable {a b t : ℕ} {V : Type}

abbrev layout (t a b k : ℕ) := copies t (prod (fin a) (fin b)) k

@[simp] theorem layout_size (t a b k : ℕ) : (layout t a b k).size=t*(a*b)^k := by
  simp only [layout,copies,prod,fin,power_size]

def rank (k : ℕ) (x : Fin t×PowerIndex (Fin a×Fin b) k) : Result ℕ :=
  let word := BinaryRecursiveAddress.rank k x.2
  let stride := BinaryPowerAddress.stride (a*b) k
  let address := BinaryMatrixAddress.join stride.value x.1.val word.value
  ⟨address.value,word.bitSteps+stride.bitSteps+address.bitSteps+8⟩

theorem rank_value (k : ℕ) (x : Fin t×PowerIndex (Fin a×Fin b) k) :
    (rank k x).value=((layout t a b k).index x).val := by
  simp only [rank,BinaryMatrixAddress.join_value,BinaryRecursiveAddress.rank_value,BinaryPowerAddress.stride_value]
  change _=((power (prod (fin a) (fin b)) k).index x.2).val+
    (power (prod (fin a) (fin b)) k).size*x.1.val
  simp only [power_size,prod,fin]

def unrank (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin (t*(a*b)^k)) :
    Result (Fin t×PowerIndex (Fin a×Fin b) k) :=
  let stride := BinaryPowerAddress.stride (a*b) k
  let split := BinaryMatrixAddress.split stride.value i.val
  have hs : split.value=(i.val/((a*b)^k),i.val%((a*b)^k)) := by
    rw [BinaryMatrixAddress.split_value _ _ (by rw [BinaryPowerAddress.stride_value];positivity),BinaryPowerAddress.stride_value]
  let copy : Fin t := ⟨split.value.1,by rw [hs];exact (Nat.div_lt_iff_lt_mul (pow_pos (Nat.mul_pos ha hb) k)).mpr i.isLt⟩
  let word : Fin ((a*b)^k) := ⟨split.value.2,by rw [hs];exact Nat.mod_lt _ (pow_pos (Nat.mul_pos ha hb) k)⟩
  let out := BinaryRecursiveAddress.unrank ha hb k word
  ⟨(copy,out.value),stride.bitSteps+split.bitSteps+out.bitSteps+8⟩

theorem rank_unrank (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin (t*(a*b)^k)) :
    (rank k (unrank ha hb k i).value).value=i.val := by
  simp only [rank,unrank,BinaryMatrixAddress.join_value,BinaryPowerAddress.stride_value,BinaryRecursiveAddress.rank_unrank]
  rw [BinaryMatrixAddress.split_value _ _ (pow_pos (Nat.mul_pos ha hb) k)]
  exact Nat.mod_add_div _ _

theorem unrank_value (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin (t*(a*b)^k)) :
    (unrank ha hb k i).value=(layout t a b k).index.symm (Fin.cast (layout_size t a b k).symm i) := by
  apply (layout t a b k).index.injective
  apply Fin.ext
  rw [←rank_value,rank_unrank]
  simp

def read (k : ℕ) (x : Table (layout t a b k) V) (i : Fin t×PowerIndex (Fin a×Fin b) k) : Result V :=
  let address := rank k i
  have ha : address.value<(layout t a b k).size := by rw [rank_value];exact ((layout t a b k).index i).isLt
  ⟨x.get ⟨address.value,ha⟩,address.bitSteps+4⟩

theorem read_value (k : ℕ) (x : Table (layout t a b k) V) (i : Fin t×PowerIndex (Fin a×Fin b) k) :
    (read k x i).value=RecursiveTable.read x i := by
  dsimp only [read,RecursiveTable.read]
  apply congrArg x.get
  exact Fin.ext (rank_value k i)

def tabulate (ha : 0<a) (hb : 0<b) (k : ℕ)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run V) : Run (Table (layout t a b k) V) :=
  let rows := Vector.ofFn (fun j : Fin (layout t a b k).size =>
    let address := unrank ha hb k (Fin.cast (layout_size t a b k) j)
    let out := f address.value
    (⟨out.value,address.bitSteps+out.bitSteps,out.control+8⟩ : Run V))
  ⟨rows.map Run.value,(rows.toList.map Run.bitSteps).sum,
    (rows.toList.map Run.control).sum+32*(layout t a b k).size+8⟩

theorem tabulate_value (ha : 0<a) (hb : 0<b) (k : ℕ)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run V) :
    (tabulate ha hb k f).value=(BinaryRecursiveDot.tabulate (layout t a b k) f).value := by
  apply Vector.ext
  intro i hi
  simp only [tabulate,Vector.getElem_map,Vector.getElem_ofFn,unrank_value,Fin.cast_cast,Fin.cast_refl,
    BinaryRecursiveDot.tabulate,RecursiveTable.store,id_eq]

theorem tabulate_read (ha : 0<a) (hb : 0<b) (k : ℕ)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run V) (i : Fin t×PowerIndex (Fin a×Fin b) k) :
    RecursiveTable.read (tabulate ha hb k f).value i=(f i).value := by
  rw [tabulate_value,BinaryRecursiveDot.tabulate_read]

theorem tabulate_control (ha : 0<a) (hb : 0<b) (k : ℕ)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run V) :
    (tabulate ha hb k f).control=(BinaryRecursiveDot.tabulate (layout t a b k) f).control+
      8*(t*(a*b)^k) := by
  simp only [tabulate,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    BinaryRecursiveDot.tabulate,RecursiveTable.store,Finset.sum_add_distrib,unrank_value,Fin.cast_cast,Fin.cast_refl,id_eq,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,layout_size]
  ring

theorem rank_bits (k W : ℕ) (ha : 0<a) (hb : 0<b)
    (hbase : (a*b).size≤W) (hpow : ((a*b)^k).size≤W) (ht : t.size≤W)
    (i : Fin t×PowerIndex (Fin a×Fin b) k) :
    (rank k i).bitSteps≤32768*(k+1)^2*(W+1)^2 := by
  have hw := BinaryRecursiveAddress.rank_bits k W ha hb hbase hpow i.2
  have hs := BinaryPowerAddress.stride_bits (a*b) k W (Nat.mul_pos ha hb) hbase hpow
  have hword : (BinaryRecursiveAddress.rank k i.2).value<(a*b)^k := by
    rw [BinaryRecursiveAddress.rank_value]
    simpa only [power_size,prod,fin] using ((power (prod (fin a) (fin b)) k).index i.2).isLt
  have hj := BinaryMatrixAddress.join_bits (BinaryPowerAddress.stride (a*b) k).value i.1.val
    (BinaryRecursiveAddress.rank k i.2).value W
    (by simpa only [BinaryPowerAddress.stride_value] using hpow)
    ((Nat.size_le_size i.1.isLt.le).trans ht) ((Nat.size_le_size hword.le).trans hpow)
  simp only [rank]
  nlinarith

theorem unrank_bits (k W : ℕ) (ha : 0<a) (hb : 0<b)
    (hbase : (a*b).size≤W) (hpow : ((a*b)^k).size≤W) (ht : (t*(a*b)^k).size≤W)
    (i : Fin (t*(a*b)^k)) :
    (unrank ha hb k i).bitSteps≤32768*(k+1)^2*(W+1)^2 := by
  have hs := BinaryPowerAddress.stride_bits (a*b) k W (Nat.mul_pos ha hb) hbase hpow
  have hsplit := BinaryMatrixAddress.split_bits (BinaryPowerAddress.stride (a*b) k).value i.val W
    (by simpa only [BinaryPowerAddress.stride_value] using hpow) ((Nat.size_le_size i.isLt.le).trans ht)
  have hout := BinaryRecursiveAddress.unrank_bits (a:=a) (b:=b) k W ha hb hbase hpow
  dsimp only [unrank]
  have hh := hout ⟨(BinaryMatrixAddress.split (BinaryPowerAddress.stride (a*b) k).value i.val).value.2,by
    rw [BinaryMatrixAddress.split_value _ _ (by rw [BinaryPowerAddress.stride_value];positivity),BinaryPowerAddress.stride_value]
    exact Nat.mod_lt _ (pow_pos (Nat.mul_pos ha hb) k)⟩
  nlinarith

theorem read_bits (k W : ℕ) (ha : 0<a) (hb : 0<b)
    (hbase : (a*b).size≤W) (hpow : ((a*b)^k).size≤W) (ht : t.size≤W)
    (x : Table (layout t a b k) V) (i : Fin t×PowerIndex (Fin a×Fin b) k) :
    (read k x i).bitSteps≤32772*(k+1)^2*(W+1)^2 := by
  have hh := rank_bits k W ha hb hbase hpow ht i
  have hunit : 0<(k+1)^2*(W+1)^2 := by positivity
  simp only [read]
  nlinarith

theorem tabulate_bits (ha : 0<a) (hb : 0<b) (k W : ℕ)
    (hbase : (a*b).size≤W) (hpow : ((a*b)^k).size≤W) (ht : (t*(a*b)^k).size≤W)
    (f : Fin t×PowerIndex (Fin a×Fin b) k → Run V) :
    (tabulate ha hb k f).bitSteps≤
      (BinaryRecursiveDot.tabulate (layout t a b k) f).bitSteps+
        t*(a*b)^k*(32768*(k+1)^2*(W+1)^2) := by
  simp only [tabulate,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    BinaryRecursiveDot.tabulate,RecursiveTable.store,Finset.sum_add_distrib,unrank_value,Fin.cast_cast,Fin.cast_refl,id_eq]
  have hh := Finset.sum_le_sum (fun (i : Fin (layout t a b k).size) (_ : i∈Finset.univ) =>
    unrank_bits k W ha hb hbase hpow ht (Fin.cast (layout_size t a b k) i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,layout_size] at hh
  omega

#print axioms layout_size
#print axioms rank_value
#print axioms rank_unrank
#print axioms unrank_value
#print axioms read_value
#print axioms tabulate_value
#print axioms tabulate_read
#print axioms tabulate_control
#print axioms rank_bits
#print axioms unrank_bits
#print axioms read_bits
#print axioms tabulate_bits
end ThinMatrix.BinaryRecursiveTable
