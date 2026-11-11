(* Probe interface: pending write regions account separately for byte and
   expansion differences. This is not yet an execution simulation. *)
Theory deadStoreElimMemory
Ancestors
  deadStoreElimEquiv deadStoreElimFrame deadStoreElimDefs venomMemProps
  venomState venomExecSemantics venomMemDefs list rich_list arithmetic
  regularCallEmitSim codegenRel
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Definition dse_memory_byte_def:
  dse_memory_byte s i = EL i (s.vs_memory ++ REPLICATE (SUC i) (0w:word8))
End

Definition dse_pending_memory_def:
  dse_pending_memory (pending : (num # num) list) s t <=>
    dse_equiv AddrSp_Memory s t /\
    (!i. (!b n. MEM (b,n) pending ==> i < b \/ b + n <= i) ==>
         dse_memory_byte s i = dse_memory_byte t i) /\
    LENGTH t.vs_memory <= LENGTH s.vs_memory /\
    LENGTH s.vs_memory <=
      MAX (LENGTH t.vs_memory) (MAX_LIST (MAP (\(b,n). b+n) pending))
End

Theorem dse_pending_memory_refl:
  dse_pending_memory pending s s
Proof
  simp[dse_pending_memory_def, dse_equiv_refl]
QED

Theorem dse_pending_memory_equiv:
  dse_pending_memory pending s t ==> dse_equiv AddrSp_Memory s t
Proof
  simp[dse_pending_memory_def]
QED

Theorem dse_pending_memory_byte:
  dse_pending_memory pending s t /\
  (!b n. MEM (b,n) pending ==> i < b \/ b+n <= i) ==>
  dse_memory_byte s i = dse_memory_byte t i
Proof
  simp[dse_pending_memory_def] >> metis_tac[]
QED

(* A positive-size removed write may change the memory-size observation. *)
Theorem dse_mstore_expansion_probe:
  s.vs_memory = [] ==>
  LENGTH (mstore 0 1w s).vs_memory = 32 /\ LENGTH s.vs_memory = 0
Proof
  simp[LENGTH_mstore_eq, wordsTheory.dimword_def, dimindex_256]
QED

Theorem dse_mstore_pending_probe:
  s.vs_memory = [] ==>
  dse_pending_memory [(0,32)] (mstore 0 1w s) s
Proof
  strip_tac >>
  simp[dse_pending_memory_def, mstore_eq_write_mem,
       write_memory_with_expansion_def, dse_equiv_def, lookup_var_def,
       byteTheory.LENGTH_word_to_bytes, dse_memory_byte_def,
       EL_APPEND_EQN] >>
  rpt strip_tac >>
  Cases_on `i - 32` >> Cases_on `i` >>
  gvs[rich_listTheory.EL_REPLICATE]
QED

(* Identical complete overwrites restore both contents and expansion. *)
Theorem dse_mstore_clobber_probe:
  s.vs_memory = [] ==>
  mstore 0 2w (mstore 0 1w s) = mstore 0 2w s
Proof
  `DROP 32 (word_to_bytes (1w:bytes32) T) = []` by
    (irule DROP_LENGTH_TOO_LONG >> simp[byteTheory.LENGTH_word_to_bytes]) >>
  simp[mstore_eq_write_mem, write_memory_with_expansion_def,
       byteTheory.LENGTH_word_to_bytes]
QED

Theorem dse_mstore_disjoint_load_probe:
  s.vs_memory = [] ==>
  mload 32 (mstore 0 1w s) = mload 32 s
Proof
  `DROP 32 (word_to_bytes (1w:bytes32) T) = []` by
    (irule DROP_LENGTH_TOO_LONG >> simp[byteTheory.LENGTH_word_to_bytes]) >>
  simp[mload_def, mstore_eq_write_mem, write_memory_with_expansion_def,
       byteTheory.LENGTH_word_to_bytes]
QED

(* The rounded size queried by MEMTOP distinguishes these states,
   although a disjoint MLOAD cannot distinguish their padded bytes. *)
Theorem dse_mstore_memtop_probe:
  s.vs_memory = [] ==>
  (n2w (((LENGTH (mstore 0 1w s).vs_memory + 31) DIV 32) * 32):bytes32) <>
  n2w (((LENGTH s.vs_memory + 31) DIV 32) * 32)
Proof
  simp[LENGTH_mstore_eq, wordsTheory.dimword_def, dimindex_256]
QED

(* Disjoint reads see equal padded bytes, independently of expansion. *)
Theorem dse_pending_memory_disjoint_byte:
  dse_pending_memory P s t /\
  (!b n. MEM (b,n) P ==> regions_disjoint (a,k) (b,n)) /\
  i < k ==>
  dse_memory_byte s (a+i) = dse_memory_byte t (a+i)
Proof
  rpt strip_tac >> irule dse_pending_memory_byte >>
  qexists_tac `P` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

(* Covered endpoints are bounded even for zero-byte footprints. *)
Theorem dse_pending_endpoint_filter:
  MAX_LIST (MAP (\(b,n). b+n) P) <=
  MAX (a+k) (MAX_LIST (MAP (\(b,n). b+n)
    (FILTER (\(b,n). ~(a <= b /\ b+n <= a+k)) P)))
Proof
  Induct_on `P` >- simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `a <= h0 /\ h0+h1 <= a+k` >>
  gvs[MAX_DEF] >> decide_tac
QED

Theorem dse_pending_memory_empty:
  dse_pending_memory [] s t ==> s.vs_memory = t.vs_memory
Proof
  simp[dse_pending_memory_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH s.vs_memory = LENGTH t.vs_memory` by decide_tac >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!i. dse_memory_byte s i = _`
    (qspec_then `x` mp_tac) >>
  simp[dse_memory_byte_def, EL_APPEND_EQN]
QED

Theorem dse_memory_byte_read_byte:
  dse_memory_byte s i = read_byte i s.vs_memory
Proof
  simp[dse_memory_byte_def, read_byte_def, EL_APPEND_EQN] >>
  Cases_on `i < LENGTH s.vs_memory` >> simp[] >>
  Cases_on `i - LENGTH s.vs_memory` >> simp[EL_REPLICATE]
QED

Theorem dse_pending_memory_insert:
  dse_pending_memory P s t ==>
  dse_pending_memory ((a,LENGTH bytes)::P)
    (write_memory_with_expansion a bytes s) t
Proof
  strip_tac >>
  `dse_equiv AddrSp_Memory (write_memory_with_expansion a bytes s) t` by
    (gvs[dse_pending_memory_def, dse_equiv_def] >>
     simp[write_memory_with_expansion_def, lookup_var_def]) >>
  rewrite_tac[dse_pending_memory_def] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >>
      `i < a \/ a + LENGTH bytes <= i` by metis_tac[MEM] >>
      `~(a <= i /\ i < a + LENGTH bytes)` by decide_tac >>
      simp[dse_memory_byte_read_byte, read_byte_write_memory_with_expansion] >>
      rewrite_tac[GSYM dse_memory_byte_read_byte] >>
      irule dse_pending_memory_byte >> qexists_tac `P` >>
      simp[] >> metis_tac[MEM]) >>
  gvs[dse_pending_memory_def] >>
  simp[LENGTH_write_memory_with_expansion, MAX_DEF] >> decide_tac
QED

Theorem dse_pending_memory_overwrite:
  dse_pending_memory P s t ==>
  dse_pending_memory
    (FILTER (\(b,n). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    (write_memory_with_expansion a bytes s)
    (write_memory_with_expansion a bytes t)
Proof
  strip_tac >> rewrite_tac[dse_pending_memory_def] >>
  conj_tac
  >- (gvs[dse_pending_memory_def, dse_equiv_def] >>
      simp[write_memory_with_expansion_def, lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      simp[dse_memory_byte_read_byte, read_byte_write_memory_with_expansion] >>
      IF_CASES_TAC >- simp[] >>
      rewrite_tac[GSYM dse_memory_byte_read_byte] >>
      irule dse_pending_memory_byte >> qexists_tac `P` >> simp[] >>
      rpt strip_tac >>
      Cases_on `a <= b /\ b+n <= a+LENGTH bytes`
      >- decide_tac >>
      first_x_assum irule >> simp[MEM_FILTER]) >>
  qspec_then `LENGTH bytes` assume_tac
    (Q.GEN `k` dse_pending_endpoint_filter) >>
  gvs[dse_pending_memory_def] >>
  simp[LENGTH_write_memory_with_expansion, MAX_DEF] >> decide_tac
QED

Theorem dse_pending_memory_common_write:
  dse_pending_memory P s t ==>
  dse_pending_memory P (write_memory_with_expansion a bytes s)
    (write_memory_with_expansion a bytes t)
Proof
  strip_tac >> rewrite_tac[dse_pending_memory_def] >>
  conj_tac
  >- (gvs[dse_pending_memory_def, dse_equiv_def] >>
      simp[write_memory_with_expansion_def, lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      simp[dse_memory_byte_read_byte, read_byte_write_memory_with_expansion] >>
      IF_CASES_TAC >- simp[] >>
      rewrite_tac[GSYM dse_memory_byte_read_byte] >>
      irule dse_pending_memory_byte >> qexists_tac `P` >> simp[]) >>
  gvs[dse_pending_memory_def] >>
  simp[LENGTH_write_memory_with_expansion, MAX_DEF] >> decide_tac
QED

(* Enlarging the exceptional union also needs its endpoint bound: an empty
   interval contributes no bytes, but may still account for expansion. *)
Theorem dse_pending_memory_subsume:
  dse_pending_memory P s t /\
  (!i. (!b n. MEM (b,n) Q ==> i < b \/ b+n <= i) ==>
       (!b n. MEM (b,n) P ==> i < b \/ b+n <= i)) /\
  MAX_LIST (MAP (\(b,n). b+n) P) <= MAX_LIST (MAP (\(b,n). b+n) Q) ==>
  dse_pending_memory Q s t
Proof
  rewrite_tac[dse_pending_memory_def] >> rpt strip_tac
  >- simp[]
  >- metis_tac[]
  >- simp[] >>
  gvs[MAX_DEF] >> decide_tac
QED

Theorem dse_pending_memory_cover:
  dse_pending_memory P s t ==>
  dse_pending_memory
    ((a,k)::FILTER (\(b,n). ~(a <= b /\ b+n <= a+k)) P) s t
Proof
  strip_tac >> irule dse_pending_memory_subsume >>
  qexists_tac `P` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `a <= b /\ b+n <= a+k`
      >- (first_x_assum (qspecl_then [`a`, `k`] mp_tac) >>
          simp[] >> decide_tac) >>
      first_x_assum irule >> simp[MEM_FILTER]) >>
  mp_tac dse_pending_endpoint_filter >> simp[]
QED

Theorem dse_pending_memory_insert_cover:
  dse_pending_memory P s t ==>
  dse_pending_memory
    ((a,LENGTH bytes)::FILTER (\(b,n). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    (write_memory_with_expansion a bytes s) t
Proof
  strip_tac >> drule dse_pending_memory_insert >>
  disch_then (qspecl_then [`bytes`, `a`] assume_tac) >>
  drule dse_pending_memory_cover >>
  disch_then (qspecl_then [`LENGTH bytes`, `a`] mp_tac) >> simp[]
QED

Theorem dse_pending_memory_read_memory:
  dse_pending_memory R s t /\
  (!a n. MEM (a,n) R ==> regions_disjoint (a,n) (r,m)) ==>
  read_memory r m s = read_memory r m t
Proof
  strip_tac >> irule LIST_EQ >>
  simp[read_memory_def, LENGTH_TAKE_EQ] >>
  qx_gen_tac `i` >> strip_tac >>
  `dse_memory_byte s (r+i) = dse_memory_byte t (r+i)` by
    (irule dse_pending_memory_disjoint_byte >>
     qexists_tac `R` >> simp[] >>
     metis_tac[regions_disjoint_def]) >>
  Cases_on `r+i < LENGTH s.vs_memory` >>
  Cases_on `r+i < LENGTH t.vs_memory` >>
  gvs[read_memory_def, EL_TAKE, EL_APPEND_EQN, EL_DROP,
      dse_memory_byte_def, EL_REPLICATE,
      arithmeticTheory.ADD_COMM]
QED
