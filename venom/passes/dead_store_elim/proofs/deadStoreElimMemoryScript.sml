(* Probe interface: pending write regions account separately for byte and
   expansion differences. This is not yet an execution simulation. *)
Theory deadStoreElimMemory
Ancestors
  deadStoreElimEquiv deadStoreElimFrame deadStoreElimDefs venomMemProps
  venomState venomExecSemantics list rich_list arithmetic
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
