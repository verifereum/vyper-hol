(*
 * Memmerging — Core Copy Equivalence
 *
 * The mathematical core of the simulation argument:
 * a sequence of 32-byte memory copies is equivalent to a single
 * bulk copy, under appropriate conditions.
 *
 * TOP-LEVEL:
 *   word_bytes_roundtrip      — word_to_bytes ∘ word_of_bytes = id (len 32)
 *   mload_mstore_is_mcopy     — mstore dst (mload src s) ≡ mcopy dst src 32
 *   write_mem_append          — two adjacent writes = one combined write
 *   mcopy_merge               — mcopy d₂ s₂ 32 ∘ mcopy d₁ s₁ 32 = mcopy d s 64
 *                                (when contiguous, non-overlapping)
 *)

Theory mmCopyEquiv
Ancestors
  mmCopy mmInterval venomState venomExecSemantics
  byte words fcp list rich_list arithmetic

(* ===== dimindex(:256) helpers ===== *)

Theorem dimindex_256[simp]:
  dimindex(:256) = 256
Proof
  simp[index_bit0, dimindex_128, finite_bit0, finite_128, index_one, finite_one]
QED

Theorem dimword_256_val:
  dimword(:256) =
    115792089237316195423570985008687907853269984665640564039457584007913129639936
Proof
  simp[dimword_def]
QED

(* ===== Word ↔ Bytes roundtrip ===== *)

(* Key property: converting 32 bytes to a word and back is identity.
   This underlies the equivalence between mload+mstore and mcopy.
   Uses get_byte_word_of_bytes_be + first_byte_at_0w to show
   each byte of the output matches the input. *)
Theorem word_bytes_roundtrip:
  !bytes.
    LENGTH bytes = 32 ==>
    word_to_bytes (word_of_bytes T (0w:bytes32) bytes) T = bytes
Proof
  rw[LIST_EQ_REWRITE, LENGTH_word_to_bytes]
  >> fs[]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux]
  >> simp[get_byte_word_of_bytes_be]
  >> simp[first_byte_at_0w, dimword_256_val]
QED

(* ===== mload+mstore = mcopy 32 ===== *)

(* A single mload followed by mstore is equivalent to mcopy of 32 bytes.
   Both read 32 bytes from src and write them to dst.

   mload src s = word_of_bytes T 0w (TAKE 32 (DROP src mem ++ REPLICATE 32 0w))
   mstore dst val s = write_memory_with_expansion dst (word_to_bytes val T) s
   mcopy dst src 32 s = write_memory_with_expansion dst
                          (TAKE 32 (DROP src mem ++ REPLICATE 32 0w)) s

   By word_bytes_roundtrip, mstore(dst, mload(src, s), s).vs_memory
   = mcopy(dst, src, 32, s).vs_memory *)
(* The full state equivalence: mstore(dst, mload(src,s), s)
   agrees with mcopy(dst, src, 32, s) on everything.
   Both expand memory by the same amount and write the same bytes,
   thanks to word_bytes_roundtrip. *)
Theorem mload_mstore_eq_mcopy_state:
  !dst src s.
    mstore dst (mload src s) s = mcopy dst src 32 s
Proof
  rw[mstore_def, mload_def, mcopy_def, write_memory_with_expansion_def]
  >> simp[LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND]
  >> simp[word_bytes_roundtrip]
QED

Theorem mload_mstore_is_mcopy:
  !dst src s.
    (mstore dst (mload src s) s).vs_memory =
    (mcopy dst src 32 s).vs_memory
Proof
  simp[mload_mstore_eq_mcopy_state]
QED

(* ===== Adjacent writes combine ===== *)

(* Helper: expand memory to at least n bytes *)
Definition expand_mem_def:
  expand_mem mem n =
    if n > LENGTH mem then mem ++ REPLICATE (n - LENGTH mem) (0w:word8) else mem
End

(* Helper: replace bytes at offset *)
Definition replace_bytes_def:
  replace_bytes off (bytes:word8 list) mem =
    TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem
End

Theorem expand_mem_len[simp]:
  !mem n. LENGTH (expand_mem mem n) = MAX n (LENGTH mem)
Proof
  rw[expand_mem_def, LENGTH_APPEND, LENGTH_REPLICATE, MAX_DEF]
QED

Theorem expand_mem_ge:
  !mem n. n <= LENGTH (expand_mem mem n)
Proof
  simp[MAX_DEF]
QED

Theorem expand_mem_monotone:
  !mem n m. n <= m ==> expand_mem (expand_mem mem n) m = expand_mem mem m
Proof
  rw[expand_mem_def, LENGTH_APPEND, LENGTH_REPLICATE]
  >> simp[MAX_DEF, REPLICATE_APPEND]
  >> fs[MAX_DEF]
  >> TRY (Cases_on `n < LENGTH mem` >> fs[]
          >> `n = LENGTH mem` by decide_tac >> simp[] >> NO_TAC)
  >> `n = m` by decide_tac >> simp[]
QED

Theorem write_as_replace:
  !off bytes s.
    write_memory_with_expansion off bytes s =
    s with vs_memory := replace_bytes off bytes (expand_mem s.vs_memory (off + LENGTH bytes))
Proof
  rw[write_memory_with_expansion_def, replace_bytes_def, expand_mem_def]
QED

Theorem replace_bytes_len:
  !off (bytes:word8 list) mem.
    off + LENGTH bytes <= LENGTH mem ==>
    LENGTH (replace_bytes off bytes mem) = LENGTH mem
Proof
  rw[replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP]
QED

Theorem replace_bytes_append:
  !off1 (bytes1:word8 list) bytes2 mem.
    off1 + LENGTH bytes1 + LENGTH bytes2 <= LENGTH mem ==>
    replace_bytes (off1 + LENGTH bytes1) bytes2
      (replace_bytes off1 bytes1 mem) =
    replace_bytes off1 (bytes1 ++ bytes2) mem
Proof
  rw[replace_bytes_def, LENGTH_APPEND]
  >> simp[TAKE_APPEND1, TAKE_APPEND2, DROP_APPEND1, DROP_APPEND2,
          LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND]
  >> simp[TAKE_TAKE, DROP_DROP, TAKE_LENGTH_TOO_LONG]
QED

Theorem expand_replace:
  !off (bytes:word8 list) mem n.
    off + LENGTH bytes <= LENGTH mem ==>
    expand_mem (replace_bytes off bytes mem) n =
    replace_bytes off bytes (expand_mem mem n)
Proof
  rw[expand_mem_def, replace_bytes_def, LENGTH_APPEND,
     LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> simp[TAKE_APPEND1, DROP_APPEND1]
QED

(* Two adjacent non-overlapping writes to memory combine into one.
   write_mem(off2, bytes2, write_mem(off1, bytes1, s))
   = write_mem(off1, bytes1 ++ bytes2, s)
   when off2 = off1 + LENGTH bytes1. *)
Theorem write_memory_append:
  !off1 bytes1 bytes2 s.
    write_memory_with_expansion (off1 + LENGTH bytes1) bytes2
      (write_memory_with_expansion off1 bytes1 s)
    = write_memory_with_expansion off1 (bytes1 ++ bytes2) s
Proof
  rw[write_as_replace, LENGTH_APPEND]
  >> `off1 + LENGTH bytes1 <= LENGTH (expand_mem s.vs_memory (off1 + LENGTH bytes1))`
       by simp[expand_mem_ge]
  >> simp[expand_replace]
  >> simp[expand_mem_monotone]
  >> simp[GSYM replace_bytes_append, expand_mem_ge, MAX_DEF]
QED

(* ===== Contiguous mcopy merge ===== *)

(* Reading from non-overlapping write+expand gives same as reading original *)
Theorem read_nonoverlap_expand:
  !off (bytes:word8 list) mem rd_off rd_sz.
    (rd_off + rd_sz <= off \/ off + LENGTH bytes <= rd_off) ==>
    TAKE rd_sz
      (DROP rd_off (replace_bytes off bytes (expand_mem mem (off + LENGTH bytes)))
       ++ REPLICATE rd_sz (0w:word8)) =
    TAKE rd_sz (DROP rd_off mem ++ REPLICATE rd_sz 0w)
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, expand_mem_def,
     LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
        LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE, MAX_DEF]
  >> fs[]
QED

(* Two adjacent TAKE/DROP segments with padding combine *)
Theorem take_split_padded:
  !mem:word8 list.
    TAKE 32 (mem ++ REPLICATE 32 0w) ++
    TAKE 32 (DROP 32 mem ++ REPLICATE 32 0w) =
    TAKE 64 (mem ++ REPLICATE 64 0w)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
        LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> fs[]
QED

(* Two contiguous non-overlapping mcopies merge into one.
   Precondition: dst and src ranges don't overlap with each other. *)
Theorem mcopy_merge:
  !dst src s.
    ~interval_overlaps
      (mk_interval dst 64)
      (mk_interval src 64) ==>
    mcopy (dst + 32) (src + 32) 32 (mcopy dst src 32 s) =
    mcopy dst src 64 s
Proof
  rw[mcopy_def] >> simp[write_as_replace]
  >> simp[venom_state_component_equality]
  >> qabbrev_tac `mem = s.vs_memory`
  >> qabbrev_tac `data1 = TAKE 32 (DROP src mem ++ REPLICATE 32 (0w:word8))`
  >> `LENGTH data1 = 32` by simp[Abbr `data1`]
  (* Simplify expand(replace(expand(...))) to replace(expand(...)) *)
  >> `dst + 32 <= LENGTH (expand_mem mem (dst + 32))` by simp[expand_mem_ge]
  >> `expand_mem (replace_bytes dst data1 (expand_mem mem (dst + 32))) (dst + 64)
      = replace_bytes dst data1 (expand_mem mem (dst + 64))`
       by simp[expand_replace, expand_mem_monotone]
  >> pop_assum SUBST_ALL_TAC
  (* Show read at [src+32, src+64) is unaffected by write at [dst, dst+32) *)
  >> `TAKE 32 (DROP (src + 32) (replace_bytes dst data1
        (expand_mem mem (dst + 32))) ++ REPLICATE 32 0w)
      = TAKE 32 (DROP (src + 32) mem ++ REPLICATE 32 0w)`
       by (simp[Abbr`data1`]
           >> rw[LIST_EQ_REWRITE, replace_bytes_def, expand_mem_def,
                 LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
           >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
                 LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE, MAX_DEF]
           >> fs[interval_overlaps_def, mk_interval_def, interval_end_def])
  >> pop_assum SUBST_ALL_TAC
  (* Combine adjacent replace_bytes *)
  >> qabbrev_tac `data2 = TAKE 32 (DROP (src + 32) mem ++ REPLICATE 32 (0w:word8))`
  >> `LENGTH data2 = 32` by simp[Abbr `data2`]
  >> `replace_bytes (dst + 32) data2
        (replace_bytes dst data1 (expand_mem mem (dst + 64)))
      = replace_bytes dst (data1 ++ data2) (expand_mem mem (dst + 64))`
       by (`dst + LENGTH data1 = dst + 32` by simp[]
           >> pop_assum (SUBST1_TAC o SYM)
           >> irule replace_bytes_append >> simp[expand_mem_ge])
  >> pop_assum SUBST_ALL_TAC
  (* Show data1 ++ data2 = TAKE 64 (...) using take_split_padded *)
  >> `data1 ++ data2 = TAKE 64 (DROP src mem ++ REPLICATE 64 0w)`
       suffices_by simp[]
  >> simp[Abbr`data1`, Abbr`data2`]
  >> simp_tac std_ss []
  >> rw[LIST_EQ_REWRITE, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
        LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> fs[]
QED

(* General merge step: extend an mcopy by 32 bytes *)
Theorem mcopy_merge_step:
  !dst src sz s.
    ~interval_overlaps
      (mk_interval dst (sz + 32))
      (mk_interval src (sz + 32)) ==>
    mcopy (dst + sz) (src + sz) 32 (mcopy dst src sz s) =
    mcopy dst src (sz + 32) s
Proof
  rw[mcopy_def] >> simp[write_as_replace]
  >> simp[venom_state_component_equality]
  >> qabbrev_tac `mem = s.vs_memory`
  >> qabbrev_tac `data1 = TAKE sz (DROP src mem ++ REPLICATE sz (0w:word8))`
  >> `LENGTH data1 = sz` by simp[Abbr `data1`]
  >> `dst + sz <= LENGTH (expand_mem mem (dst + sz))` by simp[expand_mem_ge]
  >> `dst + (sz + 32) = dst + sz + 32` by simp[]
  >> pop_assum SUBST_ALL_TAC
  >> `expand_mem (replace_bytes dst data1 (expand_mem mem (dst + sz)))
        (dst + sz + 32)
      = replace_bytes dst data1 (expand_mem mem (dst + sz + 32))`
       by simp[expand_replace, expand_mem_monotone]
  >> pop_assum SUBST_ALL_TAC
  (* Non-overlap reading *)
  >> `TAKE 32 (DROP (src + sz) (replace_bytes dst data1
        (expand_mem mem (dst + sz))) ++ REPLICATE 32 0w)
      = TAKE 32 (DROP (src + sz) mem ++ REPLICATE 32 0w)`
       by (rw[LIST_EQ_REWRITE, replace_bytes_def, expand_mem_def,
              LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
           >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
                 LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE, MAX_DEF]
           >> fs[interval_overlaps_def, mk_interval_def, interval_end_def])
  >> pop_assum SUBST_ALL_TAC
  (* Combine replace_bytes *)
  >> qabbrev_tac `data2 = TAKE 32 (DROP (src + sz) mem ++ REPLICATE 32 (0w:word8))`
  >> `LENGTH data2 = 32` by simp[Abbr `data2`]
  >> `replace_bytes (dst + sz) data2
        (replace_bytes dst data1 (expand_mem mem (dst + sz + 32)))
      = replace_bytes dst (data1 ++ data2) (expand_mem mem (dst + sz + 32))`
       by (`dst + LENGTH data1 = dst + sz` by simp[]
           >> pop_assum (SUBST1_TAC o SYM)
           >> irule replace_bytes_append >> simp[expand_mem_ge])
  >> pop_assum SUBST_ALL_TAC
  (* TAKE concatenation *)
  >> `data1 ++ data2 = TAKE (sz + 32) (DROP src mem ++ REPLICATE (sz + 32) 0w)`
       suffices_by simp[]
  >> simp[Abbr`data1`, Abbr`data2`]
  >> rw[LIST_EQ_REWRITE, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
        LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE]
  >> fs[]
QED

(* General N-copy merge by induction (N >= 1).
   N contiguous 32-byte copies from [src, src+32*N) to [dst, dst+32*N)
   equal mcopy dst src (32*N). *)
(* Non-overlap of larger interval implies non-overlap of smaller *)
Theorem interval_overlaps_shrink:
  !dst src n.
    ~interval_overlaps (mk_interval dst (32 * SUC n))
                       (mk_interval src (32 * SUC n)) ==>
    ~interval_overlaps (mk_interval dst (32 * n))
                       (mk_interval src (32 * n))
Proof
  fs[interval_overlaps_def, mk_interval_def, interval_end_def, MULT_CLAUSES]
QED

Theorem mcopy_merge_n:
  !n dst src s.
    0 < n /\
    ~interval_overlaps
      (mk_interval dst (32 * n))
      (mk_interval src (32 * n)) ==>
    FOLDL (\st i. mcopy (dst + 32 * i) (src + 32 * i) 32 st)
          s (GENLIST I n)
    = mcopy dst src (32 * n) s
Proof
  Induct_on `n` >> simp[]
  >> rpt gen_tac >> strip_tac
  >> simp[GENLIST, FOLDL_SNOC]
  >> Cases_on `n = 0` >- simp[GENLIST_ID, FOLDL]
  >> `0 < n` by simp[]
  >> drule_all interval_overlaps_shrink >> strip_tac
  >> first_x_assum (qspecl_then [`dst`,`src`,`s`] mp_tac) >> simp[]
  >> strip_tac
  >> `32 * SUC n = 32 * n + 32` by simp[MULT_CLAUSES]
  >> pop_assum SUBST_ALL_TAC
  >> `32 * n + src = src + 32 * n` by simp[]
  >> pop_assum SUBST_ALL_TAC
  >> irule mcopy_merge_step >> simp[]
QED

(* ===== Calldata/Dload equivalence ===== *)

(* calldataload+mstore = calldatacopy 32.
   Similar to mload_mstore but reading from calldata. *)
Theorem calldataload_mstore_eq_calldatacopy:
  !src dst s.
    let val = word_of_bytes T (0w:bytes32)
                (TAKE 32 (DROP src s.vs_call_ctx.cc_calldata ++
                          REPLICATE 32 0w)) in
    mstore dst val s =
    write_memory_with_expansion dst
      (TAKE 32 (DROP src s.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w)) s
Proof
  rw[mstore_def, write_memory_with_expansion_def]
  >> simp[LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND]
  >> simp[word_bytes_roundtrip]
QED

(* dload+mstore = dloadbytes 32.
   Similar but reading from data section. *)
Theorem dload_mstore_eq_dloadbytes:
  !src dst s.
    let val = word_of_bytes T (0w:bytes32)
                (TAKE 32 (DROP src s.vs_data_section ++
                          REPLICATE 32 0w)) in
    mstore dst val s =
    write_memory_with_expansion dst
      (TAKE 32 (DROP src s.vs_data_section ++ REPLICATE 32 0w)) s
Proof
  rw[mstore_def, write_memory_with_expansion_def]
  >> simp[LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND]
  >> simp[word_bytes_roundtrip]
QED

(* ===== Zero word helper ===== *)

Theorem word_to_bytes_0w[simp]:
  word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)
Proof
  simp[LIST_EQ_REWRITE, LENGTH_word_to_bytes, LENGTH_REPLICATE]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux, EL_REPLICATE, get_byte_def, byte_index_def]
  >> simp[ZERO_SHIFT, w2w_0]
QED

(* mstore of 0w = write_memory_with_expansion of 32 zero bytes *)
Theorem mstore_0w_eq_write:
  !dst (s:venom_state).
    mstore dst (0w:bytes32) s =
    write_memory_with_expansion dst (REPLICATE 32 (0w:word8)) s
Proof
  rw[mstore_def, write_memory_with_expansion_def, LET_THM]
QED

(* N consecutive zero-stores = one write of 32*n zero bytes.
   FOLDL (\st i. mstore (dst + 32*i) 0w st) s (GENLIST I n)
   = write_memory_with_expansion dst (REPLICATE (32*n) 0w) s
   Base case: n=1 (single mstore). Inductive: SNOC composition. *)
Theorem n_zero_stores_eq_write:
  !n dst (s:venom_state).
    0 < n ==>
    FOLDL (\st i. mstore (dst + 32 * i) (0w:bytes32) st)
          s (GENLIST I n)
    = write_memory_with_expansion dst (REPLICATE (32 * n) (0w:word8)) s
Proof
  Induct >- simp[]
  >> rpt strip_tac
  >> simp[GENLIST, FOLDL_SNOC]
  >> Cases_on `n = 0`
  >- (simp[GENLIST, FOLDL, mstore_0w_eq_write] >>
      simp[LENGTH_REPLICATE])
  >> `0 < n` by simp[]
  >> `32 * SUC n = 32 * n + 32` by simp[MULT_CLAUSES]
  >> pop_assum SUBST_ALL_TAC
  >> first_x_assum (qspecl_then [`dst`, `s`] mp_tac) >> simp[]
  >> disch_then SUBST1_TAC
  >> simp[mstore_0w_eq_write]
  >> `REPLICATE (32 * n + 32) (0w:word8) =
      REPLICATE (32 * n) 0w ++ REPLICATE 32 0w` by
    simp[GSYM REPLICATE_APPEND]
  >> pop_assum SUBST_ALL_TAC
  >> `dst + 32 * n = dst + LENGTH (REPLICATE (32 * n) (0w:word8))` by
    simp[LENGTH_REPLICATE]
  >> pop_assum SUBST_ALL_TAC
  >> simp[GSYM write_memory_append]
QED

(* Calldatacopy past end writes zero bytes.
   When offset >= LENGTH calldata, the copied bytes are all zero. *)
Theorem calldatacopy_past_end_bytes:
  !offset size calldata.
    LENGTH calldata <= offset ==>
    TAKE size (DROP offset calldata ++ REPLICATE size (0w:word8)) =
    REPLICATE size (0w:word8)
Proof
  rw[] >> `DROP offset calldata = []` by simp[DROP_LENGTH_TOO_LONG]
  >> simp[TAKE_APPEND1, LENGTH_REPLICATE, TAKE_LENGTH_ID_rwt]
QED

(* N zero-stores = calldatacopy past end of calldata *)
Theorem n_zero_stores_eq_calldatacopy_past_end:
  !n dst (s:venom_state) offset.
    0 < n /\
    LENGTH s.vs_call_ctx.cc_calldata <= offset ==>
    FOLDL (\st i. mstore (dst + 32 * i) (0w:bytes32) st)
          s (GENLIST I n)
    = write_memory_with_expansion dst
        (TAKE (32 * n)
          (DROP offset s.vs_call_ctx.cc_calldata ++
           REPLICATE (32 * n) (0w:word8))) s
Proof
  rw[n_zero_stores_eq_write, calldatacopy_past_end_bytes]
QED

(* ===== Memzero equivalence ===== *)

(* mstore(0, dst) writes 32 zero bytes.
   calldatacopy(dst, calldatasize, 32) reads past end of calldata,
   which is zero-padded, writing 32 zero bytes. *)
Theorem zero_store_eq_calldatacopy_past_end:
  !dst s offset.
    LENGTH s.vs_call_ctx.cc_calldata <= offset ==>
    mstore dst (0w:bytes32) s =
    write_memory_with_expansion dst
      (TAKE 32 (DROP offset s.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w)) s
Proof
  rw[mstore_def, write_memory_with_expansion_def]
  >> `DROP offset s.vs_call_ctx.cc_calldata = []` by simp[DROP_LENGTH_TOO_LONG]
  >> simp[TAKE_APPEND1, LENGTH_REPLICATE]
  >> simp[TAKE_LENGTH_ID_rwt, LENGTH_REPLICATE]
QED
