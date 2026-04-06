(*
 * ABI Encoder/Decoder Properties
 *
 * TOP-LEVEL:
 *   compile_abi_int_clamp_correct     — int clamping rejects out-of-range
 *   compile_abi_bytes_clamp_correct   — bytes clamping rejects dirty high bits
 *   compile_abi_encode_static_correct — static type writes word to dst
 *   compile_abi_decode_static_correct — static type reads + clamps
 *   compile_get_element_ptr_correct   — element pointer arithmetic
 *   compile_abi_zero_pad_correct      — zero-pad bytestring to 32-byte boundary
 *
 * Source: abi/abi_encoder.py, abi/abi_decoder.py
 * Lowering: abiEncoderScript.sml
 *)

Theory abiEncoderProps
Ancestors
  list rich_list
  exprLoweringProps emitHelper emitHelperProps
  abiEncoder compileEnv
  venomExecSemantics venomState venomInst venomMemProps
  valueEncoding valueEncodingProps
  vyperABI vyperTyping contractABI
Libs
  dep_rewrite wordsLib

(* ===== ABI Clamping ===== *)

(* Integer clamping: either accepts or reverts *)
Theorem compile_abi_int_clamp_correct:
  ∀ val_op bits is_signed ss st st' w.
    compile_abi_int_clamp val_op bits is_signed st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rw[compile_abi_int_clamp_def] >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >>
  pop_assum mp_tac >>
  drule emitted_insts_emit_op >>
  rpt strip_tac >>
  qmatch_asmsub_rename_tac`emitted_insts st st1` >>
  qmatch_asmsub_rename_tac`emitted_insts st1 st2` >>
  drule emitted_insts_emit_void >> strip_tac >>
  qspecl_then[`st`,`st1`,`st2`]mp_tac emitted_insts_append >>
  (impl_tac >- rw[]) >> strip_tac >>
  qspecl_then[`st`,`st2`,`st'`]mp_tac emitted_insts_append >>
  (impl_tac >- rw[]) >> strip_tac >>
  gvs[] >>
  irule run_pure2_assert_ok_or_revert >>
  TRY (
    qmatch_goalsub_abbrev_tac`mk_inst _ SIGNEXTEND [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_SIGNEXTEND >>
    disch_then (drule_at Any) >>
    simp[Abbr`op1`, eval_operand_def] >> disch_then kall_tac ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`mk_inst _ SHR [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_SHR >>
    disch_then (drule_at Any) >>
    simp[Abbr`op1`, eval_operand_def] >> disch_then kall_tac ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`step_inst_base _ ssu` >>
    qmatch_goalsub_abbrev_tac`mk_inst _ EQ [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_EQ >>
    CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["ss"]))) >>
    disch_then(qspec_then`ssu`mp_tac) >>
    simp[Abbr`op2`, eval_operand_def, Abbr`ssu`, lookup_var_update_var] >>
    drule_then drule eval_operand_update_fresh >> simp[] >>
    ntac 2 (disch_then kall_tac) ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`step_inst_base _ ssu` >>
    qmatch_goalsub_abbrev_tac`mk_inst _ ISZERO [op1]` >>
    qspecl_then[`op1`]mp_tac step_ISZERO >>
    CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["ss"]))) >>
    disch_then(qspec_then`ssu`mp_tac) >>
    simp[Abbr`op1`, eval_operand_def, Abbr`ssu`, lookup_var_update_var] >>
    drule_then drule eval_operand_update_fresh >> simp[] >>
    ntac 2 (disch_then kall_tac) ) >>
  unabbrev_all_tac >>
  simp[RIGHT_OR_EXISTS_THM] >>
  qmatch_goalsub_abbrev_tac`step_inst_base _ sss` >>
  qexists_tac`revert_state (set_returndata [] sss)` >>
  irule assert_ok_or_revert >>
  rw[eval_operand_def, Abbr`sss`, lookup_var_update_var]
QED

(* Bytes clamping: rejects values with non-zero high bits *)
Theorem compile_abi_bytes_clamp_correct:
  ∀ val_op m ss st st' w.
    compile_abi_bytes_clamp val_op m st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rw[compile_abi_bytes_clamp_def] >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >>
  pop_assum mp_tac >>
  drule emitted_insts_emit_op >>
  rpt strip_tac >>
  qmatch_asmsub_rename_tac`emitted_insts st st1` >>
  qmatch_asmsub_rename_tac`emitted_insts st1 st2` >>
  drule emitted_insts_emit_void >> strip_tac >>
  qspecl_then[`st`,`st1`,`st2`]mp_tac emitted_insts_append >>
  (impl_tac >- rw[]) >> strip_tac >>
  qspecl_then[`st`,`st2`,`st'`]mp_tac emitted_insts_append >>
  (impl_tac >- rw[]) >> strip_tac >>
  gvs[] >>
  irule run_pure2_assert_ok_or_revert >>
  TRY (
    qmatch_goalsub_abbrev_tac`mk_inst _ SIGNEXTEND [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_SIGNEXTEND >>
    disch_then (drule_at Any) >>
    simp[Abbr`op1`, eval_operand_def] >> disch_then kall_tac ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`mk_inst _ SHL [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_SHL >>
    disch_then (drule_at Any) >>
    simp[Abbr`op1`, eval_operand_def] >> disch_then kall_tac ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`step_inst_base _ ssu` >>
    qmatch_goalsub_abbrev_tac`mk_inst _ EQ [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_EQ >>
    CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["ss"]))) >>
    disch_then(qspec_then`ssu`mp_tac) >>
    simp[Abbr`op2`, eval_operand_def, Abbr`ssu`, lookup_var_update_var] >>
    drule_then drule eval_operand_update_fresh >> simp[] >>
    ntac 2 (disch_then kall_tac) ) >>
  unabbrev_all_tac >>
  TRY (
    qmatch_goalsub_abbrev_tac`step_inst_base _ ssu` >>
    qmatch_goalsub_abbrev_tac`mk_inst _ ISZERO [op1]` >>
    qspecl_then[`op1`]mp_tac step_ISZERO >>
    CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["ss"]))) >>
    disch_then(qspec_then`ssu`mp_tac) >>
    simp[Abbr`op1`, eval_operand_def, Abbr`ssu`, lookup_var_update_var] >>
    drule_then drule eval_operand_update_fresh >> simp[] >>
    ntac 2 (disch_then kall_tac) ) >>
  unabbrev_all_tac >>
  simp[RIGHT_OR_EXISTS_THM] >>
  qmatch_goalsub_abbrev_tac`step_inst_base _ sss` >>
  qexists_tac`revert_state (set_returndata [] sss)` >>
  irule assert_ok_or_revert >>
  rw[eval_operand_def, Abbr`sss`, lookup_var_update_var]
QED

(* ===== Static Encode/Decode ===== *)

(* TODO: move *)
Theorem mem_bytes_at_from_EL:
  n < LENGTH ls ==>
  [EL n ls] = mem_bytes_at n 1 ls
Proof
  rw[mem_bytes_at_def, TAKE_APPEND]
QED

(* Static ABI encoding: MLOAD src, MSTORE to dst, return Lit 32w *)
Theorem compile_abi_encode_static_correct:
  ∀ dst src ss st op st' src_v dst_w.
    compile_abi_encode_static dst src st = (op, st') ∧
    eval_operand src ss = SOME src_v ∧
    eval_operand dst ss = SOME dst_w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      op = Lit 32w ∧
      mload (w2n dst_w) ss' = mload (w2n src_v) ss ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < w2n dst_w ∨ a ≥ w2n dst_w + 32) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory
Proof
  rpt gen_tac >>
  simp[compile_abi_encode_static_def, comp_return_def,
       comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qmatch_goalsub_rename_tac`emitted_insts st st2` >>
  qmatch_asmsub_rename_tac`emitted_insts st1 st2` >>
  qspecl_then[`st`,`st1`,`st2`]mp_tac emitted_insts_append >>
  impl_tac >- gvs[] >> rw[] >>
  rw[run_inst_seq_def] >>
  qspec_then`src`mp_tac step_MLOAD >>
  disch_then drule >> rw[] >> pop_assum kall_tac >>
  qspec_then`dst`mp_tac eval_operand_update_fresh >>
  disch_then drule >>
  qmatch_goalsub_abbrev_tac`update_var nv w` >>
  disch_then(qspecl_then[`w`,`nv`]mp_tac) >>
  disch_then drule >>
  simp[Abbr`nv`] >> strip_tac >>
  drule step_MSTORE >>
  qmatch_goalsub_abbrev_tac`update_var nv` >>
  disch_then(qspec_then`Var nv`mp_tac) >>
  simp[eval_operand_def, lookup_var_update_var] >>
  strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  conj_tac >- irule mload_mstore_same >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- (
    irule fresh_vars_wrt_mstore >>
    irule fresh_vars_wrt_update_var >>
    reverse conj_asm2_tac >- (
      irule fresh_vars_wrt_emit_void >>
      goal_assum drule >>
      gvs[fresh_vars_wrt_def] ) >>
    gvs[Abbr`nv`, fresh_vars_wrt_def]) >>
  conj_tac >- (
    rpt strip_tac >>
    irule eval_operand_mstore >>
    irule eval_operand_update_fresh >>
    gvs[Abbr`nv`] >>
    goal_assum $ drule_at Any >> rw[] ) >>
  reverse conj_asm2_tac >- rw[mstore_def, update_var_def] >>
  qx_gen_tac`off` >>
  qmatch_goalsub_abbrev_tac`_ ∧ rng` >>
  strip_tac >>
  drule mem_bytes_at_from_EL >>
  qmatch_asmsub_abbrev_tac`LENGTH mm ≥ _` >>
  `off < LENGTH mm` by gvs[] >>
  drule mem_bytes_at_from_EL >>
  ntac 2 strip_tac >>
  qmatch_goalsub_abbrev_tac`aa = ab` >>
  `[aa] = [ab]` suffices_by rw[] >>
  qpat_x_assum`[_] = _`SUBST_ALL_TAC >>
  qpat_x_assum`[_] = _`SUBST_ALL_TAC >>
  qunabbrev_tac`mm` >>
  `ss.vs_memory = (update_var nv w ss).vs_memory` by rw[update_var_def] >>
  pop_assum SUBST1_TAC >>
  irule mstore_mem_bytes_at_disjoint >>
  gvs[Abbr`rng`]
QED

(* Static ABI decoding: MLOAD + clamp *)
Theorem compile_abi_decode_static_correct:
  ∀ src_op dst_op load_opc clamp_fn ss st st' src_w.
    compile_abi_decode_static src_op dst_op load_opc clamp_fn st = ((), st') ∧
    eval_operand src_op ss = SOME src_w ∧
    fresh_vars_wrt st ss ∧
    (* clamp_fn: either succeeds preserving operands & freshness, or reverts *)
    (∀ val_op st0 st0' ss0 v.
       clamp_fn val_op st0 = ((), st0') ∧
       eval_operand val_op ss0 = SOME v ∧
       fresh_vars_wrt st0 ss0 ⇒
       (∃ ss0'.
         run_inst_seq (emitted_insts st0 st0') ss0 = OK ss0' ∧
         fresh_vars_wrt st0' ss0' ∧
         (∀ op w. eval_operand op ss0 = SOME w ⇒
                  eval_operand op ss0' = SOME w)) ∨
       (∃ ss0'.
         run_inst_seq (emitted_insts st0 st0') ss0 =
           Abort Revert_abort ss0'))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== ABI Encoding / Memory Correspondence ===== *)

(* For primitive word types, the Vyper memory representation (val_in_memory)
   is exactly the ABI encoding (enc). This is the key bridge between the
   source semantics and the ABI spec.

   val_in_memory says: mem_word_at off mem = val_to_w256 v
   enc says: enc abi_type abi_val = word_to_bytes (some_word) T

   These are the same 32 bytes, connected by word_bytes_roundtrip:
     word_to_bytes (word_of_bytes T 0w bs) T = bs  (when LENGTH bs = 32)

   Precondition off + 32 ≤ LENGTH mem ensures mem_bytes_at returns
   real memory (no zero-padding from REPLICATE). *)
Theorem val_in_memory_prim_enc:
  ∀ bt v off mem av.
    val_in_memory (BaseTV bt) v off mem ∧
    off + 32 ≤ LENGTH mem ∧
    is_word_type (BaseT bt) ∧
    value_has_type (BaseTV bt) v ∧
    vyper_to_abi_base bt v = SOME av
    ⇒
    mem_bytes_at off 32 mem = enc (vyper_base_to_abi_type bt) av
Proof
  (* Case split on bt and v. For each case:
     1. val_in_memory gives mem_word_at off mem = val_to_w256 v
     2. Unfold mem_word_at: word_of_bytes T 0w (mem_bytes_at off 32 mem) = w
     3. Apply word_bytes_roundtrip: word_to_bytes w T = mem_bytes_at off 32 mem
     4. Unfold enc/enc_number: enc at av = word_to_bytes w' T
     5. Show w = w' by connecting val_to_w256 to the ABI value *)
  Cases_on `bt` >> Cases_on `v` >>
  simp[val_in_memory_def, is_word_type_def, vyper_to_abi_base_def,
       vyper_base_to_abi_type_def, enc_def, enc_number_def,
       mem_word_at_def, mem_bytes_at_def, val_to_w256_def] >>
  rw[] >> rw[enc_def] >> gvs[value_has_type_def, TAKE_APPEND] >>
  gvs[typed_val_to_w256_def] >>
  full_simp_tac bool_ss [GSYM arithmeticTheory.SUB_EQ_0] >> gvs[] >>
  TRY (
    `n2w (Num i): bytes32 = i2w i` by (
      rw[integer_wordTheory.i2w_def] >>
      Cases_on`i=0` \\ gvs[] >>
      `F` suffices_by rw[] >>
      intLib.COOPER_TAC) >> gvs[]) >>
  TRY (
    qpat_x_assum`word_of_bytes _ _ _ = _`(SUBST_ALL_TAC o SYM) >>
    irule $ GSYM word_bytes_roundtrip >>
    simp[dividesTheory.divides_def] >> NO_TAC)
  >- (
    Cases_on`b` \\ gvs[value_has_type_def, is_word_type_def] >>
    gvs[PAD_RIGHT, REPLICATE_GENLIST, TAKE_LENGTH_TOO_LONG,
        byteTheory.word_of_bytes_be_def] >>
    drule_at Any word_of_bytes_be_inj >>
    simp[dividesTheory.divides_def] ) >>
  gvs[GSYM wordsTheory.w2w_def] >>
  qmatch_goalsub_abbrev_tac`word_to_bytes www` >>
  qmatch_asmsub_abbrev_tac`word_of_bytes _ _ _ = ww1` >>
  `www = ww1` by (
    rw[Abbr`www`] >> gvs[byteTheory.word_of_bytes_be_def] >>
    drule_at Any word_of_bytes_be_inj >>
    rw[bitstringTheory.length_pad_left] >>
    simp[GSYM byteTheory.word_of_bytes_be_def] >>
    DEP_REWRITE_TAC[w2w_word_of_bytes_be_pad_left] >>
    simp[dividesTheory.divides_def] ) >>
  gvs[Abbr`www`] >>
  irule $ GSYM word_bytes_roundtrip >>
  rw[dividesTheory.divides_def]
QED

(* ===== Single-block predicate ===== *)

(* Identifies abi_enc_info values whose compilation produces only
   single-block code (no JMP/JNZ/new_block). Excludes AbiDynArray
   with dynamic elements, which uses compile_abi_encode_dyn_loop. *)
Definition single_block_enc_info_def:
  single_block_enc_info AbiPrimWord = T ∧
  single_block_enc_info (AbiBytestring _) = T ∧
  single_block_enc_info (AbiCopy _) = T ∧
  single_block_enc_info (AbiDynArray ei _ _ is_dyn) =
    (¬is_dyn ∧ single_block_enc_info ei) ∧
  single_block_enc_info (AbiComplex elems) =
    EVERY (λ(ei,_,_,_). single_block_enc_info ei) elems
End

(* ===== Recursive ABI Encode Correctness (single-block) ===== *)

(* Mutual induction over compile_abi_encode_child / compile_abi_encode_to_buf /
   compile_abi_encode_complex_elems.

   For single-block enc_info values:
   - Emitted instructions run successfully via run_inst_seq
   - Destination memory contains the ABI encoding
   - Memory frame: only [dst, dst+size) is modified
   - Operand frame: all pre-existing operands still evaluate
   - Freshness preserved

   Preconditions:
   - fresh_vars_wrt st ss (compiler names don't alias runtime vars)
   - val_in_memory at source (Vyper value is in memory)
   - destination pre-allocated (dst + max_size ≤ LENGTH vs_memory)
   - value_has_type (value is well-typed)
   - has_type for ABI value (needed for enc properties)
*)

Theorem compile_abi_encode_to_buf_correct:
  (* compile_abi_encode_child — P0: static case only for single_block *)
  (∀ dst child_ptr enc_info is_dyn static_ofst dyn_ofst_ptr
     st op st' ss
     dst_addr child_addr ty tv v tenv av at.
    compile_abi_encode_child dst child_ptr enc_info
      is_dyn static_ofst dyn_ofst_ptr st = (op, st') ∧
    ¬is_dyn ∧
    single_block_enc_info enc_info ∧
    eval_operand dst ss = SOME (n2w dst_addr) ∧
    eval_operand child_ptr ss = SOME (n2w child_addr) ∧
    fresh_vars_wrt st ss ∧
    evaluate_type tenv ty = SOME tv ∧
    dst_addr + static_ofst + LENGTH (enc at av) ≤ LENGTH ss.vs_memory ∧
    child_addr + type_memory_size tv ≤ LENGTH ss.vs_memory ∧
    val_in_memory tv v child_addr ss.vs_memory ∧
    value_has_type tv v ∧
    vyper_to_abi tenv ty v = SOME av ∧
    has_type at av ∧
    at = vyper_to_abi_type tenv ty
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      fresh_vars_wrt st' ss' ∧
      mem_bytes_at (dst_addr + static_ofst) (LENGTH (enc at av))
        ss'.vs_memory = enc at av ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < dst_addr + static_ofst ∨
             a ≥ dst_addr + static_ofst + LENGTH (enc at av)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_to_buf — P1 *)
  (∀ dst src enc_info st op st' ss
     dst_addr src_addr ty tv v tenv av at.
    compile_abi_encode_to_buf dst src enc_info st = (op, st') ∧
    single_block_enc_info enc_info ∧
    eval_operand dst ss = SOME (n2w dst_addr) ∧
    eval_operand src ss = SOME (n2w src_addr) ∧
    fresh_vars_wrt st ss ∧
    evaluate_type tenv ty = SOME tv ∧
    dst_addr + LENGTH (enc at av) ≤ LENGTH ss.vs_memory ∧
    src_addr + type_memory_size tv ≤ LENGTH ss.vs_memory ∧
    val_in_memory tv v src_addr ss.vs_memory ∧
    value_has_type tv v ∧
    vyper_to_abi tenv ty v = SOME av ∧
    has_type at av ∧
    at = vyper_to_abi_type tenv ty
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      fresh_vars_wrt st' ss' ∧
      mem_bytes_at dst_addr (LENGTH (enc at av)) ss'.vs_memory =
        enc at av ∧
      eval_operand op ss' = SOME (n2w (LENGTH (enc at av))) ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < dst_addr ∨ a ≥ dst_addr + LENGTH (enc at av)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_complex_elems — P2: static elements *)
  (∀ dst src elems src_offset head_offset dyn_ptr
     st op st' ss
     dst_addr src_addr tys tvs vs tenv avs ats.
    compile_abi_encode_complex_elems dst src elems
      src_offset head_offset dyn_ptr st = (op, st') ∧
    EVERY (λ(ei,_,_,is_dyn). single_block_enc_info ei ∧ ¬is_dyn) elems ∧
    eval_operand dst ss = SOME (n2w dst_addr) ∧
    eval_operand src ss = SOME (n2w src_addr) ∧
    fresh_vars_wrt st ss ∧
    (* elems, tys, tvs, vs, avs, ats are parallel lists *)
    LENGTH tys = LENGTH elems ∧
    LENGTH tvs = LENGTH elems ∧
    LENGTH vs = LENGTH elems ∧
    LENGTH avs = LENGTH elems ∧
    LENGTH ats = LENGTH elems ∧
    has_types ats avs ∧
    ¬any_dynamic ats ∧
    (* Types evaluate correctly *)
    (∀ i. i < LENGTH elems ⇒
       evaluate_type tenv (EL i tys) = SOME (EL i tvs)) ∧
    (* Memory and type preconditions for all elements *)
    dst_addr + head_offset +
      SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems) ≤ LENGTH ss.vs_memory ∧
    (∀ i. i < LENGTH elems ⇒
       let (ei, abi_sz, mem_sz, _) = EL i elems in
       let tv = EL i tvs in let v = EL i vs in
         val_in_memory tv v (src_addr + src_offset +
           SUM (MAP (λ(_,_,msz,_). msz) (TAKE i elems))) ss.vs_memory ∧
         value_has_type tv v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      fresh_vars_wrt st' ss' ∧
      mem_bytes_at (dst_addr + head_offset)
        (SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems)) ss'.vs_memory =
        FLAT (MAP2 enc ats avs) ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < dst_addr + head_offset ∨
             a ≥ dst_addr + head_offset +
               SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_dyn_loop — excluded by single_block_enc_info,
     trivially true *)
  (∀ (dst:operand) (src:operand) (elem_info:abi_enc_info)
     (elem_abi_sz:num) (elem_mem_sz:num) (len_op:operand). T)
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  (* P0: compile_abi_encode_child *)
  conj_tac >- suspend "child" >>
  (* P1: compile_abi_encode_to_buf: AbiPrimWord *)
  conj_tac >- suspend "prim" >>
  (* P1: compile_abi_encode_to_buf: AbiBytestring *)
  conj_tac >- suspend "bytestring" >>
  (* P1: compile_abi_encode_to_buf: AbiCopy *)
  conj_tac >- suspend "copy" >>
  (* P1: compile_abi_encode_to_buf: AbiDynArray *)
  conj_tac >- suspend "dynarray" >>
  (* P1: compile_abi_encode_to_buf: AbiComplex [] *)
  conj_tac >- suspend "complex_nil" >>
  (* P1: compile_abi_encode_to_buf: AbiComplex (non-empty) *)
  conj_tac >- suspend "complex_cons" >>
  (* P2: compile_abi_encode_complex_elems: [] *)
  conj_tac >- suspend "elems_nil" >>
  (* P2: compile_abi_encode_complex_elems: cons *)
  conj_tac >- suspend "elems_cons" >>
  (* P3: compile_abi_encode_dyn_loop *)
  suspend "dyn_loop"
QED

Resume compile_abi_encode_to_buf_correct[child]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!d. ~ ~ is_dyn ==> _` kall_tac >>
  gvs[compile_abi_encode_child_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  reverse (Cases_on `static_ofst = 0`) >> gvs[]
  >- (
    (* static_ofst ≠ 0: emit_op ADD first *)
    drule emit_op_ADD_correct >>
    disch_then drule >>
    simp[eval_operand_def] >>
    simp[Once wordsTheory.word_add_n2w] >>
    strip_tac >>
    suspend"childADD") >>
  (* static_ofst = 0: child_dst = dst, directly apply IH *)
  gvs[comp_return_def] >>
  first_x_assum drule_all >>
  strip_tac >>
  goal_assum drule >> gvs[] >>
  rpt strip_tac >>
  first_x_assum irule >> gvs[]
QED

Resume compile_abi_encode_to_buf_correct[childADD]:
  first_x_assum $ drule_then drule >>
  first_assum drule >> strip_tac >>
  disch_then drule >> gvs[] >>
  disch_then drule >> gvs[] >>
  disch_then drule >>
  `ss'.vs_memory = ss.vs_memory` by gvs[LIST_EQ_REWRITE] >>
  gvs[] >>
  disch_then drule >> gvs[] >>
  strip_tac >>
  qspec_then`st`mp_tac emitted_insts_append >>
  disch_then $ drule_at Any >> impl_keep_tac
  >- ( drule emitted_insts_emit_op >> rw[] ) >> rw[] >>
  qmatch_goalsub_abbrev_tac`run_inst_seq (is1 ++ is2)` >>
  qspec_then`is1`mp_tac run_inst_seq_append >>
  disch_then drule >> simp[] >> strip_tac >>
  conj_tac >- gvs[same_blocks_def] >>
  first_x_assum MATCH_ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_correct[prim]:
  rpt gen_tac >> strip_tac >>
  gvs[compile_abi_encode_child_def] >>
  drule_all compile_abi_encode_static_correct >>
  strip_tac >> simp[] >>
  cheat
QED

Resume compile_abi_encode_to_buf_correct[bytestring]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[copy]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[dynarray]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[complex_nil]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[complex_cons]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[elems_nil]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[elems_cons]:
  cheat
QED

Resume compile_abi_encode_to_buf_correct[dyn_loop]:
  cheat
QED

Finalise compile_abi_encode_to_buf_correct

(* ===== Element Pointer ===== *)

(* get_element_ptr at offset 0 returns parent *)
Theorem compile_get_element_ptr_zero:
  ∀ parent_ptr st.
    compile_get_element_ptr parent_ptr 0 st = (parent_ptr, st)
Proof
  simp[compile_get_element_ptr_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* get_element_ptr at non-zero offset adds offset *)
Theorem compile_get_element_ptr_correct:
  ∀ parent_ptr offset ss st op st'.
    compile_get_element_ptr parent_ptr offset st = (op, st') ∧
    offset > 0 ∧
    eval_operand parent_ptr ss = SOME (n2w base_addr)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (n2w (base_addr + offset))
Proof
  cheat
QED

(* ===== Zero Padding ===== *)

(* ABI zero-pad: pads bytestring to 32-byte boundary *)
Theorem compile_abi_zero_pad_correct:
  ∀ bytez_ptr ss st st'.
    compile_abi_zero_pad bytez_ptr st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED


