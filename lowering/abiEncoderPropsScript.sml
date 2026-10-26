(*
 * ABI Encoder/Decoder Properties
 *
 * TOP-LEVEL:
 *   compile_abi_int_clamp_correct       — int clamping either accepts or reverts on out-of-range
 *   compile_abi_bytes_clamp_correct   — bytes clamping either accepts or reverts on dirty high bits
 *   compile_abi_encode_static_correct — static type writes word to dst
 *   compile_abi_decode_static_correct — static type reads + clamps
 *   compile_abi_encode_to_buf_correct — recursive ABI encode correctness (single-block)
 *   compile_abi_encode_frag           — recursive ABI encode correctness over frag_exec,
 *                                       for an encoding plan abi_enc_plan
 *   compile_get_element_ptr_zero       — zero-offset pointer ADD preserves value
 *   compile_get_element_ptr_correct   — get_element_ptr adds offset to parent pointer
 *   val_in_memory_prim_enc            — primitive val_in_memory matches ABI encoding
 *   val_in_memory_flag_enc            — flag val_in_memory matches ABI encoding
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
  vyperABI vyperTyping contractABI fragExec
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

(* Flag types: same argument as prims but FlagTV instead of BaseTV *)
Theorem val_in_memory_flag_enc:
  ∀ m k off mem.
    val_in_memory (FlagTV m) (FlagV k) off mem ∧
    off + 32 ≤ LENGTH mem
    ⇒
    mem_bytes_at off 32 mem = enc (Uint 256) (NumV k)
Proof
  metis_tac[valueEncodingProofsTheory.val_in_memory_flag_abi]
QED

(* Memory length fits in a word — needed so w2n/n2w round-trips *)
Definition venom_memory_bound_def:
  venom_memory_bound ss ⇔ LENGTH ss.vs_memory < dimword(:256)
End

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
  (* compile_abi_encode_child — static case only for single_block *)
  (∀ dst child_ptr enc_info is_dyn static_ofst dyn_ofst_ptr
     st op st' ss
     dst_w child_w ty tv v tenv av at
     (sfields : (string, (string # type # num) list) fmap) cenv.
    compile_abi_encode_child dst child_ptr enc_info
      is_dyn static_ofst dyn_ofst_ptr st = (op, st') ∧
    ¬is_dyn ∧
    single_block_enc_info enc_info ∧
    enc_info = type_to_abi_enc_info sfields cenv ty ∧
    sfields_tenv_consistent sfields tenv ∧
    eval_operand dst ss = SOME dst_w ∧
    eval_operand child_ptr ss = SOME child_w ∧
    fresh_vars_wrt st ss ∧
    venom_memory_bound ss ∧
    evaluate_type tenv ty = SOME tv ∧
    w2n dst_w + static_ofst + LENGTH (enc at av) ≤ LENGTH ss.vs_memory ∧
    w2n child_w + type_memory_size tv ≤ LENGTH ss.vs_memory ∧
    val_in_memory tv v (w2n child_w) ss.vs_memory ∧
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
      mem_bytes_at (w2n dst_w + static_ofst) (LENGTH (enc at av))
        ss'.vs_memory = enc at av ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < w2n dst_w + static_ofst ∨
             a ≥ w2n dst_w + static_ofst + LENGTH (enc at av)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_to_buf *)
  (∀ dst src enc_info st op st' ss
     dst_w src_w ty tv v tenv av at
     (sfields : (string, (string # type # num) list) fmap) cenv.
    compile_abi_encode_to_buf dst src enc_info st = (op, st') ∧
    single_block_enc_info enc_info ∧
    enc_info = type_to_abi_enc_info sfields cenv ty ∧
    sfields_tenv_consistent sfields tenv ∧
    eval_operand dst ss = SOME dst_w ∧
    eval_operand src ss = SOME src_w ∧
    fresh_vars_wrt st ss ∧
    venom_memory_bound ss ∧
    evaluate_type tenv ty = SOME tv ∧
    w2n dst_w + LENGTH (enc at av) ≤ LENGTH ss.vs_memory ∧
    w2n src_w + type_memory_size tv ≤ LENGTH ss.vs_memory ∧
    val_in_memory tv v (w2n src_w) ss.vs_memory ∧
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
      mem_bytes_at (w2n dst_w) (LENGTH (enc at av)) ss'.vs_memory =
        enc at av ∧
      eval_operand op ss' = SOME (n2w (LENGTH (enc at av))) ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < w2n dst_w ∨ a ≥ w2n dst_w + LENGTH (enc at av)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_complex_elems — static elements *)
  (∀ dst src elems src_offset head_offset dyn_ptr
     st op st' ss
     dst_w src_w tys tvs vs tenv avs ats
     (sfields : (string, (string # type # num) list) fmap) cenv.
    compile_abi_encode_complex_elems dst src elems
      src_offset head_offset dyn_ptr st = (op, st') ∧
    EVERY (λ(ei,_,_,is_dyn). single_block_enc_info ei ∧ ¬is_dyn) elems ∧
    (* enc_info correspondence per element *)
    (∀ i. i < LENGTH elems ⇒
       FST (EL i elems) = type_to_abi_enc_info sfields cenv (EL i tys)) ∧
    sfields_tenv_consistent sfields tenv ∧
    eval_operand dst ss = SOME dst_w ∧
    eval_operand src ss = SOME src_w ∧
    fresh_vars_wrt st ss ∧
    venom_memory_bound ss ∧
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
    w2n dst_w + head_offset +
      SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems) ≤ LENGTH ss.vs_memory ∧
    (∀ i. i < LENGTH elems ⇒
       let (ei, abi_sz, mem_sz, _) = EL i elems in
       let tv = EL i tvs in let v = EL i vs in
         val_in_memory tv v (w2n src_w + src_offset +
           SUM (MAP (λ(_,_,msz,_). msz) (TAKE i elems))) ss.vs_memory ∧
         value_has_type tv v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      fresh_vars_wrt st' ss' ∧
      mem_bytes_at (w2n dst_w + head_offset)
        (SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems)) ss'.vs_memory =
        FLAT (MAP2 enc ats avs) ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ∧
            (a < w2n dst_w + head_offset ∨
             a ≥ w2n dst_w + head_offset +
               SUM (MAP (λ(_,abi_sz,_,_). abi_sz) elems)) ⇒
            EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory ≥ LENGTH ss.vs_memory) ∧

  (* compile_abi_encode_dyn_loop — excluded by single_block_enc_info,
     trivially true *)
  (∀ (dst:operand) (src:operand) (elem_info:abi_enc_info)
     (elem_abi_sz:num) (elem_mem_sz:num) (len_op:operand). T)
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  (* compile_abi_encode_child *)
  conj_tac >- suspend "child" >>
  (* compile_abi_encode_to_buf: AbiPrimWord *)
  conj_tac >- suspend "prim" >>
  (* compile_abi_encode_to_buf: AbiBytestring *)
  conj_tac >- suspend "bytestring" >>
  (* compile_abi_encode_to_buf: AbiCopy *)
  conj_tac >- suspend "copy" >>
  (* compile_abi_encode_to_buf: AbiDynArray *)
  conj_tac >- suspend "dynarray" >>
  (* compile_abi_encode_to_buf: AbiComplex [] *)
  conj_tac >- suspend "complex_nil" >>
  (* compile_abi_encode_to_buf: AbiComplex (non-empty) *)
  conj_tac >- suspend "complex_cons" >>
  (* compile_abi_encode_complex_elems: [] *)
  conj_tac >- suspend "elems_nil" >>
  (* compile_abi_encode_complex_elems: cons *)
  conj_tac >- suspend "elems_cons" >>
  (* compile_abi_encode_dyn_loop *)
  suspend "dyn_loop"
QED

Resume compile_abi_encode_to_buf_correct[child]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!d. ~ ~ is_dyn ==> _` kall_tac >>
  gvs[compile_abi_encode_child_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  (* Pinned Python computes every child head pointer with ADD, including
     zero offsets, so establish the emitted ADD before applying the child IH. *)
  drule emit_op_ADD_correct >>
  disch_then drule >>
  simp[eval_operand_def] >>
  simp[Once wordsTheory.word_add_n2w] >>
  strip_tac >>
  suspend"childADD"
QED

Resume compile_abi_encode_to_buf_correct[childADD]:
  first_x_assum $ drule_then $ drule_at Any >>
  first_assum drule >> strip_tac >>
  `ss'.vs_memory = ss.vs_memory` by gvs[LIST_EQ_REWRITE] >>
  disch_then (drule_at Any) >>
  disch_then (drule_at Any) >>
  disch_then (drule_at Any) >> gvs[] >>
  disch_then (drule_at Any) >> gvs[] >>
  disch_then(qspecl_then[`sfields`,`cenv`]mp_tac) >>
  impl_tac >- (
    simp[] >>
    gvs[venom_memory_bound_def] >>
    Cases_on`dst_w` \\ gvs[wordsTheory.word_add_n2w] ) >>
  strip_tac >>
  qspec_then`st`mp_tac emitted_insts_append >>
  disch_then $ drule_at Any >> impl_keep_tac
  >- ( drule emitted_insts_emit_op >> rw[] ) >> rw[] >>
  qmatch_goalsub_abbrev_tac`run_inst_seq (is1 ++ is2)` >>
  qspec_then`is1`mp_tac run_inst_seq_append >>
  disch_then drule >> simp[] >> strip_tac >>
  conj_tac >- gvs[same_blocks_def] >>
  Cases_on`dst_w` \\ gvs[wordsTheory.word_add_n2w, venom_memory_bound_def]
  >> first_x_assum MATCH_ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_correct[prim]:
  rpt gen_tac >> strip_tac >>
  gvs[compile_abi_encode_child_def] >>
  drule_all compile_abi_encode_static_correct >>
  strip_tac >> simp[] >>
  drule mload_eq_mem_bytes_at_eq >> strip_tac >>
  qmatch_goalsub_abbrev_tac`enc aty av` >>
  Cases_on`is_dynamic aty`
  >- (
    `F` suffices_by rw[] >>
    qhdtm_x_assum`type_to_abi_enc_info`mp_tac >>
    qhdtm_x_assum`evaluate_type`mp_tac >>
    qhdtm_x_assum`sfields_tenv_consistent`mp_tac >>
    simp[sfields_tenv_consistent_def] >> strip_tac >>
    qunabbrev_tac`aty` >> Cases_on`ty` >>
    simp[exprLoweringTheory.type_to_abi_enc_info_def,
         vyperValueTheory.evaluate_type_def, CaseEq"option"] >>
    strip_tac >> gvs[]
    >- (
      Cases_on`b` \\ gvs[exprLoweringTheory.type_to_abi_enc_info_def] >>
      Cases_on`b'` \\ gvs[exprLoweringTheory.type_to_abi_enc_info_def] )
    >- (BasicProvers.EVERY_CASE_TAC >>
        gvs[exprLoweringTheory.type_to_abi_enc_info_def]) >>
    FIRST
      [Cases_on`b` >> gvs[exprLoweringTheory.type_to_abi_enc_info_def] >>
       BasicProvers.EVERY_CASE_TAC >>
       gvs[exprLoweringTheory.type_to_abi_enc_info_def],
       Cases_on`v1` >> gvs[] >>
       first_x_assum drule >>
       rw[] >> rw[]] ) >>
  drule_all $ cj 1 enc_has_static_length >> strip_tac >>
  `∀tys. ty ≠ TupleT tys` by (
    rpt strip_tac >>
    Cases_on `is_abi_dynamic cenv.ce_struct_fields (TupleT tys)` >>
    gvs[exprLoweringTheory.type_to_abi_enc_info_def]) >>
  `∀a b. ty ≠ ArrayT a b` by (
    strip_tac >> Cases >> rpt strip_tac >>
    FIRST
      [Cases_on `is_abi_dynamic cenv.ce_struct_fields (ArrayT a (Fixed n))` >>
       gvs[exprLoweringTheory.type_to_abi_enc_info_def],
       gvs[exprLoweringTheory.type_to_abi_enc_info_def]]) >>
  `ty ≠ NoneT` by (
      strip_tac >> gvs[exprLoweringTheory.type_to_abi_enc_info_def]) >>
  `static_length aty = 32` by (
    ntac 4 (pop_assum mp_tac) >>
    qunabbrev_tac`aty` >>
    Cases_on`ty` \\ simp[] >>
    TRY (Cases_on`b`) >> simp[] >>
    TRY (Cases_on`b'`) >> simp[] >>
    qhdtm_x_assum`type_to_abi_enc_info`mp_tac >>
    simp[exprLoweringTheory.type_to_abi_enc_info_def] >>
    qhdtm_x_assum`sfields_tenv_consistent`mp_tac >>
    simp[sfields_tenv_consistent_def] >>
    CASE_TAC >> simp[] >>
    strip_tac >>
    reverse CASE_TAC >> simp[]
    >- (
      CASE_TAC >> simp[]
      >- gvs[vyperValueTheory.evaluate_type_def]
      >- (Cases_on `x` >> gvs[vyperValueTheory.evaluate_type_def] >>
          res_tac >> gvs[]) ) >>
    gvs[vyperValueTheory.evaluate_type_def] ) >>
  simp[eval_operand_def] >>
  reverse conj_tac >- first_x_assum MATCH_ACCEPT_TAC >>
  qunabbrev_tac`aty` >>
  Cases_on`∃n. ty = FlagT n` >- (
    gvs[vyper_to_abi_type_def] >>
    Cases_on`av` >> gvs[has_type_def,Excl"enc_def"] >>
    irule val_in_memory_flag_enc >>
    gvs[vyperValueTheory.evaluate_type_def,
        CaseEq"option",CaseEq"type_args",PULL_EXISTS] >>
    Cases_on`v` >> gvs[value_has_type_def] >>
    goal_assum $ drule_at Any >>
    gvs[type_memory_size_def]) >>
  `∃bt. ty = BaseT bt` by (
     Cases_on`ty` \\ gvs[] >>
     pop_assum mp_tac >> CASE_TAC >> gvs[] >>
     CASE_TAC >> gvs[vyperValueTheory.evaluate_type_def] >>
     gvs[exprLoweringTheory.type_to_abi_enc_info_def] >>
     gvs[AllCaseEqs()] >>
     gvs[sfields_tenv_consistent_def] >>
     first_x_assum drule >>
     first_x_assum drule >>
     rw[] ) >>
  BasicProvers.VAR_EQ_TAC >>
  simp[vyper_to_abi_type_def] >>
  irule val_in_memory_prim_enc >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  simp[PULL_EXISTS] >>
  goal_assum $ drule_at Any >> simp[] >>
  Cases_on`bt` >> gvs[type_memory_size_def, is_word_type_def] >>
  Cases_on`b` >> gvs[type_memory_size_def, is_word_type_def] >>
  gvs[exprLoweringTheory.type_to_abi_enc_info_def] >>
  Cases_on`av` >> gvs[has_type_def]
QED

Resume compile_abi_encode_to_buf_correct[bytestring]:
  (* False as stated: dst and src may overlap.  The MSTORE that zeroes the
     last data word runs before MCOPY reads the source, so with dst = src = 0
     and a Bytes[1] value [5], the data byte at 32 is zeroed before it is
     copied. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[copy]:
  (* False as stated: cenv's struct field sizes are not tied to tenv, so a
     static struct with cenv.ce_struct_fields = FEMPTY compiles to AbiCopy 0
     and copies nothing.  For the compile environment the compiler builds,
     build_compile_env_type_memory_bytes (structFieldsProps) gives the size;
     the copy itself is a single MCOPY. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[dynarray]:
  (* False as stated: single_block_enc_info accepts AbiDynArray with static
     elements, but compile_abi_encode_dyn_static_loop opens three new blocks
     for its loop, so same_blocks fails, e.g. for DynArray[uint256, 3]
     holding []. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[complex_nil]:
  (* True; not yet proved. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[complex_cons]:
  (* False as stated, and not provable from its induction hypothesis: in a
     single-block encoding only the has-dynamic-part branch is reachable, but
     the child hypothesis covers only static (~is_dyn) children, and the
     dynamic-offset ALLOCA cell is unconstrained, so the memory frame
     conjunct can fail. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[elems_nil]:
  (* True; not yet proved. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[elems_cons]:
  (* False as stated: nothing ties an element's value to vyper_to_abi or
     its encoded size to abi_sz, so an element can be claimed at a size its
     encoding does not have. *)
  cheat
QED

Resume compile_abi_encode_to_buf_correct[dyn_loop]:
  simp[]
QED

Finalise compile_abi_encode_to_buf_correct

(* ===== Static copy ===== *)

(* An ABI-static value is laid out in memory exactly as its ABI encoding, so
   AbiCopy encodes it with one MCOPY.  Venom's mcopy reads the whole source
   before writing, so the source and destination may overlap; the
   destination may lie past the end of memory, which then grows.
   mem_size < dimword (:256) is not implied by evaluate_type, which bounds
   the slot size, not the memory size. *)
Theorem compile_abi_encode_copy_frag:
  ∀ctx dst src mem_size st op st' s0 dst_w src_w tenv ty tv v av R.
    compile_abi_encode_to_buf dst src (AbiCopy mem_size) st = (op, st') ∧
    evaluate_type tenv ty = SOME tv ∧
    ¬is_dynamic (vyper_to_abi_type tenv ty) ∧
    mem_size = type_memory_size tv ∧
    mem_size < dimword (:256) ∧
    value_has_type tv v ∧
    vyper_to_abi tenv ty v = SOME av ∧
    eval_operand dst s0 = SOME dst_w ∧
    eval_operand src s0 = SOME src_w ∧
    val_in_memory tv v (w2n src_w) s0.vs_memory
    ⇒
    frag_exec ctx st st' (λs. s = s0)
      (λs. eval_operand op s = SOME (n2w mem_size) ∧
           mem_bytes_at (w2n dst_w) mem_size s.vs_memory =
             enc (vyper_to_abi_type tenv ty) av ∧
           (∀x w. not_fresh_at st x ∧ lookup_var x s0 = SOME w ⇒
                  lookup_var x s = SOME w) ∧
           s.vs_allocas = s0.vs_allocas ∧
           (∀a. a < LENGTH s0.vs_memory ∧
                (a < w2n dst_w ∨ w2n dst_w + mem_size ≤ a) ⇒
                EL a s.vs_memory = EL a s0.vs_memory) ∧
           LENGTH s0.vs_memory ≤ LENGTH s.vs_memory) R
Proof
  rpt strip_tac >>
  gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule emit_void_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  simp[same_blocks_def] >>
  reverse conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      gvs[same_blocks_def, mk_inst_def, is_terminator_def]) >>
  disj1_tac >>
  qexists_tac `mcopy (w2n dst_w) (w2n src_w) (type_memory_size tv) s0` >>
  conj_tac
  >- (drule emit_void_MCOPY_run >> simp[eval_operand_def]) >>
  simp[eval_operand_def, lookup_var_def] >>
  simp[GSYM lookup_var_def, mcopy_memory_nondecreasing] >>
  conj_tac
  >- (rewrite_tac[mem_bytes_at_def, mcopy_padded_read] >>
      rewrite_tac[GSYM mem_bytes_at_def] >>
      irule val_in_memory_static_abi >> goal_assum drule >>
      simp[] >> qexists_tac `v` >> simp[]) >>
  rpt strip_tac >> irule mcopy_byte_frame >> simp[]
QED

(* ===== Encoding plans ===== *)

(* abi_enc_plan env ty ei: ei is a right plan for encoding a value of type
   ty, in type environment env.  It fixes what the encoder takes on trust
   from its abi_enc_info: an AbiCopy size is the value's memory size, an
   element's head size, memory size and dynamic flag are those of its
   type, and an aggregate's elements are its components, in order (for a
   struct, typed in env \\ nsid, as vyper_to_abi_type does).  AbiComplex
   is for dynamic aggregates only: a static one is an AbiCopy, which is what
   the static-element loop of a dynamic array handles.  type_to_abi_enc_info
   builds such plans, except AbiComplex [] for NoneT, which has none (a
   return of no value doesn't encode). *)
Inductive abi_enc_plan:
[~prim:]
  is_word_type ty ==> abi_enc_plan env ty AbiPrimWord
[~bytes:]
  abi_enc_plan env (BaseT (BytesT (Dynamic n))) (AbiBytestring n)
[~string:]
  abi_enc_plan env (BaseT (StringT n)) (AbiBytestring n)
[~copy:]
  ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv ==>
  abi_enc_plan env ty (AbiCopy (type_memory_size tv))
[~dynarray:]
  evaluate_type env t = SOME tv /\ abi_enc_plan env t ei ==>
  abi_enc_plan env (ArrayT t (Dynamic n))
    (AbiDynArray ei
       (if is_dynamic (vyper_to_abi_type env t) then 32
        else static_length (vyper_to_abi_type env t))
       (type_memory_size tv) (is_dynamic (vyper_to_abi_type env t)))
[~tuple:]
  is_dynamic (vyper_to_abi_type env (TupleT ts)) /\
  abi_enc_plans env ts elems ==>
  abi_enc_plan env (TupleT ts) (AbiComplex elems)
[~sarray:]
  is_dynamic (vyper_to_abi_type env t) /\
  abi_enc_plans env (REPLICATE n t) elems ==>
  abi_enc_plan env (ArrayT t (Fixed n)) (AbiComplex elems)
[~struct:]
  FLOOKUP env nsid = SOME (StructArgs args) /\
  is_dynamic (vyper_to_abi_type env (StructT nsid)) /\
  abi_enc_plans (env \\ nsid) (MAP SND args) elems ==>
  abi_enc_plan env (StructT nsid) (AbiComplex elems)
[~nil:]
  abi_enc_plans env [] []
[~cons:]
  evaluate_type env t = SOME tv /\ abi_enc_plan env t ei /\
  abi_enc_plans env ts elems ==>
  abi_enc_plans env (t::ts)
    ((ei,
      (if is_dynamic (vyper_to_abi_type env t) then 32
       else static_length (vyper_to_abi_type env t)),
      type_memory_size tv, is_dynamic (vyper_to_abi_type env t)) :: elems)
End

(* ===== Scratch cells and frames ===== *)

(* The instruction ids a compiled fragment emits. *)
Definition frag_ids_def:
  frag_ids (st : compile_state) (st' : compile_state) =
    {i | st.cs_next_id <= i /\ i < st'.cs_next_id}
End

(* The encoder's scratch cells (its ALLOCAs of 32 bytes) at ids in ids:
   each one already run lies at or above lo, and running the rest keeps
   the alloca frontier at or below top, which is below 2 ** 256, so no
   pointer wraps.  An encoder in a loop body runs again with its cells of
   the last iteration allocated, which ALLOCA then returns again. *)
Definition enc_scratch_def:
  enc_scratch ids lo top (s : venom_state) <=>
    alloca_inv s /\ lo <= s.vs_alloca_next /\ top < dimword (:256) /\
    (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b, sz) ==>
              lo <= b /\ sz = 32) /\
    s.vs_alloca_next +
      32 * CARD {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE} <= top
End

(* What running encoder code from st to st' changes from s0 to s: the
   memory only in the output regions outs and in the fragment's own
   scratch cells; the allocas only at the fragment's ids, keeping those
   already run; no variable bound before st; none of the effects. *)
Definition enc_frame_def:
  enc_frame st st' lo top outs (s0 : venom_state) (s : venom_state) <=>
    (!x w. not_fresh_at st x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!a. EVERY (\(b, n). a < b \/ b + n <= a) outs /\
         (!i b sz. i IN frag_ids st st' /\
                   FLOOKUP s.vs_allocas i = SOME (b, sz) ==>
                   a < b \/ b + sz <= a) ==>
         mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 s0.vs_memory) /\
    (!i. i NOTIN frag_ids st st' ==>
         FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\
    (!i r. FLOOKUP s0.vs_allocas i = SOME r ==>
           FLOOKUP s.vs_allocas i = SOME r) /\
    enc_scratch (frag_ids st st') lo top s /\
    s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
    s.vs_logs = s0.vs_logs /\ s.vs_requests = s0.vs_requests
End

(* The encoder's inputs at s0: its operands are bound before st, the
   source value of type tv is in memory at src below lo, each output
   region lies below lo and misses the source, and the scratch cells are
   as enc_scratch says. *)
Definition enc_pre_def:
  enc_pre st st' ops lo top tv v src outs (s0 : venom_state) <=>
    (!y. MEM (Var y) ops ==> not_fresh_at st y) /\
    val_in_memory tv v src s0.vs_memory /\
    src + type_memory_size tv <= lo /\
    EVERY (\(b, n). b + n <= lo /\
                    regions_disjoint (src, type_memory_size tv) (b, n)) outs /\
    enc_scratch (frag_ids st st') lo top s0
End

(* ===== Encoding plan boundaries ===== *)

Theorem abi_enc_plans_nil[simp]:
  abi_enc_plans env [] elems <=> elems = []
Proof
  simp[Once abi_enc_plan_cases]
QED

Theorem abi_enc_plans_cons:
  abi_enc_plans env (t::ts) elems <=>
    ?tv ei rest.
      evaluate_type env t = SOME tv /\ abi_enc_plan env t ei /\
      abi_enc_plans env ts rest /\
      elems = (ei,
        (if is_dynamic (vyper_to_abi_type env t) then 32
         else static_length (vyper_to_abi_type env t)),
        type_memory_size tv, is_dynamic (vyper_to_abi_type env t))::rest
Proof
  simp[Once abi_enc_plan_cases] >> metis_tac[]
QED

Theorem abi_enc_plans_memory_sizes:
  !ts elems tvs.
    abi_enc_plans env ts elems /\
    LIST_REL (\t tv. evaluate_type env t = SOME tv) ts tvs ==>
    MAP (\(_, _, msz, _). msz) elems = MAP type_memory_size tvs
Proof
  Induct >> simp[abi_enc_plans_cons, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >>
  goal_assum drule >> simp[]
QED

Theorem abi_enc_plan_static:
  abi_enc_plan env ty ei /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  ei = AbiPrimWord \/ ?n. ei = AbiCopy n
Proof
  simp[Once abi_enc_plan_cases] >> rpt strip_tac >>
  gvs[vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_enc_plan_prim_size:
  abi_enc_plan env ty AbiPrimWord /\ evaluate_type env ty = SOME tv ==>
  type_memory_size tv = 32
Proof
  simp[Once abi_enc_plan_cases] >> strip_tac >>
  Cases_on `ty` >>
  gvs[is_word_type_def, vyperValueTheory.evaluate_type_def,
      type_memory_size_def, AllCaseEqs()] >>
  rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_word_type_def, vyperValueTheory.evaluate_type_def,
      type_memory_size_def, AllCaseEqs()]
QED

Theorem compile_abi_encode_static_info_plan:
  abi_enc_plan env ty ei /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  compile_abi_encode_static_info dst src ei =
    compile_abi_encode_to_buf dst src ei
Proof
  strip_tac >> drule_all abi_enc_plan_static >> strip_tac >>
  gvs[compile_abi_encode_static_info_def, Once compile_abi_encode_child_def]
QED

Theorem abi_enc_plans_head_lengths:
  !ts elems a.
    abi_enc_plans env ts elems ==>
    head_lengths (vyper_to_abi_types env ts) a =
      a + SUM (MAP (\(_, asz, _, _). asz) elems)
Proof
  Induct >> simp[abi_enc_plans_cons, head_lengths_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  rename1 `abi_enc_plan env t ei` >>
  first_x_assum drule >> disch_then (qspec_then
    `a + if is_dynamic (vyper_to_abi_type env t) then 32
         else static_length (vyper_to_abi_type env t)` SUBST1_TAC) >>
  decide_tac
QED


Theorem val_in_memory_static_enc_length:
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\ val_in_memory tv v off mem ==>
  LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv
Proof
  strip_tac >> drule_all val_in_memory_static_abi >>
  disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
  simp[mem_bytes_at_def]
QED

Theorem enc_tuple_cons_parts:
  has_types ts vs ==>
  enc_tuple hl tl (t::ts) (v::vs) [] [] =
    (if is_dynamic t then enc_number (Uint 256) (NumV (hl + tl))
     else enc t v) ++
    TAKE (head_lengths ts 0)
      (enc_tuple hl (tl + LENGTH (if is_dynamic t then enc t v else []))
         ts vs [] []) ++
    (if is_dynamic t then enc t v else []) ++
    DROP (head_lengths ts 0)
      (enc_tuple hl (tl + LENGTH (if is_dynamic t then enc t v else []))
         ts vs [] [])
Proof
  strip_tac >> simp[Once enc_def] >>
  simp[Once enc_tuple_append]
QED

Theorem enc_tuple_nil[simp]:
  enc_tuple hl tl [] [] [] [] = []
Proof
  simp[Once enc_def, REV_REVERSE_LEM]
QED

Theorem enc_dynarray_parts:
  has_types (REPLICATE (LENGTH vs) t) vs ==>
  enc (Array NONE t) (ListV vs) =
    enc_number (Uint 256) (NumV (LENGTH vs)) ++
    enc_tuple (head_lengths (REPLICATE (LENGTH vs) t) 0) 0
      (REPLICATE (LENGTH vs) t) vs [] []
Proof
  strip_tac >> simp[Once enc_def] >>
  simp[Once enc_tuple_append, TAKE_DROP]
QED

Theorem enc_dynarray_payload:
  has_types (REPLICATE (LENGTH vs) t) vs ==>
  DROP 32 (enc (Array NONE t) (ListV vs)) =
    enc_tuple (head_lengths (REPLICATE (LENGTH vs) t) 0) 0
      (REPLICATE (LENGTH vs) t) vs [] []
Proof
  strip_tac >> drule enc_dynarray_parts >>
  disch_then SUBST1_TAC >>
  simp[enc_number_def, DROP_APPEND, byteTheory.LENGTH_word_to_bytes]
QED

(* The general ABI bound head_lengths_leq_LENGTH_enc_tuple supplies
   head_lengths ts 0 <= LENGTH (enc_tuple hl tl ts vs [] []) under
   has_types ts vs (instantiate its hds, tls with [] and n with 0).
   Together with LENGTH_DROP this gives the exact tail-length subtraction;
   no encoder-specific duplicate of that bound is needed. *)

(* ===== Separated ABI prefixes ===== *)

Definition enc_prefix_tail_def:
  (enc_prefix_tail [] vs = []) /\
  (enc_prefix_tail (t::ts) [] = []) /\
  (enc_prefix_tail (t::ts) (v::vs) =
    (if is_dynamic t then enc t v else []) ++ enc_prefix_tail ts vs)
End

Definition enc_prefix_head_def:
  (enc_prefix_head q [] vs = []) /\
  (enc_prefix_head q (t::ts) [] = []) /\
  (enc_prefix_head q (t::ts) (v::vs) =
    (if is_dynamic t then enc_number (Uint 256) (NumV q) else enc t v) ++
    enc_prefix_head (q + LENGTH (if is_dynamic t then enc t v else [])) ts vs)
End

Definition enc_head_upto_def:
  enc_head_upto B ts vs k = enc_prefix_head B (TAKE k ts) (TAKE k vs)
End

Definition enc_tail_upto_def:
  enc_tail_upto ts vs k = enc_prefix_tail (TAKE k ts) (TAKE k vs)
End

Definition enc_offset_upto_def:
  enc_offset_upto B ts vs k = B + LENGTH (enc_tail_upto ts vs k)
End

Theorem enc_prefix_zero[simp]:
  enc_head_upto B ts vs 0 = [] /\ enc_tail_upto ts vs 0 = [] /\
  enc_offset_upto B ts vs 0 = B
Proof
  simp[enc_head_upto_def, enc_tail_upto_def, enc_offset_upto_def,
       enc_prefix_head_def, enc_prefix_tail_def]
QED

Theorem enc_prefix_tail_append:
  !ts vs us ws.
    LENGTH ts = LENGTH vs ==>
    enc_prefix_tail (ts ++ us) (vs ++ ws) =
      enc_prefix_tail ts vs ++ enc_prefix_tail us ws
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[enc_prefix_tail_def, APPEND_ASSOC]
QED

Theorem enc_prefix_head_append:
  !ts vs q us ws.
    LENGTH ts = LENGTH vs ==>
    enc_prefix_head q (ts ++ us) (vs ++ ws) =
      enc_prefix_head q ts vs ++
      enc_prefix_head (q + LENGTH (enc_prefix_tail ts vs)) us ws
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[enc_prefix_head_def, enc_prefix_tail_def, APPEND_ASSOC]
QED

Theorem enc_prefix_suc:
  LENGTH ts = LENGTH vs /\ k < LENGTH vs ==>
  enc_head_upto B ts vs (SUC k) = enc_head_upto B ts vs k ++
    (if is_dynamic (EL k ts) then
       enc_number (Uint 256) (NumV (enc_offset_upto B ts vs k))
     else enc (EL k ts) (EL k vs)) /\
  enc_tail_upto ts vs (SUC k) = enc_tail_upto ts vs k ++
    (if is_dynamic (EL k ts) then enc (EL k ts) (EL k vs) else []) /\
  enc_offset_upto B ts vs (SUC k) = enc_offset_upto B ts vs k +
    LENGTH (if is_dynamic (EL k ts) then enc (EL k ts) (EL k vs) else [])
Proof
  strip_tac >>
  `TAKE (SUC k) ts = TAKE k ts ++ [EL k ts]` by
    simp[arithmeticTheory.ADD1, TAKE_EL_SNOC, SNOC_APPEND] >>
  `TAKE (SUC k) vs = TAKE k vs ++ [EL k vs]` by
    simp[arithmeticTheory.ADD1, TAKE_EL_SNOC, SNOC_APPEND] >>
  simp[enc_head_upto_def, enc_tail_upto_def, enc_offset_upto_def,
       enc_prefix_head_append, enc_prefix_tail_append, enc_prefix_head_def, enc_prefix_tail_def]
QED

Theorem enc_prefix_head_length:
  !ts vs q. has_types ts vs ==>
    LENGTH (enc_prefix_head q ts vs) = head_lengths ts 0
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[enc_prefix_head_def, head_lengths_def] >>
  rpt strip_tac >> rename1 `has_type ty av` >>
  simp[SimpRHS, Once head_lengths_add] >>
  Cases_on `is_dynamic ty`
  >- simp[] >>
  drule (cj 1 enc_has_static_length) >> simp[]
QED

Theorem enc_prefix_assembly:
  !ts vs hl tl. has_types ts vs ==>
    enc_prefix_head (hl + tl) ts vs ++ enc_prefix_tail ts vs =
      enc_tuple hl tl ts vs [] []
Proof
  Induct_on `ts` >> Cases_on `vs` >> simp[enc_prefix_head_def,
    enc_prefix_tail_def, enc_tuple_cons_parts] >>
  rpt strip_tac >>
  qpat_x_assum `!vs hl tl. _` (fn th =>
    simp[GSYM th, enc_prefix_head_length,
         TAKE_APPEND1, DROP_APPEND, APPEND_ASSOC,
         TAKE_LENGTH_ID_rwt, DROP_LENGTH_TOO_LONG])
QED

Theorem enc_head_upto_length:
  has_types ts vs ==>
  LENGTH (enc_head_upto B ts vs k) = head_lengths (TAKE k ts) 0
Proof
  strip_tac >> simp[enc_head_upto_def] >>
  irule enc_prefix_head_length >>
  gvs[has_types_LIST_REL] >> irule LIST_REL_TAKE >> goal_assum drule
QED

Theorem enc_prefix_full:
  has_types ts vs ==>
  enc_head_upto B ts vs (LENGTH vs) ++ enc_tail_upto ts vs (LENGTH vs) =
    enc_tuple B 0 ts vs [] []
Proof
  strip_tac >>
  `LENGTH ts = LENGTH vs` by metis_tac[has_types_LIST_REL, LIST_REL_LENGTH] >>
  simp[enc_head_upto_def, enc_tail_upto_def, TAKE_LENGTH_ID_rwt] >>
  metis_tac[enc_prefix_assembly, arithmeticTheory.ADD_0]
QED

Theorem enc_prefix_tail_static:
  !ts vs. EVERY (\t. ~is_dynamic t) ts ==> enc_prefix_tail ts vs = []
Proof
  Induct_on `ts` >> Cases_on `vs` >> simp[enc_prefix_tail_def]
QED

Theorem enc_tail_upto_static:
  ~is_dynamic t ==> enc_tail_upto (REPLICATE N t) vs k = []
Proof
  strip_tac >> simp[enc_tail_upto_def] >>
  irule enc_prefix_tail_static >> simp[EVERY_TAKE]
QED

Theorem enc_head_upto_dynamic_length:
  has_types (REPLICATE N t) vs /\ k <= N /\ N = LENGTH vs /\
  is_dynamic t ==>
  LENGTH (enc_head_upto B (REPLICATE N t) vs k) = 32 * k
Proof
  strip_tac >>
  `TAKE k (REPLICATE N t) = REPLICATE k t` by
    (gvs[] >> simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
     AP_TERM_TAC >> simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  drule head_lengths_REPLICATE >>
  disch_then (qspec_then `0` assume_tac) >>
  drule enc_head_upto_length >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `B` mp_tac) >>
  qpat_x_assum `TAKE _ _ = _` kall_tac >>
  simp[] >> decide_tac
QED

Definition enc_prefix_mem_def:
  enc_prefix_mem p B ts vs k (s : venom_state) <=>
    mem_bytes_at p (LENGTH (enc_head_upto B ts vs k)) s.vs_memory =
      enc_head_upto B ts vs k /\
    mem_bytes_at (p + B) (LENGTH (enc_tail_upto ts vs k)) s.vs_memory =
      enc_tail_upto ts vs k
End

Theorem enc_prefix_mem_zero[simp]:
  enc_prefix_mem p B ts vs 0 s
Proof
  simp[enc_prefix_mem_def, mem_bytes_at_def]
QED

Theorem enc_prefix_mem_suc:
  has_types ts vs /\ k < LENGTH vs /\
  h = (if is_dynamic (EL k ts) then
         enc_number (Uint 256) (NumV (enc_offset_upto B ts vs k))
       else enc (EL k ts) (EL k vs)) /\
  z = (if is_dynamic (EL k ts) then enc (EL k ts) (EL k vs) else []) /\
  mem_bytes_at p (LENGTH (enc_head_upto B ts vs k)) s.vs_memory =
    enc_head_upto B ts vs k /\
  mem_bytes_at (p+B) (LENGTH (enc_tail_upto ts vs k)) s.vs_memory =
    enc_tail_upto ts vs k /\
  mem_bytes_at (p+LENGTH (enc_head_upto B ts vs k)) (LENGTH h) s.vs_memory =
    h /\
  mem_bytes_at (p+enc_offset_upto B ts vs k) (LENGTH z) s.vs_memory = z ==>
  enc_prefix_mem p B ts vs (SUC k) s
Proof
  rpt strip_tac >>
  `LENGTH ts = LENGTH vs` by metis_tac[has_types_LIST_REL, LIST_REL_LENGTH] >>
  drule_all enc_prefix_suc >> disch_then (qspec_then `B` strip_assume_tac) >>
  pure_rewrite_tac[enc_prefix_mem_def] >>
  pure_asm_rewrite_tac[] >>
  pure_rewrite_tac[LENGTH_APPEND, valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
  gvs[enc_offset_upto_def]
QED

Theorem enc_prefix_mem_exit_parts:
  has_types ts vs /\ enc_prefix_mem p B ts vs (LENGTH vs) s ==>
  mem_bytes_at p (head_lengths ts 0) s.vs_memory ++
    mem_bytes_at (p+B) (LENGTH (enc_tail_upto ts vs (LENGTH vs))) s.vs_memory =
    enc_tuple B 0 ts vs [] []
Proof
  strip_tac >>
  `LENGTH ts = LENGTH vs` by metis_tac[has_types_LIST_REL, LIST_REL_LENGTH] >>
  drule enc_prefix_full >> disch_then (qspec_then `B` mp_tac) >>
  drule enc_head_upto_length >>
  disch_then (qspecl_then [`LENGTH vs`, `B`] mp_tac) >>
  simp[TAKE_LENGTH_ID_rwt] >> rpt strip_tac >>
  gvs[enc_prefix_mem_def]
QED

Theorem enc_prefix_mem_exit:
  has_types ts vs /\ B = head_lengths ts 0 /\
  enc_prefix_mem p B ts vs (LENGTH vs) s ==>
  mem_bytes_at p (LENGTH (enc_tuple B 0 ts vs [] [])) s.vs_memory =
    enc_tuple B 0 ts vs [] []
Proof
  strip_tac >> drule_all enc_prefix_mem_exit_parts >>
  disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
  pure_rewrite_tac[LENGTH_APPEND, LENGTH_mem_bytes_at] >>
  disch_then (SUBST1_TAC o SYM) >>
  pure_rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
  metis_tac[enc_prefix_mem_exit_parts]
QED

(* K carries the global source, operand and frame facts; cell contents
   remain in the invariant rather than being frozen by K. *)
Definition enc_array_inv_def:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k (s : venom_state) <=>
    inv_ctx s /\ k <= LENGTH vs /\ enc_prefix_mem p B ts vs k s /\
    mem_word_at ip s.vs_memory = n2w k /\
    (case tail_cell of NONE => T
     | SOME c => mem_word_at c s.vs_memory = n2w (enc_offset_upto B ts vs k))
End

Theorem enc_array_inv_zero:
  inv_ctx s /\ mem_word_at ip s.vs_memory = 0w /\
  (case tail_cell of NONE => T
   | SOME c => mem_word_at c s.vs_memory = n2w B) ==>
  enc_array_inv inv_ctx p B ts vs ip tail_cell 0 s
Proof
  Cases_on `tail_cell` >> simp[enc_array_inv_def, enc_offset_upto_def]
QED

Theorem enc_array_inv_suc:
  inv_ctx s /\ SUC k <= LENGTH vs /\
  enc_prefix_mem p B ts vs (SUC k) s /\
  mem_word_at ip s.vs_memory = n2w (SUC k) /\
  (case tail_cell of NONE => T
   | SOME c =>
       mem_word_at c s.vs_memory = n2w (enc_offset_upto B ts vs (SUC k))) ==>
  enc_array_inv inv_ctx p B ts vs ip tail_cell (SUC k) s
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_array_inv_context:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s ==> inv_ctx s
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_array_inv_bound:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s ==> k <= LENGTH vs
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_array_inv_prefix:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s ==> enc_prefix_mem p B ts vs k s
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_array_inv_count:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s ==>
  mem_word_at ip s.vs_memory = n2w k
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_array_inv_tail:
  enc_array_inv inv_ctx p B ts vs ip (SOME c) k s ==>
  mem_word_at c s.vs_memory = n2w (enc_offset_upto B ts vs k)
Proof
  simp[enc_array_inv_def]
QED

Theorem enc_prefix_mem_jump[simp]:
  enc_prefix_mem p B ts vs k (jump_to l s) = enc_prefix_mem p B ts vs k s
Proof
  simp[enc_prefix_mem_def, jump_to_def]
QED

Theorem enc_array_inv_jump:
  (!s l. inv_ctx s ==> inv_ctx (jump_to l s)) /\
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s ==>
  enc_array_inv inv_ctx p B ts vs ip tail_cell k (jump_to l s)
Proof
  Cases_on `tail_cell` >> simp[enc_array_inv_def, jump_to_def]
QED

Theorem enc_eval_operand_jump[simp]:
  eval_operand op (jump_to l s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, jump_to_def]
QED

Theorem enc_frame_jump[simp]:
  enc_frame st st' lo top outs s0 (jump_to l s) =
  enc_frame st st' lo top outs s0 s
Proof
  simp[enc_frame_def, enc_scratch_def, jump_to_def, lookup_var_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Definition enc_array_header_def:
  enc_array_header inv_ctx p B ts vs ip tail_cell cnd k s <=>
    enc_array_inv inv_ctx p B ts vs ip tail_cell k s /\
    eval_operand cnd s = SOME (if k < LENGTH vs then 0w else 1w)
End

Theorem enc_array_header_jump:
  (!s l. inv_ctx s ==> inv_ctx (jump_to l s)) /\
  enc_array_header inv_ctx p B ts vs ip tail_cell cnd k s ==>
  enc_array_header inv_ctx p B ts vs ip tail_cell cnd k (jump_to l s)
Proof
  simp[enc_array_header_def] >> metis_tac[enc_array_inv_jump]
QED

Theorem enc_array_header_condition:
  enc_array_header inv_ctx p B ts vs ip tail_cell cnd k s ==>
  ?w. eval_operand cnd s = SOME w /\ (w = 0w <=> k < LENGTH vs)
Proof
  simp[enc_array_header_def] >> strip_tac >>
  Cases_on `k < LENGTH vs` >> gvs[]
QED

(* ===== Source and region boundaries ===== *)

Theorem enc_pre_bounds:
  enc_pre st st' ops lo top tv v src outs s ==>
  src + type_memory_size tv <= lo /\ lo <= top /\
  top < dimword (:256)
Proof
  rewrite_tac[enc_pre_def, enc_scratch_def] >> strip_tac >>
  rpt conj_tac >> decide_tac
QED

Theorem regions_disjoint_subregions:
  regions_disjoint (a, n) (b, m) /\
  a <= a' /\ a' + n' <= a + n /\
  b <= b' /\ b' + m' <= b + m ==>
  regions_disjoint (a', n') (b', m')
Proof
  rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem enc_alloca_inv_cong:
  (t : venom_state).vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s)
Proof
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem enc_scratch_cong:
  (t : venom_state).vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  (enc_scratch ids lo top t <=> enc_scratch ids lo top s)
Proof
  strip_tac >> drule_all enc_alloca_inv_cong >>
  simp[enc_scratch_def]
QED

Theorem enc_write_memory_allocas[simp]:
  (write_memory_with_expansion dst bytes s).vs_allocas = s.vs_allocas
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem enc_write_memory_alloca_next[simp]:
  (write_memory_with_expansion dst bytes s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem enc_mcopy_allocas[simp]:
  (mcopy dst src len s).vs_allocas = s.vs_allocas
Proof
  simp[mcopy_def]
QED

Theorem enc_mcopy_alloca_next[simp]:
  (mcopy dst src len s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[mcopy_def]
QED

Theorem enc_scratch_write_memory[simp]:
  enc_scratch ids lo top (write_memory_with_expansion dst bytes s) =
  enc_scratch ids lo top s
Proof
  irule enc_scratch_cong >> simp[]
QED

Theorem enc_scratch_mcopy[simp]:
  enc_scratch ids lo top (mcopy dst src len s) = enc_scratch ids lo top s
Proof
  irule enc_scratch_cong >> simp[]
QED

Theorem enc_scratch_alloca_bound:
  enc_scratch ids lo top s /\
  FLOOKUP s.vs_allocas j = SOME (c, n) ==> c + n <= top
Proof
  rewrite_tac[enc_scratch_def, venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem enc_alloca_missing_update:
  {j | j IN ids /\ FLOOKUP (allocas |+ (i, r)) j = NONE} =
  {j | j IN ids /\ FLOOKUP allocas j = NONE} DELETE i
Proof
  simp[pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem enc_alloca_missing_credit:
  FINITE ids /\ i IN ids /\ FLOOKUP allocas i = NONE ==>
  CARD {j | j IN ids /\ FLOOKUP allocas j = NONE} =
    SUC (CARD {j | j IN ids /\ FLOOKUP (allocas |+ (i, r)) j = NONE})
Proof
  strip_tac >> rewrite_tac[enc_alloca_missing_update] >>
  `FINITE {j | j IN ids /\ FLOOKUP allocas j = NONE}` by
    (irule pred_setTheory.SUBSET_FINITE >> qexists_tac `ids` >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  simp[pred_setTheory.CARD_DELETE] >>
  `i IN {j | j IN ids /\ FLOOKUP allocas j = NONE}` by simp[] >>
  `CARD {j | j IN ids /\ FLOOKUP allocas j = NONE} <> 0` by
    (drule pred_setTheory.CARD_EQ_0 >>
     metis_tac[pred_setTheory.NOT_IN_EMPTY]) >> decide_tac
QED

Theorem enc_alloca_inv_extend:
  alloca_inv s /\ FLOOKUP s.vs_allocas i = NONE ==>
  alloca_inv (s with <|
    vs_allocas := s.vs_allocas |+ (i, (s.vs_alloca_next, sz));
    vs_alloca_next := s.vs_alloca_next + sz |> )
Proof
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  qpat_assum `!aid base n. FLOOKUP _ aid = SOME (base,n) ==> _`
    (fn th => imp_res_tac th) >>
  gvs[] >> metis_tac[]
QED

Theorem enc_scratch_alloca_fresh:
  FINITE ids /\ i IN ids /\ enc_scratch ids lo top s /\
  FLOOKUP s.vs_allocas i = NONE ==>
  enc_scratch ids lo top (s with <|
    vs_allocas := s.vs_allocas |+ (i, (s.vs_alloca_next, 32));
    vs_alloca_next := s.vs_alloca_next + 32 |> )
Proof
  rpt strip_tac >>
  `alloca_inv s` by fs[enc_scratch_def] >>
  drule_all enc_alloca_inv_extend >>
  disch_then (qspec_then `32` assume_tac) >>
  drule_all enc_alloca_missing_credit >>
  disch_then (qspec_then `(s.vs_alloca_next,32)` assume_tac) >>
  qpat_x_assum `enc_scratch ids lo top s` mp_tac >>
  pure_rewrite_tac[enc_scratch_def, venom_state_accfupds, combinTheory.K_THM] >>
  strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every qx_gen_tac [`j`, `b`, `sz`] >> strip_tac >>
      qpat_x_assum `FLOOKUP (_ |+ _) j = SOME _` mp_tac >>
      Cases_on `i = j` >>
      asm_simp_tac (srw_ss()) [finite_mapTheory.FLOOKUP_UPDATE] >>
      strip_tac >> metis_tac[]) >>
  decide_tac
QED

Theorem enc_scratch_outside_disjoint:
  enc_scratch ids lo top s /\ j NOTIN ids /\ i IN ids /\
  FLOOKUP s.vs_allocas j = SOME (c, n) /\
  FLOOKUP s.vs_allocas i = SOME (b, m) ==>
  regions_disjoint (c, n) (b, m)
Proof
  rewrite_tac[enc_scratch_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
  `j <> i` by metis_tac[] >> metis_tac[]
QED

Theorem tuple_in_memory_append:
  !vs tvs off ws tws.
    LENGTH vs = LENGTH tvs ==>
    (tuple_in_memory (vs ++ ws) (tvs ++ tws) off mem <=>
     tuple_in_memory vs tvs off mem /\
     tuple_in_memory ws tws (off + SUM (MAP type_memory_size tvs)) mem)
Proof
  Induct >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  rpt strip_tac >> simp[CONJ_ASSOC]
QED

Theorem elems_in_memory_EL:
  !vs off k.
    elems_in_memory vs off tv mem /\ k < LENGTH vs ==>
    val_in_memory tv (EL k vs) (off + k * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >>
  rpt gen_tac >> Cases_on `k` >>
  simp[val_in_memory_def, arithmeticTheory.MULT_CLAUSES] >>
  rpt strip_tac >> rename1 `k' < LENGTH vs` >>
  first_x_assum drule >>
  disch_then (qspec_then `k'` mp_tac) >> simp[]
QED

Theorem mem_bytes_at_pointwise:
  (!a. off <= a /\ a < off + n ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 mem') ==>
  mem_bytes_at off n mem = mem_bytes_at off n mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `k < n` >>
  first_x_assum (qspec_then `off + k` mp_tac) >> simp[] >>
  disch_then (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem word_size_covers[local]:
  n <= 32 * word_size n
Proof
  simp[vfmConstantsTheory.word_size_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
  rewrite_tac[EVAL ``0 < 32``] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >> decide_tac
QED

Theorem value_has_type_val_wf_mutual[local]:
  (!tv v. value_has_type tv v ==> val_wf tv v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n kvs. sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!fts fields. struct_has_type fts fields ==> fields_val_wf fields fts)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >> rename1 `word_size cap` >>
  qspec_then `cap` mp_tac (GEN_ALL word_size_covers) >> decide_tac
QED

Theorem value_has_type_val_wf:
  !tv v. value_has_type tv v ==> val_wf tv v
Proof
  metis_tac[value_has_type_val_wf_mutual]
QED

Theorem val_in_memory_pointwise:
  val_in_memory tv v off mem /\ val_wf tv v /\
  (!a. off <= a /\ a < off + type_memory_size tv ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 mem') ==>
  val_in_memory tv v off mem'
Proof
  strip_tac >> irule val_in_memory_mem_agree >>
  goal_assum drule >> simp[] >>
  qexists_tac `type_memory_size tv` >> simp[] >>
  qexists_tac `mem` >> simp[] >>
  irule mem_bytes_at_pointwise >> simp[]
QED

Theorem typed_val_in_memory_pointwise:
  value_has_type tv v /\ val_in_memory tv v src mem /\
  (!a. src <= a /\ a < src + type_memory_size tv ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 mem') ==>
  val_in_memory tv v src mem'
Proof
  strip_tac >> drule value_has_type_val_wf >> strip_tac >>
  irule val_in_memory_pointwise >> goal_assum drule >> simp[] >>
  qexists_tac `mem` >> simp[]
QED

Theorem enc_frame_preserves_source:
  enc_frame st st' lo top outs s0 s /\
  value_has_type tv v /\ val_in_memory tv v src s0.vs_memory /\
  src + type_memory_size tv <= lo /\
  EVERY (regions_disjoint (src, type_memory_size tv)) outs ==>
  val_in_memory tv v src s.vs_memory
Proof
  strip_tac >> irule typed_val_in_memory_pointwise >>
  goal_assum drule >> simp[] >>
  qexists_tac `s0.vs_memory` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `enc_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[enc_frame_def, enc_scratch_def] >> strip_tac >>
  sym_tac >> first_x_assum irule >> reverse conj_tac
  >- (qpat_x_assum `EVERY _ outs` mp_tac >>
      rewrite_tac[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
      rename1 `MEM p outs` >> Cases_on `p` >>
      first_x_assum drule >>
      rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >>
      simp[] >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule_all >> decide_tac
QED

Theorem tuple_in_memory_EL:
  !vs tvs off k.
    LENGTH vs = LENGTH tvs /\ tuple_in_memory vs tvs off mem /\
    k < LENGTH vs ==>
    val_in_memory (EL k tvs) (EL k vs)
      (off + SUM (MAP type_memory_size (TAKE k tvs))) mem
Proof
  Induct >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  rpt gen_tac >> Cases_on `k` >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

(* ===== Scratch and frame calculus ===== *)

Theorem frag_ids_finite[simp]:
  FINITE (frag_ids st st')
Proof
  irule pred_setTheory.SUBSET_FINITE_I >> qexists_tac `count st'.cs_next_id` >>
  simp[frag_ids_def, pred_setTheory.SUBSET_DEF]
QED

Theorem frag_ids_same[simp]:
  frag_ids st st = {}
Proof
  simp[frag_ids_def, pred_setTheory.EXTENSION]
QED

Theorem frag_ids_split:
  st0.cs_next_id <= st1.cs_next_id /\
  st1.cs_next_id <= st2.cs_next_id ==>
  frag_ids st0 st2 = frag_ids st0 st1 UNION frag_ids st1 st2
Proof
  simp[frag_ids_def, pred_setTheory.EXTENSION] >> rpt strip_tac >> decide_tac
QED

Theorem frag_ids_disjoint:
  DISJOINT (frag_ids st0 st1) (frag_ids st1 st2)
Proof
  simp[frag_ids_def, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> decide_tac
QED

Theorem enc_frame_refl:
  enc_scratch (frag_ids st st') lo top s ==>
  enc_frame st st' lo top outs s s
Proof
  simp[enc_frame_def]
QED

(* Label equality is an execution invariant separate from enc_frame. *)
Theorem enc_frame_preserves_operand:
  enc_frame st st' lo top outs s0 s /\
  s.vs_labels = s0.vs_labels /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >> strip_tac >>
  gvs[] >> qpat_x_assum `enc_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[enc_frame_def] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem enc_missing_union_card:
  FINITE ids /\ FINITE rest /\ DISJOINT ids rest ==>
  CARD {i | i IN ids UNION rest /\ FLOOKUP s.vs_allocas i = NONE} =
  CARD {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE} +
  CARD {i | i IN rest /\ FLOOKUP s.vs_allocas i = NONE}
Proof
  strip_tac >>
  `{i | i IN ids UNION rest /\ FLOOKUP s.vs_allocas i = NONE} =
   {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE} UNION
   {i | i IN rest /\ FLOOKUP s.vs_allocas i = NONE}` by
    (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> irule pred_setTheory.CARD_UNION_DISJOINT >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  conj_tac
  >- (irule pred_setTheory.SUBSET_FINITE_I >> qexists_tac `ids` >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  irule pred_setTheory.SUBSET_FINITE_I >> qexists_tac `rest` >>
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem enc_scratch_restrict_reserved:
  FINITE ids /\ FINITE rest /\ DISJOINT ids rest /\
  enc_scratch (ids UNION rest) lo top s ==>
  enc_scratch ids lo
    (top - 32 * CARD {i | i IN rest /\ FLOOKUP s.vs_allocas i = NONE}) s
Proof
  strip_tac >> drule_all enc_missing_union_card >>
  disch_then (qspec_then `s` assume_tac) >>
  qpat_x_assum `enc_scratch _ _ _ _` mp_tac >>
  rewrite_tac[enc_scratch_def] >> strip_tac >>
  asm_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB] >>
  conj_tac >- decide_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!i b sz. _` (qspecl_then [`i`, `b`, `sz`] mp_tac) >> simp[]) >>
  qpat_x_assum `_ + 32 * _ <= top` mp_tac >>
  asm_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem enc_scratch_restore_reserved:
  FINITE ids /\ FINITE rest /\ DISJOINT ids rest /\
  enc_scratch (ids UNION rest) lo top s0 /\
  (!i. i IN rest ==> FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\
  enc_scratch ids lo
    (top - 32 * CARD {i | i IN rest /\ FLOOKUP s0.vs_allocas i = NONE}) s ==>
  enc_scratch (ids UNION rest) lo top s
Proof
  strip_tac >> drule_all enc_missing_union_card >>
  disch_then (fn th => map_every (fn q => qspec_then q assume_tac th) [`s`, `s0`]) >>
  `{i | i IN rest /\ FLOOKUP s.vs_allocas i = NONE} =
   {i | i IN rest /\ FLOOKUP s0.vs_allocas i = NONE}` by
    (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `enc_scratch (ids UNION rest) _ _ _` mp_tac >>
  qpat_x_assum `enc_scratch ids _ _ _` mp_tac >>
  rewrite_tac[enc_scratch_def] >> ntac 2 strip_tac >>
  asm_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB] >> conj_tac
  >- (ntac 2 (qpat_x_assum `CARD _ = _` kall_tac) >>
      rpt gen_tac >> strip_tac >>
      Cases_on `i IN rest`
      >- (qpat_x_assum `!i b sz. i IN ids UNION rest /\ _ ==> _`
            (qspecl_then [`i`, `b`, `sz`] mp_tac) >>
          qpat_x_assum `!i. i IN rest ==> _`
            (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_x_assum `!i b sz. i IN ids /\ _ ==> _`
        (qspecl_then [`i`, `b`, `sz`] mp_tac) >>
      qpat_x_assum `i IN ids UNION rest` mp_tac >> simp[]) >>
  qpat_x_assum `_ + 32 * _ <= top - _` mp_tac >>
  qpat_x_assum `_.vs_alloca_next + 32 * _ <= top` mp_tac >>
  asm_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem enc_frame_enlarge_outputs:
  enc_frame st st' lo top outs s0 s /\
  (!r. MEM r outs ==> MEM r larger) ==>
  enc_frame st st' lo top larger s0 s
Proof
  rewrite_tac[enc_frame_def] >> strip_tac >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qpat_x_assum `EVERY _ larger` mp_tac >>
  rewrite_tac[EVERY_MEM] >> metis_tac[]
QED

Theorem enc_frame_compose:
  st0.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= st2.cs_next_id /\
  (!x. not_fresh_at st0 x ==> not_fresh_at st1 x) /\
  enc_frame st0 st1 lo top1 outs1 s0 s1 /\
  enc_frame st1 st2 lo top2 outs2 s1 s2 /\
  enc_scratch (frag_ids st0 st2) lo top s2 ==>
  enc_frame st0 st2 lo top (outs1 ++ outs2) s0 s2
Proof
  strip_tac >> drule_all frag_ids_split >> strip_tac >>
  qpat_x_assum `enc_frame st0 _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `enc_frame st1 _ _ _ _ _ _` mp_tac >>
  rewrite_tac[enc_frame_def, EVERY_APPEND] >> ntac 2 strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >> conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a 1 s2.vs_memory = mem_bytes_at a 1 s1.vs_memory` by
        (qpat_x_assum `!a. _ ==> mem_bytes_at _ _ s2.vs_memory = _` irule >>
         simp[] >> rpt strip_tac >>
         qpat_x_assum `!i b sz. i IN frag_ids st0 st1 UNION _ /\ _ ==> _`
           irule >> simp[] >> goal_assum drule >> simp[]) >>
      asm_rewrite_tac[] >>
      qpat_x_assum `!a. _ ==> mem_bytes_at _ _ s1.vs_memory = _` irule >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!i b sz. i IN frag_ids st0 st1 UNION _ /\ _ ==> _`
        irule >> simp[] >> qexists_tac `i` >> simp[] >>
      qpat_x_assum `!i r. FLOOKUP s1.vs_allocas i = SOME r ==> _` irule >>
      simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem enc_frame_trans:
  enc_frame st st' lo top outs s0 s1 /\
  enc_frame st st' lo top outs s1 s2 ==>
  enc_frame st st' lo top outs s0 s2
Proof
  rewrite_tac[enc_frame_def] >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a 1 s2.vs_memory = mem_bytes_at a 1 s1.vs_memory` by
        (qpat_x_assum `!a. _ ==> mem_bytes_at _ _ s2.vs_memory = _` irule >>
         conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[] >>
      qpat_x_assum `!a. _ ==> mem_bytes_at _ _ s1.vs_memory = _` irule >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!i b sz. _ /\ _ ==> a < b \/ b + sz <= a` irule >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `!i r. FLOOKUP s1.vs_allocas i = SOME r ==> _` irule >>
      simp[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem enc_frame_cover_outputs:
  enc_frame st st' lo top outs s0 s /\
  (!b n. MEM (b,n) outs ==>
     ?b' n'. MEM (b',n') larger /\ b' <= b /\ b + n <= b' + n') ==>
  enc_frame st st' lo top larger s0 s
Proof
  rewrite_tac[enc_frame_def] >> strip_tac >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  qpat_x_assum `!b n. MEM (b,n) outs ==> _` drule >> strip_tac >>
  qpat_x_assum `EVERY _ larger` mp_tac >>
  rewrite_tac[EVERY_MEM, pairTheory.FORALL_PROD] >>
  disch_then drule >> simp[] >> decide_tac
QED


(* Padded observations are stable even when a disjoint write grows memory. *)
Theorem enc_write_memory_disjoint:
  !a n d bytes s.
    a + n <= d \/ d + LENGTH bytes <= a ==>
    mem_bytes_at a n (write_memory_with_expansion d bytes s).vs_memory =
    mem_bytes_at a n s.vs_memory
Proof
  rpt gen_tac >> disch_tac >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < d + LENGTH bytes - LENGTH s.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE d expanded` >>
      `d + LENGTH bytes <= LENGTH expanded` by simp[Abbr `expanded`] >>
      `mem_bytes_at a n
        (TAKE d expanded ++ bytes ++ DROP (d + LENGTH bytes) expanded) =
       mem_bytes_at a n expanded` by
        (simp[mem_bytes_at_def] >>
         irule valueEncodingProofsTheory.take_drop_splice_disjoint >> simp[]) >>
      simp[Abbr `expanded`, valueEncodingProofsTheory.mem_bytes_at_append_zero]) >>
  `d + LENGTH bytes <= LENGTH s.vs_memory` by simp[] >>
  simp[mem_bytes_at_def] >>
  irule valueEncodingProofsTheory.take_drop_splice_disjoint >> simp[]
QED

Theorem enc_mcopy_disjoint:
  !a n dst src len s.
    a + n <= dst \/ dst + len <= a ==>
    mem_bytes_at a n (mcopy dst src len s).vs_memory =
    mem_bytes_at a n s.vs_memory
Proof
  rpt strip_tac >> simp[mcopy_def] >>
  irule enc_write_memory_disjoint >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem enc_frame_write_memory:
  enc_scratch (frag_ids st st') lo top s ==>
  enc_frame st st' lo top [(dst, LENGTH bytes)] s
    (write_memory_with_expansion dst bytes s)
Proof
  strip_tac >> rewrite_tac[enc_frame_def] >>
  simp[enc_scratch_write_memory] >>
  conj_tac
  >- (rpt strip_tac >> irule enc_write_memory_disjoint >> gvs[]) >>
  simp[write_memory_with_expansion_def]
QED

Theorem enc_frame_mcopy:
  enc_scratch (frag_ids st st') lo top s ==>
  enc_frame st st' lo top [(dst, len)] s (mcopy dst src len s)
Proof
  strip_tac >> rewrite_tac[enc_frame_def] >>
  simp[enc_scratch_mcopy] >>
  conj_tac
  >- (rpt strip_tac >> irule enc_mcopy_disjoint >> gvs[]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem enc_frame_mstore:
  enc_scratch (frag_ids st st') lo top s ==>
  enc_frame st st' lo top [(dst, 32)] s (mstore dst w s)
Proof
  strip_tac >>
  `32 = LENGTH (word_to_bytes (w : bytes32) T)` by
    simp[byteTheory.LENGTH_word_to_bytes] >>
  once_asm_rewrite_tac[] >>
  rewrite_tac[valueEncodingProofsTheory.mstore_eq_wmwe] >>
  irule enc_frame_write_memory >> simp[]
QED

Theorem enc_frame_inst_idx[simp]:
  enc_frame st st' lo top outs s0 (s with vs_inst_idx := idx) =
  enc_frame st st' lo top outs s0 s
Proof
  simp[enc_frame_def, enc_scratch_def, lookup_var_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem enc_scratch_update_var[simp]:
  enc_scratch ids lo top (update_var y w s) = enc_scratch ids lo top s
Proof
  irule enc_scratch_cong >> simp[update_var_def]
QED

Theorem enc_exec_alloca_scratch:
  FINITE ids /\ inst.inst_id IN ids /\ enc_scratch ids lo top s /\
  inst.inst_outputs = [out] ==>
  ?b t. exec_alloca inst s (32w:256 word) = OK t /\
    lo <= b /\ b + 32 <= top /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32) /\
    lookup_var out t = SOME (n2w b) /\ enc_scratch ids lo top t
Proof
  rpt strip_tac >>
  `lo <= s.vs_alloca_next` by fs[enc_scratch_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all enc_scratch_alloca_fresh >> strip_tac >>
      qmatch_asmsub_abbrev_tac `enc_scratch ids lo top t` >>
      `FLOOKUP t.vs_allocas inst.inst_id =
         SOME (s.vs_alloca_next,32)` by
        simp[Abbr `t`, finite_mapTheory.FLOOKUP_UPDATE] >>
      drule_all enc_scratch_alloca_bound >> strip_tac >>
      qexistsl_tac [`s.vs_alloca_next`,
        `update_var out (n2w s.vs_alloca_next) t`] >>
      simp[exec_alloca_def, Abbr `t`, lookup_var_update_var,
           enc_scratch_update_var, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME r` >>
  PairCases_on `r` >>
  `lo <= r0 /\ r1 = 32` by
    (fs[enc_scratch_def] >> first_x_assum irule >> metis_tac[]) >>
  drule_all enc_scratch_alloca_bound >> strip_tac >>
  qexistsl_tac [`r0`, `update_var out (n2w r0) s`] >>
  simp[exec_alloca_def, lookup_var_update_var, enc_scratch_update_var,
       update_var_def]
QED

Theorem enc_exec_alloca_preserves:
  inst.inst_outputs = [out] /\ exec_alloca inst s alloc_size = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  (!j. j <> inst.inst_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j) /\
  (!j r. FLOOKUP s.vs_allocas j = SOME r ==> FLOOKUP t.vs_allocas j = SOME r) /\
  (!x. x <> out ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  asm_simp_tac (srw_ss()) [exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `inst.inst_id = j` >> gvs[]
QED

Theorem enc_compile_alloc_buffer_run:
  compile_alloc_buffer 32 st = (buf, st') /\
  FINITE ids /\ st.cs_next_id IN ids /\ enc_scratch ids lo top s ==>
  ?b t. run_inst_seq (emitted_insts st st') s = OK t /\
    same_blocks st st' /\ lo <= b /\ b + 32 <= top /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    enc_scratch ids lo top t /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    (!j. j <> st.cs_next_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j) /\
    (!j r. FLOOKUP s.vs_allocas j = SOME r ==> FLOOKUP t.vs_allocas j = SOME r) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def,
      AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts st st' = [inst]` >>
  `inst.inst_id = st.cs_next_id /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  `inst.inst_id IN ids` by simp[] >>
  drule_all enc_exec_alloca_scratch >> strip_tac >>
  drule_all enc_exec_alloca_preserves >> strip_tac >>
  qexistsl_tac [`b`, `t`] >>
  simp[run_inst_seq_def, eval_operand_def] >>
  conj_tac
  >- (qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
      simp[Abbr `inst`, step_inst_base_def, mk_inst_def]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> first_x_assum irule >>
  fs[not_fresh_at_def]
QED

Theorem enc_compile_alloc_buffer_frag:
  compile_alloc_buffer 32 st = (buf, st') /\
  st.cs_next_id IN frag_ids a z /\ a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a z) lo top s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. ?b. lo <= b /\ b + 32 <= top /\
       eval_operand buf.buf_operand s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,32) /\
       s.vs_memory = s0.vs_memory /\ s.vs_labels = s0.vs_labels /\
       enc_frame a z lo top outs s0 s) R
Proof
  rpt strip_tac >>
  `FINITE (frag_ids a z)` by simp[] >>
  drule_all enc_compile_alloc_buffer_run >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[same_blocks_def] >>
  reverse conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
           comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule emitted_insts_emit_op >> strip_tac >>
      drule emit_op_extends >> strip_tac >>
      gvs[same_blocks_def, mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (Cases_on `buf.buf_operand` >>
      gvs[eval_operand_def, lookup_var_def]) >>
  simp[enc_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at st x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

(* Named compiler phases keep loop consumers above the monadic plumbing. *)
Definition enc_static_loop_init_def:
  enc_static_loop_init =
    do buf <- compile_alloc_buffer 32;
       emit_void MSTORE [buf.buf_operand; Lit 0w];
       hdr <- fresh_label "enc_dyn_hdr";
       body <- fresh_label "enc_dyn_body";
       exit <- fresh_label "enc_dyn_exit";
       return (buf.buf_operand, hdr, body, exit)
    od
End

Definition enc_static_loop_header_def:
  enc_static_loop_header count_ptr len_op =
    do i <- emit_op MLOAD [count_ptr];
       cmp <- emit_op LT [i; len_op];
       emit_op ISZERO [cmp]
    od
End

Definition enc_static_loop_body_def:
  enc_static_loop_body dst src ei asz msz count_ptr =
    do i <- emit_op MLOAD [count_ptr];
       src_data <- emit_op ADD [src; Lit 32w];
       src_off <- emit_op MUL [i; Lit (n2w msz)];
       child_src <- emit_op ADD [src_data; src_off];
       dst_data <- emit_op ADD [dst; Lit 32w];
       dst_off <- emit_op MUL [i; Lit (n2w asz)];
       child_dst <- emit_op ADD [dst_data; dst_off];
       compile_abi_encode_static_info child_dst child_src ei;
       next <- emit_op ADD [i; Lit 1w];
       emit_void MSTORE [count_ptr; next]
    od
End

Definition enc_static_loop_exit_def:
  enc_static_loop_exit src asz =
    do len <- emit_op MLOAD [src];
       payload <- emit_op MUL [len; Lit (n2w asz)];
       emit_op ADD [Lit 32w; payload]
    od
End

Theorem enc_comp_bind_return[local]:
  comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem enc_static_loop_phases:
  compile_abi_encode_dyn_static_loop dst src ei asz msz len_op =
    do phase <- enc_static_loop_init;
       let (count_ptr,hdr,body,exit) = phase in
       do emit_inst JMP [Label hdr] [];
          new_block hdr;
          done_op <- enc_static_loop_header count_ptr len_op;
          emit_inst JNZ [done_op; Label exit; Label body] [];
          new_block body;
          enc_static_loop_body dst src ei asz msz count_ptr;
          emit_inst JMP [Label hdr] [];
          new_block exit;
          enc_static_loop_exit src asz
       od
    od
Proof
  simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_def, enc_static_loop_init_def,
       enc_static_loop_header_def, enc_static_loop_body_def,
       enc_static_loop_exit_def, comp_ignore_bind_def, comp_bind_assoc,
       enc_comp_bind_return, LET_THM]
QED

Definition enc_static_loop_edges_def:
  enc_static_loop_edges hdr body exit cnd
      (si,s1,sh,sj,s2,sb,se,s3,sx) <=>
    emit_inst JMP [Label hdr] [] si = ((),s1) /\
    new_block hdr s1 = (s1.cs_current_bb,sh) /\
    emit_inst JNZ [cnd; Label exit; Label body] [] sj = ((),s2) /\
    new_block body s2 = (s2.cs_current_bb,sb) /\
    emit_inst JMP [Label hdr] [] se = ((),s3) /\
    new_block exit s3 = (s3.cs_current_bb,sx)
End

Theorem enc_static_loop_decompose:
  compile_abi_encode_dyn_static_loop dst src ei asz msz len_op st = (op,st') ==>
  ?count_ptr hdr body exit cnd si s1 sh sj s2 sb se s3 sx.
    enc_static_loop_init st = ((count_ptr,hdr,body,exit),si) /\
    enc_static_loop_header count_ptr len_op sh = (cnd,sj) /\
    enc_static_loop_body dst src ei asz msz count_ptr sb = ((),se) /\
    enc_static_loop_exit src asz sx = (op,st') /\
    enc_static_loop_edges hdr body exit cnd (si,s1,sh,sj,s2,sb,se,s3,sx)
Proof
  rpt gen_tac >>
  simp[enc_static_loop_phases, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >>
       gvs[comp_bind_def, comp_ignore_bind_def]) >>
  strip_tac >> gvs[] >>
  simp[enc_static_loop_edges_def] >>
  gvs[new_block_def]
QED

Theorem enc_static_info_appends:
  cs_appends (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >>
  simp[compile_abi_encode_static_info_def, compile_abi_encode_static_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  rw[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem enc_static_loop_phase_appends:
  cs_appends enc_static_loop_init /\
  cs_appends (enc_static_loop_header count_ptr len_op) /\
  cs_appends (enc_static_loop_body dst src ei asz msz count_ptr) /\
  cs_appends (enc_static_loop_exit src asz)
Proof
  `cs_appends (compile_alloc_buffer 32)` by
    (simp[contextTheory.compile_alloc_buffer_def] >>
     irule cs_appends_bind >>
     rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[enc_static_loop_init_def, enc_static_loop_header_def,
       enc_static_loop_body_def, enc_static_loop_exit_def] >>
  rpt conj_tac >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, cs_appends_prims,
          enc_static_info_appends]) >>
  rw[cs_appends_emit_helpers, cs_appends_return, cs_appends_prims,
     enc_static_info_appends]
QED

Theorem enc_static_info_frontiers:
  compile_abi_encode_static_info dst src ei st = (op,st') ==>
  st.cs_next_id <= st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var
Proof
  Cases_on `ei` >>
  simp[compile_abi_encode_static_info_def, compile_abi_encode_static_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem enc_static_loop_header_frontiers:
  enc_static_loop_header count_ptr len_op st = (op,st') ==>
  st'.cs_next_id = st.cs_next_id + 3 /\
  st'.cs_next_var = st.cs_next_var + 3
Proof
  simp[enc_static_loop_header_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem enc_static_loop_exit_frontiers:
  enc_static_loop_exit src asz st = (op,st') ==>
  st'.cs_next_id = st.cs_next_id + 3 /\
  st'.cs_next_var = st.cs_next_var + 3
Proof
  simp[enc_static_loop_exit_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem enc_static_loop_body_frontiers:
  enc_static_loop_body dst src ei asz msz count_ptr st = (u,st') ==>
  st.cs_next_id + 9 <= st'.cs_next_id /\
  st.cs_next_var + 8 <= st'.cs_next_var
Proof
  rpt gen_tac >>
  simp[enc_static_loop_body_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac (cj 3 emitted_insts_emit_op) >>
  imp_res_tac (cj 4 emitted_insts_emit_op) >>
  imp_res_tac (cj 2 emitted_insts_emit_void) >>
  imp_res_tac (cj 3 emitted_insts_emit_void) >>
  imp_res_tac enc_static_info_frontiers >> decide_tac
QED

Theorem enc_static_loop_init_frontiers:
  enc_static_loop_init st = ((count_ptr,hdr,body_lbl,exit),st') ==>
  st'.cs_next_id = st.cs_next_id + 2 /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  count_ptr = Var (STRING #"%" (toString st.cs_next_var))
Proof
  simp[enc_static_loop_init_def, contextTheory.compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       fresh_label_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem enc_new_block_frontiers[local]:
  new_block lbl st = (old_lbl,st') ==>
  st'.cs_next_id = st.cs_next_id /\ st'.cs_next_var = st.cs_next_var
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[]
QED

Theorem enc_static_loop_edges_frontiers:
  enc_static_loop_edges hdr body_lbl exit cnd (si,s1,sh,sj,s2,sb,se,s3,sx) ==>
  sh.cs_next_id = si.cs_next_id + 1 /\ sh.cs_next_var = si.cs_next_var /\
  sb.cs_next_id = sj.cs_next_id + 1 /\ sb.cs_next_var = sj.cs_next_var /\
  sx.cs_next_id = se.cs_next_id + 1 /\ sx.cs_next_var = se.cs_next_var
Proof
  simp[enc_static_loop_edges_def] >> strip_tac >>
  imp_res_tac (cj 2 emitted_insts_emit_inst) >>
  imp_res_tac (cj 3 emitted_insts_emit_inst) >>
  imp_res_tac enc_new_block_frontiers >> simp[]
QED

Theorem enc_static_loop_phase_extends:
  (enc_static_loop_init st = (phase,si) ==> cs_extends st si) /\
  (enc_static_loop_header count_ptr len_op sh = (cnd,sj) ==> cs_extends sh sj) /\
  (enc_static_loop_body dst src ei asz msz count_ptr sb = (u,se) ==> cs_extends sb se) /\
  (enc_static_loop_exit src asz sx = (op,st') ==> cs_extends sx st')
Proof
  mp_tac enc_static_loop_phase_appends >>
  simp[cs_appends_def] >> metis_tac[]
QED

Theorem enc_static_loop_phase_safety:
  enc_static_loop_init st = ((count_ptr,hdr,body_lbl,exit),si) /\
  enc_static_loop_header count_ptr len_op sh = (cnd,sj) /\
  enc_static_loop_body dst src ei asz msz count_ptr sb = (u,se) /\
  enc_static_loop_exit src asz sx = (op,st') /\
  enc_static_loop_edges hdr body_lbl exit cnd (si,s1,sh,sj,s2,sb,se,s3,sx) ==>
  st.cs_next_id IN frag_ids st st' /\
  frag_ids si sx SUBSET frag_ids st st' /\
  st.cs_next_var <= sh.cs_next_var /\
  sh.cs_next_var <= sb.cs_next_var /\
  sb.cs_next_var <= sx.cs_next_var /\
  sx.cs_next_var <= st'.cs_next_var /\
  (!x. count_ptr = Var x ==> not_fresh_at sh x) /\
  (!x. count_ptr = Var x ==> not_fresh_at sb x) /\
  (!x. count_ptr = Var x ==> not_fresh_at sx x)
Proof
  strip_tac >>
  drule enc_static_loop_init_frontiers >> strip_tac >>
  drule enc_static_loop_header_frontiers >> strip_tac >>
  drule enc_static_loop_body_frontiers >> strip_tac >>
  drule enc_static_loop_exit_frontiers >> strip_tac >>
  drule enc_static_loop_edges_frontiers >> strip_tac >>
  simp[frag_ids_def, pred_setTheory.SUBSET_DEF, not_fresh_at_def,
       ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem enc_frame_update_var:
  (!x. not_fresh_at st x ==> x <> y) /\
  enc_frame st st' lo top outs s0 s ==>
  enc_frame st st' lo top outs s0 (update_var y w s)
Proof
  simp[enc_frame_def, lookup_var_update_var, enc_scratch_update_var,
       update_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem enc_mstore_update_var:
  mstore dst v (update_var y w s) = update_var y w (mstore dst v s)
Proof
  simp[mstore_def, update_var_def]
QED

Theorem compile_abi_encode_copy_frame_frag:
  compile_abi_encode_to_buf dst src (AbiCopy mem_size) st = (op, st') /\
  mem_size < dimword (:256) /\
  eval_operand dst s0 = SOME dst_w /\ 
  eval_operand src s0 = SOME src_w /\
  enc_scratch (frag_ids st st') lo top s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. s.vs_memory = (mcopy (w2n dst_w) (w2n src_w) mem_size s0).vs_memory /\
         s.vs_labels = s0.vs_labels /\
         eval_operand op s = SOME (n2w mem_size) /\
         enc_frame st st' lo top [(w2n dst_w, mem_size)] s0 s) R
Proof
  rpt strip_tac >>
  gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule emit_void_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[same_blocks_def] >>
  reverse conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      gvs[same_blocks_def, mk_inst_def, is_terminator_def]) >>
  disj1_tac >>
  qexists_tac `mcopy (w2n dst_w) (w2n src_w) mem_size s0` >>
  conj_tac
  >- (drule emit_void_MCOPY_run >> simp[eval_operand_def]) >>
  simp[eval_operand_def, enc_frame_mcopy] >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem enc_eval_operand_update_old:
  (!y. op = Var y ==> not_fresh_at st y) /\ st.cs_next_var <= n ==>
  eval_operand op (update_var (STRING #"%" (toString n)) w s) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_update_var,
                           update_var_def, lookup_var_def] >>
  metis_tac[not_fresh_at_def]
QED

Theorem enc_emit_op_run_frame:
  emit_op opc args st = (op, st') /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
       eval_operand op s' = SOME w /\ same_blocks st st' /\
       s'.vs_memory = s.vs_memory /\ s'.vs_labels = s.vs_labels /\
       (!old. (!y. old = Var y ==> not_fresh_at st y) ==>
          eval_operand old s' = eval_operand old s) /\
       enc_frame a b lo top outs s s'
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) w s` >>
  simp[run_inst_seq_def, eval_operand_update_var, same_blocks_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule enc_eval_operand_update_old >>
      qexists_tac `st` >> simp[]) >>
  irule enc_frame_update_var >>
  simp[not_fresh_at_def, enc_frame_refl] >> decide_tac
QED

Theorem enc_emit_mcopy_run_frame:
  emit_void MCOPY [dst; src; sz] st = ((), st') /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand sz s = SOME nw /\
  enc_scratch (frag_ids a b) lo top s /\
  MEM (out_base,out_len) outs /\ out_base <= w2n dw /\
  w2n dw + w2n nw <= out_base + out_len ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
       s'.vs_memory = (mcopy (w2n dw) (w2n sw) (w2n nw) s).vs_memory /\
       same_blocks st st' /\ s'.vs_labels = s.vs_labels /\
       (!op. eval_operand op s' = eval_operand op s) /\
       enc_frame a b lo top outs s s'
Proof
  rpt strip_tac >> drule_all emit_void_MCOPY_run >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  qexists_tac `mcopy (w2n dw) (w2n sw) (w2n nw) s` >>
  simp[] >> conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (Cases >> simp[eval_operand_def, lookup_var_def, mcopy_def,
                    write_memory_with_expansion_def]) >>
  irule enc_frame_cover_outputs >>
  qexists_tac `[(w2n dw, w2n nw)]` >>
  simp[enc_frame_mcopy] >> metis_tac[]
QED

Theorem enc_emit_mstore_run_frame:
  emit_void MSTORE [dst; value] st = ((), st') /\
  eval_operand dst s = SOME dw /\ eval_operand value s = SOME w /\
  enc_scratch (frag_ids a b) lo top s /\
  MEM (out_base,out_len) outs /\ out_base <= w2n dw /\
  w2n dw + 32 <= out_base + out_len ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
       s'.vs_memory = (mstore (w2n dw) w s).vs_memory /\
       same_blocks st st' /\ s'.vs_labels = s.vs_labels /\
       (!op. eval_operand op s' = eval_operand op s) /\
       enc_frame a b lo top outs s s'
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  qexists_tac `mstore (w2n dw) w s` >>
  conj_tac
  >- simp[run_inst_seq_def, step_inst_base_def, exec_write2_def, mk_inst_def] >>
  simp[] >> conj_tac
  >- (Cases >> simp[eval_operand_def, lookup_var_def, mstore_def]) >>
  irule enc_frame_cover_outputs >>
  qexists_tac `[(w2n dw, 32)]` >>
  simp[enc_frame_mstore] >> metis_tac[]
QED

Theorem enc_round32_bounds:
  l <= 32 * ((l + 31) DIV 32) /\
  32 * ((l + 31) DIV 32) < l + 32
Proof
  `(l + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `l + 31` mp_tac) >> decide_tac
QED

Theorem enc_round32_word:
  l + 31 < dimword (:256) ==>
  (n2w (l + 31) : bytes32) &&
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
  n2w (32 * ((l + 31) DIV 32))
Proof
  strip_tac >>
  `0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w : bytes32 =
     UINT_MAXw << 5` by EVAL_TAC >>
  asm_rewrite_tac[GSYM alignmentTheory.align_bitwise_and] >>
  simp[alignmentTheory.align_w2n, arithmeticTheory.MULT_COMM]
QED

Theorem enc_mem_bytes_subrange:
  start + n <= len ==>
  mem_bytes_at (off + start) n mem =
    TAKE n (DROP start (mem_bytes_at off len mem))
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  `x + start < len` by decide_tac >>
  simp[EL_TAKE, EL_DROP] >>
  `start + x < len` by decide_tac >>
  asm_simp_tac bool_ss [valueEncodingProofsTheory.EL_mem_bytes_at,
                       arithmeticTheory.ADD_ASSOC]
QED

Theorem enc_mstore_zero_subrange:
  start + n <= 32 ==>
  mem_bytes_at (off + start) n (mstore off 0w s).vs_memory =
    REPLICATE n 0w
Proof
  strip_tac >>
  `word_to_bytes (0w:bytes32) T = REPLICATE 32 0w` by EVAL_TAC >>
  drule enc_mem_bytes_subrange >>
  disch_then (qspecl_then [`off`, `(mstore off 0w s).vs_memory`] mp_tac) >>
  simp[mem_bytes_at_mstore_same, DROP_REPLICATE] >>
  disch_then SUBST1_TAC >> irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ, EL_TAKE, EL_REPLICATE]
QED

Theorem enc_prezero_source:
  l <= r /\ r <= l + 32 /\
  regions_disjoint (src,32+l) (dst,32+r) ==>
  mem_bytes_at src (32+l) (mstore (dst+r) 0w s).vs_memory =
    mem_bytes_at src (32+l) s.vs_memory
Proof
  strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem enc_prezero_copy_layout:
  l <= r /\ r <= l + 32 /\
  regions_disjoint (src,32+l) (dst,32+r) ==>
  mem_bytes_at dst (32+r)
    (mcopy dst src (32+l) (mstore (dst+r) 0w s)).vs_memory =
  mem_bytes_at src (32+l) s.vs_memory ++ REPLICATE (r-l) 0w
Proof
  strip_tac >>
  `32+r = (32+l) + (r-l)` by decide_tac >>
  once_asm_rewrite_tac[] >>
  CONV_TAC (LAND_CONV (REWR_CONV
    valueEncodingProofsTheory.mem_bytes_at_split_padded)) >>
  `mem_bytes_at dst (32+l)
     (mcopy dst src (32+l) (mstore (dst+r) 0w s)).vs_memory =
   mem_bytes_at src (32+l) s.vs_memory` by
    (rewrite_tac[mem_bytes_at_def, mcopy_padded_read] >>
     rewrite_tac[GSYM mem_bytes_at_def] >>
     irule enc_prezero_source >> simp[]) >>
  asm_rewrite_tac[] >> AP_TERM_TAC >>
  `mem_bytes_at (dst+(32+l)) (r-l)
     (mcopy dst src (32+l) (mstore (dst+r) 0w s)).vs_memory =
   mem_bytes_at (dst+(32+l)) (r-l) (mstore (dst+r) 0w s).vs_memory` by
    (irule enc_mcopy_disjoint >> simp[]) >>
  asm_rewrite_tac[] >>
  `dst + (32+l) = (dst+r) + (32+l-r)` by decide_tac >>
  asm_rewrite_tac[] >> irule enc_mstore_zero_subrange >> decide_tac
QED

Theorem enc_emit_add_const_run_frame:
  emit_op ADD [Lit (n2w k); arg] st = (op, st1) /\
  eval_operand arg s = SOME (n2w l) /\
  a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s1. run_inst_seq (emitted_insts st st1) s = OK s1 /\
       eval_operand op s1 = SOME (n2w (k+l)) /\
       same_blocks st st1 /\ s1.vs_memory = s.vs_memory /\
       s1.vs_labels = s.vs_labels /\
       (!old. (!y. old = Var y ==> not_fresh_at st y) ==>
         eval_operand old s1 = eval_operand old s) /\
       enc_frame a b lo top outs s s1
Proof
  strip_tac >> irule enc_emit_op_run_frame >>
  simp[] >> qexistsl_tac [`[Lit (n2w k); arg]`, `ADD`] >> simp[] >>
  pure_once_rewrite_tac[GSYM wordsTheory.word_add_n2w] >>
  irule step_ADD >> simp[eval_operand_lit]
QED

Theorem enc_emit_and_const_run_frame:
  emit_op AND [Lit mask; arg] st = (op, st1) /\
  eval_operand arg s = SOME w /\
  a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s1. run_inst_seq (emitted_insts st st1) s = OK s1 /\
       eval_operand op s1 = SOME (mask && w) /\
       same_blocks st st1 /\ s1.vs_memory = s.vs_memory /\
       s1.vs_labels = s.vs_labels /\
       (!old. (!y. old = Var y ==> not_fresh_at st y) ==>
         eval_operand old s1 = eval_operand old s) /\
       enc_frame a b lo top outs s s1
Proof
  strip_tac >> irule enc_emit_op_run_frame >>
  simp[] >> qexistsl_tac [`[Lit mask; arg]`, `AND`] >> simp[] >>
  irule step_AND >> simp[eval_operand_lit]
QED

Theorem enc_bytes_round_run:
  emit_op ADD [Lit 31w; len_op] st = (ceil_op, st1) /\
  emit_op AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
     ceil_op] st1 = (round_op, st2) /\
  eval_operand len_op s = SOME (n2w l) /\ l+31 < dimword (:256) /\
  a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s2. run_inst_seq (emitted_insts st st2) s = OK s2 /\
       eval_operand round_op s2 = SOME (n2w (32*((l+31) DIV 32))) /\
       same_blocks st st2 /\
       st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2 /\
       s2.vs_memory = s.vs_memory /\ s2.vs_labels = s.vs_labels /\
       (!old. (!y. old = Var y ==> not_fresh_at st y) ==>
         eval_operand old s2 = eval_operand old s) /\
       enc_frame a b lo top outs s s2
Proof
  strip_tac >>
  drule_all enc_emit_add_const_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK s1` >>
  `enc_scratch (frag_ids a b) lo top s1` by fs[enc_frame_def] >>
  `a.cs_next_var <= st1.cs_next_var` by
    (rev_drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  drule_all enc_emit_and_const_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s1 = OK s2` >>
  drule emit_op_extends >> strip_tac >>
  rev_drule emit_op_extends >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> conj_tac
  >- (once_rewrite_tac[wordsTheory.WORD_AND_COMM] >>
      irule enc_round32_word >> simp[]) >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `!y. old = Var y ==> not_fresh_at st1 y` by
        (rev_drule emitted_insts_emit_op >> strip_tac >>
         rpt strip_tac >>
         qpat_x_assum `!y. old = Var y ==> _` drule >>
         simp[not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >>
      metis_tac[]) >>
  irule enc_frame_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem enc_bytes_load_round_run:
  emit_op MLOAD [src] st = (len_op, st1) /\
  emit_op ADD [Lit 31w; len_op] st1 = (ceil_op, st2) /\
  emit_op AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
     ceil_op] st2 = (round_op, st3) /\
  eval_operand src s = SOME src_w /\
  mem_word_at (w2n src_w) s.vs_memory = n2w l /\
  l+31 < dimword (:256) /\ a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s3. run_inst_seq (emitted_insts st st3) s = OK s3 /\
       eval_operand len_op s3 = SOME (n2w l) /\
       eval_operand round_op s3 = SOME (n2w (32*((l+31) DIV 32))) /\
       same_blocks st st3 /\
       st3.cs_current_insts = st.cs_current_insts ++ emitted_insts st st3 /\
       s3.vs_memory = s.vs_memory /\ s3.vs_labels = s.vs_labels /\
       enc_frame a b lo top outs s s3
Proof
  strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
      [STRING #"%" (toString st.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString st.cs_next_var)) (n2w l) s)` by
    (qpat_x_assum `mem_word_at _ _ = _` (mp_tac o REWRITE_RULE [mem_word_at_eq_mload]) >>
     disch_then (SUBST1_TAC o SYM) >> irule step_MLOAD >> simp[]) >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK s1` >>
  `enc_scratch (frag_ids a b) lo top s1` by fs[enc_frame_def] >>
  `a.cs_next_var <= st1.cs_next_var` by
    (rev_drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  drule_all enc_bytes_round_run >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st1 st3) s1 = OK s3` >>
  `!y. len_op = Var y ==> not_fresh_at st1 y` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  rev_drule emit_op_extends >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  irule enc_frame_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem enc_bytes_prefix_run:
  emit_op MLOAD [src] st = (len_op, st1) /\
  emit_op ADD [Lit 31w; len_op] st1 = (ceil_op, st2) /\
  emit_op AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
     ceil_op] st2 = (round_op, st3) /\
  emit_op ADD [dst; round_op] st3 = (ptr_op, st4) /\
  eval_operand src s = SOME src_w /\ eval_operand dst s = SOME dst_w /\
  (!y. dst = Var y ==> not_fresh_at a y) /\
  mem_word_at (w2n src_w) s.vs_memory = n2w l /\
  l+31 < dimword (:256) /\ a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s4. run_inst_seq (emitted_insts st st4) s = OK s4 /\
       eval_operand len_op s4 = SOME (n2w l) /\
       eval_operand ptr_op s4 = SOME (dst_w + n2w (32*((l+31) DIV 32))) /\
       same_blocks st st4 /\
       st4.cs_current_insts = st.cs_current_insts ++ emitted_insts st st4 /\
       s4.vs_memory = s.vs_memory /\ s4.vs_labels = s.vs_labels /\
       enc_frame a b lo top outs s s4
Proof
  strip_tac >> drule_all enc_bytes_load_round_run >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st st3) s = OK s3` >>
  `eval_operand dst s3 = SOME dst_w` by
    (drule_all enc_frame_preserves_operand >> simp[]) >>
  `a.cs_next_var <= st3.cs_next_var /\
   (!y. len_op = Var y ==> not_fresh_at st3 y)` by
    (imp_res_tac emitted_insts_emit_op >> simp[not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `enc_scratch (frag_ids a b) lo top s3` by fs[enc_frame_def] >>
  `step_inst_base (mk_inst st3.cs_next_id ADD [dst; round_op]
      [STRING #"%" (toString st3.cs_next_var)]) s3 =
    OK (update_var (STRING #"%" (toString st3.cs_next_var))
      (dst_w + n2w (32*((l+31) DIV 32))) s3)` by
    (irule step_ADD >> simp[]) >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st3 st4) s3 = OK s4` >>
  drule emit_op_extends >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `s4` >> simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  irule enc_frame_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem enc_bytes_write_run:
  emit_void MSTORE [ptr_op; Lit 0w] st = ((), st1) /\
  emit_op ADD [Lit 32w; len_op] st1 = (copy_len, st2) /\
  emit_void MCOPY [dst; src; copy_len] st2 = ((), st3) /\
  eval_operand ptr_op s = SOME (n2w (d+r)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand src s = SOME (n2w p) /\
  eval_operand len_op s = SOME (n2w l) /\
  (!arg y. MEM arg [dst; src; len_op] /\ arg = Var y ==> not_fresh_at st1 y) /\
  d+32+r < dimword (:256) /\ p < dimword (:256) /\ l <= r /\
  a.cs_next_var <= st1.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s3. run_inst_seq (emitted_insts st st3) s = OK s3 /\
       s3.vs_memory = (mcopy d p (32+l) (mstore (d+r) 0w s)).vs_memory /\
       eval_operand len_op s3 = SOME (n2w l) /\
       same_blocks st st3 /\
       st3.cs_current_insts = st.cs_current_insts ++ emitted_insts st st3 /\
       s3.vs_labels = s.vs_labels /\
       enc_frame a b lo top [(d,32+r)] s s3
Proof
  strip_tac >>
  `w2n (n2w (d+r):bytes32) = d+r /\
   w2n (n2w d:bytes32) = d /\ w2n (n2w (32+l):bytes32) = 32+l` by
    (`d+r < dimword (:256) /\ d < dimword (:256) /\
      32+l < dimword (:256)` by decide_tac >> simp[]) >>
  `?base len. MEM (base,len) [(d,32+r)] /\
     base <= w2n (n2w (d+r):bytes32) /\
     w2n (n2w (d+r):bytes32) + 32 <= base + len` by simp[] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_lit] >>
  drule_all enc_emit_mstore_run_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK s1` >>
  `enc_scratch (frag_ids a b) lo top s1` by fs[enc_frame_def] >>
  `eval_operand len_op s1 = SOME (n2w l)` by simp[] >>
  qpat_x_assum `eval_operand len_op s = _` kall_tac >>
  drule_all enc_emit_add_const_run_frame >>
  disch_then (qspec_then `[(d,32+r)]` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d) /\
   eval_operand src s2 = SOME (n2w p) /\
   eval_operand len_op s2 = SOME (n2w l)` by fs[] >>
  `enc_scratch (frag_ids a b) lo top s2` by fs[enc_frame_def] >>
  `?base len. MEM (base,len) [(d,32+r)] /\
     base <= w2n (n2w d:bytes32) /\
     w2n (n2w d:bytes32) + w2n (n2w (32+l):bytes32) <= base + len` by simp[] >>
  drule_all enc_emit_mcopy_run_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) s2 = OK s3` >>
  drule emit_op_extends >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  rev_drule emit_void_extends >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st st2) s = OK s2` by simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts st st1) s = _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >> conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- fs[same_blocks_def] >>
  `enc_frame a b lo top [(d,32+r)] s s2` by
    (irule enc_frame_trans >> qexists_tac `s1` >> simp[]) >>
  irule enc_frame_trans >> qexists_tac `s2` >>
  `r+32 = 32+r` by decide_tac >> pure_asm_rewrite_tac [] >> simp[]
QED

Theorem enc_bytes_size_run:
  emit_op ADD [Lit 31w; len_op] st = (ceil_op, st1) /\
  emit_op AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
     ceil_op] st1 = (round_op, st2) /\
  emit_op ADD [Lit 32w; round_op] st2 = (size_op, st3) /\
  eval_operand len_op s = SOME (n2w l) /\ l+31 < dimword (:256) /\
  a.cs_next_var <= st.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?s3. run_inst_seq (emitted_insts st st3) s = OK s3 /\
       eval_operand size_op s3 = SOME (n2w (32+32*((l+31) DIV 32))) /\
       same_blocks st st3 /\
       st3.cs_current_insts = st.cs_current_insts ++ emitted_insts st st3 /\
       s3.vs_memory = s.vs_memory /\ s3.vs_labels = s.vs_labels /\
       enc_frame a b lo top outs s s3
Proof
  strip_tac >> drule_all enc_bytes_round_run >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st st2) s = OK s2` >>
  `a.cs_next_var <= st2.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  `enc_scratch (frag_ids a b) lo top s2` by fs[enc_frame_def] >>
  drule_all enc_emit_add_const_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st2 st3) s2 = OK s3` >>
  drule emit_op_extends >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >>
  conj_tac >- fs[same_blocks_def] >>
  irule enc_frame_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_abi_encode_bytes_frame_frag:
  compile_abi_encode_to_buf dst src (AbiBytestring max_len) st = (op, st') /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  (!y. dst = Var y ==> not_fresh_at st y) /\
  (!y. src = Var y ==> not_fresh_at st y) /\
  mem_word_at (w2n src_w) s0.vs_memory = n2w l /\
  l+31 < dimword (:256) /\ r = 32*((l+31) DIV 32) /\
  w2n dst_w+32+r < dimword (:256) /\
  regions_disjoint (w2n src_w,32+l) (w2n dst_w,32+r) /\
  enc_scratch (frag_ids st st') lo top s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w) (32+r) s.vs_memory =
           mem_bytes_at (w2n src_w) (32+l) s0.vs_memory ++ REPLICATE (r-l) 0w /\
         eval_operand op s = SOME (n2w (32+r)) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top [(w2n dst_w,32+r)] s0 s) R
Proof
  strip_tac >>
  gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  ntac 9 (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (len_op, st1)` >>
  rename1 `emit_op ADD [Lit 31w; len_op] st1 = (ceil_op, st2)` >>
  rename1 `emit_op AND [_; ceil_op] st2 = (round_op, st3)` >>
  rename1 `emit_op ADD [dst; round_op] st3 = (ptr_op, st4)` >>
  rename1 `emit_void MSTORE [ptr_op; _] st4 = ((), st5)` >>
  rename1 `emit_op ADD [Lit 32w; len_op] st5 = (copy_len, st6)` >>
  rename1 `emit_void MCOPY [dst; src; copy_len] st6 = ((), st7)` >>
  rename1 `emit_op ADD [Lit 31w; len_op] st7 = (ceil2, st8)` >>
  rename1 `emit_op AND [_; ceil2] st8 = (round2, st9)` >>
  qabbrev_tac `r = 32*((l+31) DIV 32)` >>
  `st.cs_next_var <= st5.cs_next_var /\
   st.cs_next_var <= st7.cs_next_var` by
    (imp_res_tac (cj 4 emitted_insts_emit_op) >>
     imp_res_tac (cj 3 emitted_insts_emit_void) >> decide_tac) >>
  `!y. len_op = Var y ==> not_fresh_at st5 y` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     imp_res_tac (cj 4 emitted_insts_emit_op) >>
     imp_res_tac (cj 3 emitted_insts_emit_void) >> decide_tac) >>
  `!arg y. MEM arg [dst; src; len_op] /\ arg = Var y ==>
      not_fresh_at st5 y` by
    (simp[] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  `l+31 < dimword (:256)` by simp[] >>
  drule_all enc_bytes_prefix_run >>
  disch_then (qspec_then `[(w2n dst_w,32+r)]` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st st4) s0 = OK s4` >>
  suspend "bytes_writes"
QED

Resume compile_abi_encode_bytes_frame_frag[bytes_writes]:
  `l <= r /\ r <= l+32` by
    (mp_tac enc_round32_bounds >> simp[Abbr `r`]) >>
  `eval_operand dst s4 = SOME (n2w (w2n dst_w)) /\
   eval_operand src s4 = SOME (n2w (w2n src_w))` by
    (simp[] >> conj_tac >> irule enc_frame_preserves_operand >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand ptr_op s4 = SOME (n2w (w2n dst_w+r))` by
    (simp[Abbr `r`, GSYM wordsTheory.word_add_n2w]) >>
  `w2n dst_w+32+r < dimword (:256)` by simp[] >>
  `w2n src_w < dimword (:256)` by irule wordsTheory.w2n_lt >>
  `enc_scratch (frag_ids st st') lo top s4` by fs[enc_frame_def] >>
  drule_all enc_bytes_write_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st7) s4 = OK s7` >>
  `enc_scratch (frag_ids st st') lo top s7` by fs[enc_frame_def] >>
  qpat_x_assum `eval_operand len_op s4 = _` kall_tac >>
  drule_all enc_bytes_size_run >>
  disch_then (qspec_then `[(w2n dst_w,32+r)]` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st7 st') s7 = OK s10` >>
  qspecl_then [`st`, `st4`, `st7`] mp_tac run_inst_seq_chain >>
  disch_then (drule_all_then strip_assume_tac) >>
  `run_inst_seq (emitted_insts st st7) s0 = OK s7` by simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts st st4) s0 = _` kall_tac >>
  qspecl_then [`st`, `st7`, `st'`] mp_tac run_inst_seq_chain >>
  disch_then (drule_all_then strip_assume_tac) >>
  `enc_frame st st' lo top [(w2n dst_w,32+r)] s0 s7` by
    (irule enc_frame_trans >> qexists_tac `s4` >> simp[]) >>
  `enc_frame st st' lo top [(w2n dst_w,32+r)] s0 s10` by
    (irule enc_frame_trans >> qexists_tac `s7` >> simp[]) >>
  suspend "bytes_lift"
QED

Resume compile_abi_encode_bytes_frame_frag[bytes_lift]:
  `r+32 = 32+r /\ l+32 = 32+l` by decide_tac >>
  pure_asm_rewrite_tac[] >>
  qpat_x_assum `r+32 = 32+r` kall_tac >>
  qpat_x_assum `l+32 = 32+l` kall_tac >>
  irule frag_exec_run_inst_seq >>
  reverse conj_tac >- suspend "bytes_code" >>
  BETA_TAC >> gen_tac >> disch_then SUBST1_TAC >>
  disj1_tac >> qexists_tac `s10` >>
  conj_tac >- simp[] >>
  simp_tac (srw_ss()) [enc_frame_inst_idx] >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `s4.vs_memory = s0.vs_memory`
        (fn th => once_rewrite_tac[GSYM th]) >>
      irule enc_prezero_copy_layout >> simp[]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, Abbr `r`]) >>
  simp[]
QED

Resume compile_abi_encode_bytes_frame_frag[bytes_code]:
  conj_tac >- fs[same_blocks_def] >>
  conj_tac >- fs[same_blocks_def] >>
  reverse conj_tac >- simp[IS_PREFIX_APPEND] >>
  rpt (qpat_x_assum `_ = _ ++ emitted_insts _ _` kall_tac) >>
  imp_res_tac (cj 5 emitted_insts_emit_op) >>
  imp_res_tac (cj 4 emitted_insts_emit_void) >>
  pure_asm_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC,
    rich_listTheory.DROP_LENGTH_APPEND] >>
  simp_tac (srw_ss()) [mk_inst_def, is_terminator_def]
QED

Finalise compile_abi_encode_bytes_frame_frag

Theorem compile_abi_encode_prim_frame_frag:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (op, st') /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  (!y. dst = Var y ==> not_fresh_at st y) /\
  enc_scratch (frag_ids st st') lo top s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_word_at (w2n dst_w) s.vs_memory = mload (w2n src_w) s0 /\
         eval_operand op s = SOME 32w /\ s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top [(w2n dst_w, 32)] s0 s) R
Proof
  rpt strip_tac >>
  gvs[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  drule emit_void_extends >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[same_blocks_def] >>
  reverse conj_tac
  >- (gvs[same_blocks_def] >>
      qmatch_goalsub_rename_tac `emitted_insts st st2` >>
      qmatch_asmsub_rename_tac `emitted_insts st1 st2` >>
      qspecl_then [`st`, `st1`, `st2`] mp_tac emitted_insts_append >>
      simp[mk_inst_def, is_terminator_def, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  disj1_tac >>
  qexists_tac `mstore (w2n dst_w) (mload (w2n src_w) s0)
    (update_var (STRING #"%" (toString st.cs_next_var))
      (mload (w2n src_w) s0) s0)` >>
  conj_tac >- suspend "prim_run" >>
  suspend "prim_post"
QED

Resume compile_abi_encode_prim_frame_frag[prim_run]:
  qmatch_goalsub_rename_tac `emitted_insts st st2` >>
  qmatch_asmsub_rename_tac `emitted_insts st1 st2` >>
  qspecl_then [`st`, `st1`, `st2`] mp_tac emitted_insts_append >>
  simp[] >> disch_then SUBST1_TAC >> simp[run_inst_seq_def] >>
  qspec_then `src` mp_tac step_MLOAD >> disch_then drule >>
  strip_tac >> simp[] >>
  `eval_operand dst (update_var (STRING #"%" (toString st.cs_next_var))
     (mload (w2n src_w) s0) s0) = SOME dst_w` by
    (rewrite_tac[enc_eval_operand_update_old] >>
     drule enc_eval_operand_update_old >> simp[]) >>
  drule step_MSTORE >>
  disch_then (qspec_then `Var (STRING #"%" (toString st.cs_next_var))` mp_tac) >>
  simp[eval_operand_def, lookup_var_update_var]
QED

Resume compile_abi_encode_prim_frame_frag[prim_post]:
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same, eval_operand_def] >>
  rewrite_tac[enc_mstore_update_var] >>
  irule enc_frame_update_var >>
  simp[not_fresh_at_def, enc_frame_mstore]
QED

Finalise compile_abi_encode_prim_frame_frag

Theorem compile_abi_encode_copy_abi_frag:
  compile_abi_encode_to_buf dst src (AbiCopy (type_memory_size tv)) st =
    (op, st') /\
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  enc_pre st st' [dst; src] lo top tv v (w2n src_w)
    [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w)
           (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
         eval_operand op s =
           SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top
           [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s) R
Proof
  rpt strip_tac >>
  `val_in_memory tv v (w2n src_w) s0.vs_memory` by fs[enc_pre_def] >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv` by
    (irule val_in_memory_static_enc_length >> metis_tac[]) >>
  `type_memory_size tv < dimword (:256)` by
    (drule enc_pre_bounds >> strip_tac >> decide_tac) >>
  `enc_scratch (frag_ids st st') lo top s0` by fs[enc_pre_def] >>
  drule_all compile_abi_encode_copy_frame_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  strip_tac >> irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[] >>
  rewrite_tac[mem_bytes_at_def, mcopy_padded_read] >>
  rewrite_tac[GSYM mem_bytes_at_def] >>
  irule val_in_memory_static_abi >> metis_tac[]
QED

Theorem compile_abi_encode_prim_abi_frag:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (op, st') /\
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ type_memory_size tv = 32 /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  enc_pre st st' [dst; src] lo top tv v (w2n src_w)
    [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w)
           (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
         eval_operand op s =
           SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top
           [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s) R
Proof
  rpt strip_tac >>
  `val_in_memory tv v (w2n src_w) s0.vs_memory` by fs[enc_pre_def] >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (drule_all val_in_memory_static_enc_length >> simp[]) >>
  `mem_bytes_at (w2n src_w) 32 s0.vs_memory =
     enc (vyper_to_abi_type env ty) av` by
    (drule_all val_in_memory_static_abi >> simp[]) >>
  `enc_scratch (frag_ids st st') lo top s0` by fs[enc_pre_def] >>
  `!y. dst = Var y ==> not_fresh_at st y` by fs[enc_pre_def] >>
  drule_all compile_abi_encode_prim_frame_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >> strip_tac >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[] >>
  `mload (w2n dst_w) s = mload (w2n src_w) s0` by
    fs[GSYM mem_word_at_eq_mload] >>
  drule mload_eq_mem_bytes_at_eq >> simp[]
QED


Theorem compile_abi_encode_static_info_abi_frag:
  compile_abi_encode_static_info dst src ei st = (op, st') /\
  abi_enc_plan env ty ei /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  enc_pre st st' [dst; src] lo top tv v (w2n src_w)
    [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w)
           (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
         eval_operand op s =
           SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top
           [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s) R
Proof
  rpt strip_tac >>
  drule_all compile_abi_encode_static_info_plan >> strip_tac >>
  drule_all abi_enc_plan_static >> strip_tac >> gvs[]
  >- (drule_all abi_enc_plan_prim_size >> strip_tac >>
      drule_all compile_abi_encode_prim_abi_frag >>
      disch_then (qspecl_then [`ctx`, `R`] ACCEPT_TAC)) >>
  `n = type_memory_size tv` by
    (qpat_x_assum `abi_enc_plan env ty (AbiCopy n)` mp_tac >>
     simp[Once abi_enc_plan_cases] >> metis_tac[]) >>
  gvs[] >> irule compile_abi_encode_copy_abi_frag >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dst`, `src`, `src_w`, `tv`, `v`] >> simp[]
QED

Theorem enc_bytes_memory_layout:
  mem_word_at p mem = n2w (LENGTH bs) /\
  mem_bytes_at (p+32) (LENGTH bs) mem = bs ==>
  enc (Bytes NONE) (contractABI$BytesV bs) =
    mem_bytes_at p (32+LENGTH bs) mem ++
    REPLICATE (32*((LENGTH bs+31) DIV 32)-LENGTH bs) 0w
Proof
  strip_tac >>
  rewrite_tac[enc_def, valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word, ceil32_def]
QED

Theorem enc_typed_bytes_layout:
  (bt = BytesT (Dynamic n) \/ bt = StringT n) /\
  evaluate_type env (BaseT bt) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (BaseT bt) v = SOME av /\
  val_in_memory tv v p mem ==>
  ?bs. mem_word_at p mem = n2w (LENGTH bs) /\
       mem_bytes_at (p+32) (LENGTH bs) mem = bs /\
       32+LENGTH bs <= type_memory_size tv /\
       enc (vyper_to_abi_type env (BaseT bt)) av =
         mem_bytes_at p (32+LENGTH bs) mem ++
         REPLICATE (32*((LENGTH bs+31) DIV 32)-LENGTH bs) 0w /\
       LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av) =
         32+32*((LENGTH bs+31) DIV 32)
Proof
  strip_tac >> Cases_on `v` >>
  gvs[vyperValueTheory.evaluate_type_def, value_has_type_def,
      vyper_to_abi_base_def, vyper_to_abi_type_def,
      vyper_base_to_abi_type_def, val_in_memory_def] >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at (p+32) _ mem = bs` >>
  qexists_tac `bs` >>
  `LENGTH bs <= n` by simp[Abbr `bs`] >>
  `LENGTH bs <= 32 * word_size n` by
    (mp_tac word_size_covers >> strip_tac >> decide_tac) >>
  `LENGTH bs < dimword (:256)` by (gvs[] >> decide_tac) >>
  `mem_word_at p mem = n2w (LENGTH bs) /\
   mem_bytes_at (p+32) (LENGTH bs) mem = bs` by simp[Abbr `bs`] >>
  drule_all enc_bytes_memory_layout >>
  simp[enc_def, ceil32_def, type_memory_size_def,
       vfmConstantsTheory.word_size_def] >>
  qspec_then `LENGTH bs` mp_tac (GEN_ALL enc_round32_bounds) >>
  `n2w_o_ORD = ((n2w o ORD) : char -> word8)` by
    simp[FUN_EQ_THM, vyperMiscTheory.n2w_o_ORD_def] >>
  gvs[vfmConstantsTheory.word_size_def] >> decide_tac
QED

Theorem compile_abi_encode_bytes_abi_frag:
  (bt = BytesT (Dynamic n) \/ bt = StringT n) /\
  compile_abi_encode_to_buf dst src (AbiBytestring n) st = (op, st') /\
  evaluate_type env (BaseT bt) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (BaseT bt) v = SOME av /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  enc_pre st st' [dst; src] lo top tv v (w2n src_w)
    [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av))] s0 ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w)
           (LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av)) s.vs_memory =
           enc (vyper_to_abi_type env (BaseT bt)) av /\
         eval_operand op s =
           SOME (n2w (LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av))) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st st' lo top
           [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env (BaseT bt)) av))] s0 s) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `val_in_memory tv v (w2n src_w) s0.vs_memory` by fs[enc_pre_def] >>
  drule_all enc_typed_bytes_layout >> strip_tac >>
  qabbrev_tac `r = 32*((LENGTH bs+31) DIV 32)` >>
  `LENGTH bs <= r` by
    (qspec_then `LENGTH bs` mp_tac (GEN_ALL enc_round32_bounds) >>
     simp[Abbr `r`]) >>
  drule enc_pre_bounds >> strip_tac >>
  `w2n dst_w + (32+r) <= lo /\
   regions_disjoint (w2n src_w,type_memory_size tv) (w2n dst_w,32+r) /\
   (!y. dst = Var y ==> not_fresh_at st y) /\
   (!y. src = Var y ==> not_fresh_at st y) /\
   enc_scratch (frag_ids st st') lo top s0` by fs[enc_pre_def] >>
  `LENGTH bs+31 < dimword (:256) /\
   w2n dst_w+32+r < dimword (:256)` by decide_tac >>
  `regions_disjoint (w2n src_w,32+LENGTH bs) (w2n dst_w,32+r)` by
    (irule regions_disjoint_subregions >> goal_assum (drule_at Any) >> simp[]) >>
  `r = 32*((LENGTH bs+31) DIV 32)` by simp[Abbr `r`] >>
  drule_all compile_abi_encode_bytes_frame_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >> strip_tac >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  pure_asm_rewrite_tac[] >> rewrite_tac[]
QED

(* ===== Recursive ABI encode correctness ===== *)

(* Mutual induction over compile_abi_encode_child / _to_buf /
   _complex_elems / _dyn_loop.  Each clause runs its fragment from s0 to
   its end (it never exits: R is F), and gives the frame of enc_frame.
   With E the encoding enc (vyper_to_abi_type env ty) av:
   - to_buf writes E at dst and returns its length;
   - child writes E at dst + static_ofst for a static child; for a
     dynamic one it writes E at dst + d, where d is the dynamic offset in
     the cell at c (a scratch cell of the caller, at or above lo), and
     puts d in the head slot at dst + static_ofst and d + LENGTH E back in
     the cell;
   - complex_elems writes the element heads from dst + head_offset and the
     tails of the dynamic elements from dst + d, which together are
     enc_tuple d 0 of the elements (the heads' offsets count from d), and
     moves the cell, if there are dynamic elements, past the tails;
   - dyn_loop writes a dynamic array's encoding after its length word at
     dst and returns the encoding's whole length. *)
(* Persistent loop facts deliberately exclude the changing counter contents. *)
Definition enc_loop_ctx_def:
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s <=>
    enc_pre st st' ops lo top tv v src outs s /\
    enc_frame st st' lo top outs s0 s /\
    s.vs_labels = s0.vs_labels /\
    eval_operand count_ptr s = SOME (n2w ip) /\
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (ip,32) /\ lo <= ip
End

Theorem enc_pre_transport:
  enc_pre st st' ops lo top tv v src outs s0 /\ value_has_type tv v /\
  enc_frame st st' lo top outs s0 s ==>
  enc_pre st st' ops lo top tv v src outs s
Proof
  rpt strip_tac >>
  `val_in_memory tv v src s.vs_memory` by
    (drule enc_frame_preserves_source >>
     disch_then irule >> fs[enc_pre_def, EVERY_MEM] >>
     rpt strip_tac >> rename1 `MEM e outs` >> Cases_on `e` >>
     first_x_assum drule >> simp[]) >>
  fs[enc_pre_def, enc_frame_def]
QED

Theorem enc_frame_mstore_scratch:
  enc_scratch (frag_ids st st') lo top s /\
  j IN frag_ids st st' /\ FLOOKUP s.vs_allocas j = SOME (ip,32) ==>
  enc_frame st st' lo top outs s (mstore ip w s)
Proof
  strip_tac >>
  drule enc_frame_mstore >> disch_then (qspecl_then [`w`, `ip`] mp_tac) >>
  rewrite_tac[enc_frame_def] >> strip_tac >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!a. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[mstore_def] >> metis_tac[]
QED

Theorem enc_loop_ctx_from_frame:
  enc_pre st st' ops lo top tv v src outs s0 /\ value_has_type tv v /\
  enc_frame st st' lo top outs s0 s /\ s.vs_labels = s0.vs_labels /\
  eval_operand count_ptr s = SOME (n2w ip) /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (ip,32) /\ lo <= ip ==>
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s
Proof
  strip_tac >> simp[enc_loop_ctx_def] >> metis_tac[enc_pre_transport]
QED

Theorem enc_loop_ctx_jump[simp]:
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip
    (jump_to lbl s) =
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s
Proof
  simp[enc_loop_ctx_def, enc_frame_jump, enc_pre_def, enc_scratch_def,
       jump_to_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem enc_loop_ctx_source:
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s ==>
  val_in_memory tv v src s.vs_memory
Proof
  simp[enc_loop_ctx_def, enc_pre_def]
QED

Theorem enc_loop_ctx_operand:
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s /\
  MEM op ops /\ eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> fs[enc_loop_ctx_def, enc_pre_def] >>
  drule enc_frame_preserves_operand >> disch_then irule >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem enc_loop_ctx_bounds:
  enc_loop_ctx st st' ops lo top tv v src outs s0 count_ptr ip s ==>
  src + type_memory_size tv <= lo /\ lo <= ip /\
  ip + 32 <= top /\ top < dimword (:256)
Proof
  simp[enc_loop_ctx_def] >> strip_tac >>
  drule enc_pre_bounds >> strip_tac >>
  `enc_scratch (frag_ids st st') lo top s` by fs[enc_pre_def] >>
  drule_all enc_scratch_alloca_bound >> fs[]
QED

Theorem enc_static_loop_init_code:
  enc_static_loop_init st = ((count_ptr,hdr,body_lbl,exit),si) ==>
  ?buf sa sz.
    compile_alloc_buffer 32 st = (buf,sa) /\
    emit_void MSTORE [buf.buf_operand; Lit 0w] sa = ((),sz) /\
    count_ptr = buf.buf_operand /\
    emitted_insts st si = emitted_insts st sa ++ emitted_insts sa sz /\
    same_blocks st si /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st si) /\
    si.cs_current_insts = st.cs_current_insts ++ emitted_insts st si
Proof
  simp[enc_static_loop_init_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  rename1 `emit_void MSTORE _ sa = ((),sz)` >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  rename1 `emit_void MSTORE _ sa = ((),sz)` >>
  `emitted_insts st sz = emitted_insts st sa ++ emitted_insts sa sz` by
    (irule emitted_insts_append >> simp[]) >>
  simp[emitted_insts_def, same_blocks_def, mk_inst_def, is_terminator_def] >>
  gvs[same_blocks_def, DROP_APPEND, is_terminator_def] >>
  `LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 1) = 0` by
    decide_tac >> simp[is_terminator_def]
QED

Theorem enc_static_loop_init_run:
  enc_static_loop_init st = ((count_ptr,hdr,body_lbl,exit),si) /\
  st.cs_next_id IN frag_ids st z /\
  enc_scratch (frag_ids st z) lo top s0 ==>
  ?ip s. run_inst_seq (emitted_insts st si) s0 = OK s /\
    lo <= ip /\ ip + 32 <= top /\
    eval_operand count_ptr s = SOME (n2w ip) /\
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (ip,32) /\
    mem_word_at ip s.vs_memory = 0w /\ s.vs_labels = s0.vs_labels /\
    enc_frame st z lo top outs s0 s
Proof
  strip_tac >> drule enc_static_loop_init_code >> strip_tac >>
  `FINITE (frag_ids st z)` by simp[] >>
  drule_all enc_compile_alloc_buffer_run >> strip_tac >>
  `enc_frame st z lo top outs s0 t` by
    (simp[enc_frame_def] >> rpt strip_tac >> metis_tac[]) >>
  `enc_frame st z lo top outs t (mstore b 0w t)` by
    (irule enc_frame_mstore_scratch >> simp[] >>
     qexists_tac `st.cs_next_id` >> simp[]) >>
  qexistsl_tac [`b`, `mstore b 0w t`] >>
  conj_tac
  >- (asm_rewrite_tac[] >> drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sa sz` SUBST1_TAC) >>
      drule emitted_insts_emit_void >> strip_tac >>
      `b < dimword (:256)` by
        (qpat_assum `enc_scratch _ _ _ s0` mp_tac >>
         pure_rewrite_tac[enc_scratch_def] >> strip_tac >> decide_tac) >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_write2_def, eval_operand_def]) >>
  simp[eval_operand_mstore, valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  conj_tac >- simp[mstore_def] >>
  metis_tac[enc_frame_trans]
QED

Theorem enc_static_loop_init_frag:
  enc_static_loop_init st = ((count_ptr,hdr,body_lbl,exit),si) /\
  st.cs_next_id IN frag_ids st z /\
  enc_pre st z ops lo top tv v src outs s0 /\ value_has_type tv v ==>
  frag_exec ctx st si (\s. s = s0)
    (\s. ?ip. enc_array_inv
       (enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip)
       p B ts avs ip NONE 0 s) R
Proof
  strip_tac >>
  `enc_scratch (frag_ids st z) lo top s0` by fs[enc_pre_def] >>
  drule_all enc_static_loop_init_run >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  drule enc_static_loop_init_code >> strip_tac >>
  fs[same_blocks_def] >> irule frag_exec_run_inst_seq >>
  asm_simp_tac (srw_ss()) [rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `ip` >> irule enc_array_inv_zero >>
  simp[] >> irule enc_loop_ctx_from_frame >>
  simp[enc_frame_inst_idx] >>
  Cases_on `buf.buf_operand` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem enc_loop_ctx_dynarray_source:
  enc_loop_ctx st z ops lo top (ArrayTV tv (Dynamic n))
    (ArrayV (DynArrayV vs)) src outs s0 count_ptr ip s /\ k < LENGTH vs ==>
  mem_word_at src s.vs_memory = n2w (LENGTH vs) /\
  val_in_memory tv (EL k vs) (src + 32 + k * type_memory_size tv) s.vs_memory
Proof
  strip_tac >> drule enc_loop_ctx_source >>
  simp[valueEncodingProofsTheory.val_in_memory_dynarray_proof] >> strip_tac >>
  drule_all elems_in_memory_EL >> simp[]
QED

Theorem enc_loop_ctx_dynarray_bounds:
  enc_loop_ctx st z ops lo top (ArrayTV tv (Dynamic n))
    (ArrayV (DynArrayV vs)) src outs s0 count_ptr ip s /\
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
  k < LENGTH vs ==>
  value_has_type tv (EL k vs) /\
  src + 32 + k * type_memory_size tv + type_memory_size tv <= lo /\
  src + 32 + k * type_memory_size tv < dimword (:256)
Proof
  strip_tac >> drule enc_loop_ctx_bounds >> strip_tac >>
  fs[value_has_type_def, type_memory_size_def] >>
  conj_tac
  >- (fs[all_have_type_EVERY, EVERY_EL] >> metis_tac[]) >>
  `SUC k <= n` by decide_tac >>
  `SUC k * type_memory_size tv <= n * type_memory_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  qpat_x_assum `SUC k * _ <= _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem enc_loop_ctx_array_slot:
  enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip s /\
  MEM (dst,32 + len * asz) outs /\ k < len ==>
  dst + 32 + k * asz + asz <= lo /\
  dst + 32 + k * asz < dimword (:256) /\
  regions_disjoint (src,type_memory_size tv) (dst + 32 + k * asz,asz)
Proof
  strip_tac >> drule enc_loop_ctx_bounds >> strip_tac >>
  `dst + (32 + len * asz) <= lo /\
   regions_disjoint (src,type_memory_size tv) (dst,32 + len * asz)` by
    (qpat_x_assum `enc_loop_ctx _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[enc_loop_ctx_def, enc_pre_def] >> strip_tac >>
     qpat_x_assum `EVERY _ outs` mp_tac >>
     rewrite_tac[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `SUC k * asz <= len * asz` by simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  qpat_x_assum `SUC k * asz <= _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> strip_tac >>
  conj_tac >- decide_tac >> conj_tac >- (fs[] >> decide_tac) >>
  drule regions_disjoint_subregions >> disch_then irule >> simp[] >>
  decide_tac
QED

Theorem enc_loop_ctx_readonly:
  enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip s /\
  enc_frame st z lo top outs s t /\ t.vs_memory = s.vs_memory /\
  t.vs_labels = s.vs_labels /\
  eval_operand count_ptr t = eval_operand count_ptr s ==>
  enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip t
Proof
  strip_tac >> fs[enc_loop_ctx_def] >>
  `enc_scratch (frag_ids st z) lo top t` by fs[enc_frame_def] >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (ip,32)` by
    (qpat_x_assum `enc_frame _ _ _ _ _ s t` mp_tac >>
     rewrite_tac[enc_frame_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  simp[enc_loop_ctx_def] >> conj_tac
  >- fs[enc_pre_def] >> metis_tac[enc_frame_trans]
QED

Theorem enc_array_inv_readonly:
  enc_array_inv inv_ctx p B ts vs ip tail_cell k s /\
  inv_ctx t /\ t.vs_memory = s.vs_memory ==>
  enc_array_inv inv_ctx p B ts vs ip tail_cell k t
Proof
  Cases_on `tail_cell` >> simp[enc_array_inv_def, enc_prefix_mem_def]
QED

Theorem enc_static_loop_header_code:
  enc_static_loop_header count_ptr len_op sh = (done_op,sj) ==>
  ?i cmp sa sb.
    emit_op MLOAD [count_ptr] sh = (i,sa) /\
    emit_op LT [i;len_op] sa = (cmp,sb) /\
    emit_op ISZERO [cmp] sb = (done_op,sj) /\
    emitted_insts sh sj =
      emitted_insts sh sa ++ emitted_insts sa sb ++ emitted_insts sb sj /\
    same_blocks sh sj /\
    sj.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sj /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sh sj) /\
    sa.cs_next_var = sh.cs_next_var + 1 /\
    sb.cs_next_var = sh.cs_next_var + 2 /\
    (!x. i = Var x ==> not_fresh_at sa x) /\
    (!x. cmp = Var x ==> not_fresh_at sb x)
Proof
  simp[enc_static_loop_header_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [count_ptr] sh = (i,sa)` >>
  rename1 `emit_op LT [i;len_op] sa = (cmp,sb)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_same_blocks >>
  `emitted_insts sh sb = emitted_insts sh sa ++ emitted_insts sa sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sh sj = emitted_insts sh sb ++ emitted_insts sb sj` by
    (irule emitted_insts_append >> simp[]) >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[same_blocks_def, mk_inst_def, is_terminator_def,
      not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem enc_static_loop_header_run:
  enc_static_loop_header count_ptr len_op sh = (done_op,sj) /\
  (!x. MEM (Var x) [count_ptr;len_op] ==> not_fresh_at sh x) /\
  eval_operand count_ptr s = SOME (n2w ip) /\
  eval_operand len_op s = SOME (n2w n) /\
  mem_word_at ip s.vs_memory = n2w k /\
  ip < dimword (:256) /\ k < dimword (:256) /\ n < dimword (:256) /\
  a.cs_next_var <= sh.cs_next_var /\
  enc_scratch (frag_ids a b) lo top s ==>
  ?t. run_inst_seq (emitted_insts sh sj) s = OK t /\
      eval_operand done_op t = SOME (bool_to_word (~(k < n))) /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      (!old. (!x. old = Var x ==> not_fresh_at sh x) ==>
        eval_operand old t = eval_operand old s) /\
      enc_frame a b lo top outs s t
Proof
  strip_tac >> drule enc_static_loop_header_code >> strip_tac >>
  `step_inst_base (mk_inst sh.cs_next_id MLOAD [count_ptr]
     [STRING #"%" (toString sh.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString sh.cs_next_var)) (n2w k) s)` by
    (qpat_assum `eval_operand count_ptr s = _` (mp_tac o MATCH_MP step_MLOAD) >>
     simp[GSYM mem_word_at_eq_mload]) >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` (qx_choose_then `s1` strip_assume_tac)) >>
  `eval_operand len_op s1 = SOME (n2w n)` by (fs[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sa.cs_next_id LT [i;len_op]
     [STRING #"%" (toString sa.cs_next_var)]) s1 =
     OK (update_var (STRING #"%" (toString sa.cs_next_var))
       (bool_to_word (k < n)) s1)` by
    (qpat_assum `eval_operand i s1 = _` (mp_then (Pos hd) mp_tac step_LT) >>
     disch_then drule >> simp[]) >>
  `a.cs_next_var <= sa.cs_next_var` by simp[] >>
  `enc_scratch (frag_ids a b) lo top s1` by fs[enc_frame_def] >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` (qx_choose_then `s2` strip_assume_tac)) >>
  `step_inst_base (mk_inst sb.cs_next_id ISZERO [cmp]
     [STRING #"%" (toString sb.cs_next_var)]) s2 =
     OK (update_var (STRING #"%" (toString sb.cs_next_var))
       (bool_to_word (~(k < n))) s2)` by
    (qpat_assum `eval_operand cmp s2 = _` (mp_tac o MATCH_MP step_ISZERO) >>
     `((bool_to_word (k < n):bytes32) = 0w) = ~(k < n)` by
       (Cases_on `k < n` >> simp[] >> EVAL_TAC) >> simp[]) >>
  `a.cs_next_var <= sb.cs_next_var` by simp[] >>
  `enc_scratch (frag_ids a b) lo top s2` by fs[enc_frame_def] >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` (qx_choose_then `s3` strip_assume_tac)) >>
  qexists_tac `s3` >> simp[run_inst_seq_append] >>
  conj_tac
  >- (qspecl_then [`emitted_insts sh sa`,
        `emitted_insts sa sb ++ emitted_insts sb sj`,`s`,`s1`] mp_tac run_inst_seq_append >>
      simp[] >> disch_then SUBST1_TAC >>
      qspecl_then [`emitted_insts sa sb`,`emitted_insts sb sj`,`s1`,`s2`]
        mp_tac run_inst_seq_append >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `(!x. old = Var x ==> not_fresh_at sa x) /\
     (!x. old = Var x ==> not_fresh_at sb x)` by
      (rpt strip_tac >> pure_rewrite_tac[not_fresh_at_def] >>
       qpat_x_assum `!x. old = Var x ==> _` mp_tac >>
       pure_rewrite_tac[not_fresh_at_def] >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
    metis_tac[]) >>
  metis_tac[enc_frame_trans]
QED

Theorem enc_static_loop_header_frag:
  enc_static_loop_header count_ptr len_op sh = (done_op,sj) /\
  (!x. MEM (Var x) [count_ptr;len_op] ==> not_fresh_at sh x) /\
  st.cs_next_var <= sh.cs_next_var /\ MEM len_op ops /\
  eval_operand len_op s0 = SOME (n2w (LENGTH avs)) /\
  LENGTH avs < dimword (:256) /\ k <= LENGTH avs ==>
  frag_exec ctx sh sj
    (enc_array_inv
      (enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip)
      p B ts avs ip tail_cell k)
    (enc_array_header
      (enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip)
      p B ts avs ip tail_cell done_op k) R
Proof
  strip_tac >> drule enc_static_loop_header_code >> strip_tac >>
  fs[same_blocks_def] >> irule frag_exec_run_inst_seq >>
  asm_simp_tac (srw_ss()) [rich_listTheory.IS_PREFIX_APPEND] >>
  qx_gen_tac `s` >> strip_tac >>
  `enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip s` by
    fs[enc_array_inv_def] >>
  `eval_operand len_op s = SOME (n2w (LENGTH avs))` by
    (drule_all enc_loop_ctx_operand >> simp[]) >>
  `eval_operand count_ptr s = SOME (n2w ip) /\
   enc_scratch (frag_ids st z) lo top s` by
    fs[enc_loop_ctx_def, enc_pre_def] >>
  `mem_word_at ip s.vs_memory = n2w k` by fs[enc_array_inv_def] >>
  `ip < dimword (:256) /\ k < dimword (:256)` by
    (drule enc_loop_ctx_bounds >> simp[] >> decide_tac) >>
  fs[] >> drule_all (SRULE [] enc_static_loop_header_run) >>
  disch_then (qspec_then `outs` (qx_choose_then `t` strip_assume_tac)) >>
  `enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip t` by
    (irule enc_loop_ctx_readonly >> qexists_tac `s` >> simp[] >> metis_tac[]) >>
  `eval_operand count_ptr t = SOME (n2w ip) /\
   enc_scratch (frag_ids st z) lo top t` by
    fs[enc_loop_ctx_def, enc_pre_def] >>
  `enc_array_inv
    (enc_loop_ctx st z ops lo top tv v src outs s0 count_ptr ip)
    p B ts avs ip tail_cell k t` by
    (irule enc_array_inv_readonly >> simp[] >> qexists_tac `s` >> simp[]) >>
  simp[enc_array_header_def] >>
  disj1_tac >> qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> simp[]) >>
  conj_tac
  >- (irule enc_array_inv_readonly >> simp[] >> conj_tac
      >- (irule enc_loop_ctx_readonly >> qexists_tac `t` >>
          simp[enc_frame_refl] >>
          Cases_on `count_ptr` >> fs[eval_operand_def, lookup_var_def]) >>
      qexists_tac `t` >> simp[]) >>
  `bool_to_word (~(k < LENGTH avs)) =
    (if k < LENGTH avs then 0w else 1w)` by
    (Cases_on `k < LENGTH avs` >> simp[] >> EVAL_TAC) >>
  Cases_on `done_op` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem enc_run_inst_seq_compose:
  run_inst_seq xs s = OK t /\ run_inst_seq ys t = OK u ==>
  run_inst_seq (xs ++ ys) s = OK u
Proof
  metis_tac[run_inst_seq_append]
QED

Theorem enc_emit_op_readonly_run:
  emit_op opc args st = (op,st') /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand op t = SOME w /\
      (!old. (!x. old = Var x ==> not_fresh_at st x) ==>
        eval_operand old t = eval_operand old s) /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) w s` >>
  simp[run_inst_seq_def, eval_operand_update_var] >>
  conj_tac >- (rpt strip_tac >> irule enc_eval_operand_update_old >>
    qexists_tac `st` >> simp[]) >>
  simp[update_var_def]
QED

Theorem enc_indexed_address_code:
  emit_op ADD [base_op;Lit 32w] a = (data,b) /\
  emit_op MUL [index;Lit (n2w stride)] b = (off,c) /\
  emit_op ADD [data;off] c = (addr,d) ==>
  emitted_insts a d =
    emitted_insts a b ++ emitted_insts b c ++ emitted_insts c d /\
  b.cs_next_var = a.cs_next_var + 1 /\
  c.cs_next_var = a.cs_next_var + 2 /\
  (!x. data = Var x ==> not_fresh_at b x) /\
  (!x. off = Var x ==> not_fresh_at c x) /\
  same_blocks a d /\
  d.cs_current_insts = a.cs_current_insts ++ emitted_insts a d
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_same_blocks >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts a d = emitted_insts a c ++ emitted_insts c d` by
    (irule emitted_insts_append >> simp[]) >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[same_blocks_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem enc_indexed_address_run:
  emit_op ADD [base_op;Lit 32w] a = (data,b) /\
  emit_op MUL [index;Lit (n2w stride)] b = (off,c) /\
  emit_op ADD [data;off] c = (addr,d) /\
  (!x. MEM (Var x) [base_op;index] ==> not_fresh_at a x) /\
  eval_operand base_op s = SOME bw /\ eval_operand index s = SOME iw ==>
  ?t. run_inst_seq (emitted_insts a d) s = OK t /\
      eval_operand addr t = SOME (bw + 32w + iw * n2w stride) /\
      (!old. (!x. old = Var x ==> not_fresh_at a x) ==>
        eval_operand old t = eval_operand old s) /\
      t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  strip_tac >> drule_all enc_indexed_address_code >> strip_tac >>
  `step_inst_base (mk_inst a.cs_next_id ADD [base_op;Lit 32w]
     [STRING #"%" (toString a.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var)) (bw + 32w) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  drule_all enc_emit_op_readonly_run >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `eval_operand index s1 = SOME iw` by (fs[] >> metis_tac[]) >>
  `step_inst_base (mk_inst b.cs_next_id MUL [index;Lit (n2w stride)]
     [STRING #"%" (toString b.cs_next_var)]) s1 =
     OK (update_var (STRING #"%" (toString b.cs_next_var)) (iw * n2w stride) s1)` by
    (irule step_MUL >> simp[eval_operand_def]) >>
  drule_all enc_emit_op_readonly_run >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `eval_operand data s2 = SOME (bw + 32w)` by metis_tac[] >>
  `step_inst_base (mk_inst c.cs_next_id ADD [data;off]
     [STRING #"%" (toString c.cs_next_var)]) s2 =
     OK (update_var (STRING #"%" (toString c.cs_next_var))
       (bw + 32w + iw * n2w stride) s2)` by
    (irule step_ADD >> simp[]) >>
  drule_all enc_emit_op_readonly_run >>
  disch_then (qx_choose_then `s3` strip_assume_tac) >>
  qexists_tac `s3` >> simp[] >> conj_tac
  >- (irule enc_run_inst_seq_compose >> qexists_tac `s2` >> simp[] >>
      irule enc_run_inst_seq_compose >> qexists_tac `s1` >> simp[]) >>
  rpt strip_tac >>
  `(!x. old = Var x ==> not_fresh_at b x) /\
   (!x. old = Var x ==> not_fresh_at c x)` by
    (rpt strip_tac >> pure_rewrite_tac[not_fresh_at_def] >>
     qpat_x_assum `!x. old = Var x ==> _` mp_tac >>
     pure_rewrite_tac[not_fresh_at_def] >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem enc_static_info_same_block:
  compile_abi_encode_static_info dst src ei st = (op,st') ==>
  same_blocks st st' /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  Cases_on `ei` >>
  simp[compile_abi_encode_static_info_def, compile_abi_encode_static_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem enc_emit_op_append:
  emit_op opc args a = (op,b) ==>
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b
Proof
  metis_tac[emitted_insts_emit_op]
QED

Theorem enc_emit_void_append:
  emit_void opc args a = ((),b) ==>
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b
Proof
  metis_tac[emitted_insts_emit_void]
QED

Theorem enc_static_loop_body_code:
  enc_static_loop_body dst src ei asz msz count_ptr sb = ((),se) ==>
  ?i src_data src_off child_src dst_data dst_off child_dst ignored next
    s1 s2 s3 s4 s5 s6 s7 s8 s9.
    emit_op MLOAD [count_ptr] sb = (i,s1) /\
    emit_op ADD [src; Lit 32w] s1 = (src_data,s2) /\
    emit_op MUL [i; Lit (n2w msz)] s2 = (src_off,s3) /\
    emit_op ADD [src_data;src_off] s3 = (child_src,s4) /\
    emit_op ADD [dst; Lit 32w] s4 = (dst_data,s5) /\
    emit_op MUL [i; Lit (n2w asz)] s5 = (dst_off,s6) /\
    emit_op ADD [dst_data;dst_off] s6 = (child_dst,s7) /\
    compile_abi_encode_static_info child_dst child_src ei s7 = (ignored,s8) /\
    emit_op ADD [i;Lit 1w] s8 = (next,s9) /\
    emit_void MSTORE [count_ptr;next] s9 = ((),se) /\
    same_blocks sb se /\
    se.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb se /\
    emitted_insts sb se =
      emitted_insts sb s1 ++ emitted_insts s1 s4 ++
      emitted_insts s4 s7 ++ emitted_insts s7 s8 ++ emitted_insts s8 se
Proof
  simp[enc_static_loop_body_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [count_ptr] sb = (i,s1)` >>
  rename1 `emit_op ADD [src; Lit 32w] s1 = (src_data,s2)` >>
  rename1 `emit_op MUL [i; Lit (n2w msz)] s2 = (src_off,s3)` >>
  rename1 `emit_op ADD [src_data;src_off] s3 = (child_src,s4)` >>
  rename1 `emit_op ADD [dst; Lit 32w] s4 = (dst_data,s5)` >>
  rename1 `emit_op MUL [i; Lit (n2w asz)] s5 = (dst_off,s6)` >>
  rename1 `emit_op ADD [dst_data;dst_off] s6 = (child_dst,s7)` >>
  rename1 `compile_abi_encode_static_info child_dst child_src ei s7 = (ignored,s8)` >>
  rename1 `emit_op ADD [i; Lit 1w] s8 = (next,s9)` >>
  imp_res_tac (cj 7 enc_indexed_address_code) >>
  imp_res_tac (cj 6 enc_indexed_address_code) >>
  imp_res_tac enc_emit_op_append >>
  imp_res_tac enc_emit_void_append >>
  imp_res_tac emit_op_same_blocks >>
  imp_res_tac emit_void_same_blocks >>
  drule enc_static_info_same_block >> strip_tac >>
  `emitted_insts s8 se = emitted_insts s8 s9 ++ emitted_insts s9 se` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sb s4 = emitted_insts sb s1 ++ emitted_insts s1 s4` by
    (irule emitted_insts_append >> simp[] >> gvs[APPEND_ASSOC]) >>
  `emitted_insts sb s7 = emitted_insts sb s4 ++ emitted_insts s4 s7` by
    (irule emitted_insts_append >> simp[] >> gvs[APPEND_ASSOC]) >>
  `emitted_insts sb s8 = emitted_insts sb s7 ++ emitted_insts s7 s8` by
    (irule emitted_insts_append >> simp[] >> gvs[APPEND_ASSOC]) >>
  `emitted_insts sb se = emitted_insts sb s8 ++ emitted_insts s8 se` by
    (irule emitted_insts_append >> simp[] >> gvs[APPEND_ASSOC]) >>
  gvs[same_blocks_def, APPEND_ASSOC] >> metis_tac[]
QED

Theorem enc_abi_list_index:
  !ts vs avs. vyper_to_abi_list env ts vs = SOME avs ==>
  LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts /\
  (!k. k < LENGTH ts ==>
    vyper_to_abi env (EL k ts) (EL k vs) = SOME (EL k avs))
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[]
QED

Theorem enc_old_operand_mono:
  !a b op. a.cs_next_var <= b.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at a x) ==>
  (!x. op = Var x ==> not_fresh_at b x)
Proof
  simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem enc_emit_op_old_result:
  emit_op opc args a = (op,b) ==>
  (!x. op = Var x ==> not_fresh_at b x)
Proof
  strip_tac >> drule emitted_insts_emit_op >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem enc_static_loop_setup_run:
  emit_op MLOAD [count_ptr] a0 = (i,a1) /\
  emit_op ADD [src;Lit 32w] a1 = (sd,a2) /\
  emit_op MUL [i;Lit (n2w msz)] a2 = (so,a3) /\
  emit_op ADD [sd;so] a3 = (child_src,a4) /\
  emit_op ADD [dst;Lit 32w] a4 = (dd,a5) /\
  emit_op MUL [i;Lit (n2w asz)] a5 = (dof,a6) /\
  emit_op ADD [dd;dof] a6 = (child_dst,a7) /\
  (!x. MEM (Var x) [count_ptr;src;dst] ==> not_fresh_at a0 x) /\
  eval_operand count_ptr s = SOME (n2w ip) /\
  eval_operand src s = SOME (n2w src_n) /\
  eval_operand dst s = SOME (n2w dst_n) /\
  mem_word_at ip s.vs_memory = n2w k /\ ip < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts a0 a7) s = OK t /\
    eval_operand i t = SOME (n2w k) /\
    eval_operand child_src t = SOME (n2w (src_n + 32 + k * msz)) /\
    eval_operand child_dst t = SOME (n2w (dst_n + 32 + k * asz)) /\
    (!old. (!x. old = Var x ==> not_fresh_at a0 x) ==>
      eval_operand old t = eval_operand old s) /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  strip_tac >>
  `a1.cs_next_var = a0.cs_next_var + 1 /\
   a4.cs_next_var = a0.cs_next_var + 4` by
    (imp_res_tac (cj 4 emitted_insts_emit_op) >> decide_tac) >>
  `(!x. i = Var x ==> not_fresh_at a1 x) /\
   (!x. child_src = Var x ==> not_fresh_at a4 x)` by
    metis_tac[enc_emit_op_old_result] >>
  `a1.cs_current_insts = a0.cs_current_insts ++ emitted_insts a0 a1 /\
   a4.cs_current_insts = a1.cs_current_insts ++ emitted_insts a1 a4 /\
   a7.cs_current_insts = a4.cs_current_insts ++ emitted_insts a4 a7` by
    (imp_res_tac (cj 7 enc_indexed_address_code) >>
     metis_tac[enc_emit_op_append]) >>
  `step_inst_base (mk_inst a0.cs_next_id MLOAD [count_ptr]
    [STRING #"%" (toString a0.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString a0.cs_next_var)) (n2w k) s)` by
    (qpat_assum `eval_operand count_ptr s = _` (mp_tac o MATCH_MP step_MLOAD) >>
     simp[GSYM mem_word_at_eq_mload]) >>
  drule_all enc_emit_op_readonly_run >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `eval_operand src s1 = SOME (n2w src_n) /\
   eval_operand dst s1 = SOME (n2w dst_n)` by (fs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [src;i] ==> not_fresh_at a1 x` by
    (fs[] >> metis_tac[enc_old_operand_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all enc_indexed_address_run >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `eval_operand dst s2 = SOME (n2w dst_n) /\
   eval_operand i s2 = SOME (n2w k)` by
    (fs[] >> metis_tac[enc_old_operand_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  `!x. dst = Var x ==> not_fresh_at a4 x` by
    (match_mp_tac enc_old_operand_mono >> qexists_tac `a0` >> simp[] >> fs[] >> metis_tac[]) >>
  `!x. i = Var x ==> not_fresh_at a4 x` by
    (match_mp_tac enc_old_operand_mono >> qexists_tac `a1` >> simp[]) >>
  `!x. MEM (Var x) [dst;i] ==> not_fresh_at a4 x` by (fs[] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base _ s = _` kall_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD [src;_] _ = _` kall_tac >>
  qpat_x_assum `emit_op MUL [i;Lit (n2w msz)] _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD [sd;so] _ = _` kall_tac >>
  drule_all enc_indexed_address_run >>
  disch_then (qx_choose_then `s3` strip_assume_tac) >>
  `emitted_insts a0 a4 = emitted_insts a0 a1 ++ emitted_insts a1 a4` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts a0 a7 = emitted_insts a0 a4 ++ emitted_insts a4 a7` by
    (irule emitted_insts_append >> simp[]) >>
  qexists_tac `s3` >> simp[GSYM wordsTheory.word_add_n2w,
    GSYM wordsTheory.word_mul_n2w] >> conj_tac
  >- (irule enc_run_inst_seq_compose >> qexists_tac `s2` >> simp[] >>
      irule enc_run_inst_seq_compose >> qexists_tac `s1` >> simp[]) >>
  rpt strip_tac >>
  `(!x. old = Var x ==> not_fresh_at a1 x) /\
   (!x. old = Var x ==> not_fresh_at a4 x)` by
    (conj_tac >> match_mp_tac enc_old_operand_mono >>
     qexists_tac `a0` >> simp[]) >> metis_tac[]
QED

Theorem enc_frame_readonly:
  (!old. (!x. old = Var x ==> not_fresh_at st x) ==>
    eval_operand old t = eval_operand old s) /\
  t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  enc_scratch (frag_ids st z) lo top s ==>
  enc_frame st z lo top outs s t
Proof
  strip_tac >> drule_all enc_scratch_cong >> strip_tac >>
  simp[enc_frame_def] >> rpt strip_tac >>
  qpat_x_assum `!old. _` (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def]
QED

Theorem enc_scratch_subset:
  FINITE ids /\ sub SUBSET ids /\ enc_scratch ids lo top s ==>
  enc_scratch sub lo top s
Proof
  strip_tac >>
  `FINITE {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE}` by
    (irule pred_setTheory.SUBSET_FINITE_I >> qexists_tac `ids` >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `CARD {i | i IN sub /\ FLOOKUP s.vs_allocas i = NONE} <=
   CARD {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE}` by
    (irule pred_setTheory.CARD_SUBSET >> simp[] >>
     gvs[pred_setTheory.SUBSET_DEF]) >>
  qpat_x_assum `enc_scratch ids _ _ _` mp_tac >>
  rewrite_tac[enc_scratch_def] >> strip_tac >>
  simp[enc_scratch_def] >> rpt strip_tac >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem enc_static_loop_element_pre:
  enc_loop_ctx st z ops lo top (ArrayTV tv (Dynamic n))
    (ArrayV (DynArrayV vs)) src_n outs s0 count_ptr ip s /\
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
  k < LENGTH vs /\ MEM (dst_n,32 + LENGTH vs * type_memory_size tv) outs /\
  frag_ids a b SUBSET frag_ids st z /\
  (!x. MEM (Var x) [child_dst;child_src] ==> not_fresh_at a x) /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  LIST_REL (\v av. vyper_to_abi env ty v = SOME av) vs avs ==>
  value_has_type tv (EL k vs) /\
  vyper_to_abi env ty (EL k vs) = SOME (EL k avs) /\
  enc_pre a b [child_dst;child_src] lo top tv (EL k vs)
    (src_n + 32 + k * type_memory_size tv)
    [(dst_n + 32 + k * type_memory_size tv,
      LENGTH (enc (vyper_to_abi_type env ty) (EL k avs)))] s
Proof
  strip_tac >>
  drule_all enc_loop_ctx_dynarray_source >> strip_tac >>
  drule_all enc_loop_ctx_dynarray_bounds >> strip_tac >>
  drule_all enc_loop_ctx_array_slot >> strip_tac >>
  `vyper_to_abi env ty (EL k vs) = SOME (EL k avs)` by
    (fs[LIST_REL_EL_EQN]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) (EL k avs)) = type_memory_size tv` by
    (irule val_in_memory_static_enc_length >> metis_tac[]) >>
  `enc_scratch (frag_ids st z) lo top s` by fs[enc_loop_ctx_def, enc_pre_def] >>
  `enc_scratch (frag_ids a b) lo top s` by
    (irule enc_scratch_subset >> qexists_tac `frag_ids st z` >> simp[]) >>
  `SUC k <= n` by (fs[value_has_type_def]) >>
  `SUC k * type_memory_size tv <= n * type_memory_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  qpat_x_assum `SUC k * _ <= _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> strip_tac >>
  simp[enc_pre_def] >>
  irule regions_disjoint_subregions >>
  goal_assum (drule_at Any) >>
  simp[type_memory_size_def] >> decide_tac
QED

Theorem enc_abi_replicate_list:
  vyper_to_abi_list env (REPLICATE (LENGTH vs) ty) vs = SOME avs ==>
  LIST_REL (\v av. vyper_to_abi env ty v = SOME av) vs avs
Proof
  strip_tac >> drule enc_abi_list_index >>
  simp[LIST_REL_EL_EQN, EL_REPLICATE] >> metis_tac[]
QED

Theorem enc_frame_preserves_bytes:
  enc_frame st z lo top outs s t /\ p + n <= lo /\
  EVERY (regions_disjoint (p,n)) outs ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_pointwise >> rpt strip_tac >>
  qpat_x_assum `enc_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[enc_frame_def, enc_scratch_def] >> strip_tac >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> decide_tac) >>
  qpat_x_assum `EVERY _ outs` mp_tac >>
  rewrite_tac[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
  rename1 `MEM out outs` >> Cases_on `out` >>
  first_x_assum drule >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem enc_static_slot_prefix:
  has_types ts avs /\ EVERY (\t. ~is_dynamic t) ts /\
  k < LENGTH avs /\ enc_prefix_mem p B ts avs k s /\
  enc_frame a b lo top
    [(p + LENGTH (enc_head_upto B ts avs k),
      LENGTH (enc (EL k ts) (EL k avs)))] s t /\
  p + LENGTH (enc_head_upto B ts avs k) <= lo /\
  mem_bytes_at (p + LENGTH (enc_head_upto B ts avs k))
    (LENGTH (enc (EL k ts) (EL k avs))) t.vs_memory =
      enc (EL k ts) (EL k avs) ==>
  enc_prefix_mem p B ts avs (SUC k) t
Proof
  strip_tac >>
  `LENGTH ts = LENGTH avs` by metis_tac[has_types_LIST_REL, LIST_REL_LENGTH] >>
  `~is_dynamic (EL k ts)` by fs[EVERY_EL] >>
  `enc_tail_upto ts avs k = []` by
    (simp[enc_tail_upto_def] >> irule enc_prefix_tail_static >>
     simp[EVERY_TAKE]) >>
  `mem_bytes_at p (LENGTH (enc_head_upto B ts avs k)) t.vs_memory =
     enc_head_upto B ts avs k` by
    (drule enc_frame_preserves_bytes >>
     disch_then (qspecl_then [`p`, `LENGTH (enc_head_upto B ts avs k)`] mp_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >>
     fs[enc_prefix_mem_def]) >>
  irule enc_prefix_mem_suc >> simp[] >>
  fs[mem_bytes_at_def]
QED

Theorem enc_static_counter_run:
  emit_op ADD [index;Lit 1w] a = (next,b) /\
  emit_void MSTORE [count_ptr;next] b = ((),c) /\
  eval_operand index s = SOME (n2w k) /\
  eval_operand count_ptr s = SOME (n2w ip) /\
  (!x. count_ptr = Var x ==> not_fresh_at a x) /\
  st.cs_next_var <= a.cs_next_var /\
  enc_scratch (frag_ids st z) lo top s /\
  j IN frag_ids st z /\ FLOOKUP s.vs_allocas j = SOME (ip,32) ==>
  ?u. run_inst_seq (emitted_insts a b ++ emitted_insts b c) s = OK u /\
      mem_word_at ip u.vs_memory = n2w (SUC k) /\
      u.vs_labels = s.vs_labels /\
      (!p n. p + n <= lo ==>
        mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory) /\
      enc_frame st z lo top outs s u
Proof
  strip_tac >>
  `step_inst_base (mk_inst a.cs_next_id ADD [index;Lit 1w]
      [STRING #"%" (toString a.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString a.cs_next_var)) (n2w (SUC k)) s)` by
    (rewrite_tac[arithmeticTheory.ADD1, GSYM wordsTheory.word_add_n2w] >>
     irule step_ADD >> simp[eval_operand_lit]) >>
  drule_all enc_emit_op_run_frame >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  `eval_operand count_ptr s' = SOME (n2w ip)` by metis_tac[] >>
  `enc_scratch (frag_ids st z) lo top s' /\
   FLOOKUP s'.vs_allocas j = SOME (ip,32)` by fs[enc_frame_def] >>
  `ip < dimword (:256)` by
    (drule_all enc_scratch_alloca_bound >> strip_tac >>
     qpat_x_assum `enc_scratch _ _ _ s` mp_tac >>
     pure_rewrite_tac[enc_scratch_def] >> strip_tac >> decide_tac) >>
  `enc_frame st z lo top outs s' (mstore ip (n2w (SUC k)) s')` by
    (irule enc_frame_mstore_scratch >> metis_tac[]) >>
  qexists_tac `mstore ip (n2w (SUC k)) s'` >> conj_tac
  >- (irule enc_run_inst_seq_compose >> goal_assum (drule_at Any) >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_write2_def]) >>
  rewrite_tac[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  conj_tac >- simp[mstore_def] >> conj_tac
  >- (rpt strip_tac >>
      `lo <= ip` by
        (qpat_x_assum `enc_scratch _ _ _ s` mp_tac >>
         pure_rewrite_tac[enc_scratch_def] >> strip_tac >> metis_tac[]) >>
      `mem_bytes_at p n (mstore ip (n2w (SUC k)) s').vs_memory =
       mem_bytes_at p n s'.vs_memory` suffices_by simp[] >>
      irule mstore_mem_bytes_at_disjoint >>
      simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule enc_frame_trans >> qexists_tac `s'` >> simp[]
QED

Theorem enc_static_slot_counter_inv:
  has_types ts avs /\ EVERY (\t. ~is_dynamic t) ts /\
  k < LENGTH avs /\ enc_prefix_mem p B ts avs k s /\
  enc_frame a b lo top
    [(p + LENGTH (enc_head_upto B ts avs k),
      LENGTH (enc (EL k ts) (EL k avs)))] s t /\
  p + LENGTH (enc_head_upto B ts avs k) <= lo /\
  mem_bytes_at (p + LENGTH (enc_head_upto B ts avs k))
    (LENGTH (enc (EL k ts) (EL k avs))) t.vs_memory =
      enc (EL k ts) (EL k avs) /\
  p + LENGTH (enc_head_upto B ts avs (SUC k)) <= lo /\
  (!q n. q + n <= lo ==>
    mem_bytes_at q n u.vs_memory = mem_bytes_at q n t.vs_memory) /\
  mem_word_at ip u.vs_memory = n2w (SUC k) /\ inv_ctx u ==>
  enc_array_inv inv_ctx p B ts avs ip NONE (SUC k) u
Proof
  strip_tac >>
  `enc_prefix_mem p B ts avs (SUC k) t` by
    (irule enc_static_slot_prefix >> metis_tac[]) >>
  `enc_tail_upto ts avs (SUC k) = []` by
    (simp[enc_tail_upto_def] >> irule enc_prefix_tail_static >>
     simp[EVERY_TAKE]) >>
  irule enc_array_inv_suc >> simp[] >>
  fs[enc_prefix_mem_def] >>
  simp[mem_bytes_at_def]
QED

Theorem enc_frame_lift:
  enc_frame a b lo child_top local_outs s t /\
  frag_ids a b SUBSET frag_ids st z /\
  (!x. not_fresh_at st x ==> not_fresh_at a x) /\
  (!p n. MEM (p,n) local_outs ==>
    ?q m. MEM (q,m) outs /\ q <= p /\ p+n <= q+m) /\
  enc_scratch (frag_ids st z) lo top t ==>
  enc_frame st z lo top outs s t
Proof
  strip_tac >>
  `enc_frame a b lo child_top outs s t` by
    (irule enc_frame_cover_outputs >> metis_tac[]) >>
  qpat_x_assum `enc_frame a b lo child_top outs s t` mp_tac >>
  rewrite_tac[enc_frame_def] >> strip_tac >>
  simp[enc_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a. _ ==> mem_bytes_at _ _ _ = _` irule >>
      simp[] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem enc_pre_reserve_enclosing:
  enc_pre a b ops lo top tv v src local_outs s /\
  frag_ids a b SUBSET frag_ids st z /\
  enc_scratch (frag_ids st z) lo top s ==>
  enc_pre a b ops lo
    (top - 32 * CARD {i | i IN (frag_ids st z DIFF frag_ids a b) /\
                          FLOOKUP s.vs_allocas i = NONE})
    tv v src local_outs s
Proof
  strip_tac >>
  `FINITE (frag_ids st z DIFF frag_ids a b) /\
   DISJOINT (frag_ids a b) (frag_ids st z DIFF frag_ids a b) /\
   frag_ids a b UNION (frag_ids st z DIFF frag_ids a b) = frag_ids st z` by
    (simp[] >> ASM_SET_TAC[]) >>
  `enc_scratch (frag_ids a b) lo
    (top - 32 * CARD {i | i IN (frag_ids st z DIFF frag_ids a b) /\
                          FLOOKUP s.vs_allocas i = NONE}) s` by
    (irule enc_scratch_restrict_reserved >> simp[]) >>
  fs[enc_pre_def]
QED

Theorem enc_frame_restore_enclosing:
  enc_frame a b lo
    (top - 32 * CARD {i | i IN (frag_ids st z DIFF frag_ids a b) /\
                          FLOOKUP s.vs_allocas i = NONE}) local_outs s t /\
  frag_ids a b SUBSET frag_ids st z /\
  enc_scratch (frag_ids st z) lo top s /\
  (!x. not_fresh_at st x ==> not_fresh_at a x) /\
  (!p n. MEM (p,n) local_outs ==>
    ?q m. MEM (q,m) outs /\ q <= p /\ p+n <= q+m) ==>
  enc_frame st z lo top outs s t
Proof
  strip_tac >>
  `FINITE (frag_ids st z DIFF frag_ids a b) /\
   DISJOINT (frag_ids a b) (frag_ids st z DIFF frag_ids a b) /\
   frag_ids a b UNION (frag_ids st z DIFF frag_ids a b) = frag_ids st z` by
    (simp[] >> ASM_SET_TAC[]) >>
  `enc_scratch (frag_ids st z) lo top t` by
    (qpat_assum `_ UNION _ = frag_ids st z`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule enc_scratch_restore_reserved >> simp[] >>
     fs[enc_frame_def] >> metis_tac[pred_setTheory.IN_DIFF]) >>
  irule enc_frame_lift >> metis_tac[]
QED

Theorem compile_abi_encode_static_info_enclosing_frag:
  compile_abi_encode_static_info dst src ei a = (op,b) /\
  abi_enc_plan env ty ei /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
  enc_pre a b [dst;src] lo top tv v (w2n src_w)
    [(w2n dst_w,LENGTH (enc (vyper_to_abi_type env ty) av))] s0 /\
  frag_ids a b SUBSET frag_ids st z /\
  enc_scratch (frag_ids st z) lo top s0 /\
  (!x. not_fresh_at st x ==> not_fresh_at a x) /\
  (?p n. MEM (p,n) outs /\ p <= w2n dst_w /\
    w2n dst_w + LENGTH (enc (vyper_to_abi_type env ty) av) <= p+n) ==>
  frag_exec ctx a b (\s. s = s0)
    (\s. mem_bytes_at (w2n dst_w)
           (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
         eval_operand op s =
           SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
         s.vs_labels = s0.vs_labels /\
         enc_frame st z lo top outs s0 s) R
Proof
  rpt strip_tac >>
  drule_all enc_pre_reserve_enclosing >> strip_tac >>
  drule_all compile_abi_encode_static_info_abi_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >> strip_tac >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule enc_frame_restore_enclosing >> simp[] >>
  qexistsl_tac [`a`, `b`,
    `[(w2n dst_w,LENGTH (enc (vyper_to_abi_type env ty) av))]`] >>
  simp[] >> qexistsl_tac [`p`, `n`] >> simp[]
QED

Theorem compile_abi_encode_frag:
  (!dst child_ptr ei is_dyn static_ofst dyn_ptr st op st' ctx env ty tv v
    av s0 dst_w src_w lo top.
     compile_abi_encode_child dst child_ptr ei is_dyn static_ofst dyn_ptr st =
       (op, st') /\
     abi_enc_plan env ty ei /\
     is_dyn = is_dynamic (vyper_to_abi_type env ty) /\
     evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     vyper_to_abi env ty v = SOME av /\
     eval_operand dst s0 = SOME dst_w /\
     eval_operand child_ptr s0 = SOME src_w ==>
     if ~is_dyn then
       enc_pre st st' [dst; child_ptr] lo top tv v (w2n src_w)
         [(w2n dst_w + static_ofst,
           LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
       frag_exec ctx st st' (\s. s = s0)
         (\s. mem_bytes_at (w2n dst_w + static_ofst)
                (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
              enc (vyper_to_abi_type env ty) av /\
              eval_operand op s =
                SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
              enc_frame st st' lo top
                [(w2n dst_w + static_ofst,
                  LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
         (\r. F)
     else
       !c d j.
         eval_operand dyn_ptr s0 = SOME (n2w c) /\
         mem_word_at c s0.vs_memory = n2w d /\
         j NOTIN frag_ids st st' /\
         FLOOKUP s0.vs_allocas j = SOME (c, 32) /\ lo <= c /\
         static_ofst + 32 <= d /\
         enc_pre st st' [dst; child_ptr; dyn_ptr] lo top tv v (w2n src_w)
           [(w2n dst_w + static_ofst, 32);
            (w2n dst_w + d,
             LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
         frag_exec ctx st st' (\s. s = s0)
           (\s. mem_bytes_at (w2n dst_w + d)
                  (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
                enc (vyper_to_abi_type env ty) av /\
                mem_word_at (w2n dst_w + static_ofst) s.vs_memory = n2w d /\
                mem_word_at c s.vs_memory =
                  n2w (d + LENGTH (enc (vyper_to_abi_type env ty) av)) /\
                eval_operand op s =
                  SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
                enc_frame st st' lo top
                  [(w2n dst_w + static_ofst, 32);
                   (w2n dst_w + d,
                    LENGTH (enc (vyper_to_abi_type env ty) av));
                   (c, 32)] s0 s)
           (\r. F)) /\
  (!dst src ei st op st' ctx env ty tv v av s0 dst_w src_w lo top.
     compile_abi_encode_to_buf dst src ei st = (op, st') /\
     abi_enc_plan env ty ei /\
     evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     vyper_to_abi env ty v = SOME av /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     enc_pre st st' [dst; src] lo top tv v (w2n src_w)
       [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w)
              (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
            enc (vyper_to_abi_type env ty) av /\
            eval_operand op s =
              SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
            enc_frame st st' lo top
              [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
       (\r. F)) /\
  (!dst src elems src_offset head_offset dyn_ptr st op st' ctx env ts tvs vs
    avs s0 dst_w src_w lo top c d.
     compile_abi_encode_complex_elems dst src elems src_offset head_offset
       dyn_ptr st = (op, st') /\
     abi_enc_plans env ts elems /\
     LIST_REL (\t tv. evaluate_type env t = SOME tv) ts tvs /\
     LIST_REL value_has_type tvs vs /\
     vyper_to_abi_list env ts vs = SOME avs /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     (EXISTS (\(_, _, _, is_dyn). is_dyn) elems ==>
        eval_operand dyn_ptr s0 = SOME (n2w c) /\
        mem_word_at c s0.vs_memory = n2w d /\
        (?j. j NOTIN frag_ids st st' /\
             FLOOKUP s0.vs_allocas j = SOME (c, 32)) /\ lo <= c /\
        head_offset + SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems) <= d) /\
     enc_pre st st' [dst; src; dyn_ptr] lo top (TupleTV tvs)
       (ArrayV (TupleV vs)) (w2n src_w + src_offset)
       [(w2n dst_w + head_offset, SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
        (w2n dst_w + d,
         LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
         SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems))] s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w + head_offset)
              (SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems)) s.vs_memory ++
            mem_bytes_at (w2n dst_w + d)
              (LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
               SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems)) s.vs_memory =
            enc_tuple d 0 (vyper_to_abi_types env ts) avs [] [] /\
            (EXISTS (\(_, _, _, is_dyn). is_dyn) elems ==>
             mem_word_at c s.vs_memory =
               n2w (d +
                 LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
                 SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems))) /\
            enc_frame st st' lo top
              [(w2n dst_w + head_offset,
                SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
               (w2n dst_w + d,
                LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
                SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
               (c, 32)] s0 s)
       (\r. F)) /\
  (!dst src ei asz msz len_op st op st' ctx env t n tv vs av s0 dst_w src_w
    lo top.
     compile_abi_encode_dyn_loop dst src ei asz msz len_op st = (op, st') /\
     abi_enc_plan env (ArrayT t (Dynamic n))
       (AbiDynArray ei asz msz T) /\
     evaluate_type env (ArrayT t (Dynamic n)) = SOME tv /\
     value_has_type tv (ArrayV (DynArrayV vs)) /\
     vyper_to_abi env (ArrayT t (Dynamic n)) (ArrayV (DynArrayV vs)) =
       SOME av /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     eval_operand len_op s0 = SOME (n2w (LENGTH vs)) /\
     enc_pre st st' [dst; src; len_op] lo top tv (ArrayV (DynArrayV vs))
       (w2n src_w)
       [(w2n dst_w,
         LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) - 32)]
       s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w)
              (LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) -
               32) s.vs_memory =
            DROP 32 (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) /\
            eval_operand op s =
              SOME (n2w (LENGTH
                (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av))) /\
            enc_frame st st' lo top
              [(w2n dst_w,
                LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) -
                32)] s0 s)
       (\r. F))
Proof
  cheat
QED

(* ===== Element Pointer ===== *)

(* Pinned Python emits ADD even at offset zero; the fresh result operand has
   the same evaluated pointer value as its parent. *)
Theorem compile_get_element_ptr_zero:
  ∀ parent_ptr ss st op st'.
    compile_get_element_ptr parent_ptr 0 st = (op, st') ∧
    eval_operand parent_ptr ss = SOME base_w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME base_w
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_get_element_ptr_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qexists `update_var (STRING #"%" (toString st.cs_next_var)) (base_w + 0w) ss` >>
  conj_tac >- (
    irule run_inst_seq_sing_ok >>
    simp[step_ADD, eval_operand_lit]) >>
  simp[eval_operand_update_var]
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
  rpt gen_tac >> strip_tac >> gvs[compile_get_element_ptr_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
simp[step_ADD, eval_operand_lit, eval_operand_update_var] >>
qexists `update_var (STRING #"%" (toString st.cs_next_var)) (n2w base_addr + n2w offset) ss` >>
conj_tac >- (
  irule run_inst_seq_sing_ok >>
  simp[step_ADD, eval_operand_lit]
) >>
simp[eval_operand_update_var, wordsTheory.word_add_n2w]
QED

