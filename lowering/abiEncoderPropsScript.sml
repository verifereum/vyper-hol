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
      mload (w2n dst_w) ss' = mload (w2n src_v) ss
Proof
  cheat
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


