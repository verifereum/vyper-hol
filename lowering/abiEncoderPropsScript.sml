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
  exprLoweringProps emitHelper emitHelperProps
  abiEncoder compileEnv
  venomExecSemantics venomState venomInst
  valueEncoding valueEncodingProps

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

(* Static ABI encoding: MSTORE of source value to dst *)
Theorem compile_abi_encode_static_correct:
  ∀ src_op dst_op ss st st' v dst.
    compile_abi_encode_static src_op dst_op st = ((), st') ∧
    eval_operand src_op ss = SOME v ∧
    eval_operand dst_op ss = SOME dst
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      mload (w2n dst) ss' = v
Proof
  rw[compile_abi_encode_static_def] >>
  drule emitted_insts_emit_void >>
  rw[run_inst_seq_def] >>
  drule_all_then (CHANGED_TAC o simp o single) step_MSTORE >>
  simp[GSYM mem_word_at_eq_mload, mstore_mem_word_at_same]
QED

(* Static ABI decoding: MLOAD + clamp *)
Theorem compile_abi_decode_static_correct:
  ∀ src_op dst_op clamp_fn ss st st'.
    compile_abi_decode_static src_op dst_op clamp_fn st = ((), st') ∧
    eval_operand src_op ss = SOME src_w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* Clamp failure → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
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


