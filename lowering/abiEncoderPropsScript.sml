(*
 * ABI Encoder/Decoder Properties
 *
 * TOP-LEVEL:
 *   compile_abi_int_clamp_correct     — int clamping rejects out-of-range
 *   compile_abi_bytes_clamp_correct   — bytes clamping rejects dirty high bits
 *   compile_abi_encode_static_correct — static type writes word to dst
 *   compile_abi_decode_static_correct — static type reads + clamps
 *   compile_abi_encode_tuple_correct  — tuple encoding with head/tail
 *   compile_abi_decode_tuple_correct  — tuple decoding with validation
 *   compile_abi_encode_bytestring_correct — length-prefixed encoding
 *   compile_get_element_ptr_correct   — element pointer arithmetic
 *
 * Source: abi/abi_encoder.py, abi/abi_decoder.py
 * Lowering: abiEncoderScript.sml
 *)

Theory abiEncoderProps
Ancestors
  exprLoweringProps emitHelper emitHelperProps
  abiEncoder compileEnv
  venomExecSemantics venomState venomInst
  valueEncoding

(* ===== ABI Clamping ===== *)

(* Integer clamping: either accepts or reverts *)
Theorem compile_abi_int_clamp_correct:
  ∀ val_op bits is_signed ss st st'.
    compile_abi_int_clamp val_op bits is_signed st = ((), st') ∧
    eval_operand val_op ss = SOME w
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
  qmatch_goalsub_abbrev_tac`step_inst_base _ ssu` >>
  TRY (
    qmatch_goalsub_abbrev_tac`mk_inst _ EQ [op1; op2]` >>
    qspecl_then[`op1`,`op2`]mp_tac step_EQ >>
    CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["ss"]))) >>
    disch_then(qspec_then`ssu`mp_tac) >>
    simp[Abbr`op2`, eval_operand_def, Abbr`ssu`, lookup_var_update_var] >>
    NO_TAC (* TODO: continue once we have fresh var assumption *) ) >>
  cheat (* need fresh var assumption *)
  (* assert_ok_or_revert *)
QED

(* Bytes clamping: rejects values with non-zero high bits *)
Theorem compile_abi_bytes_clamp_correct:
  ∀ val_op m ss st st'.
    compile_abi_bytes_clamp val_op m st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    m ≤ 32
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Static Encode/Decode ===== *)

(* Static ABI encoding: MSTORE of source value to dst *)
Theorem compile_abi_encode_static_correct:
  ∀ src_op dst_op ss st st' v dst.
    compile_abi_encode_static src_op dst_op st = ((), st') ∧
    eval_operand src_op ss = SOME v ∧
    eval_operand dst_op ss = SOME (n2w dst)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      mload dst ss' = v
Proof
  cheat
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

(* ===== Bytestring Encode ===== *)

(* Bytestring encoding: copies length + data + zero-pads *)
Theorem compile_abi_encode_bytestring_correct:
  ∀ src_ptr dst head_offset ss st op st'.
    compile_abi_encode_bytestring src_ptr dst head_offset st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* ===== Tuple Encode/Decode ===== *)

(* Tuple encoding *)
Theorem compile_abi_encode_tuple_correct:
  ∀ src_ptr dst_ptr types sizes ss st op st'.
    compile_abi_encode_tuple src_ptr dst_ptr types sizes st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* Tuple decoding with validation *)
Theorem compile_abi_decode_tuple_correct:
  ∀ src_base dst_ptr hi_op types sizes ss st st'.
    compile_abi_decode_tuple src_base dst_ptr hi_op types sizes st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
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

(* ===== Bool Decode ===== *)

(* Bool decode: clamps to 0 or 1 *)
Theorem compile_abi_decode_bool_correct:
  ∀ src_op dst_op ss st st'.
    compile_abi_decode_bool src_op dst_op st = ((), st') ∧
    eval_operand src_op ss = SOME w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
