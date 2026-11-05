(* Static child address preparation followed by the checked word encoder. *)
Theory bodyPtrAbiEncodeStaticChild
Ancestors
  bodyPtrAbiEncodeOffset bodyPtrAbiEncodeWordChecks abiEncoderChildCode
  abiEncoderReentryLeaves abiEncoder abiDecoderContract emitHelperProps
  exprLoweringProps compileEnv emitHelper fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map words list rich_list

Theorem abi_encode_static_word_child_code:
  compile_abi_encode_child dst src AbiPrimWord F off cursor st = (out,en) ==>
  ?head mid.
    emit_op ADD [dst; Lit (n2w off)] st = (head,mid) /\
    compile_abi_encode_to_buf head src AbiPrimWord mid = (out,en) /\
    emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en /\
    LENGTH (emitted_insts st mid) = 1 /\
    LENGTH (emitted_insts mid en) = 2 /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts mid en) = [] /\
    mid.cs_next_var = st.cs_next_var+1 /\
    en.cs_next_var = mid.cs_next_var+1
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* The offset boundary's run equation also fixes the control-site fields. *)
Theorem abi_encode_static_child_address_control[local]:
  emit_op ADD [Var dst; Lit (n2w off)] st = (head,mid) /\
  lookup_var dst s = SOME a /\
  run_inst_seq (emitted_insts st mid) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, update_var_def]
QED
