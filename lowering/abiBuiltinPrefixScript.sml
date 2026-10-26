(* Pure prefixes for ABI builtin length and pointer setup.
   TOP-LEVEL: abi_builtin_prefix, abi_builtin_prefix_chain,
     abi_builtin_emit_binary, abi_builtin_emit_iszero.
   Helper: lift one register-writing instruction under enclosing freshness. *)
Theory abiBuiltinPrefix
Ancestors
  abiDecoderReentryAllocation abiDecoderReentryAddress abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderGuards abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomExecProofs venomState venomInst
  words arithmetic finite_map list

Definition abi_builtin_prefix_def:
  abi_builtin_prefix st st' limit_st s t <=>
    run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
End

Theorem abi_builtin_prefix_chain:
  abi_builtin_prefix st middle limit_st s prepared /\
  abi_builtin_prefix middle final limit_st prepared t /\
  st.cs_next_var <= middle.cs_next_var ==>
  abi_builtin_prefix st final limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_prefix_def] >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_address_frame_trans >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_emit_register:
  emit_op opc ops st = (out,st') /\
  step_inst_base (mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME w /\ abi_builtin_prefix st st' limit_st s t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `t` |-> `update_var (STRING #"%" (toString st.cs_next_var)) w s`]
    abi_decoder_register_update) >>
  impl_tac >- asm_simp_tac (srw_ss()) [update_var_def] >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) w s` >>
  asm_simp_tac (srw_ss()) [abi_builtin_prefix_def, run_inst_seq_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, abi_decoder_address_frame_def, update_var_def]
QED

Theorem abi_builtin_emit_binary:
  emit_op opc [lhs;rhs] st = (out,st') /\
  ((opc = EQ /\ w = bool_to_word (a = b)) \/
   (opc = LT /\ w = bool_to_word (w2n a < w2n b)) \/
   (opc = GT /\ w = bool_to_word (w2n a > w2n b)) \/
   (opc = AND /\ w = word_and a b)) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME w /\ abi_builtin_prefix st st' limit_st s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`ops` |-> `[lhs;rhs]`] abi_builtin_emit_register) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[] >>
    FIRST [irule step_EQ, irule step_LT, irule step_GT, irule step_AND] >> simp[]) >> simp[]
QED

Theorem abi_builtin_emit_iszero:
  emit_op ISZERO [arg] st = (out,st') /\ eval_operand arg s = SOME a /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (bool_to_word (a = 0w)) /\
    abi_builtin_prefix st st' limit_st s t
Proof
  strip_tac >> mp_tac (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[arg]`,
    `w` |-> `bool_to_word ((a:bytes32) = 0w)`] abi_builtin_emit_register) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> irule step_ISZERO >> simp[]) >> simp[]
QED

Theorem abi_builtin_emit_add:
  emit_op ADD [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (a + b) /\ abi_builtin_prefix st st' limit_st s t
Proof
  strip_tac >> drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a + b) s` >>
  fs[abi_builtin_prefix_def, abi_decoder_address_frame_def]
QED

Theorem abi_builtin_emit_load:
  emit_op MLOAD [src] st = (out,st') /\ eval_operand src s = SOME p /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (mload (w2n p) s) /\ abi_builtin_prefix st st' limit_st s t
Proof
  strip_tac >> drule_all (SIMP_RULE (srw_ss()) [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `MLOAD`] abi_decoder_read_reentry)) >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (mload (w2n p) s) s` >>
  fs[abi_builtin_prefix_def, abi_decoder_address_frame_def,
    abi_decode_load_def, update_var_def]
QED

Theorem abi_builtin_assert:
  emit_void ASSERT [arg] st = ((),st') /\ eval_operand arg s = SOME w /\ w <> 0w /\
  fresh_vars_wrt limit_st s ==>
  abi_builtin_prefix st st' limit_st s s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id ASSERT [arg] []) s = OK s` by
    (irule assert_ok >> qexists_tac `w` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_builtin_prefix_def, run_inst_seq_def, abi_decoder_address_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin prefix not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinPrefix");
