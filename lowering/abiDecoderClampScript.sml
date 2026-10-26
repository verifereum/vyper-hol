(* Successful primitive clamps. Validity is a pure property of the input word;
   the sequence theorem proves execution, freshness and operand preservation. *)
Theory abiDecoderClamp
Ancestors
  abiDecoderUnsignedClamp abiDecoderGuards abiDecoderContract abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState venomInst words arithmetic rich_list list

Definition abi_decoder_clamp_valid_def:
  abi_decoder_clamp_valid NoClamp (w:bytes32) = T /\
  abi_decoder_clamp_valid (IntClamp bits F) w =
    (bits <= 256 /\ w2n w < 2 ** bits) /\
  abi_decoder_clamp_valid (IntClamp bits T) w =
    (sign_extend (n2w (bits DIV 8 - 1)) w = w) /\
  abi_decoder_clamp_valid (BytesMClamp m) w =
    (w << w2n (n2w (m * 8) : bytes32) = 0w) /\
  abi_decoder_clamp_valid BoolClamp w = (w2n w < 2)
End

Theorem abi_clamp_emit_SIGNEXTEND[local]:
  emit_op SIGNEXTEND [op1;op2] st = (v,st') /\
  eval_operand op1 s = SOME w1 /\ eval_operand op2 s = SOME w2 /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand v t = SOME (sign_extend w1 w2) /\
    same_blocks st st' /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!a. a < LENGTH s.vs_memory ==> EL a t.vs_memory = EL a s.vs_memory) /\
    LENGTH t.vs_memory = LENGTH s.vs_memory
Proof
  rw[] >> qspecl_then [`SIGNEXTEND`, `\(x:bytes32) (y:bytes32). sign_extend x y`]
    (ho_match_mp_tac o BETA_RULE) emit_op_pure2_correct >>
  goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >>
  irule step_SIGNEXTEND >> rw[]
QED

Theorem abi_decoder_signed_clamp_sequence:
  compile_abi_int_clamp val_op bits T st = ((),st') /\
  eval_operand val_op s = SOME w /\
  sign_extend (n2w (bits DIV 8 - 1)) w = w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND [Lit (n2w (bits DIV 8 - 1)); val_op] st = (canon,c1)` >>
  rename1 `emit_op EQ [val_op;canon] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w (bits DIV 8 - 1))) s =
    SOME (n2w (bits DIV 8 - 1))` by simp[eval_operand_def] >>
  drule_all abi_clamp_emit_SIGNEXTEND >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> `eval_operand val_op s1 = SOME w` by metis_tac[] >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >> `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `SIGNEXTEND`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `EQ`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> metis_tac[]
QED

Theorem abi_clamp_emit_SHL[local]:
  emit_op SHL [op1;op2] st = (v,st') /\
  eval_operand op1 s = SOME w1 /\ eval_operand op2 s = SOME w2 /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand v t = SOME (w2 << w2n w1) /\
    same_blocks st st' /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!a. a < LENGTH s.vs_memory ==> EL a t.vs_memory = EL a s.vs_memory) /\
    LENGTH t.vs_memory = LENGTH s.vs_memory
Proof
  rw[] >> qspecl_then [`SHL`, `\x y. y << w2n x`]
    (ho_match_mp_tac o BETA_RULE) emit_op_pure2_correct >>
  goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >> irule step_SHL >> rw[]
QED

Theorem abi_decoder_bytes_clamp_sequence:
  compile_abi_bytes_clamp val_op m st = ((),st') /\
  eval_operand val_op s = SOME w /\
  w << w2n (n2w (m * 8) : bytes32) = 0w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHL [Lit (n2w (8 * m)); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w (8 * m))) s = SOME (n2w (8 * m))`
    by simp[eval_operand_def] >>
  drule_all abi_clamp_emit_SHL >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[] >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >> `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `SHL`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`] abi_decoder_clamp_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s2` >> simp[] >> metis_tac[]
QED

Theorem abi_decoder_bool_clamp:
  compile_abi_clamp_basetype val_op BoolClamp = compile_abi_int_clamp val_op 1 F
Proof
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def]
QED

Theorem abi_decoder_clamp_sequence:
  compile_abi_clamp_basetype val_op clamp st = ((),st') /\
  eval_operand val_op s = SOME w /\ abi_decoder_clamp_valid clamp w /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `clamp`
  >- (simp[compile_abi_clamp_basetype_def, abi_decoder_clamp_valid_def,
           comp_return_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def, inst_extends_def])
  >- (rename1 `IntClamp bits signed` >> Cases_on `signed` >>
      simp[compile_abi_clamp_basetype_def, abi_decoder_clamp_valid_def] >>
      rpt strip_tac >> FIRST
        [drule_all abi_decoder_unsigned_clamp_sequence >> simp[],
         drule_all abi_decoder_signed_clamp_sequence >> simp[]])
  >- (simp_tac bool_ss [compile_abi_clamp_basetype_def, abi_decoder_clamp_valid_def] >>
      rpt strip_tac >> drule_all abi_decoder_bytes_clamp_sequence >> simp[]) >>
  simp[abi_decoder_bool_clamp, abi_decoder_clamp_valid_def] >> rpt strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`bits` |-> `1`] abi_decoder_unsigned_clamp_sequence)) >> simp[]
QED

Theorem abi_decoder_clamp_shape:
  compile_abi_clamp_basetype val_op clamp st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CLAMP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive clamp not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderClamp");
