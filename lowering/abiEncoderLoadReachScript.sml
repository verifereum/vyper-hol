(* A final cursor load preserves memory and reaches its actual CFG endpoint. *)
Theory abiEncoderLoadReach
Ancestors
  abiEncoderAddressReach abiDecoderReentryAddress abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv emitHelperProps
  venomExecSemantics venomState venomInst words list rich_list

Theorem abi_encoder_load_from_state:
  emit_op MLOAD [src] st = (out,st') /\ eval_operand src initial = SOME p /\
  mload (w2n p) initial = w /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand out t = SOME w /\ fresh_vars_wrt limit_st t /\
      abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_decode_load_def, update_var_def]
QED

Theorem abi_encoder_load_reach:
  emit_op MLOAD [src] st = (out,st') /\ fn_has_code st st' func /\
  eval_operand src initial = SOME p /\ mload (w2n p) initial = w /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand out t = SOME w /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_load_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_LOAD_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder cursor load reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderLoadReach");
