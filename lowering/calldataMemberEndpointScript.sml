(* Actual member navigation endpoint, including fixed-limit freshness. *)
Theory calldataMemberEndpoint
Ancestors
  calldataMembers successfulSequenceEndpoint abiDecoderLoopRegisters
  abiDecoderContract abiDecoderReentry compileEnv emitHelper emitHelperProps
  abiEncoder exprLoweringProps venomState venomInst venomExecSemantics
  safeSequence fragExecMem instIdxIndep words list rich_list arithmetic finite_map

Theorem member_add_fresh[local]:
  n < limit.cs_next_var /\ fresh_vars_wrt limit s /\
  step_inst_base (mk_inst id ADD ops [STRING #"%" (toString n)]) s = OK t ==>
  fresh_vars_wrt limit t
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule abi_decoder_generated_update_fresh >> simp[]
QED

Theorem member_load_fresh[local]:
  n < limit.cs_next_var /\ fresh_vars_wrt limit s /\
  step_inst_base (mk_inst id CALLDATALOAD ops [STRING #"%" (toString n)]) s = OK t ==>
  fresh_vars_wrt limit t
Proof
  simp[step_inst_base_def, mk_inst_def, exec_read1_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule abi_decoder_generated_update_fresh >> simp[]
QED

Theorem member_sequence_fresh[local]:
  !is s t.
  EVERY (\i. !a b. fresh_vars_wrt limit a /\ step_inst_base i a = OK b ==>
                    fresh_vars_wrt limit b) is /\
  fresh_vars_wrt limit s /\ run_inst_seq is s = OK t ==>
  fresh_vars_wrt limit t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >> metis_tac[]
QED

Theorem member_address_limit_fresh[local]:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  run_inst_seq (emitted_insts st mid) s = OK t /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac list_ss [DROP_LENGTH_APPEND] >>
  disch_tac >> irule member_sequence_fresh >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac
  >>~- ([`step_inst_base (mk_inst _ CALLDATALOAD _ _) _ = _`],
    irule member_load_fresh >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  irule member_add_fresh >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem calldata_member_address_endpoint:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME q /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ fn_has_code st mid fn /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?endpoint. ~endpoint.vs_halted /\ endpoint.vs_current_bb = mid.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH mid.cs_current_insts /\
    eval_operand dp endpoint = SOME (q + n2w vo) /\
    eval_operand ep endpoint = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) initial
       else p + n2w ao) /\
    abi_decoder_operand_live mid.cs_next_var ep /\
    abi_decoder_operand_live mid.cs_next_var dp /\
    fresh_vars_wrt limit_st endpoint /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op endpoint = eval_operand op initial) /\
    endpoint.vs_memory = initial.vs_memory /\
    endpoint.vs_call_ctx = initial.vs_call_ctx /\
    endpoint.vs_data_section = initial.vs_data_section /\
    endpoint.vs_allocas = initial.vs_allocas /\
    endpoint.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn endpoint) ==>
      !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn endpoint = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn endpoint ==> mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >> drule calldata_member_address_shape >> strip_tac >>
  drule_all calldata_member_address_repeat >> strip_tac >>
  drule_all member_address_limit_fresh >> disch_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st mid)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st mid) initial` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `ready` |-> `mid`,
    `P` |-> `\s:venom_state. T`] (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  asm_simp_tac (srw_ss()) [eval_op_inst_idx, fresh_vars_wrt_def] >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  fs[fresh_vars_wrt_def]
QED
