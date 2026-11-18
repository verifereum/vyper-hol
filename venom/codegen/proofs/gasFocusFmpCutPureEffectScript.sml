Theory gasFocusFmpCutPureEffect
Ancestors
  fmpStageRel o1LowerDloadShared venomExecSemantics venomState venomInst
  vfmState finite_map list

val reads = ``[CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
  COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
  CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
  BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD]``;

Theorem cut_context_read[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^reads /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst_base inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out x t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
   s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
   s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section` by
    gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!a. (lookup_account a s.vs_accounts).balance =
          (lookup_account a t.vs_accounts).balance /\
        (lookup_account a s.vs_accounts).nonce =
          (lookup_account a t.vs_accounts).nonce /\
        (lookup_account a s.vs_accounts).code =
          (lookup_account a t.vs_accounts).code` by
    (fs[fmp_stage_rel_def] >> drule ld_shared_accounts_fields >>
     simp[lookup_account_def] >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     simp[account_state_component_equality]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  fs[MEM] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM, account_empty_def] >> metis_tac[]
QED
