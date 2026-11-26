(* The linked raw call can abort at the fetched instruction, before any
   oracle response or result suffix. *)
Theory bodyRawEarlyAbortMods
Ancestors
  exprSimRawCallCalldata exprSimRawCall gasOutcomeFullPostMods
  fragGasEmitCtrl createSizeExit bodyFullHashKeccakFixed stateRelProj
  venomExecSemantics venomInst venomState ptrDiscipline exprSimDefs
  words ptrSafeRun fragGasOriginPtr fragExec gasEvents gasCount memLocDefs
  bodyPtrDefs memSafeRun contextCodegenRel codegenRel exprLoweringProps

Theorem raw_fetched_abort_edge[local]:
  inst = mk_inst id (case ct of
            RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if ct = RegularCall then [gas;addr;value;dp;dl;op;Lit (n2w cap)]
     else [gas;addr;dp;dl;op;Lit (n2w cap)]) [out] /\
  eval_operand gas t = SOME gw /\ eval_operand addr t = SOME aw /\
  eval_operand value t = SOME vw /\ eval_operand dp t = SOME iw /\
  eval_operand dl t = SOME nw /\ eval_operand op t = SOME ow /\
  (t.vs_outcomes = [] \/ (ct = RegularCall /\ t.vs_call_ctx.cc_static /\ vw <> 0w)) /\
  (nw <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n nw)) /\
  (n2w cap <> (0w:bytes32) ==>
    ?p. op = Var p /\ ptr_covers G tn p t (w2n (n2w cap:bytes32))) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> j NOTIN tn.t_mem) /\
  mem_safe_step 0 ctx inst t /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
    (Abort ExHalt_abort (halt_state (set_returndata [] t)),G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!fuel. step_inst fuel ctx inst t =
    Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`inst = mk_inst _ _ _ _`, `eval_operand gas t = _`,
        `eval_operand addr t = _`, `eval_operand value t = _`,
        `eval_operand dp t = _`, `eval_operand dl t = _`,
        `eval_operand op t = _`, `t.vs_outcomes = [] \/ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 8 disch_tac >>
     Cases_on `ct` >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
         eval_operand_def, exec_ext_call_abort_iff, exec_delegatecall_abort_iff] >>
     Cases_on `t.vs_call_ctx.cc_static /\ vw <> 0w` >>
     gvs[exec_ext_call_abort_iff]) >>
  `source_memory_read_ranges inst t = [(w2n iw,w2n nw)] /\
   source_memory_write_ranges inst t = [(w2n ow,w2n (n2w cap:bytes32))]` by
    (Cases_on `ct` >>
     simp[mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
          mem_read_ops_def, mem_write_ops_def, memory_range_of_operands_def,
          eval_operand_def]) >>
  `w2n (n2w cap:bytes32) <> 0 ==>
   ?v b sz. op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= w2n ow /\ w2n ow + w2n (n2w cap:bytes32) <= b + sz` by
    (pure_rewrite_tac [w2n_eq_0] >> strip_tac >>
     qpat_assum `(n2w cap:bytes32) <> 0w ==> _` drule >>
     strip_tac >> gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `w2n nw <> 0 ==>
   ?v b sz. dp = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= w2n iw /\ w2n iw + w2n nw <= b + sz` by
    (pure_rewrite_tac [w2n_eq_0] >> strip_tac >>
     qpat_assum `nw <> 0w ==> _` drule >>
     strip_tac >> gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `w2n (n2w cap:bytes32) <> 0 ==> _`
    (assume_tac o SRULE [w2n_n2w]) >>
  `access_ok lo G func inst t` by
    (Cases_on `ct` >>
     simp[access_ok_def, mk_inst_def, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> first_assum irule >> simp[]) >>
  `taint_ok func tn inst t` by
    (qpat_assum `EVERY _ inst.inst_operands` mp_tac >>
     qpat_assum `source_memory_read_ranges inst t = _` mp_tac >>
     qpat_assum `!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[taint_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst t` by simp[ptr_inst_ok_def] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   gas_events_step 0 ctx func.fn_name inst t = [] /\ gas_count_step 0 ctx inst t = 0` by
    (Cases_on `ct` >> simp[mk_inst_def, gas_events_step_def, gas_count_step_def]) >>
  qpat_x_assum `inst = mk_inst _ _ _ _` kall_tac >>
  irule exit_inst_origin_ptr >> simp[exit_result_def]
QED

Theorem raw_abort_source[local]:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\ (flags.rcf_is_static ==> amount = 0) /\
  es.outcomes = SOME t.vs_outcomes /\
  (t.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)) ==>
  !tail. eval_raw_call cx flags target bs amount gkw (es with gas_obs := tail) =
    (INR (Error (RuntimeError (if cx.txn.is_static /\ amount <> 0
                               then "write in static context" else "take_call_outcome"))),
     es with gas_obs := tail)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (simp[] >> irule raw_call_static_value_abort >> metis_tac[]) >>
  simp[] >> irule raw_call_oracle_empty >> simp[] >> metis_tac[]
QED

Theorem raw_call_early_abort_outcome_mods:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\
  (flags.rcf_is_static ==> amount = 0) /\ amount < dimword (:256) /\
  ct = (if flags.rcf_is_delegate then DelegateCall
        else if flags.rcf_is_static then StaticCall else RegularCall) /\
  t.vs_call_ctx.cc_static = cx.txn.is_static /\ es.outcomes = SOME t.vs_outcomes /\
  (t.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es t) /\
  inst = mk_inst id (case ct of
            RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if ct = RegularCall then [gas;addr;value;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]
     else [gas;addr;dp;dl;op;Lit (n2w flags.rcf_max_outsize)]) [out] /\
  eval_operand gas t = SOME gw /\ eval_operand addr t = SOME (w2w target) /\
  eval_operand value t = SOME (n2w amount) /\ eval_operand dp t = SOME iw /\
  eval_operand dl t = SOME nw /\ eval_operand op t = SOME ow /\
  (nw <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n nw)) /\
  (n2w flags.rcf_max_outsize <> (0w:bytes32) ==>
    ?p. op = Var p /\ ptr_covers G tn p t (w2n (n2w flags.rcf_max_outsize:bytes32))) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> j NOTIN tn.t_mem) /\
  mem_safe_step 0 ctx inst t /\ allocas_from lo t /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (eval_raw_call cx flags target bs amount gkw) (es,t,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_exit >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`es`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`,
    `INR (Error (RuntimeError (if cx.txn.is_static /\ amount <> 0
                               then "write in static context" else "take_call_outcome")))`, `tn`] >>
  simp[exit_result_def] >>
  conj_tac >- (irule raw_abort_source >> simp[] >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  first_x_assum drule >> disch_tac >>
  conj_tac
  >- ((`t.vs_outcomes = [] \/
        (ct = RegularCall /\ t.vs_call_ctx.cc_static /\ (n2w amount:bytes32) <> 0w)` by
       (simp[GSYM w2n_eq_0] >> metis_tac[]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
        (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
      irule raw_fetched_abort_edge >>
      simp[] >>
      qexistsl_tac [`addr`,`w2w target`,`flags.rcf_max_outsize`,`ct`,`dl`,`dp`,
        `gas`,`gw`,`id`,`iw`,`nw`,`op`,`out`,`ow`,`value`,`n2w amount`] >>
      TRY (qpat_assum `inst = _` (fn th => pure_rewrite_tac [GSYM th])) >>
      simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      once_rewrite_tac[GSYM w2n_eq_0] >>
      FILTER_ASM_REWRITE_TAC
        (can (match_term ``w2n (n2w _ : bytes32) = _``)) [] >>
      simp[] >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `n2w flags.rcf_max_outsize <> (0w:bytes32) ==> _`
        ACCEPT_TAC) >>
      TRY (qpat_assum `!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> _`
        ACCEPT_TAC) >>
      TRY (qpat_assum `mem_safe_step 0 ctx _ t` ACCEPT_TAC) >>
      TRY (qpat_assum `EVERY _ inst.inst_operands` ACCEPT_TAC) >>
      TRY (qpat_assum `inst = _` ACCEPT_TAC) >>
      TRY (qpat_assum `inst = _` mp_tac >>
           qpat_assum `EVERY _ inst.inst_operands` mp_tac >> simp[mk_inst_def]) >>
      TRY (qpat_assum `inst = _` mp_tac >>
           qpat_assum `mem_safe_step 0 ctx inst t` mp_tac >> simp[mk_inst_def]) >>
      gvs[wordsTheory.w2n_n2w])) >>
  simp[expr_exit_def, halt_exit_def, create_size_exit_ok_def] >>
  `MEM func ctx.ctx_functions` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >>
     strip_tac >> drule lookup_function_MEM >> simp[]) >>
  rpt strip_tac >> drule_all oversized_create_abort_at_cursor >>
  Cases_on `ct` >> simp[mk_inst_def]
QED
