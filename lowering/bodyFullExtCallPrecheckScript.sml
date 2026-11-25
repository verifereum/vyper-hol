(* Joint optional code check, before the external call consumes its operands. *)
Theory bodyFullExtCallPrecheck
Ancestors
  exprSimExtCallCase exprSimSliceExtcode fragGasSeqPtr bodyPtrBopAssert
  exprSimHashBoundary bodyFullGhostFrame allocaHistory
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  fragExec ptrDiscipline ptrSafeRun unitTransformDefs contextCodegenRel codegenRel
  fragGasOriginPtr fragGasOrigin fragGasPathPtr memSafeRun instMemFrontier gasEvents gasCount
  venomExecSemantics venomInst venomState finite_map pred_set words exprSafeOperand
  loweringStateRelDefs stateRelProj accountsRelProps loweringShapeRules
  bodyFullPathHistory bodyPtrMakeArrayEmission

Theorem precheck_code_shape[local]:
  compile_extcodesize_check addr a = ((),b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_next_var = a.cs_next_var + 1 /\ b.cs_next_id = a.cs_next_id + 2 /\
  b.cs_current_insts = a.cs_current_insts ++
    [mk_inst a.cs_next_id EXTCODESIZE [addr]
       [STRING #"%" (toString a.cs_next_var)];
     mk_inst (a.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString a.cs_next_var))] []]
Proof
  simp[compile_extcodesize_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, listTheory.APPEND_ASSOC,
       arithmeticTheory.ADD1] >> disch_then (SUBST1_TAC o SYM) >>
  simp[Once (GSYM listTheory.APPEND_ASSOC)]
QED

Theorem precheck_codesize_edge[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EXTCODESIZE [addr] [out]) /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
      with vs_inst_idx := SUC s.vs_inst_idx),
     G \\ out, tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id EXTCODESIZE [addr] [out]` >>
  qabbrev_tac `u = update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s` >>
  `step_inst_base i s = OK u` by simp[Abbr `i`, Abbr `u`, slice_extcodesize_step] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   (ctx_has_dalloca ctx ==> dalloca_no_wrap i s) /\
   ptr_inst_ok D lo 0 ctx func G tn i s` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, ptr_inst_ok_def, step_inst_non_invoke,
         slice_extcodesize_step, access_ok_def, taint_ok_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         Abbr `u`, update_var_def] >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var |+ (out,{}); t_stor := tn.t_stor;
     t_trans := tn.t_trans; t_imm := tn.t_imm|> = tn with t_var := tn.t_var |+ (out,{})` by
    simp[taint_component_equality] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `i`, Abbr `u`, mk_inst_def, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def, imm_taint_def, new_site_bytes_def,
       written_taint_def, source_memory_write_ranges_def, store_taint_def,
       adopt_reset_def, range_bytes_def, update_var_def, FLOOKUP_DEF,
       GSYM fmap_domsub, SF CONJ_ss, taint_component_equality]
QED

Theorem precheck_assert_edge[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (if w = 0w then Abort Revert_abort (revert_state (set_returndata [] s))
     else OK (s with vs_inst_idx := SUC s.vs_inst_idx),G,tn)
Proof
  strip_tac >> qabbrev_tac `i = mk_inst id ASSERT [op] []` >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   (ctx_has_dalloca ctx ==> dalloca_no_wrap i s)` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  Cases_on `w = 0w` >> gvs[]
  >- (`step_inst_base i s = Abort Revert_abort (revert_state (set_returndata [] s))` by
        simp[Abbr `i`, step_ASSERT_revert] >>
      rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
      >- (rewrite_tac[gas_origin_edge_def] >> simp[] >> qexists_tac `0` >>
          simp[step_inst_non_invoke, Abbr `i`, mk_inst_def, gas_events_step_def,
               mem_safe_step_non_invoke, source_memory_write_ranges_def,
               exit_result_def] >> fs[Abbr `i`, mk_inst_def]) >>
      rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0` >>
      simp[Abbr `i`, mk_inst_def, step_inst_non_invoke, gas_count_step_def,
           ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           exit_result_def] >> fs[Abbr `i`]) >>
  `step_inst_base i s = OK s` by simp[Abbr `i`, step_ASSERT_ok] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    simp[ptr_inst_ok_def, step_inst_non_invoke, Abbr `i`, mk_inst_def,
         step_ASSERT_ok, access_ok_def, taint_ok_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  drule_all straight_line_origin_ptr_edge >> simp[Abbr `i`, mk_inst_def, bop_assert_ghost]
QED

(* The two installed instructions share the same intermediate state in
   the ghost path, the terminal fetch, and the successful base run. *)
Theorem extcall_codesize_checked_edges:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let out = STRING #"%" (toString a.cs_next_var) in
  let w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32 in
  let v = update_var out w s in
  let u = v with vs_inst_idx := SUC s.vs_inst_idx in
  let t = u with vs_inst_idx := LENGTH b.cs_current_insts in
  let abort = Abort Revert_abort (revert_state (set_returndata [] u)) in
  let tm = tn with t_var := tn.t_var |+ (out,{}) in
  (?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) /\
        get_instruction bb u.vs_inst_idx = SOME (mk_inst (a.cs_next_id + 1) ASSERT [Var out] [])) /\
  step_inst_base (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s = OK v /\
  (w <> 0w ==> run_inst_seq (emitted_insts a b) s = OK v /\
                t = v with vs_inst_idx := LENGTH b.cs_current_insts) /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
  (!D explicit.
    gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G \\ out,tm) /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G \\ out,tm) []
      (if w = 0w then abort else OK t,G \\ out,tm) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (if w = 0w then abort else OK t,G \\ out,tm))
Proof
  strip_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  drule precheck_code_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < _ ==> _` (fn th =>
    strip_assume_tac (SIMP_RULE (boss_ss()) [] (Q.SPEC `0` th)) >>
    strip_assume_tac (SIMP_RULE (boss_ss()) [] (Q.SPEC `1` th))) >>
  qmatch_goalsub_abbrev_tac `update_var out w s` >>
  qabbrev_tac `u = update_var out w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (out,{})` >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK u,G \\ out,tm)` by
    (simp[NoAsms, Abbr `u`, Abbr `tm`, Abbr `w`] >> rpt gen_tac >>
     irule precheck_codesize_edge >> metis_tac[]) >>
  `~u.vs_halted /\ lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb u.vs_inst_idx = SOME (mk_inst (a.cs_next_id + 1) ASSERT [Var out] []) /\
   eval_operand (Var out) u = SOME w /\ op_taint tm (Var out) = {} /\ allocas_from lo u` by
    (simp[Abbr `u`, Abbr `tm`, update_var_def, allocas_from_def,
          eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def, arithmeticTheory.ADD1] >>
     fs[allocas_from_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (simp[Abbr `u`,update_var_def,allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o SRULE[allocas_below_fmp_def])) >>
  `update_var out w s with vs_inst_idx := SUC s.vs_inst_idx = u` by simp[Abbr `u`] >>
  qpat_x_assum `update_var _ _ _ with vs_inst_idx := _ = u` SUBST1_TAC >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  `step_inst_base (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s =
     OK (update_var out w s)` by simp[Abbr `w`, slice_extcodesize_step] >>
  qpat_assum `step_inst_base _ _ = _` (PURE_ONCE_REWRITE_TAC o single) >>
  simp_tac bool_ss [] >> conj_tac
  >- (strip_tac >>
      `eval_operand (Var out) (update_var out w s) = SOME w` by
        simp[eval_operand_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
      simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
           step_ASSERT_ok, Abbr `u`]) >>
  ntac 2 (conj_tac >- simp[Abbr `u`, update_var_def]) >>
  `SUC u.vs_inst_idx = LENGTH b.cs_current_insts` by simp[Abbr `u`, update_var_def] >>
  rpt gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G \\ out,tm)` by
    simp[] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G \\ out,tm) []
    (if w = 0w then Abort Revert_abort (revert_state (set_returndata [] u))
     else OK (u with vs_inst_idx := LENGTH b.cs_current_insts),G \\ out,tm)` by
    (qpat_assum `SUC _ = LENGTH _` (SUBST1_TAC o SYM) >>
     irule precheck_assert_edge >> metis_tac[]) >>
  `tm = tn with t_var := tn.t_var |+ (out,{})` by simp[Abbr `tm`] >>
  qpat_assum `tm = _` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `w = 0w` >>
  qpat_x_assum `gas_origin_ptr_edge _ (u,_,_) [] _` mp_tac
  >- (qpat_assum `w = 0w` (fn th => simp_tac bool_ss [th]) >> disch_tac >>
      qpat_assum `gas_origin_ptr_edge _ (u,_,_) [] _`
        (mp_then Any mp_tac (cj 3 gas_origin_ptr_path_rules)) >>
      simp_tac bool_ss [exit_result_def] >> disch_tac >>
      qpat_assum `gas_origin_ptr_edge _ (s,_,_) [] _`
        (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
      disch_then drule >> simp_tac bool_ss [listTheory.APPEND]) >>
  qpat_assum `w <> 0w` (fn th => simp_tac bool_ss [th]) >> disch_tac >>
  `~(u with vs_inst_idx := LENGTH b.cs_current_insts).vs_halted` by
    (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := LENGTH b.cs_current_insts,G \\ out,tm) []
     (OK (u with vs_inst_idx := LENGTH b.cs_current_insts),G \\ out,tm)` by
    (irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_origin_ptr_edge _ (u,_,_) [] _`
    (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
  disch_then drule >> simp_tac bool_ss [listTheory.APPEND] >> disch_tac >>
  qpat_assum `gas_origin_ptr_edge _ (s,_,_) [] _`
    (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
  disch_then drule >> simp_tac bool_ss [listTheory.APPEND]
QED

Theorem extcall_codesize_checked_steps:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let out = STRING #"%" (toString a.cs_next_var) in
  let w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32 in
  let v = update_var out w s in
  let u = v with vs_inst_idx := SUC s.vs_inst_idx in
  let t = u with vs_inst_idx := LENGTH b.cs_current_insts in
  let abort = Abort Revert_abort (revert_state (set_returndata [] u)) in
  let tm = tn with t_var := tn.t_var |+ (out,{}) in
  (?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) /\
        get_instruction bb u.vs_inst_idx = SOME (mk_inst (a.cs_next_id + 1) ASSERT [Var out] [])) /\
  step_inst_base (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s = OK v /\
  (w <> 0w ==> run_inst_seq (emitted_insts a b) s = OK v /\
                t = v with vs_inst_idx := LENGTH b.cs_current_insts) /\
  (!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G \\ out,tm) /\
    (w = 0w ==> gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G \\ out,tm) [] (abort,G \\ out,tm)) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (if w = 0w then abort else OK t,G \\ out,tm))
Proof
  strip_tac >> drule_all extcall_codesize_checked_edges >>
  disch_then (qspecl_then [`PG`, `G`] mp_tac) >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> first_x_assum (qspecl_then [`D`, `explicit`] strip_assume_tac) >>
  rpt conj_tac >> simp[] >> strip_tac >> gvs[]
QED

(* A single physical endpoint, including on rejection. *)
Theorem extcall_codesize_checked_path:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w
     then Abort Revert_abort (revert_state (set_returndata []
       (update_var (STRING #"%" (toString a.cs_next_var))
          (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := SUC s.vs_inst_idx)))
     else OK ((update_var (STRING #"%" (toString a.cs_next_var))
          (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx := LENGTH b.cs_current_insts),
     G \\ (STRING #"%" (toString a.cs_next_var)),
     tn with t_var := tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{}))
Proof
  strip_tac >> drule_all extcall_codesize_checked_steps >> simp[LET_THM]
QED

Theorem precheck_guard_agrees[local]:
  stmt_state_rel H ctx func cenv cx ee t /\ accounts_runtime_well_typed ee.accounts /\
  w2w aw = target ==>
  ((n2w (LENGTH (lookup_account (w2w aw) t.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_precheck_ok F NoneT target ee.accounts)
Proof
  strip_tac >>
  `accounts_agree H cx.txn.target ee.accounts t.vs_accounts` by
    metis_tac[stmt_state_rel_state_rel, state_rel_accounts] >>
  drule accountsRelPropsTheory.accounts_agree_lookup >>
  disch_then (qspec_then `target` strip_assume_tac) >>
  `LENGTH (lookup_account target ee.accounts).code <= 24576` by
    fs[vyperRuntimeAccountsTheory.accounts_runtime_well_typed_def,
       vyperRuntimeAccountsTheory.account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target ee.accounts).code < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  simp[vyperInterpreterTheory.ext_call_precheck_ok_def,
       vyperInterpreterTheory.ext_call_has_code_def, listTheory.NULL_EQ,
       n2w_11, listTheory.LENGTH_NIL]
QED

Theorem extcall_optional_precheck_steps[local]:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ w2w aw = target /\ op_taint tn addr = {} /\
  accounts_runtime_well_typed ee.accounts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ allocas_from lo s) ==>
  let checked = (ret_type = NoneT /\ ~skip) in
  let out = STRING #"%" (toString a.cs_next_var) in
  let w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32 in
  let v = update_var out w s in
  let r = if ext_call_precheck_ok skip ret_type target ee.accounts then
            OK (if checked then v with vs_inst_idx := LENGTH b.cs_current_insts else s)
          else Abort Revert_abort (revert_state
                 (set_returndata [] (v with vs_inst_idx := SUC s.vs_inst_idx))) in
  let G1 = if checked then G \\ out else G in
  let tn1 = if checked then tn with t_var := tn.t_var |+ (out,{}) else tn in
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G1,tn1)) /\
  (if checked then
    ?u. u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1) /\
          gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (u,G1,tn1) [] (r,G1,tn1)
   else r = OK s /\ G1 = G /\ tn1 = tn)
Proof
  strip_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  reverse (Cases_on `ret_type = NoneT /\ ~skip`)
  >- (`ext_call_precheck_ok skip ret_type target ee.accounts` by
        (Cases_on `ret_type` >> fs[vyperInterpreterTheory.ext_call_precheck_ok_def]) >>
      simp[] >> rpt strip_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  gvs[Excl "n2w_eq_0"] >>
  qabbrev_tac `out = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32` >>
  qabbrev_tac `u = update_var out w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (out,{})` >>
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ _ [] (r,_,_)` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G \\ out,tm) /\
     gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (u,G \\ out,tm) [] (r,G \\ out,tm) /\
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G \\ out,tm)` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s /\ allocas_from lo s` by metis_tac[] >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
          (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
     drule_all extcall_codesize_checked_edges >>
     disch_then (qspecl_then [`PG`,`G`] mp_tac) >>
     rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
     qpat_x_assum `!D explicit. _` (qspecl_then [`DF H`,`explicit`] strip_assume_tac) >>
     `(n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) <> 0w <=>
       ext_call_precheck_ok F NoneT (w2w aw) ee.accounts` by
       metis_tac[precheck_guard_agrees] >>
     Cases_on `ext_call_precheck_ok F NoneT (w2w aw) ee.accounts` >>
     fs[Excl "n2w_eq_0", Abbr `r`, Abbr `u`, Abbr `tm`, Abbr `out`, Abbr `w`] >>
     qpat_assum `s.vs_inst_idx = LENGTH _` (fn th => fs[th])) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `u` >> conj_tac >- simp[Abbr `u`,update_var_def] >>
  conj_tac >- simp[Abbr `u`] >> metis_tac[]
QED

Theorem precheck_scalar_observations[local]:
  ~not_fresh_at sp out /\ sa.cs_next_var <= sp.cs_next_var ==>
  (!x. not_fresh_at sp x ==>
    lookup_var x (update_var out w s with vs_inst_idx := idx) = lookup_var x s /\
    FLOOKUP (G \\ out) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var x) = op_taint tn (Var x)) /\
  (!op. safe_operand sp op ==>
    eval_operand op (update_var out w s with vs_inst_idx := idx) = eval_operand op s /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP (G \\ out) x = FLOOKUP G x)) /\
  (ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0 (G \\ out)
      (tn with t_var := tn.t_var |+ (out,{}))) /\
  (!cx ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
    ptr_mem_ok cx ty v op (G \\ out) (tn with t_var := tn.t_var |+ (out,{}))
      (update_var out w s with vs_inst_idx := idx))
Proof
  strip_tac >>
  `!x. not_fresh_at sp x ==> x <> out` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- (rpt strip_tac >>
    simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
         fmap_domsub, FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases >> simp[safe_operand_def, eval_operand_def, update_var_def,
    lookup_var_def, op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  conj_tac >- (simp[bodyPtrDefsTheory.ghost_kept_at_def] >> rpt strip_tac >>
    fs[op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  fs[safe_operand_def, bodyPtrDefsTheory.ptr_mem_ok_def,
     eval_operand_def, update_var_def, lookup_var_def, fmap_domsub, FLOOKUP_DRESTRICT] >>
  rename1 `FLOOKUP _ p` >> `p <> out` by metis_tac[] >> fs[FLOOKUP_UPDATE]
QED

Theorem precheck_request_scalar[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\ ~not_fresh_at sp out /\
  sp.cs_next_var <= sb.cs_next_var /\ sp.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = sp.cs_current_bb ==>
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee
    (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  qpat_x_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[extcall_request_ready_def] >> strip_tac >>
  qabbrev_tac `u = update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!x. not_fresh_at sp x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!op. safe_operand sp op ==> eval_operand op u = eval_operand op s` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee u` by
    (rpt strip_tac >> simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule hash_readonly_state_rel >> qexistsl_tac [`s`,`sp`] >>
     simp[update_var_def] >> rpt strip_tac >>
     `x <> out` by metis_tac[] >> simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  `!n b sz. local_region cenv ee.scopes u n b sz <=> local_region cenv ee.scopes s n b sz` by
    (simp[local_region_def] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 u` by
    (fs[loweringPostsTheory.wb_frame_def] >>
     simp[loweringPostsTheory.wb_frame_def] >> conj_tac
     >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     simp[Abbr `u`, update_var_def] >> conj_tac
     >- metis_tac[] >>
     irule exprSimPropsTheory.locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `local_ptrs_reserved cenv sb /\ EVERY (safe_operand sb) [addr;value;gas;buf;off;len;default_op]` by
    (fs[] >> metis_tac[local_ptrs_reserved_next_var, exprSafeOperandTheory.safe_operand_mono]) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt u` by
    (fs[extcall_default_ready_def, loweringPostsTheory.expr_val_rel_def,
        Abbr `u`, update_var_def, read_memory_def] >> metis_tac[]) >>
  `!a n. read_memory a n u = read_memory a n s` by
     simp[Abbr `u`, update_var_def, read_memory_def] >>
  `u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts` by
     simp[Abbr `u`, update_var_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
  fs[] >> simp[extcall_request_ready_def] >>
  conj_tac >- (qexists_tac `H` >> simp[]) >>
  conj_tac >- (qexistsl_tac [`live`,`buf_size`] >> simp[]) >>
  metis_tac[]
QED

(* The successful precheck leaves the request and its operands intact at the
   new compiler cut. Rejection instead exits before fetching the call. *)
Theorem extcall_precheck_to_call_steps:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) sp = ((),sb) /\ fn_has_code sp sb func /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sb = (success,sc) /\
  fn_has_code sb sc func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  op_taint tn addr = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn s) ==>
  ?r G1 tn1.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G1,tn1)) /\
    (if ret_type = NoneT /\ ~skip then
      ?u. u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
          !H. valid_horizon cx st0 H ee.storage_trace ==>
            gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1) /\
            gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (u,G1,tn1) [] (r,G1,tn1)
     else r = OK s /\ G1 = G /\ tn1 = tn) /\
    if ext_call_precheck_ok skip ret_type target ee.accounts then
      ?t out bb. r = OK t /\ success = Var out /\ ~not_fresh_at sb out /\
        lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME
          (mk_inst sb.cs_next_id (if stat then STATICCALL else CALL)
             (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
              else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]) /\
        t.vs_current_bb = sc.cs_current_bb /\ SUC t.vs_inst_idx = LENGTH sc.cs_current_insts /\
        extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
          addr value gas buf off len cap target value_opt calldata has_default
          default_op default_ty default_opt ee t /\
        allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_history func t /\
        t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
        t.vs_alloca_next = s.vs_alloca_next /\ tn1.t_mem = tn.t_mem /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn1 t) /\
        ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
         (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
         !H. valid_horizon cx st0 H ee.storage_trace /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s ==>
             ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
        (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s /\
          FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
        (!op. safe_operand sp op ==> eval_operand op t = eval_operand op s /\
          op_taint tn1 op = op_taint tn op /\
          (!x. op = Var x ==> FLOOKUP G1 x = FLOOKUP G x)) /\
        (!ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
          ptr_mem_ok cx ty v op G1 tn1 t)
    else exit_result r /\ expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r
Proof
  strip_tac >>
  qpat_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ allocas_from lo s` by metis_tac[] >>
  mp_tac (Q.INST [`a` |-> `sp`, `b` |-> `sb`] extcall_optional_precheck_steps) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `chk_out = STRING #"%" (toString sp.cs_next_var)` >>
  qabbrev_tac `w = (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32)` >>
  qabbrev_tac `t0 = if ret_type = NoneT /\ ~skip then
    update_var chk_out w s with vs_inst_idx := LENGTH sb.cs_current_insts else s` >>
  qabbrev_tac `Gc = if ret_type = NoneT /\ ~skip then G \\ chk_out else G` >>
  qabbrev_tac `tc = if ret_type = NoneT /\ ~skip then
    tn with t_var := tn.t_var |+ (chk_out,{}) else tn` >>
  reverse (Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`)
  >- (qexistsl_tac [`Abort Revert_abort (revert_state (set_returndata []
                    (update_var chk_out w s with vs_inst_idx := SUC s.vs_inst_idx)))`,`Gc`,`tc`] >>
      fs[exit_result_def,exprSimDefsTheory.expr_exit_def] >>
      qexists_tac `u` >> qpat_assum `s.vs_inst_idx = LENGTH _` (fn th => fs[th])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t0,Gc,tc)` by fs[] >>
  `alloca_history func t0` by
    (`stmt_state_rel H ctx func cenv cx ee s` by metis_tac[] >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t0,Gc,tc)` by simp[] >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `~not_fresh_at sp chk_out` by simp[Abbr `chk_out`,not_fresh_at_def] >>
  qpat_x_assum `stat <=> value_opt = NONE` kall_tac >>
  `extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
      addr value gas buf off len cap target value_opt calldata has_default
      default_op default_ty default_opt ee t0` by
    (Cases_on `ret_type = NoneT /\ ~skip`
     >- (simp[Abbr `t0`] >> irule precheck_request_scalar >> qexists_tac `sp` >>
         `compile_extcodesize_check addr sp = ((),sb)` by fs[] >>
         drule precheck_code_shape >> fs[]) >>
     `sb = sp` by (Cases_on `ret_type = NoneT` >> Cases_on `skip` >> fs[comp_return_def]) >>
     simp[Abbr `t0`] >> metis_tac[]) >>
  pop_assum $ mk_asm "after_check" >>
  `t0.vs_current_bb = sb.cs_current_bb /\ t0.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (asm "after_check" (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >> simp[]) >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choose_then `call_out` (qx_choose_then `call_bb` strip_assume_tac)) >>
  `~not_fresh_at sb call_out` by metis_tac[] >>
  qexistsl_tac [`OK t0`,`Gc`,`tc`] >> asm "after_check" (fn th => simp[th]) >>
  reverse (Cases_on `ret_type = NoneT /\ ~skip`)
  >- (Cases_on `ret_type = NoneT` >> Cases_on `skip` >>
      gvs[Abbr `t0`, Abbr `Gc`, Abbr `tc`]) >>
  drule_all precheck_scalar_observations >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [FORALL_AND_THM]) >>
  gvs[Abbr `t0`, Abbr `Gc`, Abbr `tc`] >>
  fs[update_var_def, allocas_from_def, bodyPtrDefsTheory.stor_taint_ok_at_def] >>
  rpt strip_tac
  >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
  >- (irule ghost_inv_at_exterior_frame >>
      goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `sp` >> simp[update_var_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  metis_tac[]
QED

Theorem extcall_precheck_to_call:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) sp = ((),sb) /\ fn_has_code sp sb func /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sb = (success,sc) /\
  fn_has_code sb sc func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  op_taint tn addr = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn s) ==>
  ?r G1 tn1.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G1,tn1)) /\
    if ext_call_precheck_ok skip ret_type target ee.accounts then
      ?t out bb. r = OK t /\ success = Var out /\ ~not_fresh_at sb out /\
        lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME
          (mk_inst sb.cs_next_id (if stat then STATICCALL else CALL)
             (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
              else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]) /\
        t.vs_current_bb = sc.cs_current_bb /\ SUC t.vs_inst_idx = LENGTH sc.cs_current_insts /\
        extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
          addr value gas buf off len cap target value_opt calldata has_default
          default_op default_ty default_opt ee t /\
        allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_history func t /\
        t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
        t.vs_alloca_next = s.vs_alloca_next /\ tn1.t_mem = tn.t_mem /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn1 t) /\
        ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
         (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
         !H. valid_horizon cx st0 H ee.storage_trace /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s ==>
             ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
        (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s /\
          FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
        (!op. safe_operand sp op ==> eval_operand op t = eval_operand op s /\
          op_taint tn1 op = op_taint tn op /\
          (!x. op = Var x ==> FLOOKUP G1 x = FLOOKUP G x)) /\
        (!ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
          ptr_mem_ok cx ty v op G1 tn1 t)
    else exit_result r /\ expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r
Proof
  strip_tac >> mp_tac extcall_precheck_to_call_steps >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `G1` (qx_choose_then `tn1`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`,`G1`,`tn1`] >> simp_tac bool_ss [] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
