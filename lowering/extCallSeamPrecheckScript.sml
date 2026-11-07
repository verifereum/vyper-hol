(* Optional external-call code-existence check. *)
Theory extCallSeamPrecheck
Ancestors
  extCallSeamOracle exprSimDefs fragGasPath accountsRelProps vyperRuntimeAccounts
  exprLowering exprLoweringProps rawCallFragPath emitHelperProps venomExecSemantics venomInst
  compileEnv emitHelper venomState exprSimProps loweringPosts vyperInterpreter vyperState vfmState list words

Theorem extcall_precheck_code_word:
  stmt_state_rel ctx func cenv cx es s /\
  accounts_runtime_well_typed es.accounts ==>
  ((n2w (LENGTH (lookup_account target s.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_has_code target es.accounts)
Proof
  strip_tac >>
  `accounts_agree cx es.accounts s.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `(lookup_account target es.accounts).code =
   (lookup_account target s.vs_accounts).code` by
    (fs[accounts_agree_def, lookup_account_def] >>
     Cases_on `target = cx.txn.target` >> gvs[] >>
     qpat_x_assum `_ with storage := _ = _` (mp_tac o AP_TERM ``\a:account_state. a.code``) >>
     simp[]) >>
  `LENGTH (lookup_account target es.accounts).code <= 24576` by
    fs[accounts_runtime_well_typed_def, account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target es.accounts).code < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  gvs[ext_call_has_code_def, NULL_EQ, wordsTheory.n2w_11,
      arithmeticTheory.LESS_MOD]
QED

Theorem step_extcall_codesize:
  eval_operand addr_op s = SOME aw ==>
  step_inst_base (mk_inst id EXTCODESIZE [addr_op] [out]) s =
    OK (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s)
Proof
  strip_tac >> simp[Once step_inst_base_def, mk_inst_def] >>
  simp[exec_read1_def]
QED

Theorem extcall_codesize_check_run:
  compile_extcodesize_check addr_op sa = ((),sb) /\
  eval_operand addr_op s = SOME aw ==>
  ?t. t = update_var (STRING #"%" (toString sa.cs_next_var))
           (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s /\
    run_inst_seq (emitted_insts sa sb) s =
      if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w
      then Abort Revert_abort (revert_state (set_returndata [] t)) else OK t
Proof
  strip_tac >>
  qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       GSYM listTheory.APPEND_ASSOC] >>
  drule step_extcall_codesize >>
  disch_then (qspecl_then [`STRING #"%" (toString sa.cs_next_var)`, `sa.cs_next_id`]
    assume_tac) >>
  qmatch_goalsub_abbrev_tac `update_var out cw s` >>
  `eval_operand (Var out) (update_var out cw s) = SOME cw` by
    simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `cw = 0w`
  >- (gvs[] >> drule_all step_ASSERT_revert >>
      disch_then (qspec_then `sa.cs_next_id + 1` assume_tac) >>
      gvs[run_inst_seq_def, mk_inst_def, is_terminator_def, Abbr `out`]) >>
  drule_all step_ASSERT_ok >>
  disch_then (qspec_then `sa.cs_next_id + 1` assume_tac) >>
  gvs[run_inst_seq_def, mk_inst_def, is_terminator_def, Abbr `out`, Abbr `cw`]
QED

Theorem extcall_codesize_check_shape:
  compile_extcodesize_check addr_op sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sb.cs_next_var = sa.cs_next_var + 1 /\ sb.cs_next_id = sa.cs_next_id + 2 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `cs_extends sa sb` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND_ASSOC]) >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id EXTCODESIZE [addr_op]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `cs'.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def]
QED

Theorem extcall_codesize_check_path:
  compile_extcodesize_check addr_op sa = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\
  accounts_runtime_well_typed es.accounts /\
  eval_operand addr_op s = SOME aw /\ w2w aw = target ==>
  frag_path ctx sa sb (\t. t = s)
    (\t. ext_call_has_code target es.accounts /\
      t = (update_var (STRING #"%" (toString sa.cs_next_var))
        (n2w (LENGTH (lookup_account target s.vs_accounts).code)) s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)
    (\r. ~ext_call_has_code target es.accounts /\ ?t. r = Abort Revert_abort t)
Proof
  strip_tac >>
  drule extcall_codesize_check_shape >> strip_tac >>
  drule_all extcall_codesize_check_run >> strip_tac >>
  drule_all extcall_precheck_code_word >>
  disch_then (qspec_then `target` assume_tac) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    gvs[cs_extends_def, same_blocks_def] >>
  irule frag_path_run_inst_seq >> fs[same_blocks_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `LENGTH (lookup_account (w2w aw) s.vs_accounts).code MOD dimword (:256) = 0` >>
  gvs[]
QED

Theorem extcall_optional_precheck_path:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sa = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\
  accounts_runtime_well_typed es.accounts /\
  eval_operand addr_op s = SOME aw /\ w2w aw = target ==>
  frag_path ctx sa sb (\t. t = s)
    (\t. ext_call_precheck_ok skip ret_type target es.accounts /\
      t = (if ret_type = NoneT /\ ~skip then
             update_var (STRING #"%" (toString sa.cs_next_var))
               (n2w (LENGTH (lookup_account target s.vs_accounts).code)) s
           else s) with vs_inst_idx := LENGTH sb.cs_current_insts)
    (\r. ~ext_call_precheck_ok skip ret_type target es.accounts /\
         expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r)
Proof
  strip_tac >> Cases_on `ret_type = NoneT /\ ~skip`
  >- (gvs[] >>
      drule_all (extcall_codesize_check_path |> Q.INST [`target` |-> `w2w aw`] |> SRULE []) >>
      disch_then (mp_then Any irule frag_path_conseq) >>
      simp[ext_call_precheck_ok_def, expr_exit_def] >>
      rpt strip_tac >> gvs[expr_exit_def]) >>
  `ext_call_precheck_ok skip ret_type target es.accounts` by
    (Cases_on `ret_type` >> gvs[ext_call_precheck_ok_def]) >>
  gvs[comp_return_def, frag_path_def] >> rpt strip_tac >>
  qexists_tac `0` >>
  `~(ret_type = NoneT /\ ~skip)` by metis_tac[] >>
  simp[] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  simp[fragGasPathTheory.gas_path_rules]
QED

Theorem extcall_take_outcome_obs[local]:
  take_call_outcome target data amount es = (res, consumed) ==>
  take_call_outcome target data amount (es with gas_obs := tail) =
    (res, consumed with gas_obs := tail)
Proof
  Cases_on `es.outcomes` >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.call_outcome_request_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  IF_CASES_TAC >> gvs[]
QED

Theorem extcall_adopt_outcome_obs[local]:
  SND (adopt_call_outcome rq oc (es with gas_obs := tail)) =
  (SND (adopt_call_outcome rq oc es)) with gas_obs := tail
Proof
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem extcall_source_prefix_obs:
  stmt_state_rel ctx func cenv cx es s /\
  outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  ?rq oc consumed.
    take_call_outcome target data amount es = (INL (rq,oc),consumed) /\
    LENGTH oc.co_returnData < dimword (:256) /\
    !tail.
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        amount' <- frame_call_value cx amount;
        eval_ext_call_effects cx target data amount' gas accounts
     od) (es with gas_obs := tail) =
    if ext_call_precheck_ok skip ret_type target es.accounts then
      if oc.co_success then
        (INL oc.co_returnData,
         (SND (adopt_call_outcome rq oc consumed)) with gas_obs := tail)
      else (INR (Error (RevertData oc.co_returnData)), consumed with gas_obs := tail)
    else (INR (Error (RuntimeError "ExtCall target has no code")),
          es with gas_obs := tail)
Proof
  strip_tac >> drule_all oracle_ext_call_source_cases >>
  disch_then (qspecl_then [`target`,`skip`,`ret_type`,`gas`,`data`,`amount`]
    strip_assume_tac) >>
  qexistsl_tac [`rq`,`oc`,`consumed`] >> simp[] >> gen_tac >>
  `~cx.txn.is_static /\ es.outcomes = SOME s.vs_outcomes` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule extcall_take_outcome_obs >>
  disch_then (qspec_then `tail` assume_tac) >>
  simp[get_accounts_def, check_def, assert_def, frame_call_value_def,
       eval_ext_call_effects_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `ext_call_precheck_ok skip ret_type target es.accounts` >> simp[] >>
  Cases_on `oc.co_success` >>
  simp[bind_def, return_def, raise_def, extcall_adopt_outcome_obs,
       vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> simp[]
QED

(* Metadata and transport for the optional, fresh-variable-only prefix. *)
Theorem extcall_optional_precheck_shape:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sa = ((),sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!cenv. local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sb) /\
  (!p. safe_operand sa p ==> safe_operand sb p)
Proof
  strip_tac >> Cases_on `ret_type = NoneT /\ ~skip`
  >- (gvs[] >> drule extcall_codesize_check_shape >> strip_tac >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> irule local_ptrs_reserved_next_var >>
          goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> irule exprSafeOperandTheory.safe_operand_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[comp_return_def, cs_extends_refl]
QED

Theorem extcall_optional_precheck_operands:
  pre = (if ret_type = NoneT /\ ~skip then
    update_var (STRING #"%" (toString sa.cs_next_var)) w s else s)
    with vs_inst_idx := idx /\ safe_operand sa p ==>
  eval_operand p pre = eval_operand p s
Proof
  strip_tac >> gvs[] >> simp[instIdxIndepTheory.eval_op_inst_idx] >>
  Cases_on `ret_type = NoneT /\ ~skip` >> simp[] >>
  Cases_on `p` >> gvs[exprSafeOperandTheory.safe_operand_def,
    eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]
QED

Theorem extcall_optional_precheck_stmt:
  pre = (if ret_type = NoneT /\ ~skip then
    update_var (STRING #"%" (toString sa.cs_next_var)) w s else s)
    with vs_inst_idx := idx /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel ctx func cenv cx es pre
Proof
  strip_tac >> gvs[] >> simp[stmt_state_rel_inst_idx] >>
  Cases_on `ret_type = NoneT /\ ~skip` >> simp[] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_optional_precheck_fields:
  pre = (if ret_type = NoneT /\ ~skip then
    update_var (STRING #"%" (toString sa.cs_next_var)) w s else s)
    with vs_inst_idx := idx ==>
  pre.vs_memory = s.vs_memory /\ pre.vs_allocas = s.vs_allocas /\
  pre.vs_alloca_next = s.vs_alloca_next /\ pre.vs_fmp = s.vs_fmp /\
  pre.vs_halted = s.vs_halted /\ pre.vs_returndata = s.vs_returndata /\
  pre.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> gvs[] >>
  Cases_on `ret_type = NoneT /\ ~skip` >> simp[update_var_def]
QED

Theorem extcall_optional_precheck_regions:
  pre = (if ret_type = NoneT /\ ~skip then
    update_var (STRING #"%" (toString sa.cs_next_var)) w s else s)
    with vs_inst_idx := idx /\ local_ptrs_reserved cenv sa ==>
  (local_region cenv scopes pre name b sz <=>
   local_region cenv scopes s name b sz)
Proof
  strip_tac >> gvs[] >>
  Cases_on `ret_type = NoneT /\ ~skip` >>
  simp[local_region_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  `!p. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       p <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def, not_fresh_at_def] >>
     first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem extcall_optional_precheck_wb:
  pre = (if ret_type = NoneT /\ ~skip then
    update_var (STRING #"%" (toString sp.cs_next_var)) w s else s)
    with vs_inst_idx := idx /\
  wb_frame cenv es initial s0 s /\ initial.cs_next_var <= sp.cs_next_var ==>
  wb_frame cenv es initial s0 pre
Proof
  strip_tac >> irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  qexists_tac `sp` >> simp[] >>
  gvs[] >> Cases_on `ret_type = NoneT /\ ~skip` >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED
