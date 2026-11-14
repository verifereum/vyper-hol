(* Code-presence checks shared by external-call and return-default paths. *)
Theory extCallCodeCheck
Ancestors
  exprSimSliceExtcode accountsRelProps vyperRuntimeAccounts
  fragGasSeq fragGasSeqAbort storageCopyGasPath exprSimHashBoundary
  exprSimWordArgs exprSimWordBuiltins revertReasonPrefixPtr
  exprLowering exprLoweringProps emitHelperProps emitHelper
  venomExecSemantics venomInst venomState compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vfmState list rich_list words finite_map

Theorem extcall_precheck_code_word:
  stmt_state_rel H ctx func cenv cx es s /\
  accounts_runtime_well_typed es.accounts ==>
  ((n2w (LENGTH (lookup_account target s.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_has_code target es.accounts)
Proof
  strip_tac >>
  `accounts_agree H cx es.accounts s.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `(lookup_account target es.accounts).code =
   (lookup_account target s.vs_accounts).code` by
    (drule accounts_agree_lookup >>
     disch_then (qspec_then `target` strip_assume_tac) >> simp[]) >>
  `LENGTH (lookup_account target es.accounts).code <= 24576` by
    fs[accounts_runtime_well_typed_def, account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target es.accounts).code < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  gvs[ext_call_has_code_def, NULL_EQ, wordsTheory.n2w_11,
      arithmeticTheory.LESS_MOD]
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
  drule slice_extcodesize_step >>
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

Theorem extcall_optional_check_path:
  (if enabled then compile_extcodesize_check addr_op else comp_return ()) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr_op s = SOME aw ==>
  ?t. t = (if enabled then
      update_var (STRING #"%" (toString sa.cs_next_var))
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
      else s) /\
    (if enabled /\
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w
     then ?j. gas_marked_path F ctx func s 0
       (Abort Revert_abort
         (revert_state (set_returndata [] t) with vs_inst_idx := j))
     else gas_marked_path F ctx func s 0
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb)
Proof
  reverse (Cases_on `enabled`) >> simp[comp_return_def] >> strip_tac
  >- (gvs[] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        (rewrite_tac[venom_state_component_equality] >> simp[]) >>
      simp[fragGasModeTheory.gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  drule extcall_codesize_check_run >> disch_then drule >> strip_tac >>
  drule extcall_codesize_check_shape >> strip_tac >>
  gvs[] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (fs[cs_extends_def, same_blocks_def] >>
     `new = []` by
       (qpat_x_assum `sb.cs_blocks = new ++ _`
          (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >> gvs[]) >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id EXTCODESIZE [addr_op]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
     simp[compile_extcodesize_check_def, comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `cs'.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (irule run_inst_seq_abort_zero_path >>
      conj_tac >- simp[] >>
      qexistsl [`bb`, `emitted_insts sa sb`] >>
      fs[mk_inst_def, is_terminator_def]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> gvs[DROP_LENGTH_APPEND]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  qpat_assum `emitted_insts _ _ = _`
    (fn th => pure_rewrite_tac[GSYM th]) >> strip_tac >>
  drule_all hash_run_path >> simp[mk_inst_def, update_var_def]
QED

Theorem extcall_optional_check_transport:
  (if enabled then compile_extcodesize_check addr_op else comp_return ()) sa = ((),sb) /\
  local_ptrs_reserved ce sa /\ sf.cs_next_var <= sa.cs_next_var /\
  u = ((if enabled then update_var (STRING #"%" (toString sa.cs_next_var)) w s
        else s) with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  local_ptrs_reserved ce sb /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_returndata = s.vs_returndata /\
  (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
     eval_operand op u = eval_operand op s) /\
  (!name b sz. local_region ce ee.scopes u name b sz <=>
               local_region ce ee.scopes s name b sz) /\
  (!H. stmt_state_rel H ctx func ce cx ee s ==>
       stmt_state_rel H ctx func ce cx ee u) /\
  (wb_frame ce es ee sf s0 s ==> wb_frame ce es ee sf s0 u)
Proof
  reverse (Cases_on `enabled`) >> simp[comp_return_def] >> strip_tac
  >- (gvs[] >>
      simp[same_blocks_def, cs_extends_def, stmt_state_rel_inst_idx,
           eval_operand_def, local_region_def, lookup_var_def,
           loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  drule extcall_codesize_check_shape >> strip_tac >>
  `not_local_ptr ce ee.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists `sa` >> simp[]) >>
  gvs[] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> simp[eval_operand_def] >>
      drule eval_operand_update_not_fresh >> simp[eval_operand_def])
  >- (drule local_region_update_nonlocal >>
      simp[local_region_def, lookup_var_def] >> metis_tac[])
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  strip_tac >> irule wb_frame_readonly_tail >>
  goal_assum (drule_at Any) >> qexists `sa` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
