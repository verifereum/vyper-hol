(* Policy-independent source normalization for oracle external calls. *)
Theory extCallSeamOracle
Ancestors
  exprLoweringProps extCallOracleStep exprSimRawCallCalldata
  exprSimRawCall exprSimPrecompiles exprSimHash immutableMemoryFrame
  list rich_list compileEnv loweringSlice venomMemDefs venomState
  loweringPosts exprSimProps venomInst venomExecSemantics exprSimOperands
  emitHelperProps rawCallFragPath exprSafeOperand
  vyperInterpreter vyperCallOutcome vyperState

Theorem oracle_ext_call_source:
  state_rel func cenv cx es s /\
  take_call_outcome target data amount es = (INL (rq,oc), consumed) ==>
  (do amount' <- frame_call_value cx amount;
      eval_ext_call_effects cx target data amount' gas accounts
   od) es =
  if oc.co_success then
    (INL oc.co_returnData, SND (adopt_call_outcome rq oc consumed))
  else (INR (Error (RevertData oc.co_returnData)), consumed)
Proof
  strip_tac >>
  `~cx.txn.is_static /\ es.outcomes = SOME s.vs_outcomes` by
    fs[compileEnvTheory.state_rel_def] >>
  simp[frame_call_value_def, eval_ext_call_effects_def,
       bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `oc.co_success` >>
  simp[return_def, raise_def, bind_def, adopt_call_outcome_def,
       pairTheory.UNCURRY]
QED

Theorem oracle_ext_call_source_cases:
  stmt_state_rel ctx func cenv cx es s /\
  outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  ?rq oc consumed.
    take_call_outcome target data amount es = (INL (rq,oc),consumed) /\
    LENGTH oc.co_returnData < dimword (:256) /\
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        amount' <- frame_call_value cx amount;
        eval_ext_call_effects cx target data amount' gas accounts
     od) es =
    if ext_call_precheck_ok skip ret_type target es.accounts then
      if oc.co_success then
        (INL oc.co_returnData, SND (adopt_call_outcome rq oc consumed))
      else (INR (Error (RevertData oc.co_returnData)), consumed)
    else (INR (Error (RuntimeError "ExtCall target has no code")), es)
Proof
  strip_tac >>
  `state_rel func cenv cx es s /\ IS_SOME es.outcomes` by
    fs[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  drule_all raw_call_typed_outcome >>
  disch_then (qspecl_then [`target`, `data`, `amount`] strip_assume_tac) >>
  drule_all calldata_take_call_outcome_bound >> strip_tac >>
  drule_all oracle_ext_call_source >>
  disch_then (qspecl_then [`gas`, `es.accounts`] assume_tac) >>
  qexistsl [`rq`, `outcome`, `es1`] >> simp[] >>
  simp[get_accounts_def, bind_def, ignore_bind_def, return_def,
       check_def, assert_def, raise_def] >>
  Cases_on `ext_call_precheck_ok skip ret_type target es.accounts` >>
  gvs[bind_def]
QED

(* The instruction boundary: no caller-specific result-buffer policy. *)
Theorem oracle_call_memory_exec:
  stmt_state_rel ctx func cenv cx es s /\ inst.inst_outputs = [out] /\
  w2w aw = target /\
  w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n ro \/ w2n ro + w2n rz <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + w2n rz <= off) ==>
  ?t. exec_ext_call inst s (gas:bytes32) aw vw ao az (ro:bytes32) (rz:bytes32) stat =
        OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro) (LENGTH (TAKE (w2n rz) outcome.co_returnData)) t.vs_memory =
      TAKE (w2n rz) outcome.co_returnData /\
    state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) t
Proof
  strip_tac >>
  `state_rel func cenv cx es s` by fs[stmt_state_rel_def] >>
  drule_all_then
    (strip_assume_tac o Q.ISPECL [`gas:bytes32`, `ro:bytes32`, `rz:bytes32`])
    exec_ext_call_oracle_step >>
  qabbrev_tac `payload = TAKE (w2n rz) outcome.co_returnData` >>
  qabbrev_tac `dst = w2n ro` >>
  `LENGTH payload <= w2n rz` by
    simp[Abbr `payload`, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (write_memory_with_expansion dst payload s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     conj_tac >- simp[write_memory_with_expansion_def, LET_THM] >>
     reverse conj_tac >- fs[state_rel_def] >>
     rpt strip_tac >> irule hash_write_memory_disjoint >>
     first_x_assum drule_all >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es (write_memory_with_expansion dst payload s)` by
    (irule write_memory_stmt_state_rel >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[Abbr `dst`] >> decide_tac) >>
  suspend "fields"
QED

Resume oracle_call_memory_exec[fields]:
  `s' = (write_memory_with_expansion dst payload s) with
    <| vs_outcomes := s'.vs_outcomes; vs_requests := s'.vs_requests;
       vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient;
       vs_logs := s'.vs_logs; vs_pending_deletions := s'.vs_pending_deletions;
       vs_returndata := s'.vs_returndata |>` by
    (qpat_x_assum `_ = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>` mp_tac >>
     qpat_x_assum `s'.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venom_state_component_equality, write_memory_with_expansion_def, LET_THM]) >>
  `local_ptrs_rel func cenv es.scopes s' /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s'` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `_ = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _ |>` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> once_asm_rewrite_tac[] >>
     simp[local_ptrs_rel_oracle_fields, stmt_state_rel_def, state_rel_def,
          immutables_rel_def] >> strip_tac >> simp[]) >>
  qexists_tac `s'` >> simp[hash_write_memory_read_self] >>
  metis_tac[]
QED

Finalise oracle_call_memory_exec

Theorem oracle_call_stmt_frame:
  take_call_outcome target calldata value_opt es = (INL (rq,outcome),es1) /\
  es' = SND (adopt_call_outcome rq outcome es1) /\
  stmt_state_rel ctx func cenv cx es s /\ state_rel func cenv cx es' t /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels ==>
  stmt_state_rel ctx func cenv cx es' t
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables` by
    (drule raw_call_take_adopt_fields >> simp[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`,`es`] >> gvs[] >>
      reverse conj_tac >- fs[stmt_state_rel_def] >>
      simp[local_region_def, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`es`,`s`] >> simp[]
QED

Theorem oracle_call_wb_frame:
  wb_frame cenv es sa s0 s /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_memory = (write_memory_with_expansion dst payload s).vs_memory /\
  (!aid b sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    compileEnv$regions_disjoint dst (LENGTH payload) b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    compileEnv$regions_disjoint dst (LENGTH payload) b sz) /\
  ~not_fresh_at sa out ==>
  wb_frame cenv es sa s0 (update_var out result t)
Proof
  strip_tac >>
  `!b sz. compileEnv$regions_disjoint dst (LENGTH payload) b sz ==>
    mem_bytes_at b sz (update_var out result t).vs_memory =
    mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> simp[update_var_def] >>
     asm_rewrite_tac[] >> irule hash_write_memory_disjoint >>
     fs[compileEnvTheory.regions_disjoint_def]) >>
  fs[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, update_var_def] >>
      `x <> out` by metis_tac[] >>
      simp[finite_mapTheory.FLOOKUP_UPDATE] >>
      fs[lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED

Theorem oracle_call_emit_run[local]:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + w2n (n2w cap : bytes32) <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/
      w2n ro + w2n (n2w cap : bytes32) <= off) ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro)
      (LENGTH (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData)) t.vs_memory =
      TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `emit_op _ ops sa = (ok,sb)` >>
  qabbrev_tac `call_inst = mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    ops [STRING #"%" (toString sa.cs_next_var)]` >>
  `call_inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `call_inst`, mk_inst_def] >>
  drule_all_then (qspec_then `gas`
    (qx_choose_then `oracle_state` strip_assume_tac))
    (oracle_call_memory_exec |> Q.INST
      [`inst` |-> `call_inst`, `vw` |-> `if stat then 0w else val_word`,
       `out` |-> `STRING #"%" (toString sa.cs_next_var)`,
       `rz` |-> `(n2w cap : bytes32)`]) >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `oracle_state.vs_vars = s.vs_vars /\ oracle_state.vs_allocas = s.vs_allocas /\
   oracle_state.vs_alloca_next = s.vs_alloca_next /\
   oracle_state.vs_fmp = s.vs_fmp /\ oracle_state.vs_labels = s.vs_labels` by
    (qpat_x_assum `oracle_state = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  drule_all_then (qspec_then `bool_to_word outcome.co_success`
    (qx_choose_then `result_state` strip_assume_tac)) raw_call_result_frame >>
  suspend "result"
QED

Resume oracle_call_emit_run[result]:
  `run_inst_seq (emitted_insts sa sb) s = OK result_state` by
    (fs[Abbr `ops`] >> irule raw_call_emit_run >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[eval_operand_def] >> qexists_tac `val_word` >>
     gvs[Abbr `call_inst`, bool_to_word_def] >>
     Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) oracle_state` by
    (irule oracle_call_stmt_frame >> simp[] >>
     goal_assum (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
     simp[] >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`oracle_state`,`result_state`] >> simp[] >>
  qpat_assum `result_state = _` (fn th => once_rewrite_tac[th]) >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]
QED

Finalise oracle_call_emit_run

Theorem oracle_call_emit_path[local]:
  emit_op (if stat then STATICCALL else CALL) ops sa = (ok,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  irule frag_path_run_inst_seq >>
  Cases_on `stat` >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem oracle_call_path:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  wb_frame cenv initial_es initial s0 s /\ initial.cs_next_var <= sa.cs_next_var /\
  (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    compileEnv$regions_disjoint (w2n ro) cap b sz) /\
  (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    compileEnv$regions_disjoint (w2n ro) cap b sz) ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv initial_es initial s0 u /\
      eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
      u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_memory = (write_memory_with_expansion (w2n ro)
        (TAKE cap outcome.co_returnData) s).vs_memory /\
      u.vs_returndata = outcome.co_returnData /\
      mem_bytes_at (w2n ro) (LENGTH (TAKE cap outcome.co_returnData)) u.vs_memory =
        TAKE cap outcome.co_returnData /\
      (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s)) (\r. F)
Proof
  strip_tac >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) oracle_call_emit_run >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`val_word`, `ro`, `gas`, `aw`] mp_tac) >>
  impl_tac
  >- (fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `oracle` (qx_choose_then `u` strip_assume_tac)) >>
  suspend "frame"
QED

Resume oracle_call_path[frame]:
  `oracle.vs_vars = s.vs_vars /\ oracle.vs_allocas = s.vs_allocas /\
   oracle.vs_fmp = s.vs_fmp /\ oracle.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `oracle = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `~not_fresh_at initial (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `wb_frame cenv initial_es initial s0 u` by
    (qpat_assum `u = update_var _ _ oracle` (fn th => once_rewrite_tac[th]) >>
     irule oracle_call_wb_frame >> simp[] >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
     qexistsl_tac [`w2n ro`, `TAKE cap outcome.co_returnData`] >> simp[] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (drule_all_then mp_tac) >>
     simp[compileEnvTheory.regions_disjoint_def, LENGTH_TAKE_EQ] >> decide_tac) >>
  suspend "post"
QED

Resume oracle_call_path[post]:
  drule_all oracle_call_emit_path >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_path_conseq)) >> simp[] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx] >>
  qpat_x_assum `u = update_var _ _ oracle` SUBST_ALL_TAC >>
  simp[update_var_def] >>
  gvs[] >> rpt strip_tac >>
  Cases_on `p` >> gvs[safe_operand_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]
QED

Finalise oracle_call_path
