(* Linked code Slice after the two scalar operand reads. *)
Theory bodySliceSelfRouteMods
Ancestors
  bodySliceCodeQueryLandingMods bodySliceCodeBoundsCutMods
  bodySliceCodeCopyResourcesMods bodySliceCodeSuffixPostMods bodySliceBoundsExitMods
  bodyFullPredsMods gasOutcomeFullZeroPrefixMods exprSimSliceSource
  bodyPtrBytestringBuiltinsSlice bodyPtrBytestringBuiltinsBuffer
  freshWrites localPtrsProps stateRelProj ptrDiscipline compileEnv fragExec
  bodySliceSelfCompileMods bodySliceCodeTailMods bodySliceCodeOperandPreMods
  bodySliceExternalSourceMods exprSimSliceSelfCode exprSimFullBundleProps
  exprBodyPreProps exprSimSliceOrdinaryContinue bodyInvCodeProps
  gasOutcomeFullPostMods vyperStorageTrace vyperStorageFootprint vyperState
  exprLoweringProps exprSimHypsDefs bodyFullHashKeccakFixed
  loweringStateRelDefs venomExecSemantics venomInst
  bodyForcedStorageFrameMods exprSimWordArgs wordArgsPtr loweringPosts words
  exprLowering context bodyFullPostsMods
Libs horizonTypeLib monadsyntax

Theorem slice_self_suffix_mods:
  emit_op query_op query_ops sa = (limit,sc) /\
  compile_assert_slice_bounds start cnt limit sc = ((),sd) /\
  compile_slice_out_buf N sd = ((out,data),se) /\
  emit_void copy_op copy_ops se = ((),sf) /\
  emit_void MSTORE [out;cnt] sf = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  MEM query_op [CODESIZE;EXTCODESIZE] /\ LENGTH query_ops <= 1 /\
  (!arg. MEM arg query_ops ==> op_taint tn arg = {}) /\
  step_inst_base
    (mk_inst sa.cs_next_id query_op query_ops
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH code)) s) /\
  eval_operand start s = SOME (n2w i) /\
  eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
  (!l. start <> Label l /\ cnt <> Label l) /\
  ((copy_op = CODECOPY /\ copy_ops = [data;start;cnt]) \/
   (copy_op = EXTCODECOPY /\ copy_ops = [addr;data;start;cnt] /\
    (?aw. eval_operand addr s = SOME aw) /\
    op_taint tn addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sa x) /\ (!l. addr <> Label l))) /\
  (!v wd. i+k <= LENGTH code /\
    v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
    v.vs_code = s.vs_code /\ eval_operand data v = SOME wd /\
    eval_operand start v = SOME (n2w i) /\ eval_operand cnt v = SOME (n2w k) /\
    (copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
    step_inst_base (mk_inst se.cs_next_id copy_op copy_ops []) v =
      OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i code)) v)) /\
  i < dimword (:256) /\ 0 < k /\ k < dimword (:256) /\ k <= n /\
  LENGTH code < dimword (:256) /\
  e = Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args /\
  N = type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) /\
  32+n <= N /\ N < dimword (:256) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!tail. source (es with gas_obs := tail) =
    ((case evaluate_slice (BytesV code) (IntV (&i)) (IntV (&k)) n of
        INL v => INL (Value v) | INR err => INR (Error err)),
     es with gas_obs := tail)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn)
    (\H res ee HG tm t.
      res = INL (Value (BytesV (TAKE k (DROP i code)))) /\
      vv_post_mods H ctx func cenv cx e es sa sb s ee
        (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
        ee (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee HG tm t /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic n)))
        (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) ee HG tm t /\
      ptr_buf_ok cenv e out HG t /\
      ghost_kept_at lo cenv es sa G tn s HG tm)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `alloca_inv s` by (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  `cs_extends sa sc` by metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `cs_extends sc sd` by (drule slice_bounds_extends >> simp[]) >>
  `cs_extends sd se` by
    (drule compile_slice_out_buf_compiler_parts >> metis_tac[cs_extends_trans]) >>
  `cs_extends se sf /\ cs_extends sf sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `cs_extends sd sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `cs_extends sa sc` mp_tac >> qpat_assum `cs_extends sc sd` mp_tac >>
     qpat_assum `cs_extends sd sb` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fn_has_code_split,cs_extends_trans]) >>
  drule_all slice_code_query_landing_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`zq`,`Gq`,`tq`] strip_assume_tac)) >>
  `alloca_inv zq` by
    (irule alloca_inv_fields >> qexists_tac `s` >>
     qpat_assum `zq = _` (pure_once_rewrite_tac o single) >> simp[]) >>
  `allocas_from lo zq /\ lo <= zq.vs_alloca_next` by
    (qpat_assum `zq = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `allocas_from lo s` mp_tac >>
     simp_tac bool_ss [allocas_from_def,venomStateTheory.venom_state_accfupds] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zq` by
    (qpat_assum `zq = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     pure_rewrite_tac [allocas_below_fmp_def,venomStateTheory.venom_state_accfupds] >>
     disch_then ACCEPT_TAC) >>
  reverse (Cases_on `i+k <= LENGTH code`)
  >- suspend "abort" >> suspend "copy"
QED

Resume slice_self_suffix_mods[abort]:
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Gq`,`zq`,`tq`] >> simp[] >>
  irule slice_bounds_exit_mods >>
  reverse conj_tac
  >- (simp[] >> qexistsl_tac [`LENGTH code`,`cnt`,`i`,`k`,`limit`,`sc`,`sd`,`start`] >>
      simp[] >> qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
      simp[listTheory.MEM] >> metis_tac[]) >>
  qpat_assum `!tail. source _ = _` mp_tac >> simp[slice_bytes_nat]
QED

Resume slice_self_suffix_mods[copy]:
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  drule_all slice_code_bounds_cut_mods >>
  disch_then (qspecl_then [`es`,`cx`]
    (qx_choosel_then [`zb`,`Gb`,`tb`] strip_assume_tac)) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es zb` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` (drule_then ACCEPT_TAC)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zb /\
    zb.vs_alloca_next + pending_alloca_size func zb <= w2n zb.vs_initial_fmp` by
    (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `zb.vs_accounts = s.vs_accounts /\ zb.vs_call_ctx = s.vs_call_ctx /\ zb.vs_code = s.vs_code` by
    (qpat_assum `zb = _` (pure_once_rewrite_tac o single) >> simp[]) >>
  `eval_operand start zb = SOME (n2w i) /\ eval_operand cnt zb = SOME (n2w k) /\
   op_taint tb start = {} /\ op_taint tb cnt = {}` by
    (qpat_assum `!op. MEM op [start;cnt;limit] ==> eval_operand op zb = _ /\ _`
      (fn th => map_every (fn opnd => qspec_then opnd mp_tac th) [`start`,`cnt`]) >> simp[]) >>
  `!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sd x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` irule >> simp[]) >>
  `copy_op = EXTCODECOPY ==> eval_operand addr zb = eval_operand addr s /\
    op_taint tb addr = op_taint tn addr` by
    (strip_tac >> qpat_assum `(_ = CODECOPY /\ _) \/ (_ = EXTCODECOPY /\ _)`
       (DISJ_CASES_THEN strip_assume_tac)
     >- gvs[] >>
     qpat_assum `!op. _ ==> eval_operand op zb = eval_operand op s /\ _`
       (qspec_then `addr` mp_tac) >> simp[]) >>
  Q.SUBGOAL_THEN `((copy_op = CODECOPY /\ copy_ops = [data;start;cnt]) \/
    (copy_op = EXTCODECOPY /\ copy_ops = [addr;data;start;cnt] /\
     (?aw. eval_operand addr zb = SOME aw) /\ op_taint tb addr = {} /\
     (!x. addr = Var x ==> not_fresh_at sd x)))` ASSUME_TAC
  >- (qpat_assum `(_ = CODECOPY /\ _) \/ (_ = EXTCODECOPY /\ _)`
       (DISJ_CASES_THEN strip_assume_tac) >- simp[] >> simp[] >> metis_tac[]) >>
  `!v wd. v.vs_accounts = zb.vs_accounts /\ v.vs_call_ctx = zb.vs_call_ctx /\
    v.vs_code = zb.vs_code /\ eval_operand data v = SOME wd /\
    eval_operand start v = SOME (n2w i) /\ eval_operand cnt v = SOME (n2w k) /\
    (copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr zb) ==>
    step_inst_base (mk_inst se.cs_next_id copy_op copy_ops []) v =
      OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i code)) v)` by
    (rpt gen_tac >> strip_tac >>
     `copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s` by
       (strip_tac >>
        qpat_assum `copy_op = EXTCODECOPY ==> eval_operand addr zb = _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `copy_op = EXTCODECOPY ==> eval_operand addr v = _`
          (drule_then assume_tac) >> gvs[]) >>
     qpat_assum `!v wd. _ ==> step_inst_base _ v = _` irule >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  `32+k <= N` by decide_tac >>
  `LENGTH (TAKE k (DROP i code)) = k` by
    (simp[listTheory.LENGTH_TAKE_EQ,listTheory.LENGTH_DROP] >> decide_tac) >>
  suspend "resources"
QED

Resume slice_self_suffix_mods[resources]:
  (* The copy theorem is relative to the reached bounds cut; its n is the
     copied count, not the declared bound of the Slice result. *)
  mp_tac (slice_code_copy_resources_mods |> Q.INST
    [`sa` |-> `sd`,`sc` |-> `se`,`sd` |-> `sf`,`opc` |-> `copy_op`,`ops` |-> `copy_ops`,
     `s` |-> `zb`,`G` |-> `Gb`,`tn` |-> `tb`,`bound` |-> `n`,`n` |-> `k`,
     `wa` |-> `n2w i`,`bytes` |-> `TAKE k (DROP i code)`,
     `H0` |-> `storage_trace_horizon es.storage_trace`]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`p`,`w`,`t`,`HG`,`tm`] strip_assume_tac) >>
  suspend "normal"
QED

Resume slice_self_suffix_mods[normal]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK zb,Gb,tb)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zb,Gb,tb) _ (OK t,HG,tm)`
       (qspec_then `D` mp_tac) >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  qpat_assum `out = Var p` SUBST_ALL_TAC >>
  qpat_assum `e = Builtin _ _ _` SUBST_ALL_TAC >>
  mp_tac slice_code_suffix_post_mods >>
  simp_tac bool_ss [LET_THM] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule gasOutcomeFullPostModsTheory.gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`HG`,`es`,`INL (Value (BytesV (TAKE k (DROP i code))))`,`t`,`tm`] >>
  conj_tac >-
    (qpat_assum `!tail. source _ = _` mp_tac >> simp[slice_bytes_nat]) >>
  `es with gas_obs := [] = es` by
    (qpat_assum `es.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise slice_self_suffix_mods


val self_suffix_src = ``\v w. do
  acc <- get_accounts;
  r <- lift_sum (evaluate_slice (BytesV cx.txn.code) v w n);
  return (Value r)
  od``;

Triviality self_suffix_eval:
  !st. ^self_suffix_src (IntV (&i)) (IntV (&k)) st =
    ((case evaluate_slice (BytesV cx.txn.code) (IntV (&i)) (IntV (&k)) n of
        INL v => INL (Value v) | INR err => INR (Error err)), st)
Proof
  BETA_TAC >> Cases_on `evaluate_slice (BytesV cx.txn.code) (IntV (&i)) (IntV (&k)) n` >>
  simp[get_accounts_def,bind_def,lift_sum_def,return_def,raise_def]
QED

Triviality self_launch:
  expr_sim_inv_mods mods cenv cx env fin /\
  stmt_state_rel H ctx func cenv cx fin t2 ==>
  LENGTH cx.txn.code < dimword (:256) /\
  step_inst_base (mk_inst s2.cs_next_id CODESIZE []
    [STRING #"%" (toString s2.cs_next_var)]) t2 =
    OK (update_var (STRING #"%" (toString s2.cs_next_var))
      (n2w (LENGTH cx.txn.code)) t2) /\
  (!v wd. i+k <= LENGTH cx.txn.code /\
    v.vs_code = t2.vs_code /\ eval_operand data v = SOME wd /\
    eval_operand x v = SOME (n2w i) /\ eval_operand y v = SOME (n2w k) /\
    i < dimword (:256) /\ k < dimword (:256) ==>
    step_inst_base (mk_inst se.cs_next_id CODECOPY [data;x;y] []) v =
      OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i cx.txn.code)) v)) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t2 /\
     t2.vs_alloca_next + pending_alloca_size func t2 <= w2n t2.vs_initial_fmp)
Proof
  strip_tac >>
  `t2.vs_code = cx.txn.code` by
    (drule stmt_state_rel_state_rel >> simp[state_rel_def,accounts_rel_def]) >>
  conj_tac
  >- fs[expr_sim_inv_mods_def,vyperTypeInvariantsTheory.context_well_typed_def,dimword_def] >>
  conj_tac
  >- simp[step_inst_base_opcode_eqs,mk_inst_def,exec_read0_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `TAKE k (DROP i cx.txn.code ++ REPLICATE k 0w) = TAKE k (DROP i cx.txn.code)` by
        (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
      simp[step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def,w2n_n2w]) >>
  strip_tac >> drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac
QED

Triviality self_slice_read_frame:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\ valid_horizon cx st0 H mid.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace /\ MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  conj_tac
  >- (qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
      simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Triviality self_slice_memory_post:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value (BytesV bs))
    (LocatedValue ann (mk_ptr out LocMemory)) t <=>
  vv_post H ctx func cenv cx e es sa sb s0 ee (Value (BytesV bs))
    (LocatedValue ann (mk_ptr out LocMemory)) t /\ immutable_frame_mods func cenv cx ee t
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
  metis_tac[]
QED

Triviality self_slice_ghost_rebase:
  expr_post (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid v op s /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sm /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 s HG tm ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm
Proof
  strip_tac >> drule_then assume_tac expr_post_frame >>
  fs[ci_mono_def] >> drule_all ghost_kept_at_wb_trans >> simp[]
QED

Theorem slice_self_from_tail_mods:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty
    a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok_mods mods exps cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok_mods mods exps cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok_mods mods exps cx [addr])) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env
      (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) /\
    is_self_code (Builtin code_ty (Acc Code) [addr]) /\
    (!cenv' cx' env' a' n' ct addr' start len es' ee e' tops' ctx'
       DF' lo' d' shadow_ctx' PG' func' shadow_func' ty'.
       expr_body_pre_mods mods cenv' cx' env'
         (Builtin a' (Slice n') [Builtin ct (Acc Code) [addr'];start;len]) es' /\
       body_const_cells_agree_mods mods cx' env' ee /\
       expr_sim_inv_mods mods cenv' cx' env' ee /\
       (e' = start \/ e' = len \/ e' = addr') /\
       body_expr_full_ok_mods mods exps cx' e' /\
       contract_inv mods exps ctx' cenv' cx' /\
       module_body_inv mods src tops' cenv' cx' /\
       shadow_body_inv_mods mods exps ctx' shadow_ctx' ==>
       expr_sim_full_mods (DF',lo',d',ctx',shadow_ctx',PG',func',shadow_func')
         cenv' cx' ty' e' ee /\
       expr_vv_sim_full_mods (DF',lo',d',ctx',shadow_ctx',PG',func',shadow_func')
         cenv' cx' ty' e' ee) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`start`,`len`] strip_assume_tac)
    slice_code_operand_pre_mods >>
  qpat_assum `args = _` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx [start;len]` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> _` mp_tac >>
     simp[vyperContextTheory.builtin_args_length_ok_def,
          vyperInterpreterTheory.code_slice_source_def] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `?at. addr = Builtin at (Env SelfAddr) []` by
    (`!e. is_self_code e ==>
          ?ct st. e = Builtin ct (Acc Code) [Builtin st (Env SelfAddr) []]` by
       (ho_match_mp_tac exprLoweringTheory.is_self_code_ind >>
        simp[exprLoweringTheory.is_self_code_def]) >>
     first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  gvs[] >> drule_then strip_assume_tac slice_external_source_mods >>
  gvs[vyperASTTheory.expr_type_def] >>
  rewrite_tac[bodyFullPostsModsTheory.expr_vv_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`vv`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then (qx_choosel_then
    [`x`,`s1`,`y`,`s2`,`sh1`,`sh2`,`out`,`sc`,`sd`,`se`,`sf`,`limit`,`data`]
    (map_every assume_tac o CONJUNCTS)) (BETA_RULE slice_self_compile_mods) >>
  qpat_assum `vv = _` SUBST_ALL_TAC >>
  qpat_x_assum `gas_admissible (eval_expr cx _) _ _`
    (assume_tac o REWRITE_RULE [slice_self_code_actions]) >>
  rewrite_tac[slice_self_code_actions] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ Q R` >>
  suspend "join"
QED

Resume slice_self_from_tail_mods[join]:
  irule (BETA_RULE (Q.INST [`k` |-> `^self_suffix_src`] slice_code_tail_mods)) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv ty start _ = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv ty len _ = _` (irule_at Any) >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`tops`,`src`,`shadow_func`,`sha`,`sh2`,`sh1`,`exps`,`d`] >>
  asm_rewrite_tac[] >> conj_tac >- simp[Abbr `R`] >>
  conj_tac
  >- (rpt gen_tac >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts,storage_trace_frame_return]) >>
  qx_genl_tac [`marks1`,`v1`,`mid`,`G1`,`tn1`,`t1`,
               `marks2`,`v2`,`fin`,`G2`,`tn2`,`t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "suffix"
QED

Resume slice_self_from_tail_mods[suffix]:
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `i = w2n (val_to_w256 v1)` >>
  qabbrev_tac `k = w2n (val_to_w256 v2)` >>
  `i < dimword (:256) /\ k < dimword (:256) /\
   eval_operand x t2 = SOME (n2w i) /\ eval_operand y t2 = SOME (n2w k)` by
    simp[Abbr `i`,Abbr `k`,w2n_lt] >>
  `0 < k /\ k <= n` by
    (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `v2 = IntV _` (fn th => pure_once_rewrite_tac [th]) >>
     disch_tac >> qpat_assum `!st ee k. _ ==> 0 < k /\ k <= n`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ fin t2`
    (mp_then Any (drule_then strip_assume_tac) self_launch) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any (Q.INST [`code` |-> `cx.txn.code`] slice_self_suffix_mods) >>
  qpat_assum `emit_op CODESIZE [] s2 = _` (irule_at Any) >>
  qpat_assum `compile_assert_slice_bounds x y limit sc = _` (irule_at Any) >>
  qpat_assum `compile_slice_out_buf _ sd = ((out,data),se)` (irule_at Any) >>
  qpat_assum `emit_void CODECOPY _ se = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ sf = _` (irule_at Any) >>
  qpat_assum `eval_operand x t2 = SOME (n2w i)` (irule_at Any) >>
  qpat_assum `eval_operand y t2 = SOME (n2w k)` (irule_at Any) >>
  qexistsl_tac [`tops`,`src`,`shadow_ctx`,`n`,`exps`,`env`,
    `Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
        [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len]`,
    `d`,`cenv`,`[Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
        [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len]`,`x`] >>
  qpat_assum `contract_inv mods _ _ _ _`
    (assume_tac o MATCH_MP contract_inv_cenv_modules) >>
  `(!z. (x = Var z \/ y = Var z) ==> not_fresh_at s2 z) /\
    (!l. x <> Label l /\ y <> Label l)` by simp[DISJ_IMP_THM,FORALL_AND_THM] >>
  asm_simp_tac (srw_ss()) [Abbr `R`] >>
  conj_tac >- simp[DISJ_IMP_THM] >>
  conj_tac >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[BETA_RULE self_suffix_eval] >>
  qx_genl_tac [`H`,`ee`,`HG`,`tm`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee = fin` by
    (qpat_assum `?xs. !tail. _ = _` strip_assume_tac >>
     qpat_assum `!tail. _ (fin with gas_obs := xs ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     simp_tac bool_ss [BETA_RULE self_suffix_eval,pairTheory.PAIR_EQ] >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (mp_tac o Q.AP_TERM `\z:evaluation_state. z with gas_obs := []`) >>
     `fin with gas_obs := [] = fin /\ ee with gas_obs := [] = ee` by
       simp[evaluation_state_component_equality] >> simp[]) >>
  qpat_assum `ee = fin` SUBST_ALL_TAC >>
  suspend "rebase"
QED

Resume slice_self_from_tail_mods[rebase]:
  qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
    (mp_then Any (drule_then strip_assume_tac) self_slice_read_frame) >>
  qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
    (mp_then Any (drule_then strip_assume_tac) self_slice_read_frame) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `expr_post_mods H _ _ _ _ start _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_x_assum `expr_post_mods H _ _ _ _ len _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_x_assum `vv_post_mods H _ _ _ _ _ fin _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [self_slice_memory_post]) >>
  `stmt_state_rel H ctx func cenv cx mid t1` by
    (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
      (mp_then Any ACCEPT_TAC expr_post_state)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `vv_post H _ _ _ _ _ fin _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     qpat_assum `stmt_state_rel H _ _ _ _ fin t`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= t1.vs_alloca_next` mp_tac >>
     qpat_assum `t1.vs_alloca_next <= t2.vs_alloca_next` mp_tac >>
     qpat_assum `t2.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  simp[Abbr `Q`,self_slice_memory_post,vyperASTTheory.expr_type_def,
       lowered_value_type_def,mk_ptr_def,vv_location_def,is_bytestring_type_def] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM mk_ptr_def,self_slice_memory_post] >> simp[] >>
      qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
        (mp_then (Pat `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`) match_mp_tac
          slice_two_operand_post_rebase) >>
      qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
      fs[ci_mono_def]) >>
  conj_tac >- (pure_rewrite_tac[GSYM mk_ptr_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (pure_rewrite_tac[GSYM mk_ptr_def] >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv mid s1 G1 tn1 t1 HG tm` by
    (irule self_slice_ghost_rebase >>
     qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv fin s2 G2 tn2 t2 HG tm` (irule_at Any) >>
     simp[]) >>
  irule self_slice_ghost_rebase >>
  qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t1 HG tm` (irule_at Any) >>
  simp[]
QED

Finalise slice_self_from_tail_mods
