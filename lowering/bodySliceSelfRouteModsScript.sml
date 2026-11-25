(* Linked code Slice after the two scalar operand reads. *)
Theory bodySliceSelfRouteMods
Ancestors
  bodySliceCodeQueryLandingMods bodySliceCodeBoundsCutMods
  bodySliceCodeCopyResourcesMods bodySliceCodeSuffixPostMods bodySliceBoundsExitMods
  bodyFullPredsMods gasOutcomeFullZeroPrefixMods exprSimSliceSource
  bodyPtrBytestringBuiltinsSlice bodyPtrBytestringBuiltinsBuffer
  freshWrites localPtrsProps stateRelProj ptrDiscipline compileEnv fragExec
Libs horizonTypeLib

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
