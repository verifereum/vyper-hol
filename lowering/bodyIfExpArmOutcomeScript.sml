Theory bodyIfExpArmOutcome
Ancestors
  context loweringPosts exprLowering exprSimMemDefs
  gasOutcome gasSummary gasStorage fragGasMode fragGasPath vyperStorageFootprint
  exprSimUnwrap
  bodyIfExpSelectedMemory bodyIfExpBytesAdapter exprSimMemUnwrap
  exprSimUnwrapProps exprSimUnwrap exprLoweringProps fragGasPathMem

(* An arm result held other than behind a memory pointer is no memory place. *)
Theorem ifexp_arm_raw_not_place[local]:
  vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
  ~is_word_type (expr_type e) /\ post_value_type ce e = expr_type e /\
  (!vt p. vv = LocatedValue vt p ==> p.ptr_location <> LocMemory) ==>
  !id path. raw <> PlaceR (MemoryPlace id path)
Proof
  strip_tac >> qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  Cases_on `vv` >> gvs[vv_post_def, vv_at_def]
QED

(* An arm result that is no memory place keeps the operand's expr_val_at. *)
Theorem ifexp_arm_vv_at_not_place[local]:
  expr_post H ctx func ce cx e es sa sb s0 ee v op u /\
  read_result cx raw ee = (INL v,ee) /\
  ~is_word_type (expr_type e) /\ post_value_type ce e = expr_type e /\
  (!id path. raw <> PlaceR (MemoryPlace id path)) /\
  (tv = raw \/ tv = Value v) ==>
  vv_at ce cx (expr_type e) sa sb ee tv
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u
Proof
  strip_tac >>
  `expr_val_at ce cx (expr_type e) sa sb ee v op u` by gvs[expr_post_def] >>
  `read_result cx tv ee = (INL v,ee) /\ !id path. tv <> PlaceR (MemoryPlace id path)` by
    gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all exprSimIfExpTheory.ifexp_vv_at_of_val_at >> simp[]
QED

Theorem ifexp_selected_arm_path_mem:
  post_value_type ce e = expr_type e /\
  expr_type e = t /\ at = lowered_value_type ce e /\ ~is_word_type t /\
  (~same_memory_layout ce at t ==> is_bytestring_type t) /\
  compile_ifexp_arm ce t at vv sm = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
     type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  (!tv. same_memory_layout ce at t /\ evaluate_type (get_tenv cx) t = SOME tv ==>
     ?avt. evaluate_type (get_tenv cx) at = SOME avt /\
       type_memory_size tv <= type_memory_size avt) /\
  stmt_state_rel (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx t at ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    expr_post H ctx func ce cx e es sa sb s0 ee v op u /\
    vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!tv. (tv = raw \/ tv = Value v) ==>
      vv_at ce cx (expr_type e) sa sb ee tv
        (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u) /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `same_memory_layout ce at t`
  >- suspend "same" >>
  `?u. gas_path_mem ctx func s 0 (OK u) /\
     expr_post H ctx func ce cx e es sa sb s0 ee v op u /\
     vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) u /\
     u.vs_current_bb = sb.cs_current_bb /\
     u.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
     (!tv'. read_result cx tv' ee = (INL v,ee) ==>
       vv_at ce cx t sa sb ee tv' (LocatedValue t (mk_ptr op LocMemory)) u) /\
     u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
     u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx`
    suffices_by
    (strip_tac >> qexists_tac `u` >> gvs[] >> rpt strip_tac >>
     qpat_x_assum `!tv'. _` irule >>
     fs[vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  mp_tac (Q.INST [`arm_ty` |-> `at`, `origin` |-> `sa`, `sa` |-> `sm`]
            bodyIfExpBytesAdapterTheory.ifexp_bytestring_adapter_path_mem) >>
  impl_tac
  >- (simp[] >> conj_tac >- (qpat_x_assum `!tv. _ ==> _ /\ _` drule >> simp[]) >>
      gvs[]) >>
  strip_tac >> qexists_tac `u` >> simp[]
QED

Resume ifexp_selected_arm_path_mem[same]:
  `vv_post H ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `vv` >- suspend "stack" >>
  rename1 `LocatedValue vt p` >>
  Cases_on `p.ptr_location = LocMemory` >- suspend "memory" >>
  `vt = t` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ (Value v) _ _` mp_tac >>
     qpat_assum `post_value_type ce e = _`
       (fn th => rewrite_tac[vv_post_def, vv_holds_def, th]) >>
     qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `~(p.ptr_location = LocMemory)` (fn th => rewrite_tac[th]) >>
     strip_tac >> simp[]) >>
  qpat_x_assum `vt = t` SUBST_ALL_TAC >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by
    (Cases_on `p.ptr_location` >> fs[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCalldata` (fn th =>
       simp_tac (srw_ss()) [vv_post_def, vv_holds_def, th])) >>
  (`unwrap_value ce (LocatedValue t p) sm = (op,sb)` by
    fs[compile_ifexp_arm_def] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_copy_capacity_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[vv_operand_def] >> strip_tac >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _`
       (mp_then Any mp_tac ifexp_arm_raw_not_place) >>
     impl_tac >> gvs[]) >>
  `!tv. (tv = raw \/ tv = Value v) ==>
     vv_at ce cx (expr_type e) sa sb ee tv
       (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u` by
    (rpt strip_tac >>
     drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_arm_vv_at_not_place >>
     disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
     disch_then irule >> gvs[]) >>
  qexists_tac `u` >> simp[] >>
  fs[vv_store_bound_def, vyperStateTheory.read_result_def,
     vyperStateTheory.return_def] >> metis_tac[])
QED

Resume ifexp_selected_arm_path_mem[stack]:
  fs[compile_ifexp_arm_def, unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- metis_tac[gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
  conj_tac
  >- (drule_all ifexp_arm_store_bound >>
      simp[vv_store_bound_def, contextTheory.mk_ptr_def]) >>
  `expr_post H ctx func ce cx e es sa sb s0 ee v op s` by
    metis_tac[expr_post_of_vv_post_stack] >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _`
       (mp_then Any mp_tac ifexp_arm_raw_not_place) >>
     impl_tac >> gvs[]) >>
  `!tv. (tv = raw \/ tv = Value v) ==>
     vv_at ce cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) s` by
    (qpat_assum `expr_type e = t` (fn th => rewrite_tac[GSYM th]) >>
     rpt strip_tac >>
     drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_arm_vv_at_not_place >>
     disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
     disch_then irule >> gvs[]) >>
  first_assum ACCEPT_TAC
QED

Resume ifexp_selected_arm_path_mem[memory]:
  `~is_word_type vt` by
    (`vt = t \/ is_bytestring_type vt` suffices_by
       metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ (Value v) _ _` mp_tac >>
     qpat_assum `post_value_type ce e = _`
       (fn th => rewrite_tac[vv_post_def, vv_holds_def, th]) >>
     qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
     strip_tac >> simp[]) >>
  `vv_store_bound cx t t ee raw (LocatedValue vt p) s` by
    (irule ifexp_arm_store_bound >> metis_tac[]) >>
  gvs[compile_ifexp_arm_def, unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- metis_tac[gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  conj_tac >- fs[vv_store_bound_def, mk_ptr_def] >>
  rpt strip_tac >> irule exprSimIfExpTheory.ifexp_vv_at_conditional >>
  qexistsl_tac [`raw`, `v`] >> simp[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ raw _ _` mp_tac >>
  gvs[vv_at_def, mk_ptr_def]
QED

Finalise ifexp_selected_arm_path_mem

(* A gas outcome whose Q-state is extended by a memory-checked zero-gas path
   keeps its end state across every horizon: the path is chosen for one
   horizon, so the continuation supplies one end state and the post at each
   valid horizon. *)
Theorem ifexp_outcome_suffix_mem:
  gas_outcome T tops (ctx,func) cx st0 source (es,s0) Q R /\
  (!res ee u.
     (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee u) /\
     (?H. valid_horizon cx st0 H ee.storage_trace) /\ ~u.vs_halted ==>
     ?v. gas_path_mem ctx func u 0 (OK v) /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==> Q' H res ee v)) ==>
  gas_outcome T tops (ctx,func) cx st0 source (es,s0) Q' R
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choosel_then [`res`, `es_end`, `r`]
        (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        (qexists_tac `storage_trace_horizon es_end.storage_trace` >>
         fs[storage_trace_domain_def]) >>
      `?H. valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
        (qexists_tac `H0` >> simp[]) >>
      disj2_tac >> disj1_tac >>
      qpat_x_assum `_ \/ _` strip_assume_tac
      >- (gvs[] >>
          `~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             drule gas_path_mem_exec >> metis_tac[gas_path_normal]) >>
          qpat_x_assum `!res ee u. _` (qspecl_then [`res`, `es_end with gas_obs := []`, `t`]
            mp_tac) >>
          (impl_tac >- (rpt conj_tac >> simp[])) >> strip_tac >>
          qexistsl_tac [`res`, `es_end`, `OK v`] >> conj_tac
          >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
              simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
              simp[] >>
              metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
          disj1_tac >> qexists_tac `v` >> simp[]) >>
      qexistsl_tac [`res`, `es_end`, `r`] >> conj_tac
      >- first_assum ACCEPT_TAC >>
      disj2_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  first_assum ACCEPT_TAC
QED

Theorem ifexp_selected_arm_outcome_mem:
  post_value_type ce e = expr_type e /\
  expr_type e = t /\ ~is_word_type t /\
  (~same_memory_layout ce (lowered_value_type ce e) t ==> is_bytestring_type t) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
    type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  (!tv. same_memory_layout ce (lowered_value_type ce e) t /\
    evaluate_type (get_tenv cx) t = SOME tv ==>
    ?avt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME avt /\
      type_memory_size tv <= type_memory_size avt) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  gas_outcome T tops (ctx,func) cx st0 source (es,s0)
    (\H res ee s. ?raw v tvt. res = INL raw /\
      read_result cx raw ee = (INL v,ee) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
      vv_store_bound cx t (lowered_value_type ce e) ee raw vv s /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) R ==>
  gas_outcome T tops (ctx,func) cx st0 source (es,s0)
    (\H res ee s. ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
      expr_post H ctx func ce cx e es sa sb s0 ee v op s /\
      vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) s /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) R
Proof
  strip_tac >> rename1 `valid_horizon cx st0 H1 es.storage_trace` >>
  `stmt_state_rel H1 ctx func ce cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >> simp[]) >>
  irule ifexp_outcome_suffix_mem >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 H2 ee.storage_trace` >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> BETA_TAC >> strip_tac >>
  drule ifexp_selected_arm_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK u')` >>
  qexists_tac `u'` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> rename1 `valid_horizon cx st0 H3 ee.storage_trace` >>
  `stmt_state_rel H3 ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H3)` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `H3` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> BETA_TAC >> strip_tac >>
     qpat_x_assum `vv_post H3 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def] >> rpt strip_tac >> simp[]) >>
  `expr_post H3 ctx func ce cx e es sa sb s0 ee v op u'` by
    (drule_all exprSimUnwrapTheory.expr_post_fields_transport >> simp[]) >>
  qexistsl_tac [`raw`, `v`] >> simp[]
QED
