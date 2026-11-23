(* Uniform IfExp VV preparation, independent of the VV-to-expression conversion. *)
Theory bodyFullIfExpPrepare
Ancestors
  bodyFullIfExpObserve bodyFullIfExpWiden bodyFullIfExpWidenCall
  bodyFullIfExpFinish bodyFullIfExpShadow bodyFullAllocGeneric typedCopyOriginPtr
  bodyFullUnwrap bodyFullPreds bodyFullIfExpReach bodyFullHashKeccakFixed
  bodySimFull gasOutcomeFullCompose gasOutcomeFull gasOutcomeFullGuarded gasShadowCompile
  fragGasPathFrameMem
  gasShadowCompileHelpers gasShadowCompileStmtHelpers
  exprSimMemorySource exprSimIfExp exprSimDefs
  exprSimCalldataSlice exprSimIfExpWidenedAdapter
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering exprLoweringProps
  typedCopyDomain vyperTypeSystem vyperTypeInvariants compileEnv context vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

Theorem ifexp_outcome_zero_suffix_framed[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\ storage_trace_frame source /\
  (!res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee G1 tn1 t) ==>
    ?t' G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK t',G2,tn2) /\ Q' H res ee G2 tn2 t') ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists `marks` >>
      disj1_tac >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists `marks` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  Cases_on `exit_result r`
  >- (disj2_tac >> disj1_tac >>
      qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- fs[] >- fs[] >>
      rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_x_assum `!tail. source _ = _`
       (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!res ee G1 tn1 t. _ /\ _ /\ _ ==> _`
    (qspecl_then [`res`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  disj2_tac >> disj1_tac >>
  qexistsl [`res`,`ee`,`OK t'`,`G2`,`tn2`] >>
  rpt conj_tac >- fs[] >- fs[] >>
  rpt strip_tac >> res_tac >> fs[] >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, listTheory.APPEND_NIL]
QED

(* An owned physical value never needs the local-place alternative. *)
Theorem ifexp_nocopy_physical_owned_vv[local]:
  ~is_word_type src /\ ~is_word_type dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  expr_val_own ce cx src sa sb ee v op s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_at ce cx dst sa sb ee tv (LocatedValue dst (mk_ptr op LocMemory)) s /\
  vv_own ce cx dst sa sb ee tv (LocatedValue dst (mk_ptr op LocMemory)) s
Proof
  simp[vv_at_def, vv_own_def, mk_ptr_def, expr_val_own_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `sv` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_post[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce (post_value_type ce e) (expr_type e) /\
  arg_type_fits (post_value_type ce e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dv /\
  ~is_word_type (expr_type e) /\ value_has_type dv v /\
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_post H ctx func ce cx e es sa sb s0 ee v op s ==>
  expr_post H ctx func ce cx (IfExp (expr_type e) c a b) es sa sb s0 ee v op s
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- (gvs[expr_post_def, expr_type_def] >> metis_tac[]) >>
  qpat_assum `expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >>
  `expr_val_rel cx (expr_type e) v op s` by
    (irule exprSimLayoutTransportTheory.expr_val_rel_layout_transport >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_val_at ce cx (expr_type e) sa sb ee v op s` by
    (irule exprSimLayoutTransportTheory.expr_val_at_layout_transport >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[expr_post_def, expr_type_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_endpoint_vv[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce (post_value_type ce e) (expr_type e) /\
  arg_type_fits (post_value_type ce e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dv /\
  ~is_word_type (expr_type e) /\ value_has_type dv v /\
  post_value_type ce e <> expr_type e /\
  expr_post H ctx fn ce cx e es sa sb s0 ee v op s /\
  read_result cx raw ee = (INL v,ee) ==>
  vv_at ce cx (expr_type e) sa sb ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s /\
  vv_own ce cx (expr_type e) sa sb ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s
Proof
  strip_tac >> irule ifexp_nocopy_physical_owned_vv >>
  simp[] >> qexistsl_tac [`post_value_type ce e`, `sv`] >>
  simp[] >> rpt conj_tac
  >- metis_tac[exprSimLayoutTransportTheory.compatible_word_type]
  >- (fs[same_memory_layout_def] >>
      metis_tac[exprSimLayoutTransportTheory.compatible_footprint])
  >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]
  >> fs[expr_post_def]
QED

Theorem ifexp_nocopy_physical_store_size[local]:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_store_size tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[exprSimPropsTheory.val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

Theorem ifexp_nocopy_physical_buffer[local]:
  same_memory_layout ce (lowered_value_type ce e) t /\
  ptr_buf_ok ce e op G s ==>
  !e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op G s
Proof
  simp[same_memory_layout_def, ptr_buf_ok_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_bound[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce src dst /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ type_memory_size dv < 2 ** 64 ==>
  !sv. evaluate_type (get_tenv cx) src = SOME sv ==>
    type_memory_bytes ce src = type_memory_size sv /\ type_memory_size sv < 2 ** 64
Proof
  simp[same_memory_layout_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_ptr[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce src dst /\ arg_type_fits src dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type dst /\ ~is_bytestring_type src /\ ~is_bytestring_type dst /\
  ptr_val_ok cx src v op G tn s ==>
  ptr_val_ok cx dst v op G tn s
Proof
  strip_tac >>
  `~is_word_type src` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  `type_memory_size sv = type_memory_size dv` by
    (fs[same_memory_layout_def] >> metis_tac[]) >>
  `val_footprint sv v = val_footprint dv v` by
    metis_tac[exprSimLayoutTransportTheory.compatible_footprint] >>
  `val_store_size sv v = val_store_size dv v` by
    metis_tac[ifexp_nocopy_physical_store_size] >>
  `!b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem` by
    (drule exprSimLayoutTransportTheory.compatible_layout_memory >>
     strip_tac >> first_x_assum irule >>
     qexistsl_tac [`dst`, `src`] >> fs[same_memory_layout_def]) >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]
QED

(* Retyping keeps the one physical unwrap endpoint outside the horizon guard. *)
Theorem ifexp_nocopy_physical_family[local]:
  expr_type e = t /\ post_value_type ce e <> t /\
  post_value_type ce e = lowered_value_type ce e /\
  same_memory_layout ce (lowered_value_type ce e) t /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) t /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) t = SOME dv /\
  value_has_type dv v /\ ~is_word_type t /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gz,tf) /\
    expr_post H ctx func ce cx e es sa sb u ee v op z /\
    ghost_inv_at (DF H) lo d ce cx ee Gz tf z) /\
  expr_store_bound cx (post_value_type ce e) v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gz tf z /\
  ptr_buf_ok ce e op Gz z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gz,tf) /\
    expr_post H ctx func ce cx (IfExp t c a b) es sa sb u ee v op z /\
    ghost_inv_at (DF H) lo d ce cx ee Gz tf z) /\
  vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z /\
  vv_own ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z /\
  expr_store_bound cx t v op z /\
  ptr_val_ok cx t v op Gz tf z /\
  (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gz z) /\
  (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\
    eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next)
Proof
  strip_tac >>
  `arg_type_fits (post_value_type ce e) t` by
    fs[type_widens_to_def] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `type_memory_size sv = type_memory_size dv` by
    (fs[same_memory_layout_def] >> metis_tac[]) >>
  `val_store_size sv v = val_store_size dv v` by
    metis_tac[ifexp_nocopy_physical_store_size] >>
  `expr_store_bound cx t v op z` by
    (qpat_x_assum `expr_store_bound cx (post_value_type ce e) v op z` mp_tac >>
     simp[expr_store_bound_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z /\
   vv_own ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `expr_type e = t` (fn th => rewrite_tac[GSYM th]) >>
     irule (INST_TYPE [``:'a`` |-> ``:256``] ifexp_nocopy_physical_endpoint_vv) >>
     goal_assum (drule_at Any) >> gvs[] >>
     qexistsl [`storage_trace_horizon ee.storage_trace`,`ctx`,`es`,`func`,`u`] >>
     metis_tac[]) >>
  qpat_x_assum `expr_type e = t` (SUBST_ALL_TAC o SYM) >>
  rpt conj_tac
  >- (rpt strip_tac >> res_tac >> simp[] >>
      irule ifexp_nocopy_physical_post >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (irule ifexp_nocopy_physical_ptr >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> drule_all ifexp_nocopy_physical_buffer >> simp[])
  >> fs[same_memory_layout_def] >> metis_tac[]
QED

Theorem ifexp_unwrap_place_ptr_frame[local]:
  vv_holds ce cx sty (PlaceR (MemoryPlace id path)) vv ee s /\
  vv_at ce cx sty sa sm ee (PlaceR (MemoryPlace id path)) vv s /\
  vv_place_ptr ce cx ee s (PlaceR (MemoryPlace id path)) vv /\
  ~is_word_type sty /\ unwrap_value ce vv sm = (op,sb) /\
  local_ptrs_reserved ce sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  u.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  vv_place_ptr ce cx ee u (PlaceR (MemoryPlace id path))
    (LocatedValue t (mk_ptr op LocMemory))
Proof
  strip_tac >> Cases_on `vv` >> fs[vv_at_def] >>
  rename1 `LocatedValue vt p` >>
  `p.ptr_location = LocMemory` by metis_tac[] >>
  `~is_word_type vt` by
    (fs[vv_holds_def] >> metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  `eval_operand p.ptr_operand u = eval_operand p.ptr_operand s` by
    (Cases_on `p.ptr_operand` >> fs[vv_operand_def, eval_operand_def]) >>
  `!id q sz w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
    lookup_var q s = SOME w ==> lookup_var q u = SOME w` by
    (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `vv_place_ptr ce cx ee u (PlaceR (MemoryPlace id path)) (LocatedValue vt p)` by
    (irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[vv_operand_def] >>
     first_assum ACCEPT_TAC) >>
  irule ifexp_place_ptr_mem_ptr >> simp[] >> qexists_tac `vt` >> simp[]
QED

(* Uniform selected-arm conversion; the endpoint is shared by all horizons. *)
Theorem ifexp_conditional_value_eq[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL (Value v'),ee) ==> v' = v
Proof
  strip_tac >>
  `(do r <- conditional_result cx raw; read_result cx r od) ee = (INL v',ee)` by
    simp[vyperStateTheory.bind_def, read_result_def, vyperStateTheory.return_def] >>
  drule exprSimIfExpTheory.conditional_read_cases >> strip_tac >> gvs[]
QED

Theorem ifexp_vv_own_conditional_value[local]:
  vv_own ce cx t sa sb ee raw vv z /\
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL (Value v'),ee) ==>
  vv_own ce cx t sa sb ee (Value v') vv z
Proof
  strip_tac >> `v' = v` by metis_tac[ifexp_conditional_value_eq] >>
  Cases_on `vv` >> fs[vv_own_def, read_result_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> first_x_assum drule_all >> metis_tac[]
QED

Theorem ifexp_unwrap_identity_owned[local]:
  ~is_word_type t /\ ~is_bytestring_type t /\
  vv_holds ce cx t (Value v) vv ee z /\
  vv_own ce cx t sa sm ee (Value v) vv z /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  unwrap_value ce vv sm = (op,sb) /\
  local_ptrs_reserved ce sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x z' = lookup_var x z) /\
  z'.vs_labels = z.vs_labels /\
  wb_frame ce ee ee sm z z' ==>
  vv_own ce cx t sa sb ee (Value v) (LocatedValue t (mk_ptr op LocMemory)) z'
Proof
  strip_tac >>
  `!n b sz. local_region ce ee.scopes z' n b sz <=>
            local_region ce ee.scopes z n b sz` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `sm` >> simp[]) >>
  `eval_operand (vv_operand vv) z' = eval_operand (vv_operand vv) z` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def] >> metis_tac[]) >>
  `vv_own ce cx t sa sm ee (Value v) vv z'` by
    (irule exprSimIfExpWidenedAdapterTheory.vv_own_alloc_mono_frame >>
     qpat_assum `vv_own ce cx t sa sm ee (Value v) vv z` (irule_at Any) >>
     simp[] >> fs[wb_frame_def]) >>
  Cases_on `vv` >> gvs[vv_location_def]
  >- (gvs[unwrap_value_def, comp_return_def] >>
      fs[vv_own_def, expr_val_own_def, read_result_def, vyperStateTheory.return_def, mk_ptr_def] >>
      metis_tac[]) >>
  `t' = t` by (fs[vv_holds_def] >> metis_tac[]) >>
  gvs[unwrap_value_def, comp_return_def] >> fs[vv_own_def, mk_ptr_def] >> metis_tac[]
QED

Theorem typed_aggregate_memory_conditional[local]:
  evaluate_type tenv ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\ ty <> NoneT /\
  runtime_place_typed cx st (MemoryPlace id path) tv ==>
  conditional_result cx (PlaceR (MemoryPlace id path)) st =
    (INL (PlaceR (MemoryPlace id path)),st)
Proof
  strip_tac >>
  `place_type_value cx (MemoryPlace id path) st = (INL tv,st)` by
    fs[runtime_place_typed_def] >>
  simp[conditional_result_def, vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  Cases_on `ty` >>
  gvs[is_word_type_def, is_bytestring_type_def, vyperValueTheory.evaluate_type_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_word_type_def, is_bytestring_type_def, vyperValueTheory.evaluate_type_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_bytestring_type_def, vyperValueTheory.evaluate_type_def, vyperStateTheory.return_def, AllCaseEqs()]
QED

Theorem ifexp_selected_arm_step_observed:
  ifexp_observed_unwrap T obs DF lo explicit ctx func PG d cenv cx /\
  ifexp_observed_alloc obs ctx func /\
  ifexp_observed_bytes_store obs /\
  ifexp_observed_typed_store obs /\
  ifexp_observed_widening obs ctx func /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  (post_value_type cenv e = t /\
   (is_word_type t \/
    same_memory_layout cenv (lowered_value_type cenv e) t /\
    (?rtp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtp) \/
    ~same_memory_layout cenv (lowered_value_type cenv e) t /\
    is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) t) \/
   ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
   post_value_type cenv e = lowered_value_type cenv e /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv) \/
   ~is_word_type t /\ post_value_type cenv e <> t /\
   post_value_type cenv e = lowered_value_type cenv e /\
   same_memory_layout cenv (lowered_value_type cenv e) t /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==>
     value_has_type rty v /\
     !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
       value_has_type ptv v) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  (!id path. tva = PlaceR (MemoryPlace id path) ==>
    same_memory_layout cenv (lowered_value_type cenv e) t) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  eval_result_typed (env,cx,ee) tva (Type (expr_type e)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  (!v. tva = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sm ee tva vv z) /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    obs ctx func sm sb z z' /\
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    (~is_word_type t ==> !id path. tva = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr cenv cx ee z' tva (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx tva ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee ctv
        (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  strip_tac
  >>~- ([`post_value_type cenv e <> t`, `same_memory_layout cenv _ t`],
    suspend "physical")
  >>~- ([`type_widens_to _ _ _`], suspend "widened")
  >>~- ([`is_bytestring_type _`, `~same_memory_layout _ _ _`], suspend "bytes") >>
  suspend "nocopy"
QED

Resume ifexp_selected_arm_step_observed[nocopy]:
  markerLib.RESUME_TAC >>
  `unwrap_value cenv vv sm = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >> simp[compile_ifexp_arm_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2 ** 64` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` by metis_tac[] >>
  `!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v` by metis_tac[] >>
  `sm.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sm.cs_next_id` by simp[] >>
  qpat_x_assum `ifexp_observed_unwrap T obs _ _ _ _ _ _ _ _ _`
    (drule_all o SIMP_RULE bool_ss [ifexp_observed_unwrap_def]) >>
  strip_tac >>
  `z'.vs_labels = z.vs_labels` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     strip_tac >> drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >>
     strip_tac >> drule fragGasPathPtrTheory.gas_path_ptr_erase >>
     strip_tac >> drule gas_path_code_labels >> simp[]) >>
  `~is_word_type t ==> !id path. tva = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr cenv cx ee z' tva (LocatedValue t (mk_ptr op LocMemory))` by
    (rpt strip_tac >> gvs[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     simp[vv_post_def] >> strip_tac >>
     irule ifexp_unwrap_place_ptr_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z'` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `expr_post H ctx func cenv cx e es1 sa sb u ee v op z'` mp_tac >>
     simp[NoAsms, expr_post_def, post_value_type_def, expr_type_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`v`,`z'`,`G'`,`tn'`] >> gns[] >> rpt strip_tac
  >>~- ([`vv_own _ _ _ _ _ _ _ _ _ (* g *)`],
    (Cases_on `?id path. tva = PlaceR (MemoryPlace id path)`
         >- (`v' = v` by metis_tac[ifexp_conditional_value_eq] >>
             Cases_on `t = NoneT`
             >- (gvs[] >> qpat_assum `vv_at cenv cx NoneT sa sb ee _ _ z'` mp_tac >>
                 qpat_assum `read_result cx _ ee = (INL NoneV,ee)` mp_tac >>
                 POP_ASSUM_LIST (K all_tac) >>
                 simp[vv_own_def, vv_at_def, mk_ptr_def, read_result_def, vyperStateTheory.return_def,
                      vyperValueTheory.evaluate_type_def,
                      valueEncodingTheory.type_memory_size_def, val_footprint_def] >>
                 rpt strip_tac >> metis_tac[]) >>
             gvs[] >> drule_all typed_aggregate_memory_conditional >> simp[]) >>
         suspend "nocopyown"))
  >>~- ([`ptr_buf_ok _ _ _ _ _ (* g *)`],
    (irule ifexp_nocopy_physical_buffer >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[])) >>
  qpat_assum `~is_word_type t ==> !w. eval_operand op z' = SOME w ==> _` mp_tac >>
  qpat_assum `same_memory_layout cenv _ t` mp_tac >>
  qpat_assum `!ty' tvt. evaluate_type _ ty' = SOME tvt ==> _` mp_tac >>
  qpat_assum `evaluate_type _ (lowered_value_type cenv _) = SOME _` mp_tac >>
  qpat_assum `evaluate_type _ t = SOME _` mp_tac >>
  qpat_assum `~is_word_type t` mp_tac >>
  qpat_assum `eval_operand op z' = SOME _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[same_memory_layout_def] >> rpt strip_tac >> metis_tac[]
QED

Resume ifexp_selected_arm_step_observed[physical]:
  markerLib.RESUME_TAC >>
  `unwrap_value cenv vv sm = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     simp[compile_ifexp_arm_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `sa` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2 ** 64` by
    (rpt gen_tac >> disch_tac >> irule ifexp_nocopy_physical_bound >>
     qexistsl [`cx`,`t`,`rty`] >> gvs[]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv` by metis_tac[] >>
  `!v. read_result cx tva ee = (INL v,ee) ==> value_has_type stv v` by metis_tac[] >>
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tva vv z` by metis_tac[] >>
  `sm.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sm.cs_next_id` by simp[] >>
  qpat_x_assum `ifexp_observed_unwrap T obs _ _ _ _ _ _ _ _ _`
    (drule_all o SIMP_RULE bool_ss [ifexp_observed_unwrap_def]) >>
  strip_tac >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  `~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e` by
    (gvs[]) >>
  `value_has_type rty v` by metis_tac[] >>
  `z'.vs_labels = z.vs_labels` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     strip_tac >> drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >>
     strip_tac >> drule fragGasPathPtrTheory.gas_path_ptr_erase >>
     strip_tac >> drule gas_path_code_labels >> simp[]) >>
  `!id path. tva = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr cenv cx ee z' tva (LocatedValue t (mk_ptr op LocMemory))` by
    (rpt strip_tac >> gvs[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     simp[vv_post_def] >> strip_tac >>
     irule ifexp_unwrap_place_ptr_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ptr_buf_ok cenv e op G' z'` by metis_tac[] >>
  `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    eval_operand op z' = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next` by metis_tac[] >>
  drule_all ifexp_nocopy_physical_family >> strip_tac >>
  qexistsl_tac [`v`,`z'`,`G'`,`tn'`] >> simp[] >> rpt strip_tac >>
  irule ifexp_vv_own_conditional_value >>
  qpat_assum `vv_own cenv cx t sa sb ee tva _ z'` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Resume ifexp_selected_arm_step_observed[nocopyown]:
  markerLib.RESUME_TAC >>
  `v' = v` by metis_tac[ifexp_conditional_value_eq] >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  (Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`!id path. tva <> PlaceR (MemoryPlace id path)` by metis_tac[] >>
      `tva = Value v` by
        (qpat_assum `vv_at _ _ _ _ _ _ tva vv z` mp_tac >>
         qpat_assum `vv_place_ptr _ _ _ z tva vv` mp_tac >>
         qpat_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` mp_tac >>
         qpat_assum `!id path. tva <> PlaceR (MemoryPlace id path)` mp_tac >>
         qpat_assum `read_result cx tva ee = (INL v,ee)` mp_tac >>
         qpat_assum `post_value_type cenv _ = t` mp_tac >>
         qpat_assum `~is_word_type t` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         Cases_on `tva` >> Cases_on `vv` >>
         gvs[vv_location_def, read_result_def, vyperStateTheory.return_def,
             vyperStateTheory.raise_def, vv_at_def, vv_place_ptr_def] >>
         rename1 `read_place cx place ee` >> Cases_on `place` >>
         gvs[slot_loc_def, COND_RATOR, COND_RAND] >> metis_tac[]) >>
      gvs[] >>
      irule ifexp_unwrap_identity_owned >>
      qpat_assum `unwrap_value cenv vv sm = (op,sb)` (irule_at Any) >>
      simp[] >> fs[] >> metis_tac[]) >>
  `?ann p. vv = LocatedValue ann p /\ p.ptr_location <> LocMemory` by
    (qpat_assum `~(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` mp_tac >>
     Cases_on `vv` >> simp[vv_location_def]) >>
  qpat_x_assum `vv = LocatedValue ann p` SUBST_ALL_TAC >>
  `~is_word_type ann /\
   (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
    p.ptr_location = LocCode)` by
    (qpat_assum `vv_holds _ _ _ tva (LocatedValue ann p) ee z` mp_tac >>
     qpat_assum `p.ptr_location <> LocMemory` mp_tac >>
     qpat_assum `~is_word_type t` mp_tac >>
     qpat_assum `post_value_type cenv _ = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `p.ptr_location` >>
     simp[vv_holds_def] >> metis_tac[]) >>
  `vv_own cenv cx t sm sb ee (Value v)
     (LocatedValue t (mk_ptr op LocMemory)) z'` by metis_tac[] >>
  irule exprSimCalldataSliceTheory.vv_own_start_mono >>
  qexists `sm` >> simp[])
QED

Resume ifexp_selected_arm_step_observed[widened]:
  markerLib.RESUME_TAC >>
      (`!id path. tva <> PlaceR (MemoryPlace id path)` by metis_tac[] >>
      qpat_assum `!id path. tva <> PlaceR (MemoryPlace id path)`
        (fn th => SIMP_TAC bool_ss [th]) >>
      mp_tac (Q.INST [`ptv` |-> `stv`] ifexp_widened_call_arm_step_observed) >>
      impl_tac
      >- (rpt conj_tac >>
      FIRST_PROVE [(irule ifexp_observed_unwrap_drop_own >> simp[]),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             (first_assum ACCEPT_TAC),
             (qpat_assum `post_value_type cenv e = lowered_value_type cenv e`
                (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC),
             (asm_simp_tac bool_ss [] >> NO_TAC),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (qexistsl_tac [`e`,`stv`,`sm`,`stv`,`ty`,`vv`] >>
              simp[] >> rpt strip_tac >> first_x_assum drule >> simp[])] >> gvs[]) >>
      disch_then (qx_choosel_then [`v`,`z'`,`Gz`,`tf`] strip_assume_tac) >>
      qexistsl [`v`,`z'`,`Gz`,`tf`] >> simp[] >> rpt strip_tac >>
      `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
      `~is_bytestring_type (post_value_type cenv e)` by
        metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
      `v' = v` by metis_tac[ifexp_conditional_value_eq] >>
      gvs[] >> irule exprSimCalldataSliceTheory.vv_own_start_mono >>
      qexists `sm` >> simp[])
QED

Resume ifexp_selected_arm_step_observed[bytes]:
  markerLib.RESUME_TAC >>
      `!id path. tva <> PlaceR (MemoryPlace id path)` by metis_tac[] >>
      qpat_assum `!id path. tva <> PlaceR (MemoryPlace id path)`
        (fn th => SIMP_TAC bool_ss [th]) >>
      qpat_assum `is_bytestring_type t` (fn th => SIMP_TAC bool_ss [th]) >>
      irule ifexp_widen_arm_step_observed >> rpt conj_tac >>
      FIRST_PROVE [(irule ifexp_observed_unwrap_drop_own >> simp[]),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             first_assum ACCEPT_TAC,
             (asm_simp_tac bool_ss [] >> NO_TAC),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (irule valueCopyBytesTheory.is_bytestring_word_type >> first_assum MATCH_ACCEPT_TAC),
             (qexistsl_tac [`e`,`ty`,`vv`] >> gvs[]),
             FAIL_TAC "bytes concrete"] >> gvs[]
QED

Finalise ifexp_selected_arm_step_observed

Triviality ifexp_materialize_observation_true:
  ifexp_observed_unwrap T (\_ _ _ _ _ _. T) DF lo explicit ctx func PG d cenv cx /\
  ifexp_observed_alloc (\_ _ _ _ _ _. T) ctx func /\
  ifexp_observed_bytes_store (\_ _ _ _ _ _. T) /\
  ifexp_observed_typed_store (\_ _ _ _ _ _. T) /\
  ifexp_observed_widening (\_ _ _ _ _ _. T) ctx func
Proof
  pure_rewrite_tac [ifexp_observed_unwrap_def, ifexp_observed_alloc_def,
    ifexp_observed_bytes_store_def, ifexp_observed_typed_store_def,
    ifexp_observed_widening_def] >> BETA_TAC >>
  pure_rewrite_tac [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP] >>
  rpt conj_tac >> rpt gen_tac >>
  FIRST [MATCH_ACCEPT_TAC unwrap_value_origin_ptr,
         MATCH_ACCEPT_TAC compile_store_bytestring_origin_ptr_path,
         MATCH_ACCEPT_TAC compile_store_memory_typed_origin_ptr_path]
QED

(* Keep the ordinary arm step as the True specialization of the observed one. *)
local
  val arm_step_unobserved =
    PURE_REWRITE_RULE [AND_CLAUSES, ifexp_materialize_observation_true]
      (BETA_RULE (Q.INST [`obs` |-> `\_ _ _ _ _ _. T`] ifexp_selected_arm_step_observed))
in
Theorem ifexp_selected_arm_step_full:
  ^(concl arm_step_unobserved)
Proof
  ACCEPT_TAC arm_step_unobserved
QED
end

(* Source composition is independent of the proof of arm conversion.
   The conversion contract is specialized at the fixed compiler layout;
   only its runtime endpoint is universally quantified. *)
(* Source facts shared by the ordinary and first-exit arm callbacks. *)
Theorem ifexp_arm_raw_admissible:
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gasContextTheory.gas_admissible_def] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  Cases_on `res` >> simp[vyperStateTheory.bind_def, expr_vv_res_ok_def] >>
  rename1 `INL rv0` >> Cases_on `rv0` >>
  simp[conditional_result_def, vyperStateTheory.raise_def, expr_vv_res_ok_def]
QED

Theorem ifexp_arm_raw_source:
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  (!gs raw ee. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) ==>
    eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
    value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv ==>
      value_has_type ptv v) ==>
  eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!id path. tv = PlaceR (MemoryPlace id path) ==>
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
    value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv ==>
      value_has_type ptv v)
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac >- (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> drule ifexp_raw_place_layout >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!gs v ee. bind _ _ _ = _ ==> _`
    (qspecl_then [`gs`,`v`,`ee`] mp_tac) >> simp[vyperStateTheory.bind_def]
QED

Theorem ifexp_arm_pure_source:
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  read_result cx tv ee = (INL v,ee) ==>
  ?ctv. (!tail. conditional_result cx tv (ee with gas_obs := tail) =
                 (INL ctv,ee with gas_obs := tail)) /\
        read_result cx ctv ee = (INL v,ee)
Proof
  strip_tac >> Cases_on `conditional_result cx tv ee` >>
  rename1 `conditional_result cx tv ee = (cr,ces)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
      (qspec_then `gs` mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     fs[vyperStateTheory.bind_def]) >>
  metis_tac[bodyPtrIfExpConditionalSourceTheory.ifexp_conditional_source_success]
QED

Theorem ifexp_arm_conditional_vv_facts:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  (~is_word_type t ==> vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z) /\
  (~is_word_type t ==> !id path. raw = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr ce cx ee z raw (LocatedValue t (mk_ptr op LocMemory))) /\
  (!ctv w. conditional_result cx raw ee = (INL ctv,ee) /\ ctv = Value w /\
     ~is_word_type t /\ ~is_bytestring_type t ==>
     vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr op LocMemory)) z) ==>
  (~is_word_type t ==> vv_at ce cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z) /\
  (~is_word_type t ==> vv_place_ptr ce cx ee z tv (LocatedValue t (mk_ptr op LocMemory))) /\
  (!w. tv = Value w /\ ~is_word_type t /\ ~is_bytestring_type t ==>
     vv_own ce cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z)
Proof
  strip_tac >> conj_tac
  >- (strip_tac >> irule ifexp_vv_at_conditional >> qexistsl [`raw`,`v`] >> simp[] >>
      drule ifexp_conditional_result_shape >> strip_tac >>
      fs[read_result_def, vyperStateTheory.return_def]) >>
  conj_tac
  >- (strip_tac >> drule ifexp_conditional_result_place >> strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem ifexp_arm_outcome_full_conditional[local]:
  (!ee tv z G tn.
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
    (!id path. tv = PlaceR (MemoryPlace id path) ==>
      same_memory_layout cenv (lowered_value_type cenv e) t) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es1 sa sm u ee tv vv z /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv z /\
    z.vs_current_bb = sm.cs_current_bb /\
    z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
        ~is_bytestring_type (post_value_type cenv e) ==>
        vv_own cenv cx (post_value_type cenv e) sa sm ee tv vv z) /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn z /\
    (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G z) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G z) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) z = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u G tn /\
    (!v. read_result cx tv ee = (INL v,ee) ==>
      value_has_type rty v /\
      !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
        value_has_type ptv v) ==>
    ?v z' Gz tf.
      read_result cx tv ee = (INL v,ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,G,tn) [] (OK z',Gz,tf) /\
        expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
        ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
      (~is_word_type t ==>
        vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z') /\
      (~is_word_type t ==> !id path. tv = PlaceR (MemoryPlace id path) ==>
        vv_place_ptr cenv cx ee z' tv (LocatedValue t (mk_ptr op LocMemory))) /\
      (!ctv v. conditional_result cx tv ee = (INL ctv,ee) /\
        ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
        vv_own cenv cx t sa sb ee ctv
          (LocatedValue t (mk_ptr op LocMemory)) z') /\
      expr_store_bound cx t v op z' /\
      z'.vs_current_bb = sb.cs_current_bb /\
      z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
      ptr_val_ok cx t v op Gz tf z' /\
      (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
      (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op z' = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf) /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es1 /\
  expr_type e = t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es1 /\
  return_buf_frame d cenv sa u /\ alloca_history func u /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es1 u /\
    storage_well_formed_on cx es1 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es1 G1 tn1 u) /\
  ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs raw ee. eval_expr cx e (es1 with gas_obs := gs) = (INL raw,ee) ==>
    eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs) =
    (INL v,ee) ==>
    value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
      value_has_type ptv v) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (conditional_result cx))
    (es1,u,G1,tn1)
    (\H res ee G tn z. ?tv v. res = INL tv /\
      read_result cx tv ee = (INL v,ee) /\
      MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
      expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z /\
      (~is_word_type t ==>
        vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z) /\
      (~is_word_type t ==>
        vv_place_ptr cenv cx ee z tv (LocatedValue t (mk_ptr op LocMemory))) /\
      (!v. tv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
        vv_own cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx t v op z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      u.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx t v op G tn z /\
      (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G z) /\
      (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule ifexp_arm_raw_admissible >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ armQ armR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl [`mid`,`t'`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >- (gen_tac >> simp[vyperStorageTraceTheory.storage_trace_frame_conditional_result]) >>
  qexists `\H res ee G tn z. armQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `armR`] >> rpt strip_tac >>
      Cases_on `res` >> fs[expr_exit_def]) >>
  suspend "selected"
QED

Resume ifexp_arm_outcome_full_conditional[selected]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`z`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `armQ`] >> BETA_TAC >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists `tv` >> simp[] >>
  `eval_expr cx e (es1 with gas_obs := gas_explicit marks u.vs_gas_readings) = (INL tv,ee)` by
    (`ee with gas_obs := [] = ee` by
       (Cases_on `ee` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac [listTheory.APPEND_NIL] >>
     disch_then assume_tac >> fs[]) >>
  drule_all ifexp_arm_raw_source >> strip_tac >> fs[] >>
  qpat_x_assum `!ee tv z G tn. _`
    (qspecl_then [`ee`,`tv`,`z`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  strip_tac >>
  suspend "pure"
QED

Resume ifexp_arm_outcome_full_conditional[pure]:
  drule_all ifexp_arm_pure_source >>
  disch_then (qx_choose_then `ctv` strip_assume_tac) >>
  rename1 `expr_store_bound cx t v op zf` >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- fs[] >>
  qexistsl [`Gz`,`ee`,`INL ctv`,`zf`,`tf`] >>
  fs[] >>
  suspend "post"
QED

Resume ifexp_arm_outcome_full_conditional[post]:
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
  fs[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp zf)` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ zf`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [expr_post_def]) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >> simp[] >>
  `~zf.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def] >> metis_tac[])
  >>
  `conditional_result cx tv ee = (INL ctv,ee)` by
    (qpat_assum `!tail. conditional_result _ _ _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => PURE_REWRITE_TAC [th]) >> disch_then ACCEPT_TAC) >>
  drule_all (SIMP_RULE (srw_ss()) [] ifexp_arm_conditional_vv_facts) >> simp[]
QED

Finalise ifexp_arm_outcome_full_conditional

(* The ternary's root from the condition's value judgment and the arms'
   vv judgments.  Each arm is one of the three arm steps' kinds. *)
Theorem ifexp_body_post_nonword[local]:
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) ==>
  ~is_word_type (post_value_type ce e)
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- gvs[] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_bytestring] >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  gvs[expr_type_def] >>
  drule_all exprSimHypsTheory.ifexp_intcall_copy_source >> strip_tac >>
  fs[type_widens_to_def] >> metis_tac[exprSimLayoutTransportTheory.compatible_word_type]
QED

Theorem ifexp_body_punnable_refl[local]:
  (!t. punnable ce t t) /\ (!ts. punnable_list ce ts ts)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
  simp[punnable_def]
QED

Theorem ifexp_body_bytestring_evaluates[local]:
  !src dst tenv tv.
    is_bytestring_type src /\ is_bytestring_type dst /\
    arg_type_fits src dst /\ evaluate_type tenv dst = SOME tv ==>
    ?sv. evaluate_type tenv src = SOME sv
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `src` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT sb)` >> Cases_on `sb` >>
  gvs[is_bytestring_type_def] >>
  Cases_on `dst` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT db)` >> Cases_on `db` >>
  gvs[is_bytestring_type_def, arg_type_fits_def,
      vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def] >>
  TRY (rename1 `arg_type_fits (BaseT (BytesT sbd)) (BaseT (BytesT dbd))` >>
       Cases_on `sbd` >> Cases_on `dbd` >>
       gvs[is_bytestring_type_def, arg_type_fits_def,
           vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def]) >>
  rename1 `word_size n + 1 <= dimword (:256)` >>
  qpat_x_assum `n <= m` mp_tac >>
  disch_then (mp_tac o MATCH_MP exprSimPropsTheory.word_size_monotone) >> simp[]
QED

Theorem ifexp_body_arm_kind:
  expr_body_pre ce cx env e es ==>
  (is_word_type (post_value_type ce e) ==> is_word_type (expr_type e)) /\
  (post_value_type ce e = expr_type e /\
    (is_word_type (expr_type e) \/
     same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
       (?rtp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rtp) \/
     ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
       is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
       arg_type_fits (lowered_value_type ce e) (expr_type e)) \/
   ~is_word_type (expr_type e) /\
     post_value_type ce e = lowered_value_type ce e /\
     type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
     (?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv))
Proof
  strip_tac >> conj_tac >- metis_tac[ifexp_body_post_nonword] >>
  Cases_on `is_word_type (expr_type e)` >- simp[] >>
  Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
  >- (Cases_on `is_bytestring_type (expr_type e)`
      >- (gvs[expr_type_def] >>
          drule exprSimHypsTheory.ifexp_body_pre_intcall_physical >> strip_tac >>
          Cases_on `same_memory_layout ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) ann` >>
          simp[] >> Cases_on `ann` >>
          gvs[is_bytestring_type_def, arg_type_fits_def] >>
          Cases_on `lowered_value_type ce (Call (BaseT b) (IntCall fid) args drv)` >>
          gvs[arg_type_fits_def, is_bytestring_type_def] >>
          Cases_on `b` >> gvs[is_bytestring_type_def, arg_type_fits_def] >>
          Cases_on `b'` >> gvs[is_bytestring_type_def, arg_type_fits_def] >>
          rename1 `arg_type_fits (BaseT (BytesT src)) (BaseT (BytesT dst))` >>
          Cases_on `src` >> Cases_on `dst` >>
          gvs[is_bytestring_type_def, is_word_type_def, arg_type_fits_def]) >>
      gvs[expr_type_def] >> drule_all exprSimHypsTheory.ifexp_intcall_copy_source >> simp[]) >>
  `lowered_value_type ce e = expr_type e \/
   is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >> disch_then assume_tac >>
     mp_tac exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
     disch_then (qspecl_then [`ce`, `e`, `env`] mp_tac) >>
     gvs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_not_int_call] >>
  drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  Cases_on `same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- (drule ifexp_body_pre_lowered_type_compatible >> simp[] >>
      metis_tac[ifexp_body_bytestring_evaluates]) >>
  gvs[] >> metis_tac[same_memory_layout_def, ifexp_body_punnable_refl]
QED

Theorem ifexp_body_pre_children:
  !cenv cx env t c a b es.
    expr_body_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_body_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' ==>
          expr_body_pre cenv cx env a es' /\ expr_body_pre cenv cx env b es'
Proof
  rpt gen_tac >>
  simp[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeCallGraphTheory.int_calls_expr_def,
       exprSimHypsDefsTheory.byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_evm_run_root_def, listTheory.EVERY_APPEND] >>
  strip_tac >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
QED

Theorem ifexp_root_jnz_origin_path:
  expr_post H ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  allocas_from lo u /\ op_taint tn cop = {} ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,G,tn) [] (OK (jump_to (if sel then tl else el) u),G,tn)
Proof
  strip_tac >> irule fragGasEmitCtrlTheory.emit_jnz_origin_ptr >> simp[] >>
  qexistsl_tac [`cop`,`sj`,`sn`] >> simp[] >>
  fs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def, is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def,
     valueEncodingTheory.val_to_w256_def]
QED

Theorem ifexp_ghost_inv_at_jump:
  ghost_inv_at D lo d cenv cx es G tn (jump_to l s) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  `es with gas_obs := es.gas_obs = es` by
    simp[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`gs` |-> `es.gas_obs`]
    fragGasEmitCtrlTheory.ghost_inv_at_jump_to) >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem ifexp_vv_own_assigned_root_frame[local]:
  vv_own ce cx ty sc sd es tv (LocatedValue ty (mk_ptr op LocMemory)) u /\
  eval_operand op u = SOME w /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_id <= sc.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id ==>
  vv_own ce cx ty sa sb es tv (LocatedValue ty (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_allocas = u.vs_allocas /\ lookup_var rv ss = SOME w` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sa x ==> lookup_var x ss = lookup_var x u` by
    (rpt strip_tac >> `x <> rv` by metis_tac[] >>
     simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  `!n b sz. local_region ce es.scopes ss n b sz <=>
            local_region ce es.scopes u n b sz` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `sa` >> simp[]) >>
  qpat_x_assum `vv_own _ _ _ sc sd _ _ _ u` mp_tac >>
  simp[vv_own_def, mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[] >>
  disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
  `sa.cs_next_id <= aid /\ aid < sb.cs_next_id` by decide_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ifexp_arm_finish_vv_family_observed:
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H tr ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
     expr_post H ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
     stmt_state_rel H ctx func cenv cx es1 (jump_to lbl tt) /\
     expr_post H ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn u) /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  read_result cx tv ee = (INL v,ee) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  (~is_word_type t ==>
   vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~is_word_type t ==>
   vv_place_ptr cenv cx ee u tv (LocatedValue t (mk_ptr op LocMemory))) /\
  (!v. tv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
    vv_own cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  expr_store_bound cx t v op u /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next /\
  ptr_val_ok cx t v op G tn u /\
  (~is_word_type t ==>
   !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G u) /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/
          w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv es1 sc G1 tn1 (jump_to lbl tt) G tn /\
  expr_type e = t /\ post_value_type cenv e = t /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  (!w. eval_operand op u = SOME w ==>
       finish_at (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts))) ==>
  ?z Gz tf. ((?H0. valid_horizon cx st0 H0 tr) ==> finish_at z) /\
    !H. valid_horizon cx st0 H tr ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,Gz,tf) /\
    (?tv'. INL tv = INL tv' /\
      vv_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv'
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
      vv_store_bound cx (expr_type (IfExp t c a b))
        (lowered_value_type cenv (IfExp t c a b)) ee tv'
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee Gz tf z /\
      ptr_vv_ok cx (post_value_type cenv (IfExp t c a b)) tv'
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) ee Gz tf z /\
      (!v. tv' = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
        vv_own cenv cx t sa sb ee tv'
          (LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
        (!t' p. LocatedValue t (mk_ptr (Var rv) LocMemory) = LocatedValue t' p ==>
          p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\
       vv_location (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) = SOME LocCode ==>
       ?val. read_result cx tv' ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (IfExp t c a b)) = SOME rt /\
          eval_operand (vv_operand (if is_word_type t then StackValue t (Var rv)
           else LocatedValue t (mk_ptr (Var rv) LocMemory))) z = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt val (w2n w) mem) /\
      (!t' op'. (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) = StackValue t' op' /\
         ~is_word_type (post_value_type cenv (IfExp t c a b)) ==>
         ptr_buf_ok cenv (IfExp t c a b) op' Gz z) /\
      (!t' p. (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) = LocatedValue t' p /\
         p.ptr_location = LocMemory ==> ptr_buf_ok cenv (IfExp t c a b) p.ptr_operand Gz z) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tf)
Proof
  strip_tac >>
  reverse (Cases_on `?H0. valid_horizon cx st0 H0 tr`)
  >- (fs[] >> qexistsl [`ARB`,`ARB`,`ARB`] >> simp[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `?w. eval_operand op u = SOME w` by
    (qpat_assum `!H. valid_horizon _ _ H tr ==> _`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexistsl
    [`jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)`,
     `step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u)`,
     `step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn`] >>
  conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H tr ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `dead_lo_ok H (DF H) lo cenv cx` by first_assum (qspec_then `H` ACCEPT_TAC) >>
  drule_all (Q.INST [`D` |-> `DF H`] bodyFullIfExpFinishTheory.ifexp_arm_finish_full) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `expr_type e = t` kall_tac >>
  qpat_x_assum `post_value_type cenv e = t` kall_tac >>
  qpat_x_assum `sb.cs_current_bb = xl` kall_tac >> gvs[] >>
  `(ctx_has_dalloca ctx ==>
    allocas_below_fmp (jump_to xl
      (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))` by
    (qpat_assum `vv_post H _ _ _ _ (IfExp _ _ _ _) _ _ _ _ _ _ _ _`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [vv_post_def]) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  Cases_on `is_word_type t` >>
  gvs[contextTheory.vv_location_def, post_value_type_def, expr_type_def, mk_ptr_def] >>
  rpt strip_tac >>
  irule (REWRITE_RULE [mk_ptr_def]
    (Q.INST [`sc` |-> `sc`,`sd` |-> `sd`,`op` |-> `op`,`u` |-> `u`]
      ifexp_vv_own_assigned_root_frame)) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Frames at the selected arm entry, before attaching an arm outcome. *)
Theorem ifexp_selected_jump_ready:
  compile_expr ce ty e se = (av,sm) /\
  compile_ifexp_arm ce rt (lowered_value_type ce e) av sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  fn_has_code se sm fn /\ fn_has_code sm sx fn /\ fn_has_code sx sy fn /\
  se.cs_current_insts = [] /\ se.cs_current_bb = lbl /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s0,G0,tn0) marks (OK z,G,tn) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (z,G,tn) [] (OK (jump_to lbl z),G,tn) /\
  (!f i u. frag_reachable ctx fn s0 f i u ==> dalloca_fmp_headroom i u) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  alloca_history fn z /\ ~z.vs_halted /\
  return_buf_frame d ce sa s0 /\ sa.cs_next_var <= se.cs_next_var /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  expr_post H ctx fn ce cx c es sa sc s0 mid v cop z ==>
  (!f i u. frag_reachable ctx fn (jump_to lbl z) f i u ==> dalloca_fmp_headroom i u) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to lbl z)) /\
  alloca_history fn (jump_to lbl z) /\ ~ (jump_to lbl z).vs_halted /\
  (jump_to lbl z).vs_current_bb = se.cs_current_bb /\
  (jump_to lbl z).vs_inst_idx = LENGTH se.cs_current_insts /\
  return_buf_frame d ce se (jump_to lbl z)
Proof
  strip_tac >>
  `!i. active_inst fn i (jump_to lbl z) ==>
       frag_reachable ctx fn s0 fn i (jump_to lbl z)` by
    (rpt strip_tac >> irule ifexp_selected_entry_reachable >>
     qpat_assum `compile_expr _ _ _ se = _` (irule_at Any) >>
     qpat_assum `compile_ifexp_arm _ _ _ _ sm = _` (irule_at Any) >>
     qpat_assum `emit_inst ASSIGN _ _ sx = _` (irule_at Any) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ _` (irule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[contextRawReachableTheory.frag_reachable_trans] >>
  conj_tac
  >- (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp z` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[jump_to_def, ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac
  >- (irule allocaHistoryTheory.alloca_history_jump >>
      simp[jump_to_def] >> qexists `z` >> simp[]) >>
  simp[bodyMemoryDefsTheory.return_buf_frame_jump_to] >>
  `~(jump_to lbl z).vs_halted /\ (jump_to lbl z).vs_current_bb = se.cs_current_bb /\
   (jump_to lbl z).vs_inst_idx = LENGTH se.cs_current_insts` by simp[jump_to_def] >>
  simp[] >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qexistsl [`ce`,`s0`,`sa`] >> fs[expr_post_def]
QED

Theorem ifexp_vv_full_root_uniform:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e sa sm av op sb es1 u G1 tn1 st0.
    (e = a \/ e = b) /\
    compile_expr cenv ty e sa = (av,sm) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv e) av sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    !ee tv z G tn.
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
      (!id path. tv = PlaceR (MemoryPlace id path) ==>
        same_memory_layout cenv (lowered_value_type cenv e) t) /\
      storage_trace_domain cx st0 ee.storage_trace /\
      eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx func cenv cx e es1 sa sm u ee tv av z /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv av z /\
      z.vs_current_bb = sm.cs_current_bb /\
      z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sm ee tv av z) /\
      ptr_vv_ok cx (post_value_type cenv e) tv av ee G tn z /\
      (!t' op0. av = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op0 G z) /\
      (!t' p. av = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G z) /\
      (cenv.ce_is_ctor /\ vv_location av = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand av) z = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn /\
      (!v. read_result cx tv ee = (INL v,ee) ==>
        value_has_type rty v /\
        !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) ==>
      ?v z' Gz tf.
        read_result cx tv ee = (INL v,ee) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (z,G,tn) [] (OK z',Gz,tf) /\
          expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
          ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
        (~is_word_type t ==>
          vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z') /\
        (~is_word_type t ==> !id path. tv = PlaceR (MemoryPlace id path) ==>
          vv_place_ptr cenv cx ee z' tv (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx tv ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee ctv
        (LocatedValue t (mk_ptr op LocMemory)) z') /\
        expr_store_bound cx t v op z' /\
        z'.vs_current_bb = sb.cs_current_bb /\
        z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
        ptr_val_ok cx t v op Gz tf z' /\
        (~is_word_type t ==>
          !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
        (~is_word_type t ==>
          !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
        ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     (!e gs' raw ee. (e = a \/ e = b) /\
       eval_expr cx e (es1 with gas_obs := gs') = (INL raw,ee) ==>
       eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') ==>
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_def] >> rpt strip_tac >>
  `!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
      (compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gas_shadow_stmt_compile_expr_env) >>
  `!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
      (lower_value compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gas_shadow_stmt_lower_value_env) >>
  `!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
      (compile_ifexp_arm (gas_shadow_env T cenv) rt at av)` by
    simp[gasShadowCompileConvertTheory.gas_shadow_compiles_ifexp_arm] >>
  drule_all bodyFullIfExpShadowTheory.ifexp_shadow_code_layout >>
  disch_then (assume_tac o GEN_ALL) >>
  `?cop sc shadow_sc.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr c) shadow_sa = (cop,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\ fn_has_code sa sc func /\
    fn_has_code shadow_sa shadow_sc shadow_func` by
    (qpat_assum `!sel. ?cop. _` (qspec_then `T` strip_assume_tac) >>
     qexistsl [`cop`,`sc`,`shadow_sc`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimIfExpTheory.ifexp_root_condition_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ c _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`cop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rewrite_tac[exprSimIfExpTheory.ifexp_root_eval_forced] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ0 condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx c) (read_result cx))
     (es,s0,G0,tn0)
     (\H res ee G tn z. condQ0 H res ee G tn z /\
       ?cm. gas_origin_ptr_path
         (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK z,G,tn)) condR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ condQ0 condR` (irule_at Any) >>
     qx_genl_tac [`cm`,`H`,`cr`,`ces`,`CG`,`Ctn`,`cz`] >> strip_tac >>
     simp[] >> qexists_tac `cm` >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ condQ0 condR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ finalQ finalR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t'`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >> simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_conditional_result,
       vyperStorageTraceTheory.storage_trace_frame_raise]) >>
  qexists `\H res ee G tn z. condQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >> simp[Abbr `condR`] >> rpt strip_tac >>
      Cases_on `res` >- fs[expr_exit_def] >>
      qpat_assum `halt_exit H cx ee (INR y) r`
        (assume_tac o REWRITE_RULE [halt_exit_def]) >>
      qexists `y` >> simp[Abbr `finalR`, halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
        stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`z`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `condQ`, Abbr `condQ0`] >> BETA_TAC >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists `v` >> simp[] >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by
       (Cases_on `mid` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac [listTheory.APPEND_NIL] >>
     disch_then assume_tac >> fs[]) >>
  drule_all exprSimIfExpTheory.ifexp_root_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  qpat_assum `!sel. ?cop. _` (qspec_then `sel` strip_assume_tac) >>
  `cop' = cop /\ sc' = sc /\ shadow_sc' = shadow_sc` by
    (qpat_x_assum `lower_value compile_expr cenv (BaseT BoolT) c sa = (cop',sc')` mp_tac >>
     qpat_x_assum `lower_value compile_expr _ (BaseT BoolT) (gas_shadow_expr c) shadow_sa = (cop',shadow_sc')` mp_tac >> simp[]) >>
  qpat_x_assum `cop' = cop` SUBST_ALL_TAC >>
  qpat_x_assum `sc' = sc` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_sc' = shadow_sc` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (z,G1,tn1) [] (OK (jump_to (if sel then tl else el) z),G1,tn1)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `allocas_from lo z` by fs[ghost_inv_at_def] >>
     `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
       (qpat_assum `expr_post H _ _ _ _ c _ _ _ _ _ _ _ z`
          (assume_tac o CONJUNCT1 o REWRITE_RULE [expr_post_def]) >>
        drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
     `op_taint tn1 cop = {}` by
       fs[ptr_val_ok_def, is_word_type_def] >>
     drule_all ifexp_root_jnz_origin_path >> simp[]) >>
  `(!gs v es1. bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
      (INL v,es1) ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty (if sel then a else b) es1)` by
    (Cases_on `sel` >> simp[] >> metis_tac[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty (if sel then a else b) mid` by metis_tac[] >>
  `(!gs raw ee. eval_expr cx (if sel then a else b)
       (mid with gas_obs := gs) = (INL raw,ee) ==>
       eval_result_typed (env,cx,ee) raw
         (Type (expr_type (if sel then a else b))))` by
    (Cases_on `sel` >> simp[] >> metis_tac[]) >>
  `(!gs v ee. bind (eval_expr cx (if sel then a else b)) (read_result cx)
       (mid with gas_obs := gs) = (INL v,ee) ==>
       value_has_type rty v /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv (if sel then a else b)) = SOME ptv ==>
         value_has_type ptv v)` by
    (qpat_assum `!gs v es1. bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==> _ /\ _`
       (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`BoolV sel`,`mid`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_x_assum `!e gs v ee. _ ==> value_has_type rty v /\ _`
       (qspec_then `if sel then a else b` mp_tac) >>
     Cases_on `sel` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      expr_vv_res_ok mid` by
    (drule_all exprSimIfExpTheory.ifexp_root_branch_admissible >>
     `mid with gas_obs := [] = mid` by
       (Cases_on `mid` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     (mid,z,G1,tn1)
     finalQ finalR` suffices_by (Cases_on `sel` >> simp[]) >>
  irule gas_outcome_full_zero_prefix_guarded >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
    vyperStorageTraceTheory.evaluate_storage_trace_frame,
    vyperStorageTraceTheory.storage_trace_frame_conditional_result] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G1`,`jump_to (if sel then tl else el) z`,`tn1`] >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_conditional_result] >>
  suspend "arm"
QED

Resume ifexp_vv_full_root_uniform[arm]:
  `gas_origin_ptr_path
     (DF (storage_trace_horizon mid.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (z,G1,tn1) [] (OK (jump_to (if sel then tl else el) z),G1,tn1)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `sa.cs_next_var <= se.cs_next_var` by decide_tac >>
  drule_all ifexp_selected_jump_ready >> strip_tac >>
  simp[Abbr `finalR`] >>
  irule ifexp_outcome_zero_suffix_framed >>
  irule_at Any (Q.INST [`t` |-> `t`, `c` |-> `c`, `a` |-> `a`, `b` |-> `b`]
    ifexp_arm_outcome_full_conditional) >>
  qpat_assum `compile_expr cenv ty (if sel then a else b) se = (av,sea)` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_se = _`
    (irule_at Any) >>
  qpat_assum `expr_vv_sim_full _ _ _ _ (if sel then a else b) mid` (irule_at Any) >>
  qexistsl [`t`,`sx`,`rty`,`aop`,`env`,`c`,`b`,`a`] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!e sa sm av op sb es1 u G1 tn1 st0. _` mp_tac >>
      simp[] >> disch_then irule >> simp[] >>
      qexistsl [`av`,`if sel then a else b`,`sea`] >> simp[] >>
      Cases_on `sel` >> simp[]) >>
  conj_tac >- (Cases_on `sel` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ((?v. _) /\ _) /\ _`
        (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >>
      simp[ifexp_ghost_inv_at_jump,
           exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
      `stmt_state_rel H ctx func cenv cx mid z /\
       storage_well_formed_on cx mid (FST H)` by
        (qpat_x_assum `expr_post H _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
         simp[expr_post_def]) >>
      simp[]) >>
  simp[jump_to_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_conditional_result]) >>
  qx_genl_tac [`res`,`ee`,`Gf`,`tnf`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  simp[NoAsms, Abbr `finalQ`] >>
  qpat_assum `res = INL tv` (fn th => rewrite_tac[th]) >>
  qpat_assum `vv = _` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, expr_type_def] >>
  irule (CONV_RULE (RAND_CONV
    (SIMP_CONV (srw_ss() ++ numSimps.ARITH_ss) [post_value_type_def, expr_type_def]))
    (PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES, FORALL_SIMP]
      (BETA_RULE (Q.INST [`finish_at` |-> `\s. T`] ifexp_arm_finish_vv_family_observed)))) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G1`,`cop`,`IfExp t c a b`,`mid`,`if sel then tl else el`,
    `aop`,`sc`,`se`,`sx`,`sy`,`sz`,`tn1`,`z`,`BoolV sel`] >>
  simp[jump_to_def] >>
  reverse conj_tac
  >- (simp[expr_type_def] >>
      `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
        (qpat_x_assum `expr_post _ _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
         simp[expr_post_def, locals_kept_def]) >>
      metis_tac[]) >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  `storage_trace_frame (bind (eval_expr cx c) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ((?v. _) /\ _) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ?tv v. _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (qpat_x_assum `expr_post H _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
     simp[expr_post_def]) >>
  gvs[] >>
  qpat_x_assum `z.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[GSYM jump_to_def, exprLoweringPropsTheory.stmt_state_rel_jump_to]
QED

Finalise ifexp_vv_full_root_uniform
