(* A ternary at the joint judgments, on finite horizons: the condition's
   value, the JNZ into the selected arm's block, the arm (no copy, a
   bytestring widening copy, or a widened internal call's typed copy), the
   ASSIGN and the JMP.  The value judgment follows from the vv judgment by
   the shared joint unwrap_value lemma (bodyFullUnwrap).

   The helper lemmas the arm steps take as premises are discharged here:
   the generic ALLOCA/bytestring ones from bodyFullAllocGeneric, the joint
   typed copy from typedCopyOriginPtr.

   DRAFT: statements only; the proofs are not written yet.
 *
 * TOP-LEVEL:
 *   expr_sim_full_of_vv -- the value judgment from the vv judgment
 *   ifexp_vv_full_root -- the ternary's vv judgment from its parts
 *   ifexp_expr_full_ok -- bodyFullCases' IfExp case (body_ifexp_case_full)
 *)
Theory bodyFullIfExp
Ancestors
  bodyFullIfExpArm bodyFullIfExpWiden bodyFullIfExpWidenCall
  bodyFullIfExpFinish bodyFullIfExpShadow bodyFullAllocGeneric typedCopyOriginPtr
  bodyFullUnwrap bodyFullPreds
  bodySimFull gasOutcomeFullCompose gasOutcomeFull gasShadowCompile
  gasShadowCompileHelpers exprSimMemorySource exprSimIfExp exprSimDefs
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering exprLoweringProps
  typedCopyDomain vyperTypeSystem compileEnv context vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

(* An owned physical value never needs the local-place alternative. *)
Theorem ifexp_nocopy_physical_owned_vv[local]:
  ~is_word_type src /\ ~is_word_type dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  expr_val_own ce cx src sa sb ee v op s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_at ce cx dst sa sb ee tv (LocatedValue dst (mk_ptr op LocMemory)) s
Proof
  simp[vv_at_def, mk_ptr_def, expr_val_own_def] >> rpt strip_tac >>
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
  expr_store_bound cx t v op z /\
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
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `expr_type e = t` (SUBST_ALL_TAC o SYM) >>
  rpt conj_tac
  >- (rpt strip_tac >> res_tac >> simp[] >>
      irule ifexp_nocopy_physical_post >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      irule (INST_TYPE [``:'a`` |-> ``:256``] ifexp_nocopy_physical_endpoint_vv) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`storage_trace_horizon ee.storage_trace`, `ctx`, `es`, `func`, `u`] >>
      first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (irule ifexp_nocopy_physical_ptr >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> drule_all ifexp_nocopy_physical_buffer >> simp[])
  >> fs[same_memory_layout_def] >> metis_tac[]
QED

(* The value judgment from the vv judgment: lower_value is compile_expr
   then unwrap_value, whose code reads no GAS (unwrap_value_origin_ptr). *)
Theorem expr_sim_full_of_vv:
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es ==>
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_def] >> rpt strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty (gas_shadow_expr e) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (vv', shadow_sm)` >> simp[] >> strip_tac >>
  `vv' = vv /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`cenv`,`ty`,`e`,`T`] mp_tac (cj 1 gas_shadow_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qpat_assum `compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >> fs[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  suspend "read"
QED

Resume expr_sim_full_of_vv[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>

  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `sm`, `sc` |-> `sb`, `G` |-> `G1`,
    `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL unwrap_value_origin_ptr)) >>
  impl_tac >- simp[] >>
  suspend "unwrap"
QED

Resume expr_sim_full_of_vv[unwrap]:
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Finalise expr_sim_full_of_vv

(* Uniform selected-arm conversion; the endpoint is shared by all horizons. *)
Theorem ifexp_selected_arm_step_full[local]:
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
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
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
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
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
  >>~- ([`type_widens_to _ _ _`], (irule ifexp_widened_call_arm_step_full >>
      rpt conj_tac >>
      FIRST_PROVE [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_store_memory_typed_origin_ptr_path),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (qexistsl_tac [`e`,`stv`,`sm`,`stv`,`ty`,`vv`] >>
              simp[] >> rpt strip_tac >> first_x_assum drule >> simp[])] >> gvs[]))
  >>~- ([`is_bytestring_type _`, `~same_memory_layout _ _ _`], (irule ifexp_widen_arm_step_full >> rpt conj_tac >>
      FIRST [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_store_bytestring_origin_ptr_path),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (irule valueCopyBytesTheory.is_bytestring_word_type >> first_assum MATCH_ACCEPT_TAC),
             (qexistsl_tac [`e`,`sm`,`ty`,`vv`] >> gvs[]),
             FAIL_TAC "bytes concrete"] >> gvs[])) >>
  irule ifexp_unwrap_arm_step_full >> rpt conj_tac >>
  FIRST [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
         first_assum MATCH_ACCEPT_TAC,
         (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
          qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
         (qexistsl_tac [`e`,`sm`,`ty`,`vv`] >> simp[]),
         FAIL_TAC "unwrap concrete"] >> simp[] >>
  gvs[]
QED

(* Source composition is independent of the proof of arm conversion.
   The conversion contract is specialized at the fixed compiler layout;
   only its runtime endpoint is universally quantified. *)
Theorem ifexp_arm_outcome_full_conditional[local]:
  (!ee tv z G tn.
    MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es1 sa sm u ee tv vv z /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv z /\
    z.vs_current_bb = sm.cs_current_bb /\
    z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
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
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
      expr_store_bound cx t v op z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx t v op G tn z /\
      (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G z) /\
      (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es1` by
    (rw[gasContextTheory.gas_admissible_def] >>
     qpat_x_assum `gas_admissible (bind _ _) _ _`
       (qspec_then `gs` mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     Cases_on `res` >> simp[bind_def, expr_vv_res_ok_def] >>
     rename1 `INL rv0` >> Cases_on `rv0` >>
     simp[conditional_result_def, raise_def, expr_vv_res_ok_def]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ armQ armR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl [`mid`,`t'`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
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
  `MAP FDOM es1.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
     value_has_type rty v /\
     !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
       value_has_type ptv v` by
    (rpt strip_tac >>
     qpat_x_assum `!gs v ee. bind _ _ _ = _ ==> _`
       (qspecl_then [`gas_explicit marks u.vs_gas_readings`,`v`,`ee`] mp_tac) >>
     simp[bind_def]) >>
  fs[] >>
  qpat_x_assum `!ee tv z G tn. _`
    (qspecl_then [`ee`,`tv`,`z`,`G`,`tn`] mp_tac) >>
  (impl_tac >- fs[]) >>
  strip_tac >>
  suspend "pure"
QED

Resume ifexp_arm_outcome_full_conditional[pure]:
  Cases_on `conditional_result cx tv ee` >>
  rename1 `conditional_result cx tv ee = (cr,ces)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
      (qspec_then `gas_explicit marks u.vs_gas_readings` mp_tac o
       REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     fs[bind_def]) >>
  drule_all bodyPtrIfExpConditionalSourceTheory.ifexp_conditional_source_success >>
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
  `~zf.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def] >> metis_tac[]) >>
  irule ifexp_vv_at_conditional >>
  qexistsl [`tv`,`v`] >> fs[] >>
  qpat_assum `!tail. conditional_result _ _ _ = _`
    (qspec_then `ee.gas_obs` mp_tac) >>
  pure_rewrite_tac (TypeBase.updates_of ``:evaluation_state``) >>
  disch_then (mp_tac o MATCH_MP ifexp_conditional_result_shape) >>
  strip_tac >> fs[read_result_def, return_def]
QED

Finalise ifexp_arm_outcome_full_conditional

(* The ternary's root from the condition's value judgment and the arms'
   vv judgments.  Each arm is one of the three arm steps' kinds. *)
Theorem ifexp_vv_full_root:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e. (e = a \/ e = b) ==>
       (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
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
        (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))) /\
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
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') ==>
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

(* bodyFullCases' IfExp case: the side facts the root takes come from
   body_inv and expr_body_pre, the word agreement by the contrapositive of
   post_value_type_nonword. *)
Theorem ifexp_expr_full_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED
