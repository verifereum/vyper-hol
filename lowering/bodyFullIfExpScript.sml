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
