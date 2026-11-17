(*
 * The internal call full case's argument stage over the finite-horizon
 * joint judgment.
 *
 * TOP-LEVEL:
 *   intcall_args_full
 *)
Theory bodyFullIntCallArgs
Ancestors ptrDiscipline[qualified,ignore_grammar]
  bodyFullIntCallDefs bodyIntCallSeams bodyFullPreds bodySimFull bodyFullUnwrap
  gasOutcomeFull bodyPtrDefs gasShadow gasContext exprSimHypsDefs
  loweringPosts exprSimVVFrame valueEncodingProofs bodyPtrBytestringBuiltinsWindowGhost
  exprReasonOperand typedMemoryCopy
  exprSimHyps exprSimSend aggregateEvaluatedLayout vyperTypeSystem context compileEnv
  exprLowering vyperInterpreter vyperState vyperAST vyperStorageTrace fragExec list

val _ = Parse.hide "body";

(* Lock acquisition precedes push_function.  Only its successful endpoint
   commutes with the scope update; failures retain the original scopes. *)
Theorem intcall_args_lock_push_success:
  lock_if_nr cx nr (is_view_mut mut) st = (INL (),locked) ==>
  bind (lock_if_nr cx nr (is_view_mut mut))
    (\u. bind (push_function (NONE,name) penv cx)
      (\cxf. bind
        (finally_unless_halt
          (finally
            (try (bind (eval_stmts cxf ss) (\u. return NoneV))
                 handle_function)
            (pop_function prev))
          (unlock_if_nr cx nr (is_view_mut mut)))
        (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                   (\crv. return (Value crv))))) st =
  intcall_rest cx name mut nr ss prev rtv (st with scopes := [penv])
Proof
  strip_tac >>
  `lock_if_nr cx nr (is_view_mut mut) (st with scopes := [penv]) =
   (INL (), locked with scopes := [penv])` by
    (qpat_x_assum `lock_if_nr _ _ _ st = _` mp_tac >>
     Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
     simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
       get_transient_storage_def, update_transient_def,
       record_storage_event_def, return_def, raise_def,
       check_not_static_def, check_def, assert_def, COND_RATOR] >>
     rpt IF_CASES_TAC >>
     simp[bind_def, return_def, raise_def, update_transient_def,
          assert_def] >>
     Cases_on `is_view_mut mut` >> simp[] >> rpt strip_tac >> gvs[]) >>
  pure_rewrite_tac[intcall_rest_def, ignore_bind_def] >>
  pure_asm_rewrite_tac[bind_def] >>
  simp[bind_def, push_function_def, return_def]
QED

Theorem intcall_args_lock_push_failure:
  lock_if_nr cx nr (is_view_mut mut) st = (INR err,failed) ==>
  bind (lock_if_nr cx nr (is_view_mut mut))
    (\u. bind (push_function (NONE,name) penv cx)
      (\cxf. bind
        (finally_unless_halt
          (finally
            (try (bind (eval_stmts cxf ss) (\u. return NoneV))
                 handle_function)
            (pop_function prev))
          (unlock_if_nr cx nr (is_view_mut mut)))
        (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                   (\crv. return (Value crv))))) st =
  (INR err,failed)
Proof
  simp[bind_def]
QED

Theorem intcall_args_aggregate_physical_type:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx tenv e esi /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) (expr_type e) dty ==>
  vv_type vv = lowered_value_type cenv e
Proof
  strip_tac >>
  `well_typed_expr tenv e /\
   (!id t. FLOOKUP tenv.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def] >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type cenv e` by
    (drule_all compile_expr_reason_uniform >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum (qspec_then `expr_type e` strip_assume_tac) >>
     first_x_assum drule >> Cases_on `vv` >>
     gvs[reason_result_shape_def, vv_type_def] >> metis_tac[]) >>
  Cases_on `lowered_value_type cenv e = expr_type e` >- gvs[] >>
  `(?n s. e = Literal (BaseT (StringT n)) (StringL s)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?ty n args. e = Builtin ty (Concat n) args) \/
   (?ann ensure method_id tys args.
      e = TypeBuiltin ann (AbiEncode ensure method_id) tys args) \/
   (?ann fid args dret. e = Call ann (IntCall fid) args dret)` by
    (qpat_x_assum `lowered_value_type cenv e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def]
     >~ [`Literal t l`]
     >- (Cases_on `t` >> simp[lowered_value_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         Cases_on `l` >> simp[lowered_value_type_def] >>
         rename1 `BytesT bound` >> Cases_on `bound` >>
         simp[lowered_value_type_def])
     >~ [`Builtin t b l`]
     >- (Cases_on `b` >> simp[lowered_value_type_def])
     >~ [`TypeBuiltin ann tb tys args`]
     >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
     rename1 `Call ann target args dret` >> Cases_on `target` >>
     simp[lowered_value_type_def]) >>
  pop_assum mp_tac >> strip_tac >> gvs[expr_type_def]
  >- (drule type_widens_from_bytestring >> simp[is_bytestring_type_def])
  >- (drule type_widens_from_bytestring >> simp[is_bytestring_type_def])
  >- (gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
      drule type_widens_from_bytestring >> simp[is_bytestring_type_def])
  >- (gvs[well_typed_expr_def, type_builtin_result_ok_def] >>
      drule type_widens_from_bytestring >> simp[is_bytestring_type_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[compile_expr_call] >> strip_tac >>
  drule reason_compile_call >> Cases_on `vv` >>
  gvs[reason_result_shape_def, vv_type_def]
QED

(* A completed memory argument is protected by its full allocation, not by
   an arbitrary fixed-low memory frame.  Restrict both byte and taint frames
   to its value footprint before applying the canonical robust transport. *)
Theorem intcall_args_old_site_robust[local]:
  wb_frame cenv es ee si s t /\
  ghost_kept_at lo cenv es si G tn s G' tn' /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < si.cs_next_id /\
  (!n lb sz. local_region cenv es.scopes s n lb sz ==>
     b+cap <= lb \/ lb+sz <= b) /\
  b <= a /\ a + val_footprint rt v <= b+cap /\ val_wf rt v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt v a mem) ==>
  !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
     val_in_memory rt v a mem
Proof
  strip_tac >>
  `mem_bytes_at b cap t.vs_memory = mem_bytes_at b cap s.vs_memory` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  `mem_bytes_at a (val_footprint rt v) t.vs_memory =
   mem_bytes_at a (val_footprint rt v) s.vs_memory` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`a-b`,`val_footprint rt v`] mp_tac) >>
     simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_window_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`,`tn'.t_mem`,`val_footprint rt v`,
                `s.vs_memory`,`t.vs_memory`] >>
  simp[] >> rpt strip_tac >>
  `b <= i /\ i < b+cap` by decide_tac >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED

Theorem intcall_args_prefix_frame:
  LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
  LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
  eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
  (!j rt. j < LENGTH ops /\
     evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
     value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
     val_footprint rt (EL j vals) <= type_memory_size rt /\
     (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals)) /\
     (~EL j pflags ==> ?b cap aid.
       op_prov G (EL j ops) = SOME (b,cap) /\
       FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
       lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
       w2n (EL j ws) + type_memory_size rt <= b+cap /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+cap <= lb \/ lb+sz <= b) /\
       (case pin of NONE => T | SOME (rb,pb,pk) =>
         b+cap <= pb \/ pb+pk <= b))) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
     lookup_var rb s = SOME (n2w b) /\
     FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
     not_fresh_at si rb /\
     (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
       b+k <= lb \/ lb+sz <= b)) /\
  wb_frame cenv esi ee si s t /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!n b k. local_region cenv esi.scopes s n b k <=>
           local_region cenv ee.scopes t n b k) /\
  (!lbl. FLOOKUP t.vs_labels lbl = FLOOKUP s.vs_labels lbl) ==>
  LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
  LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
  eval_operands ops t = SOME ws /\ EVERY (\op. op_taint tn1 op = {}) ops /\
  (!x. MEM (Var x) ops ==> not_fresh_at sj x) /\
  (!j rt. j < LENGTH ops /\
     evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
     value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
     val_footprint rt (EL j vals) <= type_memory_size rt /\
     (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals)) /\
     (~EL j pflags ==> ?b cap aid.
       op_prov G1 (EL j ops) = SOME (b,cap) /\
       FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
       sa.cs_next_id <= aid /\ aid < sj.cs_next_id /\
       lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws) /\
       w2n (EL j ws) + type_memory_size rt <= b+cap /\
       (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
       (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
         b+cap <= lb \/ lb+sz <= b) /\
       (case pin of NONE => T | SOME (rb,pb,pk) =>
         b+cap <= pb \/ pb+pk <= b))) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
     lookup_var rb t = SOME (n2w b) /\
     FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < sj.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
     not_fresh_at sj rb /\
     (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
       b+k <= lb \/ lb+sz <= b))
Proof
  strip_tac >>
  `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w` by metis_tac[wb_frame_def] >>
  `!x. not_fresh_at si x ==>
      FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
    metis_tac[ghost_kept_at_def] >>
  `!a w. MEM a ops /\ eval_operand a s = SOME w ==>
      eval_operand a t = SOME w` by
    (rpt strip_tac >> Cases_on `a` >>
     gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operands ops t = SOME ws` by
    (qpat_x_assum `eval_operands ops s = SOME ws` mp_tac >>
     qpat_x_assum `!a w. MEM a ops /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `ws` >>
     Induct_on `ops` >> simp[venomStateTheory.eval_operands_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `EVERY (\op. op_taint tn1 op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def] >>
     metis_tac[ptrDisciplineTheory.op_taint_def]) >>
  simp[] >> conj_tac
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!j rt. _` (qspecl_then [`j`,`rt`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      simp[] >> strip_tac >>
      qpat_x_assum `~EL j pflags ==> _` (drule_then strip_assume_tac) >>
      `op_prov G1 (EL j ops) = SOME (b,cap)` by
        (Cases_on `EL j ops` >>
         gvs[ptrDisciplineTheory.op_prov_def] >>
         metis_tac[MEM_EL]) >>
      `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
         val_in_memory rt (EL j vals) (w2n (EL j ws)) mem` by
        (`w2n (EL j ws) + val_footprint rt (EL j vals) <= b+cap`
           by decide_tac >>
         metis_tac[intcall_args_old_site_robust]) >>
      qexistsl_tac [`b`,`cap`,`aid`] >>
      fs[wb_frame_def] >> metis_tac[]) >>
  Cases_on `pin` >> simp[] >>
  PairCases_on `x` >> gvs[] >>
  fs[wb_frame_def] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

(* The completed prefix and the pinned return allocation are proof data only.
   The source continuation receives just the values read by the remaining list. *)
Theorem intcall_args_locals_compose[local]:
  !cenv es es1 es2 s0 s1 s2.
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
               local_region cenv es1.scopes s1 n b sz) /\
    locals_kept cenv es es1 s0 s1 /\
    locals_kept cenv es1 es2 s1 s2 ==>
    locals_kept cenv es es2 s0 s2
Proof
  rpt gen_tac >> strip_tac >>
  fs[loweringPostsTheory.locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[vyperEvalScopesProgressTheory.scopes_progress_trans]
  >- (rpt strip_tac >>
      `?entry entry1. lookup_scopes n es.scopes = SOME entry /\
                      lookup_scopes n es1.scopes = SOME entry1` by
        (gvs[loweringStateRelDefsTheory.local_region_def] >>
         metis_tac[optionTheory.option_CASES]) >>
      `entry1 = entry` by
        (qpat_x_assum `scopes_progress es.scopes _`
           (qspecl_then [`n`, `entry`, `entry1`] mp_tac o
             SIMP_RULE std_ss [vyperEvalScopesProgressTheory.scopes_progress_def]) >>
         qpat_x_assum `scopes_progress es1.scopes _`
           (qspecl_then [`n`, `entry1`, `entry`] mp_tac o
             SIMP_RULE std_ss [vyperEvalScopesProgressTheory.scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[loweringPostsTheory.popped_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!n b sz entry' h. local_region _ es1.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz entry' h. local_region _ es.scopes _ _ _ _ /\ _ ==> _`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `n` >> fs[])
  >- simp[] >>
  metis_tac[]
QED

(* Compose the original caller frame once, for both staging branches. *)
Theorem intcall_args_frame_compose[local]:
  wb_frame cenv es0 esi sa s0 s /\
  wb_frame cenv esi mid si s t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  sa.cs_next_id <= si.cs_next_id /\
  sa.cs_next_var <= si.cs_next_var /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv esi.scopes s n b sz) ==>
  wb_frame cenv es0 mid sa s0 t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  conj_tac >-
    (fs[loweringPostsTheory.wb_frame_def] >>
     conj_tac >-
       (rpt strip_tac >> `aid < si.cs_next_id` by decide_tac >> metis_tac[]) >>
     irule intcall_args_locals_compose >>
     qexistsl [`esi`, `s`] >> simp[]) >>
  fs[bodyPtrDefsTheory.ghost_kept_at_def, loweringPostsTheory.wb_frame_def] >>
  conj_tac >-
    (rpt strip_tac >>
     `aid < si.cs_next_id` by decide_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `i IN tn.t_mem` by
       (qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
        simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
     simp[] >> disch_then irule >> rpt strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem intcall_args_parameter_allocation_bounds[local]:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops ==>
  EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) (MAP SND args)
Proof
  rpt strip_tac >>
  `MEM (subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,[],ret,ss))
      (FST (SND (classify_functions tops)))` by
    (simp[constSubstTheory.subst_consts_fn_def,
          loweringShapePropsTheory.MEM_classify_internal] >>
     qexistsl_tac [`[]`,`ss`] >> simp[]) >>
  qpat_x_assum `body_inv _ _ _ _` mp_tac >>
  simp[bodySimTheory.body_inv_def] >> strip_tac >>
  Cases_on `classify_functions tops` >> rename1 `classify_functions tops = (exts,rest)` >>
  PairCases_on `rest` >>
  `fn_allocs_ok tops (subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,[],ret,ss))` by
    (Cases_on `cx.in_deploy`
     >- (gvs[] >> irule compileVyperTheory.lower_vyper_deploy_unit_allocs_ok >>
         metis_tac[]) >>
     gvs[] >> irule compileVyperTheory.lower_vyper_runtime_unit_allocs_ok >>
     metis_tac[]) >>
  qpat_x_assum `fn_allocs_ok _ _` mp_tac >>
  simp[constSubstTheory.subst_consts_fn_def, compileVyperTheory.fn_allocs_ok_def] >>
  strip_tac >>
  `type_memory_bytes
     (build_compile_env tops Internal mut name args ret
       (subst_consts_stmts (module_consts_env tops []) ss) F) =
     type_memory_bytes cenv` by
    (irule compileEnvTheory.type_memory_bytes_frame >>
     simp[compileVyperTheory.build_compile_env_ce_struct_fields]) >>
  gvs[EVERY_MAP, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem intcall_args_read_result_prefix[local]:
  ~s.vs_halted /\
  read_result cx tv es = (INL v,es) /\
  (!x. storage_trace_frame (k x)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 (k v)
    (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (read_result cx tv) k) (es,s,G,tn) Q R
Proof
  strip_tac >>
  irule (gasOutcomeFullComposeTheory.gas_outcome_full_bind_all
    |> Q.INST [`Q1` |-> `\H res ee G1 tn1 t.
       res = INL v /\ ee = (es with gas_obs := []) /\
       G1 = G /\ tn1 = tn /\ t = s`]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`gas_outcome_full _ _ _ _ (read_result cx tv) _ _ _`]
  >- (qexists_tac `v` >> reverse conj_tac
      >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
          conj_tac >- (qexistsl_tac [`G`,`es`,`INL v`,`s`,`tn`] >>
            simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
            metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
          simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
          metis_tac[exprSimMemorySourceTheory.read_result_gas_obs]) >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >> disj1_tac >> simp[])
  >~ [`storage_trace_frame (read_result cx tv)`]
  >- simp[storage_trace_frame_read_result]
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      metis_tac[]) >>
  rpt strip_tac >>
  irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED

Theorem intcall_args_stage_full:
  !es DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
   st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin f P Q R.
    body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (supported_value_type tops) dtys /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr cenv (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (vyperState$bind (eval_exprs cx es) f) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (!H res ee gt r. expr_exit res r ==> R H res ee gt r) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) /\
    (!marks xs ee t G1 tn1.
       (!tail. eval_exprs cx es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       LENGTH xs = LENGTH es /\ expr_sim_inv cenv cx tenv ee /\
       (?ws1.
         LENGTH ws1 = LENGTH (ops ++ newops) /\
         LENGTH (vals ++ xs) = LENGTH (ops ++ newops) /\
         LENGTH (ptys ++ dtys) = LENGTH (ops ++ newops) /\
         LENGTH (pflags ++ flags) = LENGTH (ops ++ newops) /\
         eval_operands (ops ++ newops) t = SOME ws1 /\
         EVERY (\op. op_taint tn1 op = {}) (ops ++ newops) /\
         (!x. MEM (Var x) (ops ++ newops) ==> not_fresh_at sf x) /\
         (!j rt. j < LENGTH (ops ++ newops) /\
           evaluate_type (get_tenv cx) (EL j (ptys ++ dtys)) = SOME rt ==>
           value_has_type rt (EL j (vals ++ xs)) /\
           val_wf rt (EL j (vals ++ xs)) /\
           val_footprint rt (EL j (vals ++ xs)) <= type_memory_size rt /\
           (EL j (pflags ++ flags) ==>
             EL j ws1 = typed_val_to_w256 rt (EL j (vals ++ xs))) /\
           (~EL j (pflags ++ flags) ==>
             ?b cap aid.
               op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
               FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
               sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
               lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws1) /\
               w2n (EL j ws1) + type_memory_size rt <= b+cap /\
               (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
                 val_in_memory rt (EL j (vals ++ xs)) (w2n (EL j ws1)) mem) /\
               (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
                 b+cap <= lb \/ lb+sz <= b) /\
               (case pin of NONE => T | SOME (rb,pb,pk) =>
                 b+cap <= pb \/ pb+pk <= b)))) /\
       (case pin of NONE => T | SOME (rb,b,k) =>
         FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
         lookup_var rb t = SOME (n2w b) /\
         FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
         sa.cs_next_id < sf.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
         not_fresh_at sf rb /\
         (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
           b+k <= lb \/ lb+sz <= b)) /\
       wb_frame cenv es0 ee sa s0 t /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
       alloca_history func t /\ sa.cs_next_id <= sf.cs_next_id /\
       sa.cs_next_var <= sf.cs_next_var /\
       (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
          local_region cenv ee.scopes t n b sz) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       MAP FDOM es0.scopes = MAP FDOM ee.scopes /\
       return_buf_frame d cenv sf t /\ ~t.vs_halted /\
       t.vs_current_bb = sf.cs_current_bb /\
       t.vs_inst_idx = LENGTH sf.cs_current_insts /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
       gas_admissible (f xs) P ee ==>
       gas_outcome_full
         (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 (f xs) (ee,t,G1,tn1) Q R) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (vyperState$bind (eval_exprs cx es) f) (esi,s,G,tn) Q R
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `vyperState$bind (eval_exprs cx []) f = f []` by
        (simp[FUN_EQ_THM, Once evaluate_def, bind_def, return_def]) >>
      gvs[compile_stage_intcall_args_def, comp_return_def] >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
      simp[] >> strip_tac >>
      qpat_x_assum `!marks ee t G1 tn1. _`
        (qspecl_then [`[]`,`esi`,`s`,`G`,`tn`] mp_tac) >>
      simp[Once evaluate_def, return_def, gasSummaryTheory.gas_explicit_def] >>
      disch_then irule >> qexists_tac `ws` >> simp[])
  >> rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok cx (e::es)` >>
  `!res ee.
     vyperState$bind (eval_expr cx e) (\tv. read_result cx tv) esi = (res,ee) ==>
     expr_sim_inv cenv cx tenv ee /\
     EVERY (\arg. expr_body_pre cenv cx tenv arg ee) es` by
    (rpt gen_tac >> disch_tac >>
     `expr_body_pre cenv cx tenv e esi` by fs[] >>
     drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
     conj_tac >- simp[] >>
     fs[EVERY_MEM, expr_body_pre_def] >>
     qx_gen_tac `arg` >> strip_tac >>
     qpat_x_assum `!e'. MEM e' es ==> _`
       (qspec_then `arg` mp_tac) >> simp[]) >>
  namedCases_on `flags` ["", "flag flags1"] >- fs[] >>
  namedCases_on `dtys` ["", "dty dtys1"] >- fs[] >>
  Cases_on `flag`
  >- (Cases_on `compile_expr cenv (expr_type e) e si` >>
      rename1 `compile_expr cenv (expr_type e) e si = (vv,ci)` >>
      Cases_on `unwrap_value cenv vv ci` >>
      rename1 `unwrap_value cenv vv ci = (op,cu)` >>
      qpat_x_assum `compile_stage_intcall_args _ _ (e::es) _ _ si = _` mp_tac >>
      simp[Once compile_stage_intcall_args_def, comp_bind_def,
           comp_return_def] >>
      Cases_on `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cu` >>
      rename1 `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cu =
        (rest,cf)` >>
      simp[] >> strip_tac >>
      Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_si` >>
      rename1 `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_si =
        (shadow_vv,shadow_ci)` >>
      `vv = shadow_vv /\ gas_shadow_state ci shadow_ci` by
        (mp_tac (Q.INST [`ty` |-> `expr_type e`]
           gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr) >>
         simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[]) >>
      Cases_on `unwrap_value cenv vv shadow_ci` >>
      rename1 `unwrap_value cenv vv shadow_ci = (shadow_op,shadow_cu)` >>
      `op = shadow_op /\ gas_shadow_state cu shadow_cu` by
        (qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
         mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
         simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`ci`,`shadow_ci`] mp_tac) >> simp[]) >>
      qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `compile_stage_intcall_args _ _ _ _ _ shadow_si = _` mp_tac >>
      simp[Once compile_stage_intcall_args_def, comp_bind_def,
           comp_return_def] >>
      Cases_on `compile_stage_intcall_args compile_expr cenv
        (MAP gas_shadow_expr es) flags1 dtys1 shadow_cu` >>
      simp[] >> strip_tac >>
      `lower_value compile_expr cenv (expr_type e) e si = (op,cu)` by
        simp[lower_value_def, comp_bind_def] >>
      `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
         shadow_si = (op,shadow_cu)` by
        simp[lower_value_def, comp_bind_def] >>
      `cs_extends si cu` by
        metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
      `cs_extends cu cf` by
        (`ci_mono cu (SND (compile_stage_intcall_args compile_expr cenv
            es flags1 dtys1 cu))` by
           (irule exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args >>
            simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
         gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      `cs_extends shadow_si shadow_cu` by
        metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
      `cs_extends shadow_cu shadow_sf` by
        (`ci_mono shadow_cu (SND (compile_stage_intcall_args compile_expr cenv
            (MAP gas_shadow_expr es) flags1 dtys1 shadow_cu))` by
           (irule exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args >>
            simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
         gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      `fn_has_code si cu func /\ fn_has_code shadow_si shadow_cu shadow_func` by
        (qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` kall_tac >>
         conj_tac
         >- (mp_tac (Q.SPECL [`si`,`cu`,`cf`,`func`] fn_has_code_split) >> simp[]) >>
         mp_tac (Q.SPECL [`shadow_si`,`shadow_cu`,`shadow_sf`,`shadow_func`]
           fn_has_code_split) >> simp[]) >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx))
         expr_res_ok esi` by
        (`bind (eval_exprs cx (e::es)) f =
            bind (bind (eval_expr cx e) (read_result cx))
              (\v. bind (eval_exprs cx es) (\xs. f (v::xs)))` by
           simp[vyperInterpreterTheory.evaluate_def,
                vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
         qpat_x_assum `gas_admissible _ P esi` mp_tac >>
         pop_assum SUBST1_TAC >> strip_tac >>
         irule gas_admissible_bind_head >>
         conj_tac >- simp[exprSimDefsTheory.expr_res_ok_def] >>
         qexistsl_tac [`P`, `\v. bind (eval_exprs cx es) (\xs. f (v::xs))`] >>
         simp[] >>
         qpat_x_assum `!err. P (INR err) ==> expr_vv_res_ok (INR err)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprSimDefsTheory.expr_res_ok_def,
              exprSimDefsTheory.expr_vv_res_ok_def]) >>
      `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e esi` by
        (`body_expr_full_ok cx e` by fs[Once body_exprs_full_ok_def] >>
         `expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_x_assum `body_expr_full_ok cx e`
           (mp_tac o CONJUNCT1 o
             ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
         disch_then drule >> disch_then drule >> simp[]) >>
      qpat_x_assum `expr_sim_full _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (qspec_then `st0` mp_tac) >>
      disch_then drule >> disch_then drule >>
      simp[] >>
      disch_then (qspecl_then [`s`,`G`,`tn`] mp_tac) >>
      simp[] >> disch_then assume_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
      `bind (eval_exprs cx (e::es)) f =
         bind (bind (eval_expr cx e) (read_result cx))
           (\v. bind (eval_exprs cx es) (\xs. f (v::xs)))` by
        simp[vyperInterpreterTheory.evaluate_def,
             vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
      pop_assum SUBST1_TAC >>
      match_mp_tac (GEN_ALL
        gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path) >>
      qexists_tac `childQ` >> BETA_TAC >>
      conj_tac
      >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR`
            (irule_at Any) >> simp[Abbr `childR`] >>
          rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_def] >>
          qpat_x_assum `!H res ee gt r. expr_exit res r ==> R H res ee gt r`
            irule >>
          qpat_x_assum `expr_exit (INR y) r'` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          Cases_on `y` >> Cases_on `r'` >>
          simp[exprSimDefsTheory.expr_exit_def] >>
          rename1 `Error ex` >> Cases_on `ex` >>
          simp[exprSimDefsTheory.expr_exit_def]) >>
      reverse (rpt conj_tac)
      >- (rpt strip_tac >>
          irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
          goal_assum (drule_at Any) >> simp[])
      >- (rpt strip_tac >>
          irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
      >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame])
      >- (irule vyperStorageTraceTheory.storage_trace_frame_bind >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H _ _ _ _ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp[Abbr `childQ`, NoAsms] >> strip_tac >>
      disj1_tac >> qexists_tac `v` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      `wb_frame cenv esi mid si s t` by
        (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, wb_frame_def] >> metis_tac[]) >>
      `MAP FDOM esi.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
         imp_res_tac vyperStateTheory.read_result_state >> gvs[] >>
         drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
         simp[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         esi.storage_trace` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `valid_horizon cx st0 _ mid.storage_trace` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         drule_at Any vyperStorageFootprintTheory.valid_horizon_frame >>
         simp[vyperStorageTraceTheory.storage_trace_frame_bind,
              vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      `local_ptrs_rel func cenv esi.scopes s` by
        (qpat_x_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _`
           drule >>
         simp[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              stateRelProjTheory.state_rel_local_ptrs_rel]) >>
      `!n b sz. local_region cenv esi.scopes s n b sz <=>
                  local_region cenv mid.scopes t n b sz` by
        (qpat_assum `local_ptrs_rel func cenv esi.scopes s` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s t` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[wb_frame_def] >> rpt strip_tac >> eq_tac
         >- (rw[loweringStateRelDefsTheory.local_region_def] >>
             `lookup_scopes n mid.scopes <> NONE` by
               metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                         optionTheory.NOT_SOME_NONE] >>
             `not_fresh_at si p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
         rw[loweringStateRelDefsTheory.local_region_def] >>
         `lookup_scopes n esi.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         Cases_on `lookup_scopes n esi.scopes` >> fs[] >>
         rename1 `lookup_scopes n esi.scopes = SOME entry0` >>
         `?w0. lookup_var p s = SOME w0` by
           (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
            qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         `lookup_var p t = SOME w0` by metis_tac[] >> gvs[]) >>
      `t.vs_labels = s.vs_labels` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_labels]) >>
      `ci_mono si cu` by
        (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`si`]
           exprLoweringPropsTheory.ci_mono_lower_value_compile_expr) >> simp[]) >>
      mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cu`]
        intcall_args_prefix_frame) >>
      (impl_tac >- fs[exprLoweringPropsTheory.ci_mono_def]) >>
      strip_tac >>
      `is_word_type dty /\ expr_type e = dty` by
        (`is_word_type dty` by
           (qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
              (qspec_then `0` mp_tac) >> simp[]) >>
         fs[] >> metis_tac[compileEnvTheory.type_widens_to_word]) >>
      `post_value_type cenv e = dty` by metis_tac[post_value_type_word] >>
      `?w. eval_operand op t = SOME w /\
           (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
              w = typed_val_to_w256 rt v)` by
        (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         qpat_assum `post_value_type cenv e = dty` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tn1 op = {}` by fs[ptr_val_ok_def] >>
      `!x. op = Var x ==> not_fresh_at cu x` by
        (`expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_assum `lower_value compile_expr cenv (expr_type e) e si = (op,cu)`
           (mp_then Any mp_tac
             exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
         disch_then (qspecl_then [`cx`,`tenv`,`esi`] mp_tac) >> simp[]) >>
      `expr_result_typed tenv e (Value v)` by
        (`expr_body_pre cenv cx tenv e esi` by fs[] >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         `expr_body_pre cenv cx tenv e
            (esi with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
         drule_at (Pos hd) exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
         simp[] >> metis_tac[]) >>
      `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
             value_has_type rt v` by
        (qpat_assum `expr_result_typed tenv e (Value v)` mp_tac >>
         qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
         qpat_assum `expr_type e = dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[vyperTypeExprResultTheory.expr_result_typed_def,
              vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
              vyperTypeInvariantsTheory.value_result_typed_def,
              exprSimHypsDefsTheory.expr_sim_inv_def,
              vyperTypeInvariantsTheory.env_consistent_def,
              vyperTypeInvariantsTheory.env_context_consistent_def] >>
         rpt strip_tac >> gvs[]) >>
      `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
             value_has_type rt v /\ val_wf rt v /\
             val_footprint rt v <= type_memory_size rt` by
        (qpat_assum `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
                        value_has_type rt v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
                   exprSimPropsTheory.val_footprint_le]) >>
      qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` irule >>
      BETA_TAC >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_normal]) >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `body_exprs_full_ok cx (e::es)` mp_tac >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[Once body_exprs_full_ok_def, bind_def, AllCaseEqs()] >>
         metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G0`,`P`,`cenv`,`d`,`dtys1`,`es0`,`flags1`,`rest`,
        `ops ++ [op]`,`pflags ++ [T]`,`pin`,`ptys ++ [dty]`,`s0`,`sa`,`cf`,
        `shadow_func`,`shadow_sf`,`shadow_cu`,`cu`,`tenv`,`tn0`,`tops`,
        `vals ++ [v]`,`ws ++ [w]`] >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!marks xs ee t G1 tn1. _`
           (qspecl_then [`marks ++ marks'`,`v::xs`,`ee`,`t'`,`G1'`,`tn1'`] mp_tac) >>
         (impl_tac >- (
           conj_tac >-
             (`gas_path ctx func s (LENGTH marks) (OK t)` by
                (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
                   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                 (impl_tac >- first_assum ACCEPT_TAC) >>
                 POP_ASSUM_LIST (K all_tac) >> strip_tac >>
                 metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec]) >>
              drule gasSummaryComposeTheory.gas_explicit_append_path >>
              disch_then (qspec_then `marks'` assume_tac) >>
              qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` mp_tac >>
              qpat_assum `!tail. eval_exprs cx es _ = _` mp_tac >>
              qpat_assum `res = INL v` mp_tac >>
              pop_assum mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
              simp[Once evaluate_def, GSYM bind_assoc, APPEND_ASSOC] >>
              qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
                (qspec_then `gas_explicit marks' t.vs_gas_readings ++ tail` assume_tac) >>
              gvs[bind_def, AllCaseEqs(), return_def, APPEND_ASSOC] >>
              metis_tac[]) >>
           qpat_x_assum `op::rest = newops` (SUBST_ALL_TAC o SYM) >>
           qpat_x_assum `cf = sf` (SUBST_ALL_TAC o SYM) >>
           rule_assum_tac (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
           simp[GSYM APPEND_ASSOC] >>
           rpt strip_tac >>
           qpat_x_assum `!j rt. j < LENGTH (ops ++ op::rest) /\ _ ==> _`
             (qspecl_then [`j`,`rt`] mp_tac) >>
           simp[arithmeticTheory.ADD_SYM])) >>
         simp[]) >>
      conj_tac >-
        (qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz <=> _` mp_tac >>
         qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      ntac 2 (conj_tac >-
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[] >>
         gvs[exprLoweringPropsTheory.ci_mono_def])) >>
      conj_tac >- (simp[] >> metis_tac[]) >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >> Cases_on `j < LENGTH ops`
         >- (`j < LENGTH ptys /\ j < LENGTH vals /\
              j < LENGTH pflags /\ j < LENGTH ws` by metis_tac[] >>
             simp[EL_APPEND_EQN] >>
             qpat_x_assum `!j rt. j < LENGTH ops /\ _ ==> _`
               (qspecl_then [`j`,`rt`] mp_tac) >>
             fs[EL_APPEND_EQN, arithmeticTheory.ADD_SYM]) >>
         `j = LENGTH ops` by gvs[] >>
         gvs[EL_APPEND_EQN]) >>
      conj_tac >-
        (rpt strip_tac >>
         qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
           (qspec_then `SUC j` mp_tac) >> simp[]) >>
      conj_tac >-
        (gen_tac >> strip_tac >>
         qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> (\H res ee G' tn' t. _) H res mid G1 tn1 t`
           drule >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def] >> metis_tac[]) >>
      simp[] >>
      ntac 2 (conj_tac >-
        (qpat_assum `ci_mono si cu` mp_tac >>
         qpat_assum `sa.cs_next_id <= si.cs_next_id` mp_tac >>
         qpat_assum `sa.cs_next_var <= si.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def])) >>
      ntac 2 (conj_tac >- gvs[]) >>
      conj_tac >-
        (qpat_assum `eval_operands ops t = SOME ws` mp_tac >>
         qpat_assum `eval_operand op t = SOME w` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         qid_spec_tac `ws` >> Induct_on `ops` >>
         simp[venomStateTheory.eval_operands_def, AllCaseEqs()] >>
         rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[] >>
      conj_tac >- metis_tac[listTheory.CONS_11] >>
      `expr_sim_inv cenv cx tenv mid` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         `expr_body_pre cenv cx tenv e esi` by fs[] >>
         pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         `expr_body_pre cenv cx tenv e
           (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
         dxrule exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`res`,`mid with gas_obs := []`] mp_tac) >>
         gvs[bind_def]) >>
      conj_tac >-
        (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
         qpat_assum `expr_sim_inv cenv cx tenv mid` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[EVERY_MEM, exprSimHypsDefsTheory.expr_body_pre_def] >>
         metis_tac[]) >>
      ntac 2 (conj_tac >- fs[]) >>
      conj_tac >-
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `si` >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      conj_tac >- fs[] >>
      ntac 2 (conj_tac >- metis_tac[fragExecTheory.fn_has_code_split]) >>
      conj_tac >-
        (qpat_assum `gas_admissible _ P esi` mp_tac >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` mp_tac >>
         qpat_assum `res = INL v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[gas_admissible_def, vyperInterpreterTheory.evaluate_def,
              vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
         rpt strip_tac >>
         first_x_assum (qspec_then
           `gas_explicit marks s.vs_gas_readings ++ gs` mp_tac) >>
         qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >>
         Cases_on `eval_expr cx e (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ gs)` >>
         Cases_on `q` >> gvs[bind_def] >>
         Cases_on `read_result cx x r` >> Cases_on `q` >> gvs[bind_def] >>
         metis_tac[]) >>
      simp[] >>
      conj_tac >-
        (qpat_assum `return_buf_frame d cenv si s` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s t` mp_tac >>
         qpat_assum `ci_mono si cu` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def,
              loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >>
         simp[]) >>
      irule intcall_args_frame_compose >>
      qexistsl [`G`, `esi`, `s`, `si`, `tn`] >> simp[]) >>
  Cases_on `compile_expr cenv (expr_type e) e si` >>
  rename1 `compile_expr cenv (expr_type e) e si = (vv,ci)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci` >>
  rename1 `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci = (buf,ca)` >>
  Cases_on `unwrap_value cenv vv ca` >>
  rename1 `unwrap_value cenv vv ca = (op,cu)` >>
  qpat_x_assum `compile_stage_intcall_args _ _ (e::es) _ _ si = _` mp_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  qpat_abbrev_tac `store_step = if is_word_type dty then _ else _` >>
  Cases_on `store_step cu` >> rename1 `store_step cu = (u,cs)` >>
  Cases_on `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cs` >>
  rename1 `compile_stage_intcall_args compile_expr cenv es flags1 dtys1 cs = (rest,cf)` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >> strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_si` >>
  rename1 `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_si =
    (shadow_vv,shadow_ci)` >>
  `vv = shadow_vv /\ gas_shadow_state ci shadow_ci` by
    (mp_tac (Q.INST [`ty` |-> `expr_type e`]
       gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[]) >>
  qpat_x_assum `vv = shadow_vv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) shadow_ci` >>
  rename1 `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) shadow_ci =
    (shadow_buf,shadow_ca)` >>
  `buf = shadow_buf /\ gas_shadow_state ca shadow_ca` by
    (mp_tac (Q.INST [`nbytes` |-> `MAX 32 (type_memory_bytes cenv dty)`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`ci`,`shadow_ci`] mp_tac) >> simp[]) >>
  qpat_x_assum `buf = shadow_buf` (SUBST_ALL_TAC o SYM) >>
  Cases_on `unwrap_value cenv vv shadow_ca` >>
  rename1 `unwrap_value cenv vv shadow_ca = (shadow_op,shadow_cu)` >>
  `op = shadow_op /\ gas_shadow_state cu shadow_cu` by
    (mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`ca`,`shadow_ca`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  `gas_shadow_compiles store_step store_step` by
    (simp[Abbr `store_step`] >>
     rpt IF_CASES_TAC >>
     simp[gasShadowCompileBaseTheory.gas_shadow_compiles_ignore_bind,
          gasShadowCompileContextTheory.gas_shadow_compiles_ptr_store,
          gasShadowCompileContextTheory.gas_shadow_compiles_store_bytestring,
          gasShadowCompileContextTheory.gas_shadow_compiles_store_memory,
          gasShadowStateTheory.gas_shadow_compiles_return,
          gasShadowStateTheory.gas_shadow_compiles_emit_void]) >>
  Cases_on `store_step shadow_cu` >>
  rename1 `store_step shadow_cu = (shadow_u,shadow_cs)` >>
  `u = shadow_u /\ gas_shadow_state cs shadow_cs` by
    (qpat_assum `gas_shadow_compiles store_step store_step` mp_tac >>
     pure_rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`cu`,`shadow_cu`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_stage_intcall_args _ _ _ _ _ shadow_si = _` mp_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  qpat_assum `Abbrev (store_step = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_stage_intcall_args compile_expr cenv
    (MAP gas_shadow_expr es) flags1 dtys1 shadow_cs` >>
  rename1 `compile_stage_intcall_args compile_expr cenv
    (MAP gas_shadow_expr es) flags1 dtys1 shadow_cs = (shadow_rest,shadow_cf)` >>
  simp[] >> strip_tac >>
  `!a. ci_mono a (SND (store_step a))` by
    (gen_tac >> simp[Abbr `store_step`] >> rpt IF_CASES_TAC >>
     simp[contextTheory.compile_ptr_store_def, comp_ignore_bind_def,
          comp_bind_def, comp_return_def,
          exprLoweringPropsTheory.ci_mono_compile_store_bytestring,
          exprLoweringPropsTheory.ci_mono_compile_store_memory,
          exprLoweringPropsTheory.ci_mono_emit_void] >>
     pairarg_tac >> simp[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_bytestring,
               pairTheory.SND]) >>
  `ci_mono ci ca /\ ci_mono ca cu /\ ci_mono cu cs /\ ci_mono cs cf /\
   ci_mono shadow_ci shadow_ca /\ ci_mono shadow_ca shadow_cu /\
   ci_mono shadow_cu shadow_cs /\ ci_mono shadow_cs shadow_cf` by
    (conj_tac >-
       (qspecl_then [`MAX 32 (type_memory_bytes cenv dty)`,`ci`] mp_tac
          exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
     conj_tac >-
       (qspecl_then [`cenv`,`vv`,`ca`] mp_tac
          exprLoweringPropsTheory.ci_mono_unwrap_value >> simp[]) >>
     conj_tac >-
       (qpat_assum `!a. ci_mono a (SND (store_step a))`
          (qspec_then `cu` mp_tac) >>
        qpat_assum `store_step cu = _`
          (fn th => pure_rewrite_tac[th, pairTheory.SND]) >>
        simp[NoAsms]) >>
     conj_tac >-
       (mp_tac (Q.SPECL [`compile_expr`,`cenv`,`es`,`flags1`,`dtys1`,`cs`]
          exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args) >>
        simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
     conj_tac >-
       (qspecl_then [`MAX 32 (type_memory_bytes cenv dty)`,`shadow_ci`] mp_tac
          exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
     conj_tac >-
       (qspecl_then [`cenv`,`vv`,`shadow_ca`] mp_tac
          exprLoweringPropsTheory.ci_mono_unwrap_value >> simp[]) >>
     conj_tac >-
       (qpat_assum `!a. ci_mono a (SND (store_step a))`
          (qspec_then `shadow_cu` mp_tac) >>
        qpat_assum `store_step shadow_cu = _`
          (fn th => pure_rewrite_tac[th, pairTheory.SND]) >>
        simp[NoAsms]) >>
     mp_tac (Q.SPECL [`compile_expr`,`cenv`,`MAP gas_shadow_expr es`,`flags1`,`dtys1`,`shadow_cs`]
          exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args) >>
     simp[exprLoweringPropsTheory.compile_expr_ci_mono]) >>
  `ci_mono si ci /\ ci_mono shadow_si shadow_ci` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`si`] mp_tac
           (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono) >> simp[]) >>
     qspecl_then [`cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_si`] mp_tac
       (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono) >> simp[]) >>
  qpat_x_assum `cf = sf` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `shadow_cf = shadow_sf` (SUBST_ALL_TAC o SYM) >>
  `ci_mono ci cf /\ ci_mono shadow_ci shadow_cf` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `ca` >>
         simp[] >> irule exprLoweringPropsTheory.ci_mono_trans >>
         qexists_tac `cu` >> simp[] >>
         irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `cs` >> simp[]) >>
     irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `shadow_ca` >>
     simp[] >> irule exprLoweringPropsTheory.ci_mono_trans >>
     qexists_tac `shadow_cu` >> simp[] >>
     irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `shadow_cs` >> simp[]) >>
  `cs_extends si ci /\ cs_extends ci cf /\
   cs_extends shadow_si shadow_ci /\ cs_extends shadow_ci shadow_cf` by
    (fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code si ci func /\ fn_has_code shadow_si shadow_ci shadow_func` by
    (qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` kall_tac >>
     conj_tac
     >- (mp_tac (Q.SPECL [`si`,`ci`,`cf`,`func`] fn_has_code_split) >> simp[]) >>
     mp_tac (Q.SPECL [`shadow_si`,`shadow_ci`,`shadow_cf`,`shadow_func`]
       fn_has_code_split) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok esi` by
    (`bind (eval_exprs cx (e::es)) f =
        bind (eval_expr cx e)
          (\tv. bind (read_result cx tv)
            (\v. bind (eval_exprs cx es) (\xs. f (v::xs))))` by
       simp[vyperInterpreterTheory.evaluate_def,
            vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
     qpat_x_assum `gas_admissible _ P esi` mp_tac >>
     pop_assum SUBST1_TAC >> strip_tac >>
     rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
     qpat_x_assum `gas_admissible _ P esi`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[bind_def] >> Cases_on `res`
     >- (rename1 `eval_expr _ _ _ = (INL tv,ee)` >>
         Cases_on `tv` >> simp[exprSimDefsTheory.expr_vv_res_ok_def] >>
         simp[read_result_def, raise_def, bind_def] >>
         qpat_x_assum `!err. P (INR err) ==> _`
           (qspec_then `Error (TypeError "read_result mapping")` mp_tac) >>
         simp[exprSimDefsTheory.expr_vv_res_ok_def]) >>
     rename1 `INR exc` >>
     disch_then (qspecl_then [`INR exc`, `ee`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!err. P (INR err) ==> _` irule >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e esi` by
    (`body_expr_full_ok cx e` by fs[Once body_exprs_full_ok_def] >>
     `expr_body_pre cenv cx tenv e esi` by fs[] >>
     qpat_x_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o
         ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule >> disch_then drule >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspec_then `st0` mp_tac) >>
  disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s`,`G`,`tn`] mp_tac) >>
  simp[] >> disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `bind (eval_exprs cx (e::es)) f =
     bind (eval_expr cx e) (\tv. bind (read_result cx tv)
       (\v. bind (eval_exprs cx es) (\xs. f (v::xs))))` by
    simp[vyperInterpreterTheory.evaluate_def,
         vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac (GEN_ALL
    gasOutcomeFullComposeTheory.gas_outcome_full_bind_all_path) >>
  qexists_tac `childQ` >> BETA_TAC >>
  conj_tac
  >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR`
        (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_def] >>
      qpat_x_assum `!H res ee gt r. expr_exit res r ==> R H res ee gt r`
        irule >>
      qpat_x_assum `expr_exit (INR y) r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `y` >> Cases_on `r` >>
      simp[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error ex` >> Cases_on `ex` >>
      simp[exprSimDefsTheory.expr_exit_def]) >>
  reverse (rpt conj_tac)
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[])
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_bind]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >>
  disj1_tac >> qexists_tac `tv` >> conj_tac
  >- first_assum ACCEPT_TAC >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
      ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST (storage_trace_horizon mid.storage_trace))` by
    fs[loweringPostsTheory.vv_post_def] >>
  `MAX 32 (type_memory_bytes cenv dty) < dimword (:256)` by
    (qpat_assum `EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.dimword_def, arithmeticTheory.MAX_DEF] >>
     rpt strip_tac >> decide_tac) >>
  `fn_has_code ci ca func` by
    (qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends ci cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `local_ptrs_reserved cenv ci` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `si` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `~t.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn1`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`]
    (qx_choose_then `aq` (qx_choose_then `aw` (qx_choose_then `at`
      (qx_choose_then `aG` (qx_choose_then `atn` strip_assume_tac)))))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid aG atn at` by
    (rpt strip_tac >>
     irule (INST_TYPE [``:'a`` |-> ``:256``]
       bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G1`,`H`,`ctx`,
       `w2n aw + MAX 32 (type_memory_bytes cenv dty)`,
       `func`,`t`,`ci`,`tn1`] >>
     simp[] >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ H res mid G1 tn1 t`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[loweringPostsTheory.vv_post_def, NoAsms] >>
     rpt strip_tac >>
     `si.cs_next_var <= ci.cs_next_var` by
       (qpat_assum `ci_mono si ci` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[exprLoweringPropsTheory.ci_mono_def]) >>
     (first_assum ACCEPT_TAC ORELSE
      (irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `si` >> conj_tac >- first_assum ACCEPT_TAC >>
       (qpat_assum `cenv.ce_return_buf = SOME _` mp_tac ORELSE
        qpat_assum `cenv.ce_return_pc = SOME _` mp_tac) >>
       qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` mp_tac >>
       qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> metis_tac[]))) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at ci x` by
    (metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var]) >>
  `at.vs_labels = t.vs_labels` by
    (qpat_assum `at with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t`
       (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >> simp[]) >>
  `eval_operand (vv_operand vv) at = eval_operand (vv_operand vv) t /\
   op_prov aG (vv_operand vv) = op_prov G1 (vv_operand vv) /\
   op_taint atn (vv_operand vv) = op_taint tn1 (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) mid tv vv at` by
    (irule exprSimMemDefsTheory.vv_store_bound_frame_mem_src >>
     qexists_tac `t` >> simp[]) >>
  `ptr_buf_ok cenv e (vv_operand vv) G1 t ==>
   ptr_buf_ok cenv e (vv_operand vv) aG at` by
    (qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >>
     qexistsl_tac [`x`,`b`,`sz`] >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `(!t' op. vv = StackValue t' op /\
       ~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op aG at) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand aG at)` by
    (Cases_on `vv` >> fs[contextTheory.vv_operand_def] >> metis_tac[]) >>
  `at.vs_memory = t.vs_memory /\ at.vs_accounts = t.vs_accounts /\
   at.vs_transient = t.vs_transient /\ at.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `at with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!rt v b len.
     val_wf rt v /\ val_footprint rt v <= len /\
     b + len <= t.vs_alloca_next /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory rt v b mem) ==>
     !mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
        val_in_memory rt v b mem` by
    (rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
     irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tn1.t_mem`,`atn.t_mem`,`len`,`t.vs_memory`,`at.vs_memory`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `b + len <= t.vs_alloca_next` mp_tac >>
     qpat_assum `i < b + len` mp_tac >>
     qpat_assum `t.vs_alloca_next <= i` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     esi.storage_trace` by
    (qpat_assum `!tail. eval_expr cx e _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `valid_horizon cx st0 _ mid.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at Any vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx esi s` by
    (qpat_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _` drule >>
     simp[]) >>
  `ghost_kept_at lo cenv esi si G tn s aG atn` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G1`,`w2n aw + MAX 32 (type_memory_bytes cenv dty)`,`t`,`tn1`] >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at ci x` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >>
            fs[exprLoweringPropsTheory.ci_mono_def]) >>
         qpat_assum `!x. not_fresh_at ci x ==> _` drule >> simp[])
     >- (rpt strip_tac >>
         `b + sz <= s.vs_alloca_next` by
           (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
         qpat_assum `b + sz <= s.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     (rpt strip_tac >>
      `off + sz <= s.vs_alloca_next` by
        (qpat_assum `stmt_state_rel _ ctx func cenv cx esi s` mp_tac >>
         qpat_assum `FLOOKUP s.vs_allocas aid = SOME (off,sz)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      qpat_assum `off + sz <= s.vs_alloca_next` mp_tac >>
      qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
  `!v rt w.
     read_result cx tv mid = (INL v,mid) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) t = SOME w /\
     ((?ty op. vv = StackValue ty op /\
         ~is_word_type (post_value_type cenv e)) \/
      (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory)) ==>
     val_wf rt v /\
     (val_footprint rt v = 0 \/
      w2n w + val_footprint rt v <= t.vs_alloca_next)` by
    (rpt gen_tac >> disch_tac >>
     `vv_at cenv cx (post_value_type cenv e) si ci mid tv vv t` by
       fs[loweringPostsTheory.vv_post_def] >>
     qpat_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx mid t` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL v,mid) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     gvs[loweringPostsTheory.vv_at_def, contextTheory.vv_operand_def,
         loweringPostsTheory.expr_val_at_def] >>
     `b + sz <= t.vs_alloca_next` by
       ((drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) ORELSE
        (fs[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
            venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[])) >>
     decide_tac) >>
  `!rt v b.
     val_wf rt v /\
     (val_footprint rt v = 0 \/ b + val_footprint rt v <= t.vs_alloca_next) /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory rt v b mem) ==>
     !mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
        val_in_memory rt v b mem` by
    (rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >>
     irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
     conj_tac >- fs[] >>
     qexistsl_tac [`tn1.t_mem`,`atn.t_mem`,`val_footprint rt v`,
                    `t.vs_memory`,`at.vs_memory`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `val_wf rt v /\ _` mp_tac >>
     qpat_assum `b <= i` mp_tac >>
     qpat_assum `i < b + val_footprint rt v` mp_tac >>
     qpat_assum `t.vs_alloca_next <= i` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> decide_tac) >>
  `!v. read_result cx tv mid = (INL v,mid) /\
     ((?ty op. vv = StackValue ty op /\
         ~is_word_type (post_value_type cenv e)) \/
      (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory)) /\
     ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) G1 tn1 t ==>
     ptr_mem_ok cx (post_value_type cenv e) v (vv_operand vv) aG atn at` by
    (gen_tac >> disch_tac >>
     qpat_assum `!rt v b. val_wf rt v /\ _ ==> _` mp_tac >>
     qpat_assum `!v rt w. read_result cx tv mid = _ /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL v,mid) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> rpt strip_tac
     >- metis_tac[] >>
     Cases_on `vv_operand vv` >>> NTH_GOAL (gvs[ptrDisciplineTheory.op_prov_def]) 1 >>
     qpat_x_assum `op_prov aG _ = _` mp_tac >>
     simp[ptrDisciplineTheory.op_prov_def] >>
     qpat_x_assum `!tv w. _ ==> (!mem. _ ==> _) /\ _`
       (qspecl_then [`tv'`,`w`] mp_tac) >> simp[] >> metis_tac[]) >>
  `ptr_vv_ok cx (post_value_type cenv e) tv vv mid aG atn at` by
    (qpat_assum `ptr_vv_ok cx _ tv vv mid G1 tn1 t` mp_tac >>
     qpat_assum `!v. read_result cx tv mid = _ /\ _ ==> ptr_mem_ok _ _ _ _ aG atn at` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `op_prov aG (vv_operand vv) = _` mp_tac >>
     qpat_assum `op_taint atn (vv_operand vv) = _` mp_tac >>
     qpat_assum `at.vs_accounts = t.vs_accounts` mp_tac >>
     qpat_assum `at.vs_transient = t.vs_transient` mp_tac >>
     qpat_assum `at.vs_call_ctx = t.vs_call_ctx` mp_tac >>
     qpat_assum `atn.t_stor = tn1.t_stor` mp_tac >>
     qpat_assum `atn.t_trans = tn1.t_trans` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     gvs[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
         contextTheory.vv_operand_def] >> metis_tac[]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     !v rt. read_result cx tv mid = (INL v,mid) /\
       evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt ==>
       val_wf rt v /\ val_footprint rt v <= type_memory_size rt` by
    (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `vv` >>
     simp[contextTheory.vv_location_def, loweringPostsTheory.vv_post_def] >>
     rpt strip_tac >>
     fs[loweringPostsTheory.vv_holds_def, loweringPostsTheory.immutable_holds_def] >>
     metis_tac[valueEncodingTypingTheory.value_has_type_val_wf,
               exprSimPropsTheory.val_footprint_le]) >>
  `(cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx tv mid = (INL v,mid) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
         eval_operand (vv_operand vv) at = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside atn.t_mem at.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))` by
    (qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?v. _` mp_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> !v rt. _` mp_tac >>
     qpat_assum `!rt v b len. val_wf rt v /\ _ ==> _` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) at = _` mp_tac >>
     qpat_assum `lo <= t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> fs[] >>
     rpt strip_tac >>
     `w2n w + type_memory_size rt <= lo` by metis_tac[arithmeticTheory.ADD_COMM] >>
     simp[] >>
     `w2n w + type_memory_size rt <= t.vs_alloca_next` by decide_tac >>
     metis_tac[]) >>
  `!n b sz. local_region cenv mid.scopes at n b sz <=>
             local_region cenv mid.scopes t n b sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >>
     rpt gen_tac >> eq_tac >> strip_tac >>
     qexistsl_tac [`entry`,`p`,`w`] >> simp[] >>
     `not_fresh_at ci p` by
       (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at ci x ==> lookup_var x at = lookup_var x t /\ _`
       drule >> simp[]) >>
  `!sn H. ci.cs_next_id <= sn.cs_next_id /\
     valid_horizon cx st0 H mid.storage_trace ==>
     vv_post H ctx func cenv cx e esi si sn s mid tv vv at` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx e esi si ci s mid tv vv t` by
       (qpat_assum `!h. valid_horizon cx st0 h mid.storage_trace ==>
           (\h r ee g tn tt. ?v. r = INL v /\
             vv_post h ctx func cenv cx e esi si ci s ee v vv tt /\ _) h res mid G1 tn1 t`
          (qspec_then `H` mp_tac) >>
         (impl_tac >- simp[]) >> BETA_TAC >>
         disch_then (qx_choose_then `tv1` strip_assume_tac) >>
         `tv1 = tv` by
           (qpat_x_assum `res = INL tv1` mp_tac >> simp[]) >>
         qpat_x_assum `vv_post H ctx func cenv cx e esi si ci s mid tv1 vv t` mp_tac >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx mid at` by
       (qpat_assum `!h. stmt_state_rel h ctx func cenv cx mid t ==> stmt_state_rel h ctx func cenv cx mid at` irule >>
        qpat_assum `vv_post H ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
        simp[loweringPostsTheory.vv_post_def, NoAsms]) >>
     irule exprSimVVFrameTheory.vv_post_alloc_mono_frame >>
     simp[] >> qexistsl_tac [`t`,`ci`] >>
     simp[venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def,
          exprLoweringPropsTheory.ci_mono_def] >>
     rpt strip_tac >>
     `not_fresh_at ci x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >>
        conj_tac >-
          (qpat_assum `ci_mono si ci` mp_tac >>
           simp[exprLoweringPropsTheory.ci_mono_def, NoAsms]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at ci x ==> lookup_var x at = lookup_var x t /\ _`
       drule >> simp[]) >>
  `expr_body_pre cenv cx tenv e esi` by fs[] >>
  drule exprSimHypsTheory.post_type_evaluates >>
  disch_then (qx_choose_then `rty` assume_tac) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64` by
    (drule aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound >> simp[]) >>
  `is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)` by
    (`expr_sim_inv cenv cx tenv esi /\ well_typed_expr tenv e` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule_all exprSimHypsTheory.post_value_type_widens >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type rty v` by
    (gen_tac >> disch_tac >>
     `expr_body_pre cenv cx tenv e
        (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     `bind (eval_expr cx e) (read_result cx)
        (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ []) =
        (INL v,mid with gas_obs := [])` by
       (qpat_assum `!tail. eval_expr cx e _ = _`
          (qspec_then `[]` mp_tac) >>
        simp[bind_def, exprSimMemorySourceTheory.read_result_gas_obs]) >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
       (mp_then (Pat `bind _ _ _ = _`) mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimHypsTheory.memory_rhs_read_post_typed)) >>
     disch_then (qspecl_then [`cenv`,`tenv`] mp_tac) >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     `tenv.type_defs = get_tenv cx` by
       (qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[exprSimHypsDefsTheory.expr_sim_inv_def,
             vyperTypeInvariantsTheory.env_consistent_def,
             vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     simp[]) >>
  `ci.cs_next_var <= ca.cs_next_var /\ ci.cs_next_id <= ca.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ ci = (_,ca)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     mp_tac (Q.SPECL [`MAX 32 (type_memory_bytes cenv dty)`,`ci`]
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `si.cs_next_var <= ci.cs_next_var /\ si.cs_next_id <= ci.cs_next_id` by
    (qpat_assum `ci_mono si ci` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `MAP FDOM esi.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def] >>
     metis_tac[]) >>
  `~at.vs_halted` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK at,aG,atn)`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  `fn_has_code ca cu func` by
    (qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  qpat_assum `compile_expr cenv (expr_type e) e si = (vv,ci)`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac
      bodyFullUnwrapTheory.unwrap_value_origin_ptr) >>
  disch_then (fn th =>
    qpat_assum `unwrap_value cenv vv ca = (op,cu)`
      (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_inst_ids_distinct _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (qspec_then `rty` mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]] >> NO_TAC)) >>
  strip_tac >>
  `lookup_var aq z = SOME aw /\
   ptr_covers G' tn' aq z (MAX 32 (type_memory_bytes cenv dty))` by
    (qpat_assum `!x. not_fresh_at ca x ==> _`
       (qspec_then `aq` mp_tac) >>
     qpat_assum `not_fresh_at ca aq` mp_tac >>
     qpat_assum `lookup_var aq at = SOME aw` mp_tac >>
     qpat_assum `ptr_covers aG atn aq at _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` by metis_tac[] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ghost_inv_at _ _ _ _ _ _ G' tn' z`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> rpt strip_tac >>
     fs[bodyPtrDefsTheory.ghost_inv_def]) >>
  `~z.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec o CONJUNCT1) >>
     simp[fragExecTheory.exit_result_def]) >>
  `fn_has_code cu cs func` by
    (qpat_assum `ci_mono ca cu` mp_tac >>
     qpat_assum `ci_mono cu cs` mp_tac >>
     qpat_assum `ci_mono cs cf` mp_tac >>
     qpat_assum `cs_extends si ci` mp_tac >>
     qpat_assum `ci_mono ci ca` mp_tac >>
     qpat_assum `fn_has_code si cf func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next` by
    (qpat_assum `w2n aw + MAX 32 _ <= at.vs_alloca_next` mp_tac >>
     qpat_assum `at.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  (* One store cut: branch-specific execution, shared frame and tail IH. *)
  qsuff_tac `?wt wG wtn nw.
    nw <= MAX 32 (type_memory_bytes cenv dty) /\
    typed_copy_state_frame cu (w2n aw) nw z wt /\
    ~wt.vs_halted /\ wt.vs_current_bb = cs.cs_current_bb /\
    wt.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func wt /\
    wtn.t_stor = tn'.t_stor /\ wtn.t_trans = tn'.t_trans /\ wtn.t_imm = tn'.t_imm /\
    (!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\
      op_taint wtn (Var p) = op_taint tn' (Var p)) /\
    (!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==>
      (i IN wtn.t_mem <=> i IN tn'.t_mem)) /\
    (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
      value_has_type rt v /\ val_wf rt v /\
      type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
      (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
        val_in_memory rt v (w2n aw) mem)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK wt,wG,wtn))`
  >- (disch_then (qx_choose_then `wt` (qx_choose_then `wG`
        (qx_choose_then `wtn` (qx_choose_then `nw` strip_assume_tac)))) >>
      `si.cs_next_var <= cu.cs_next_var /\ ca.cs_next_var <= cu.cs_next_var` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`ci_mono si ci`, `ci_mono ci ca`, `ci_mono ca cu`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `not_fresh_at cu aq` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >> simp[]) >>
      irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
      conj_tac >-
        (irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_result] >>
         gen_tac >> irule storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`wG`,`wt`,`wtn`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule intcall_args_read_result_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >>
      qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin f P Q R. _` irule >>
      BETA_TAC >>
      conj_tac >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >-
        (qpat_assum `body_exprs_full_ok cx (e::es)` mp_tac >>
         qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
         qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
         qpat_assum `res = INL tv` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[Once body_exprs_full_ok_def, bind_def, AllCaseEqs()] >>
         metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G0`,`P`,`cenv`,`d`,`dtys1`,`es0`,`flags1`,`rest`,
        `ops ++ [Var aq]`,`pflags ++ [F]`,`pin`,`ptys ++ [dty]`,`s0`,`sa`,`cf`,
        `shadow_func`,`shadow_cf`,`shadow_cs`,`cs`,`tenv`,`tn0`,`tops`,
        `vals ++ [v]`,`ws ++ [aw]`] >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
         qpat_x_assum `!marks xs ee t G1 tn1. _`
           (qspecl_then [`marks ++ marks'`,`v::xs`,`ee`,`t'`,`G1'`,`tn1'`] mp_tac) >>
         (impl_tac >- (
           conj_tac >-
             (`gas_path ctx func s (LENGTH marks) (OK wt)` by
                (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (s,G,tn) marks _`
                   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                 qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ [] _`
                   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                 qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` mp_tac >>
                 POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
                 imp_res_tac fragGasOriginPtrTheory.gas_origin_ptr_path_projections >>
                 imp_res_tac fragGasOriginTheory.gas_origin_path_erase >>
                 imp_res_tac fragGasModeTheory.gas_marked_path_exec >>
                 metis_tac[fragGasPathTheory.gas_path_then, LENGTH, APPEND_NIL, arithmeticTheory.ADD_0]) >>
              drule gasSummaryComposeTheory.gas_explicit_append_path >>
              disch_then (qspec_then `marks'` assume_tac) >>
              qpat_assum `!tail. eval_expr cx e _ = _` mp_tac >>
              qpat_assum `!tail. eval_exprs cx es _ = _` mp_tac >>
              qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
              qpat_assum `res = INL tv` mp_tac >>
              pop_assum mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
              drule exprSimMemorySourceTheory.read_result_gas_obs >> strip_tac >>
              simp[Once evaluate_def, GSYM bind_assoc, APPEND_ASSOC] >>
              qpat_x_assum `!tail. eval_expr cx e _ = _`
                (qspec_then `gas_explicit marks' wt.vs_gas_readings ++ tail` assume_tac) >>
              gvs[bind_def, AllCaseEqs(), return_def, APPEND_ASSOC] >>
              metis_tac[]) >>
           qpat_x_assum `buf.buf_operand::rest = newops` (SUBST_ALL_TAC o SYM) >>
           qpat_assum `buf.buf_operand = Var aq` SUBST_ALL_TAC >>
           rule_assum_tac (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >-
             (qexists_tac `ws1` >>
              ntac 4 (conj_tac >- (simp[NoAsms] >> decide_tac)) >>
              conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- (simp[NoAsms, EVERY_APPEND] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
              conj_tac >-
                (qpat_x_assum `!x. (MEM (Var x) ops \/ x = aq) \/ _ ==> _` mp_tac >>
                 POP_ASSUM_LIST (K all_tac) >> simp[MEM_APPEND] >> metis_tac[]) >>
              qpat_x_assum `!j rt. j < LENGTH ops + _ /\ _ ==> _` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD_SYM]) >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[]) >>
      `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
          lookup_var x wt = SOME w` by
        (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
         qpat_assum `!x. not_fresh_at ci x ==> _` mp_tac >>
         qpat_assum `!x. not_fresh_at ca x ==> _` mp_tac >>
         qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `ci_mono si ci` mp_tac >>
         qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def,
              typedMemoryCopyTheory.typed_copy_state_frame_def,
              exprLoweringPropsTheory.ci_mono_def,
              loweringStateRelDefsTheory.not_fresh_at_def] >>
         rpt strip_tac >>
         `(!n. ci.cs_next_var <= n ==> x <> STRING #"%" (toString n)) /\
          (!n. ca.cs_next_var <= n ==> x <> STRING #"%" (toString n)) /\
          (!n. cu.cs_next_var <= n ==> x <> STRING #"%" (toString n))` by
           (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
         metis_tac[]) >>
      `!n b sz. local_region cenv es0.scopes s0 n b sz <=>
         local_region cenv mid.scopes wt n b sz` by
        (qpat_assum `!n b sz. local_region cenv es0.scopes s0 n b sz <=> _` mp_tac >>
         qpat_assum `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==> _` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `stmt_state_rel _ ctx func cenv cx esi s` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              stateRelProjTheory.state_rel_local_ptrs_rel] >> rpt strip_tac >>
         eq_tac
         >- (rw[loweringStateRelDefsTheory.local_region_def] >>
             `lookup_scopes n mid.scopes <> NONE` by
               metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                         optionTheory.NOT_SOME_NONE] >>
             `not_fresh_at si p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
         rw[loweringStateRelDefsTheory.local_region_def] >>
         `lookup_scopes n esi.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         Cases_on `lookup_scopes n esi.scopes` >> fs[] >>
         rename1 `lookup_scopes n esi.scopes = SOME entry0` >>
         `?w0. lookup_var p s = SOME w0` by
           (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
            qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         `lookup_var p wt = SOME w0` by metis_tac[] >> gvs[]) >>
      conj_tac >- simp[] >>
      `si.cs_next_var <= cs.cs_next_var /\ si.cs_next_id <= cs.cs_next_id` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`ci_mono si ci`, `ci_mono ci ca`, `ci_mono ca cu`, `ci_mono cu cs`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      ntac 2 (conj_tac >-
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[])) >>
      conj_tac >-
        (simp[MEM_APPEND] >> rpt strip_tac >>
         irule freshWritesTheory.not_fresh_at_mono
         >- (qexists_tac `si` >> simp[]) >>
         qexists_tac `ca` >> simp[] >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `ci_mono cu cs` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `!aid b cap. aid < si.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) ==>
         regions_disjoint (w2n aw) (MAX 32 (type_memory_bytes cenv dty)) b cap` by
        (qpat_assum `vv_post _ ctx func cenv cx e esi si ci s mid tv vv t` mp_tac >>
         qpat_assum `!aid b len. aid < ci.cs_next_id /\ _ ==> _` mp_tac >>
         qpat_assum `si.cs_next_id <= ci.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         `aid < ci.cs_next_id` by decide_tac >> metis_tac[]) >>
      `!n b cap. local_region cenv esi.scopes s n b cap ==>
         regions_disjoint (w2n aw) (MAX 32 (type_memory_bytes cenv dty)) b cap` by
        (qpat_assum `!sn H. ci.cs_next_id <= sn.cs_next_id /\ _ ==> _`
           (qspecl_then [`ca`,`storage_trace_horizon mid.storage_trace`] mp_tac) >>
         (impl_tac >- simp[]) >>
         qpat_assum `!name b len. local_region cenv mid.scopes at name b len ==> _` mp_tac >>
         qpat_assum `MAP FDOM esi.scopes = MAP FDOM mid.scopes` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `local_region cenv esi.scopes s n b cap` mp_tac >>
         simp[loweringStateRelDefsTheory.local_region_def] >> strip_tac >>
         `lookup_scopes n mid.scopes <> NONE` by
           metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom,
                     optionTheory.NOT_SOME_NONE] >>
         `not_fresh_at si p` by
           (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         Cases_on `lookup_scopes n mid.scopes` >> gvs[] >> metis_tac[]) >>
      `!x. not_fresh_at si x ==> not_fresh_at cu x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `si` >> simp[]) >>
      `ghost_kept_at lo cenv esi si G tn s wG wtn` by
        (qpat_assum `!x. not_fresh_at si x ==> not_fresh_at cu x` mp_tac >>
         qpat_assum `nw <= MAX 32 (type_memory_bytes cenv dty)` mp_tac >>
         qpat_assum `ghost_kept_at lo cenv esi si G tn s G' tn'` mp_tac >>
         qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
         qpat_assum `!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==> _` mp_tac >>
         qpat_assum `!aid b cap. aid < si.cs_next_id /\ _ ==> regions_disjoint _ _ _ _` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def,
                          loweringStateRelDefsTheory.regions_disjoint_def] >>
         rpt strip_tac
         >- metis_tac[]
         >- metis_tac[]
         >- (`w2n aw + MAX 32 (type_memory_bytes cenv dty) <= off \/ off + sz <= w2n aw` by
               (qpat_x_assum `!aid b cap. _ ==> _` irule >> metis_tac[]) >>
             `i < w2n aw \/ w2n aw + nw <= i` by
               (FIRST [qpat_assum `w2n aw + MAX 32 _ <= off` mp_tac,
                       qpat_assum `off + sz <= w2n aw` mp_tac] >>
                qpat_assum `off <= i` mp_tac >> qpat_assum `i < off + sz` mp_tac >>
                qpat_assum `nw <= MAX 32 _` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
             `i IN tn'.t_mem` by
               (qpat_x_assum `!i. _ ==> (_ <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
             metis_tac[]) >>
         `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + sz <= w2n aw` by
           (qpat_x_assum `!n b cap. local_region _ _ _ _ _ _ ==> _` irule >> metis_tac[]) >>
         `i < w2n aw \/ w2n aw + nw <= i` by
           (FIRST [qpat_assum `w2n aw + MAX 32 _ <= b` mp_tac,
                   qpat_assum `b + sz <= w2n aw` mp_tac] >>
            qpat_assum `b <= i` mp_tac >> qpat_assum `i < b + sz` mp_tac >>
            qpat_assum `nw <= MAX 32 _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
         `i IN tn'.t_mem` by
           (qpat_x_assum `!i. _ ==> (_ <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
         metis_tac[]) >>
      `wb_frame cenv esi mid si s z` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
      `!off len. off + len <= w2n aw \/ w2n aw + nw <= off ==>
         mem_bytes_at off len wt.vs_memory = mem_bytes_at off len z.vs_memory` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      `!n b cap. local_region cenv esi.scopes s n b cap ==>
         mem_bytes_at b cap wt.vs_memory = mem_bytes_at b cap z.vs_memory` by
        (rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ _ _`
           drule >>
         qpat_assum `nw <= MAX 32 _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `wt.vs_allocas = z.vs_allocas` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
         disch_then (mp_tac o AP_TERM ``\st:venom_state. st.vs_allocas`` o CONJUNCT1) >> simp[]) >>
      `wb_frame cenv esi mid si s wt` by
        (qpat_assum `nw <= MAX 32 _` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s z` mp_tac >>
         qpat_assum `!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==> _` mp_tac >>
         qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> mem_bytes_at _ _ _ = _` mp_tac >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len wt.vs_memory = _` mp_tac >>
         qpat_assum `!aid b cap. aid < si.cs_next_id /\ _ ==> regions_disjoint _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         qpat_x_assum `nw <= MAX 32 _` (mk_asm "store_extent") >>
         fs[loweringPostsTheory.wb_frame_def] >>
         conj_tac >-
           (rpt strip_tac >>
            `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= off \/ off + sz <= w2n aw` by
              metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
            `off + sz <= w2n aw \/ w2n aw + nw <= off` by
              (FIRST [qpat_assum `w2n aw + MAX 32 _ <= off` mp_tac,
                      qpat_assum `off + sz <= w2n aw` mp_tac] >>
               asm "store_extent" mp_tac >>
               POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
            `mem_bytes_at off sz wt.vs_memory = mem_bytes_at off sz z.vs_memory` by
              (qpat_x_assum `!off len. _ ==> mem_bytes_at off len wt.vs_memory = _`
                 (qspecl_then [`off`,`sz`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
            `mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz s.vs_memory` by
              (qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz z.vs_memory = _`
                 (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
               disch_then irule >> simp[] >> first_assum ACCEPT_TAC) >>
            metis_tac[]) >>
         irule exprSimPropsTheory.locals_kept_regions_tail >> qexists_tac `z` >>
         simp[] >> first_assum ACCEPT_TAC) >>
      `!n b sz. local_region cenv esi.scopes s n b sz <=>
         local_region cenv mid.scopes wt n b sz` by metis_tac[] >>
      `s.vs_alloca_next <= wt.vs_alloca_next` by
        (qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `at.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
         qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
         qpat_assum `t.vs_alloca_next <= at.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              loweringPostsTheory.wb_frame_def] >>
         rpt strip_tac >>
         qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
           vs_current_bb := _; vs_inst_idx := _|> = z`
           (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
         simp[] >> decide_tac) >>
      `wt.vs_labels = s.vs_labels` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ (s,G,tn) _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
             gas_origin_ptr_path _ (t,G1,tn1) _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
                   fragGasOriginTheory.gas_origin_path_erase,
                   fragGasModeTheory.gas_marked_path_exec,
                   fragGasPathTheory.gas_path_labels]) >>
      mp_tac (Q.INST [`ee` |-> `mid`, `sj` |-> `cs`, `t` |-> `wt`,
                     `G1` |-> `wG`, `tn1` |-> `wtn`]
        intcall_args_prefix_frame) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      conj_tac >-
        (rpt gen_tac >> strip_tac >>
         Cases_on `j < LENGTH ops`
         >- (qpat_assum `!j rt. j < LENGTH ops /\ _ ==> _ /\ _ /\ _ /\ _ /\
                (~EL j pflags ==> ?b cap aid. op_prov wG _ = _ /\ _)`
               (qspecl_then [`j`,`rt`] mp_tac) >>
             qpat_assum `evaluate_type _ (EL j (ptys ++ [dty])) = SOME rt` mp_tac >>
             qpat_assum `j < LENGTH ops` mp_tac >>
             qpat_assum `LENGTH ws = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH vals = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH ptys = LENGTH ops` mp_tac >>
             qpat_assum `LENGTH pflags = LENGTH ops` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         `j = LENGTH ops` by
           (qpat_assum `j < LENGTH (ops ++ [Var aq])` mp_tac >>
            qpat_assum `~(j < LENGTH ops)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[] ) >>
         qpat_assum `j = LENGTH ops` (fn ji =>
           qpat_assum `LENGTH vals = LENGTH ops` (fn vl =>
             qpat_assum `LENGTH ws = LENGTH ops` (fn wl =>
               qpat_assum `LENGTH pflags = LENGTH ops` (fn fl =>
                 simp[NoAsms, EL_APPEND_EQN, ji, vl, wl, fl])))) >>
         `evaluate_type (get_tenv cx) dty = SOME rt` by
           (qpat_assum `evaluate_type _ (EL j (ptys ++ [dty])) = SOME rt` mp_tac >>
            qpat_assum `j = LENGTH ops` mp_tac >>
            qpat_assum `LENGTH ptys = LENGTH ops` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         `value_has_type rt v /\ val_wf rt v /\
          type_memory_size rt <= MAX 32 (type_memory_bytes cenv dty) /\
          (!mem. mem_agree_outside wtn.t_mem wt.vs_memory mem ==>
            val_in_memory rt v (w2n aw) mem)` by
           (qpat_assum `!rt. evaluate_type (get_tenv cx) dty = SOME rt ==> _` drule >> simp[]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
         conj_tac >-
           (irule exprSimPropsTheory.val_footprint_le >>
            metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
         `FLOOKUP wt.vs_allocas ci.cs_next_id =
            SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
           (qpat_assum `wb_frame cenv mid mid ca at z` mp_tac >>
            qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
            qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
         `lo <= w2n aw` by
           (qpat_assum `allocas_from lo at` mp_tac >>
            qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
         `op_prov aG (Var aq) =
            SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
           first_assum ACCEPT_TAC >>
         `not_fresh_at cu aq` by
           (irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `ca` >> simp[] >>
            qpat_assum `ci_mono ca cu` mp_tac >>
            simp[exprLoweringPropsTheory.ci_mono_def]) >>
         `op_prov wG (Var aq) =
            SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
           (qpat_assum `not_fresh_at cu aq` mp_tac >>
            qpat_assum `!x. not_fresh_at ca x ==> _` (qspec_then `aq` mp_tac) >>
            qpat_assum `not_fresh_at ca aq` mp_tac >>
            qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` (qspec_then `aq` mp_tac) >>
            qpat_assum `op_prov aG (Var aq) = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
         qexistsl_tac [`w2n aw`,`MAX 32 (type_memory_bytes cenv dty)`,`ci.cs_next_id`] >>
         simp[] >>
         conj_tac >-
           (qpat_assum `compile_alloc_buffer _ ci = (buf,ca)` mp_tac >>
            qpat_assum `ci_mono ca cu` mp_tac >>
            qpat_assum `ci_mono cu cs` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
                 compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
                 compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_id_def,
                 compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
                 exprLoweringPropsTheory.ci_mono_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `w2n aw + MAX 32 _ <= z.vs_alloca_next` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
            rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
            simp[]) >>
         conj_tac >-
           (qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> _` mp_tac >>
            qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ b cap` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
         qpat_assum `case pin of NONE => T | SOME (rb,b,k) => FLOOKUP G rb = SOME (b,k) /\ _` mp_tac >>
         qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
         qpat_assum `!aid b len. aid < ci.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _` mp_tac >>
         qpat_assum `si.cs_next_id <= ci.cs_next_id` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         namedCases_on `pin` ["", "pp"] >> simp[] >>
         PairCases_on `pp` >>
         simp[loweringPostsTheory.vv_post_def,
              loweringStateRelDefsTheory.regions_disjoint_def] >>
         rpt strip_tac >>
         `sa.cs_next_id < ci.cs_next_id` by decide_tac >> metis_tac[]) >>
      simp[] >>
      conj_tac >-
        (rpt strip_tac >>
         qpat_x_assum `!j. j < LENGTH (e::es) /\ _ ==> _`
           (qspec_then `SUC j` mp_tac) >> simp[]) >>
      `expr_sim_inv cenv cx tenv mid` by
        (qpat_assum `!tail. eval_expr cx e _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
         qpat_assum `res = INL tv` mp_tac >>
         `expr_body_pre cenv cx tenv e esi` by
           (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         `expr_body_pre cenv cx tenv e
           (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
         dxrule exprSimSourceTheory.expr_body_pre_eval >>
         disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
         simp[bind_def, exprSimMemorySourceTheory.read_result_gas_obs]) >>
      simp[] >>
      `return_buf_frame d cenv cs wt` by
        (qpat_assum `return_buf_frame d cenv si s` mp_tac >>
         qpat_assum `wb_frame cenv esi mid si s wt` mp_tac >>
         qpat_assum `si.cs_next_var <= cs.cs_next_var` mp_tac >>
         qpat_assum `s.vs_alloca_next <= wt.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def] >> rpt strip_tac >>
         irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >> simp[]) >>
      `wb_frame cenv es0 mid sa s0 wt /\
       ghost_kept_at lo cenv es0 sa G0 tn0 s0 wG wtn` by
        (irule intcall_args_frame_compose >>
         qexistsl [`G`, `esi`, `s`, `si`, `tn`] >> simp[]) >>
      `wb_frame cenv es0 (mid with gas_obs := []) sa s0 wt` by
        (qpat_assum `wb_frame cenv es0 mid sa s0 wt` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
              loweringPostsTheory.popped_kept_def] >> metis_tac[]) >>
      simp[] >>
      reverse conj_tac >-
        (conj_tac >-
           (qpat_assum `LENGTH (F::flags1) = LENGTH (e::es)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `LENGTH (dty::dtys1) = LENGTH (e::es)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `eval_operands ops wt = SOME ws` mp_tac >>
            `lookup_var aq wt = SOME aw` by
              (qpat_assum `lookup_var aq z = SOME aw` mp_tac >>
               qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
               qpat_assum `not_fresh_at ca aq` mp_tac >>
               qpat_assum `ci_mono ca cu` mp_tac >>
               POP_ASSUM_LIST (K all_tac) >>
               simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
                    exprLoweringPropsTheory.ci_mono_def] >>
               metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
            pop_assum mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            qid_spec_tac `ws` >> Induct_on `ops` >>
            simp[venomStateTheory.eval_operands_def, venomStateTheory.eval_operand_def,
                 AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
         conj_tac >- metis_tac[listTheory.CONS_11] >>
         conj_tac >-
           (qpat_assum `EVERY (\e. expr_body_pre cenv cx tenv e esi) _` mp_tac >>
            qpat_assum `expr_sim_inv cenv cx tenv mid` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[EVERY_MEM, exprSimHypsDefsTheory.expr_body_pre_def] >> metis_tac[]) >>
         conj_tac >-
           (qpat_assum `ptr_covers aG atn aq at _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def]) >>
         conj_tac >-
           (qpat_assum `EVERY (supported_value_type tops) (dty::dtys1)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `EVERY (\ty. type_memory_bytes cenv ty < _) (dty::dtys1)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
            qexists_tac `si` >>
            qpat_assum `local_ptrs_reserved cenv si` mp_tac >>
            qpat_assum `si.cs_next_var <= cs.cs_next_var` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `LIST_REL _ (MAP expr_type (e::es)) (dty::dtys1)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         conj_tac >-
           (qpat_assum `fn_has_code shadow_si shadow_cf shadow_func` mp_tac >>
            qpat_assum `ci_mono shadow_si shadow_ci` mp_tac >>
            qpat_assum `ci_mono shadow_ci shadow_ca` mp_tac >>
            qpat_assum `ci_mono shadow_ca shadow_cu` mp_tac >>
            qpat_assum `ci_mono shadow_cu shadow_cs` mp_tac >>
            qpat_assum `ci_mono shadow_cs shadow_cf` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `ci_mono shadow_si shadow_cs` by
              metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
            fs[exprLoweringPropsTheory.ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split]) >>
         conj_tac >-
           (qpat_assum `fn_has_code si cf func` mp_tac >>
            qpat_assum `si.cs_next_var <= cs.cs_next_var` kall_tac >>
            qpat_assum `ci_mono si ci` mp_tac >>
            qpat_assum `ci_mono ci ca` mp_tac >>
            qpat_assum `ci_mono ca cu` mp_tac >>
            qpat_assum `ci_mono cu cs` mp_tac >>
            qpat_assum `ci_mono cs cf` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `ci_mono si cs` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
            fs[exprLoweringPropsTheory.ci_mono_def] >>
            metis_tac[fragExecTheory.fn_has_code_split]) >>
         conj_tac >-
           (qpat_assum `gas_admissible _ P esi` mp_tac >>
            qpat_assum `!tail. eval_expr cx e _ = _` mp_tac >>
            qpat_assum `res = INL tv` mp_tac >>
            qpat_assum `read_result cx tv mid = (INL v,mid)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[gas_admissible_def, vyperInterpreterTheory.evaluate_def,
                 vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
            rpt strip_tac >>
            first_x_assum (qspec_then
              `gas_explicit marks s.vs_gas_readings ++ gs` mp_tac) >>
            qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >>
            rpt strip_tac >>
            drule exprSimMemorySourceTheory.read_result_gas_obs >>
            disch_then (qspec_then `gs` assume_tac) >>
            gvs[bind_def] >> metis_tac[]) >>
         qpat_assum `case pin of NONE => T | SOME (rb,b,k) => FLOOKUP wG rb = SOME (b,k) /\ _` mp_tac >>
         qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
         qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         namedCases_on `pin` ["", "pp"] >> simp[] >>
         PairCases_on `pp` >> simp[] >> metis_tac[]) >>
      gen_tac >> disch_tac >>
      `expr_post H ctx func cenv cx e esi si cu s mid v op z /\
       ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
         simp[]) >>
      `stmt_state_rel H ctx func cenv cx mid z` by
        (qpat_assum `expr_post H ctx func cenv cx e esi si cu s mid v op z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
      `local_ptrs_rel func cenv mid.scopes z` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              stateRelProjTheory.state_rel_local_ptrs_rel]) >>
      `si.cs_next_var <= cu.cs_next_var` by
        (qpat_assum `ci_mono si ci` mp_tac >> qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `local_ptrs_reserved cenv cu` by
        (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `si` >> simp[]) >>
      `!n b len. local_region cenv mid.scopes z n b len ==>
         w2n aw + nw <= b \/ b + len <= w2n aw` by
        (qpat_assum `!n b sz. local_region cenv esi.scopes s n b sz <=> local_region cenv mid.scopes wt n b sz` mp_tac >>
         qpat_assum `!n b cap. local_region cenv esi.scopes s n b cap ==> regions_disjoint _ _ b cap` mp_tac >>
         qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv cu` mp_tac >>
         qpat_assum `nw <= MAX 32 _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              loweringStateRelDefsTheory.local_ptrs_reserved_def,
              loweringStateRelDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
         `local_region cenv mid.scopes wt n b len` by
           (qpat_x_assum `local_region cenv mid.scopes z n b len` mp_tac >>
            simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
         `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= b \/ b + len <= w2n aw` by metis_tac[] >>
         gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `ghost_inv_at (DF H) lo d cenv cx mid wG wtn wt` by
        (irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `lo <= z.vs_alloca_next` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >> rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >> simp[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `allocas_from lo z` mp_tac >>
            qpat_assum `wt.vs_allocas = z.vs_allocas` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def,
                 typedMemoryCopyTheory.typed_copy_state_frame_def] >> rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z`
              (mp_tac o AP_TERM ``\st:venom_state. st.vs_alloca_next``) >>
            simp[] >> metis_tac[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G' tn' z` mp_tac >>
            qpat_assum `wtn.t_stor = tn'.t_stor` mp_tac >>
            qpat_assum `wtn.t_trans = tn'.t_trans` mp_tac >>
            qpat_assum `wtn.t_imm = tn'.t_imm` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
                 bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def] >>
            rpt strip_tac >>
            qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
              vs_current_bb := _; vs_inst_idx := _|> = z` mp_tac >>
            disch_then (fn th =>
              map_every (mp_tac o C AP_TERM th)
                [``\st:venom_state. st.vs_accounts``, ``\st:venom_state. st.vs_transient``,
                 ``\st:venom_state. st.vs_call_ctx``, ``\st:venom_state. st.vs_immutables``]) >>
            simp[] >> metis_tac[]) >>
         qexistsl_tac [`G'`, `func`, `nw`, `z`, `cu`, `w2n aw`, `tn'`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `si` >> simp[] >> metis_tac[]) >>
         conj_tac >-
           (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `si` >> simp[] >> metis_tac[]) >>
         conj_tac >-
           (qpat_assum `typed_copy_state_frame cu _ _ z wt` mp_tac >>
            qpat_assum `!p. not_fresh_at cu p ==> FLOOKUP wG p = FLOOKUP G' p /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qpat_assum `!i. ~(w2n aw <= i /\ i < w2n aw + nw) ==> _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            first_x_assum irule >> decide_tac) >>
         conj_tac >-
           (qpat_assum `allocas_from lo at` mp_tac >>
            qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `FLOOKUP z.vs_allocas ci.cs_next_id =
         SOME (w2n aw, MAX 32 (type_memory_bytes cenv dty))` by
        (qpat_assum `wb_frame cenv mid mid ca at z` mp_tac >>
         qpat_assum `FLOOKUP at.vs_allocas ci.cs_next_id = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
      `fn_has_code ci ca func` by
        (qpat_assum `fn_has_code si cf func` mp_tac >>
         qpat_assum `ci_mono si ci` mp_tac >>
         qpat_assum `ci_mono ci ca` mp_tac >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `ci_mono cu cs` mp_tac >>
         qpat_assum `ci_mono cs cf` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `ci_mono ca cf` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >>
         `fn_has_code si ca func /\ fn_has_code ca cf func` by
           (irule fragExecTheory.fn_has_code_split >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
         qpat_assum `fn_has_code si ca func` mp_tac >>
         qpat_assum `cs_extends si ci` mp_tac >>
         qpat_assum `cs_extends ci ca` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[fragExecTheory.fn_has_code_split]) >>
      `MEM (mk_inst ci.cs_next_id ALLOCA
         [Lit (n2w (MAX 32 (type_memory_bytes cenv dty)))]
         [STRING #"%" (toString ci.cs_next_var)]) (fn_insts func)` by
        (irule actualAllocExecTheory.actual_alloc_buffer_site >>
         metis_tac[]) >>
      `cenv.ce_is_ctor ==> !name tv v off.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
         FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
           | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
         regions_disjoint off (type_memory_size tv) (w2n aw) nw` by
        (qpat_assum `nw <= MAX 32 _` mp_tac >>
         qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         qpat_assum `MEM (mk_inst ci.cs_next_id ALLOCA _ _) (fn_insts func)` mp_tac >>
         qpat_assum `FLOOKUP z.vs_allocas ci.cs_next_id = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              exprLoweringPropsTheory.immutable_alloca_sep_def] >> rpt strip_tac >>
         qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
         disch_then drule_all >> strip_tac >>
         qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule >>
         simp[venomInstTheory.mk_inst_def] >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
         decide_tac) >>
      conj_tac >-
        (qmatch_abbrev_tac `stmt_state_rel H ctx func cenv cx mid wt` >>
         `stmt_state_rel H ctx func cenv cx mid
           (wt with <|vs_prev_bb := z.vs_prev_bb;
             vs_current_bb := z.vs_current_bb; vs_inst_idx := z.vs_inst_idx|>)` suffices_by
           simp[bodyPtrMakeArrayCopyStateFrameTheory.literal_stmt_state_rel_cursor] >>
         irule exprSimBufferStoreTheory.buffer_store_state_frame >>
         qexistsl_tac [`w2n aw`,`nw`,`z`,`cu`] >>
         qpat_assum `typed_copy_state_frame cu (w2n aw) nw z wt` mp_tac >>
         qpat_assum `!n lb sz. local_region cenv mid.scopes z n lb sz ==> _` mp_tac >>
         qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv cu` mp_tac >>
         qpat_assum `stmt_state_rel H ctx func cenv cx mid z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              typedMemoryCopyTheory.typed_copy_frame_def,
              venomStateTheory.lookup_var_def] >> metis_tac[]) >>
      `storage_well_formed_on cx mid (FST H)` by
        (qpat_assum `expr_post H ctx func cenv cx e esi si cu s mid v op z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
      qpat_assum `storage_well_formed_on cx mid (FST H)` mp_tac >>
      qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid wG wtn wt` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[bodyPtrDefsTheory.ghost_inv_at_def,
           vyperStorageFootprintTheory.storage_well_formed_on_def,
           vyperStorageBackendTheory.get_storage_def] >>
      rpt strip_tac >> simp[]
      >- (Cases_on `b` >> gvs[vyperStorageBackendTheory.get_storage_def] >>
          metis_tac[vyperStorageBackendTheory.get_storage_def]) >>
      metis_tac[]) >>
  Cases_on `is_word_type dty`
  >- (`compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)` by
        (qpat_assum `store_step cu = (u,cs)` mp_tac >>
         qpat_assum `Abbrev (store_step = _)` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         qpat_assum `buf.buf_operand = Var aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[markerTheory.Abbrev_def, contextTheory.compile_store_memory_def] >>
         Cases_on `emit_void MSTORE [Var aq; op] cu` >> simp[]) >>
      `expr_type e = dty` by
        (qpat_assum `LIST_REL (type_widens_to _) _ (dty::dtys1)` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >>
         metis_tac[compileEnvTheory.type_widens_to_word]) >>
      `post_value_type cenv e = dty` by metis_tac[post_value_type_word] >>
      `eval_operand op z = SOME (typed_val_to_w256 rty v)` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `post_value_type cenv e = dty` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `is_word_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tn' op = {}` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def]) >>
      `ptr_covers G' tn' aq z 32` by
        (qpat_assum `ptr_covers G' tn' aq z (MAX 32 _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
         qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> gvs[arithmeticTheory.MAX_DEF]) >>
      `w2n aw + 32 <= z.vs_alloca_next` by
        (qpat_assum `w2n aw + MAX 32 _ <= z.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF]) >>
      `w2n aw + 32 < dimword (:256)` by
        (qpat_assum `w2n aw + MAX 32 _ < dimword (:256)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF]) >>
      qpat_assum `compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)`
        (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac
          logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      `evaluate_type (get_tenv cx) dty = SOME rty` by metis_tac[] >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> metis_tac[])) >>
      disch_then (qx_choose_then `wt` (qx_choose_then `wG` (qx_choose_then `wtn` strip_assume_tac))) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t,G1,tn1) [] (OK wt,wG,wtn)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) _ _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) _ _ /\ _`
           drule >>
         qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') _ _`
           (qspec_then `DF H` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
      `alloca_history func wt` by
        (`cs.cs_current_bb = cu.cs_current_bb /\
          cs.cs_current_insts = cu.cs_current_insts ++
            [mk_inst cu.cs_next_id MSTORE [Var aq;op] []]` by
           (qpat_assum `compile_store_memory cenv op (Var aq) dty (vv_type vv) cu = ((),cs)` mp_tac >>
            qpat_assum `is_word_type dty` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `emit_inst MSTORE [Var aq;op] [] cu = ((),cs)` by
              gvs[contextTheory.compile_store_memory_def,
                  emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
            drule emitHelperPropsTheory.emit_inst_extends >> simp[]) >>
         irule allocaHistoryTheory.alloca_history_frame >>
         qexists_tac `(mstore (w2n aw) (typed_val_to_w256 rty v) z)
                        with vs_inst_idx := LENGTH cs.cs_current_insts` >>
         reverse (rpt conj_tac)
         >- (irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
             conj_tac >- first_assum ACCEPT_TAC >>
             qexistsl_tac [`[mk_inst cu.cs_next_id MSTORE [Var aq;op] []]`,`z`,`cu`] >>
             simp[exprLoweringPropsTheory.run_inst_seq_def,
                  venomExecSemanticsTheory.step_inst_base_opcode_eqs,
                  venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
                  venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def]
             >-
               (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
                  (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
                (impl_tac >- first_assum ACCEPT_TAC) >>
                POP_ASSUM_LIST (K all_tac) >>
                simp[expr_post_def, stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
                metis_tac[]) >>
             FAIL_TAC "memory staging: remaining emitted word store history inputs") >>
         qpat_assum `typed_copy_state_frame _ _ _ z wt` mp_tac >>
         qpat_assum `wt.vs_inst_idx = LENGTH cs.cs_current_insts` mp_tac >>
         qpat_assum `wt.vs_current_bb = cs.cs_current_bb` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `cs.cs_current_bb = cu.cs_current_bb` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.mstore_def,
              venomStateTheory.write_memory_with_expansion_def,
              venomStateTheory.venom_state_component_equality] >>
         metis_tac[]) >>
      qexistsl_tac [`wt`,`wG`,`wtn`,`32`] >>
      simp[] >>
      conj_tac
      >- (irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
          metis_tac[]) >>
      disj1_tac >>
      `type_memory_size rty = 32` by
        metis_tac[exprSimPropsTheory.word_tv_memory_size] >> simp[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    (qpat_assum `LIST_REL (type_widens_to _) _ (dty::dtys1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `~is_word_type (expr_type e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `~is_word_type dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq]) >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
  `?sw. eval_operand op z = SOME sw` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
     metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type (expr_type e)` by
        (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `dty` >> simp[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b` >> simp[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `expr_type e` >>
         simp[vyperTypeSystemTheory.type_widens_to_def, vyperTypeSystemTheory.arg_type_fits_def] >>
         Cases_on `b` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b'` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b''` >> simp[vyperTypeSystemTheory.arg_type_fits_def,
           compileEnvTheory.is_bytestring_type_def]) >>
      `post_value_type cenv e = expr_type e` by simp[] >>
      `value_has_type rty v /\ type_memory_size rty < 2 ** 64` by simp[] >>
      `(!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           val_in_memory rty v (w2n sw) mem) /\
       (val_footprint rty v <> 0 ==> ?x b sz. op = Var x /\
         FLOOKUP G' x = SOME (b,sz) /\ b <= w2n sw /\
         w2n sw + val_store_size rty v <= b+sz)` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `eval_operand op z = SOME sw` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
         metis_tac[]) >>
      `?len. val_store_size rty v = 32 + 32 * ((len+31) DIV 32) /\
         32 + 32 * ((len+31) DIV 32) <= type_memory_size rty /\
         (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len)` by
        (qpat_assum `is_bytestring_type (expr_type e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `val_wf rty v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
         gvs[] >> drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >> gvs[] >>
         Cases_on `v` >>
         gvs[vyperTypingTheory.value_has_type_def, exprSimPropsTheory.val_store_size_def,
             valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
             vfmConstantsTheory.word_size_def] >>
         qmatch_goalsub_abbrev_tac `(actual_len + 31) DIV 32` >>
         qexists_tac `actual_len` >> simp[] >>
         irule arithmeticTheory.DIV_LE_MONOTONE >> simp[Abbr `actual_len`]) >>
      `!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn'.t_mem` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[representationCleanPtrTheory.robust_mem_word_at_clean]) >>
      `mload (w2n sw) z = n2w len` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
           mem_word_at (w2n sw) mem = n2w len`
           (qspec_then `z.vs_memory` mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def, venomStateTheory.mload_def,
              valueEncodingDefsTheory.mem_word_at_def]) >>
      `val_footprint rty v <> 0` by
        (qpat_assum `is_bytestring_type (expr_type e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >> gvs[] >>
         Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
           loweringPostsTheory.val_footprint_def]) >>
      `?src. op = Var src /\ lookup_var src z = SOME sw /\
         ptr_covers G' tn' src z (32+32*((len+31) DIV 32))` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op G' tn' z` mp_tac >>
         qpat_assum `~is_word_type (post_value_type cenv e)` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `eval_operand op z = SOME sw` mp_tac >>
         qpat_assum `val_footprint rty v <> 0` mp_tac >>
         qpat_assum `val_store_size rty v = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `32+32*((len+31) DIV 32) <= val_store_size rty v` by simp[] >>
         fs[bodyPtrDefsTheory.ptr_val_ok_def,
            bodyPtrDefsTheory.ptr_mem_ok_def] >>
         gvs[] >> simp[bodyPtrDefsTheory.ptr_covers_def] >>
         qexists_tac `w` >> gvs[venomStateTheory.eval_operand_def] >>
         decide_tac) >>
      `len+31 < dimword(:256) /\
       32+32*((len+31) DIV 32) < dimword(:256)` by
        (qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         qpat_assum `type_memory_size rty < 2 ** 64` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
         disch_then (qspec_then `len+31` strip_assume_tac) >>
         qmatch_asmsub_abbrev_tac `len+31 = _ + residue` >>
         `residue < 32` by simp[Abbr `residue`] >>
         gvs[wordsTheory.dimword_def] >> decide_tac) >>
      `type_memory_size rty <= type_memory_bytes cenv dty` by
        (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` mp_tac >>
         qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `expr_type e` >>
         gvs[vyperTypeSystemTheory.type_widens_to_def, vyperTypeSystemTheory.arg_type_fits_def,
           vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
           compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def] >>
         rename1 `expr_type e = BaseT bt` >>
         Cases_on `bt` >> gvs[vyperTypeSystemTheory.arg_type_fits_def,
           vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
           compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def] >>
         gvs[compileEnvTheory.is_bytestring_type_def] >>
         TRY (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[] >> NO_TAC) >>
         Cases_on `b'` >> gvs[compileEnvTheory.is_bytestring_type_def,
           vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.evaluate_type_def,
           valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
           vfmConstantsTheory.word_size_def] >>
         Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def,
           vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.evaluate_type_def,
           valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
           vfmConstantsTheory.word_size_def] >>
         irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
      `ptr_covers G' tn' aq z (32+32*((len+31) DIV 32))` by
        (qpat_assum `ptr_covers G' tn' aq z (MAX 32 _)` mp_tac >>
         qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         qpat_assum `type_memory_size rty <= type_memory_bytes cenv dty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
         qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >>
         gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)` by
        (qpat_assum `store_step cu = (u,cs)` mp_tac >>
         qpat_assum `Abbrev (store_step = _)` mp_tac >>
         qpat_assum `~is_word_type dty` mp_tac >>
         qpat_assum `is_bytestring_type dty` mp_tac >>
         qpat_assum `buf.buf_operand = Var aq` mp_tac >>
         qpat_assum `op = Var src` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         gvs[markerTheory.Abbrev_def, contextTheory.compile_store_memory_def,
           comp_ignore_bind_def, comp_bind_def, comp_return_def,
           compileEnvTheory.is_bytestring_type_def] >>
         Cases_on `compile_store_bytestring (Var src) (Var aq) cu` >>
         gvs[oneline compileEnvTheory.is_bytestring_type_def,
           comp_bind_def, comp_return_def]) >>
      `not_fresh_at cu src /\ not_fresh_at cu aq` by
        (conj_tac
         >- (`!x. vv_operand vv = Var x ==> not_fresh_at ca x` by
               (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `ci` >> simp[]) >>
             qpat_assum `unwrap_value cenv vv ca = (op,cu)`
               (mp_then Any mp_tac exprOperandVarTheory.compiler_unwrap_value_var) >>
             qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at ca x` mp_tac >>
             qpat_assum `op = Var src` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             Cases_on `vv` >> simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `not_fresh_at ca aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `w2n sw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next /\
       w2n aw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next` by
        (conj_tac
         >- (map_every (fn q => qpat_assum q mp_tac)
               [`expr_store_bound cx (expr_type e) v op z`,
                `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
                `post_value_type cenv e = expr_type e`,
                `~is_word_type (expr_type e)`, `eval_operand op z = SOME sw`,
                `val_store_size rty v = 32+32*((len+31) DIV 32)`] >>
             POP_ASSUM_LIST (K all_tac) >>
             simp[exprSimMemDefsTheory.expr_store_bound_def] >> metis_tac[]) >>
         map_every (fn q => qpat_assum q mp_tac)
           [`w2n aw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next`,
            `32+32*((len+31) DIV 32) <= type_memory_size rty`,
            `type_memory_size rty <= type_memory_bytes cenv dty`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `run_inst_seq_mem_ok (emitted_insts cu cs) z` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`,
            `not_fresh_at cu src`, `not_fresh_at cu aq`,
            `lookup_var src z = SOME sw`, `lookup_var aq z = SOME aw`,
            `mload (w2n sw) z = n2w len`,
            `32+32*((len+31) DIV 32) < dimword (:256)`,
            `w2n sw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next`,
            `w2n aw + (32+32*((len+31) DIV 32)) <= z.vs_alloca_next`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         irule bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok >>
         qexistsl_tac [`aw`,`Var aq`,`len`,`Var src`,`sw`] >>
         simp[venomStateTheory.eval_operand_def, vfmConstantsTheory.word_size_def] >>
         rpt strip_tac >> gvs[]) >>
      `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts cu cs) (DROP z.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         qpat_assum `fn_has_code cu cs func` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `z.vs_inst_idx = LENGTH cu.cs_current_insts` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         gvs[fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
             rich_listTheory.IS_PREFIX_APPEND,
             DROP_APPEND1, DROP_APPEND2]) >>
      qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
        (mp_then Any mp_tac bodyFullAllocGenericTheory.compile_store_bytestring_origin_ptr_path) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `mload _ _ = _`)) >>
      disch_then (drule_at (Pat `run_inst_seq_mem_ok _ _`)) >>
      disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`] mp_tac) >>
      disch_then (qspecl_then [`G'`,`tn'`,`32+32*((len+31) DIV 32)`] mp_tac) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `bG` (qx_choose_then `btn`
        (qx_choose_then `bt` strip_assume_tac))) >>
      `val_in_memory rty v (w2n sw) z.vs_memory /\ val_wf rty v` by
        (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> val_in_memory _ _ _ mem` mp_tac >>
         qpat_assum `value_has_type rty v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
      `val_in_memory rty v (w2n aw) bt.vs_memory /\
       typed_copy_state_frame cu (w2n aw) (type_memory_size rty) z bt` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`,
           `not_fresh_at cu src`, `not_fresh_at cu aq`,
           `lookup_var src z = SOME sw`, `lookup_var aq z = SOME aw`,
           `mload (w2n sw) z = n2w len`,
           `32+32*((len+31) DIV 32) < dimword (:256)`,
           `run_inst_seq (emitted_insts cu cs) z = OK bt`,
           `val_in_memory rty v (w2n sw) z.vs_memory`, `val_wf rty v`,
           `val_store_size rty v = 32+32*((len+31) DIV 32)`,
           `32+32*((len+31) DIV 32) <= type_memory_size rty`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `mem_word_at (w2n sw) z.vs_memory = n2w len` by
           gvs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
         qpat_assum `compile_store_bytestring _ _ _ = _`
           (mp_then Any mp_tac valueCopyTheory.store_bytestring_run_exact) >>
         disch_then (qspecl_then [`z`,`sw`,`aw`,`len`] mp_tac) >>
         simp[venomStateTheory.eval_operand_def, vfmConstantsTheory.word_size_def] >>
         strip_tac >> gvs[]
         >- (irule valueCopyTheory.mcopy_val_in_memory >>
             simp[vfmConstantsTheory.word_size_def] >>
             metis_tac[exprSimPropsTheory.val_footprint_le_store_size]) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
         conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
         simp[typedMemoryCopyTheory.typed_copy_frame_def] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
             simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
         simp[venomExecSemanticsTheory.mcopy_def,
              immutableMemoryFrameTheory.immutable_write_memory_capacity,
              arithmeticTheory.MAX_DEF, vfmConstantsTheory.word_size_def]) >>
      `mem_bytes_at (w2n aw) (32+32*((len+31) DIV 32)) bt.vs_memory =
         mem_bytes_at (w2n sw) (32+32*((len+31) DIV 32)) z.vs_memory` by
        (qpat_assum `bt.vs_memory = (mcopy _ _ _ z).vs_memory` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[valueEncodingProofsTheory.mcopy_mem_bytes_at_same]) >>
      `!i. i < 32+32*((len+31) DIV 32) ==>
         (w2n aw+i IN btn.t_mem <=> w2n sw+i IN tn'.t_mem)` by
        (qpat_assum `btn.t_mem = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[] >> rpt strip_tac >> simp[] >> decide_tac) >>
      `!mem. mem_agree_outside btn.t_mem bt.vs_memory mem ==>
         val_in_memory rty v (w2n aw) mem` by
        (map_every (fn q => qpat_assum q mp_tac)
          [`val_wf rty v`, `val_store_size rty v = 32+32*((len+31) DIV 32)`,
           `mem_bytes_at (w2n aw) (32+32*((len+31) DIV 32)) bt.vs_memory = _`,
           `!i. i < 32+32*((len+31) DIV 32) ==> _`,
           `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==> val_in_memory _ _ _ mem`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         `val_footprint rty v <= 32+32*((len+31) DIV 32)` by
           metis_tac[exprSimPropsTheory.val_footprint_le_store_size] >>
         rpt strip_tac >>
         irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`z.vs_memory`,`bt.vs_memory`,`32+32*((len+31) DIV 32)`,
           `w2n sw`,`tn'.t_mem`,`btn.t_mem`] >> simp[]) >>
      qabbrev_tac `bst = bt with vs_inst_idx :=
        z.vs_inst_idx + LENGTH (emitted_insts cu cs)` >>
      `bst.vs_inst_idx = LENGTH cs.cs_current_insts /\
       bst.vs_current_bb = cs.cs_current_bb` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         qpat_assum `z.vs_inst_idx = LENGTH cu.cs_current_insts` mp_tac >>
         qpat_assum `z.vs_current_bb = cu.cs_current_bb` mp_tac >>
         qpat_assum `run_inst_seq (emitted_insts cu cs) z = OK bt` mp_tac >>
         qpat_assum `isPREFIX (emitted_insts cu cs) (DROP z.vs_inst_idx _)` mp_tac >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
            (emitted_insts cu cs)` by
           gvs[bytesCopyCodeTheory.bytes_copy_insts_def,
               venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
         gvs[markerTheory.Abbrev_def, exprLoweringPropsTheory.same_blocks_def] >>
         metis_tac[fragExecTheory.exec_block_run_inst_seq]) >>
      `typed_copy_state_frame cu (w2n aw) (type_memory_size rty) z bst /\
       (!mem. mem_agree_outside btn.t_mem bst.vs_memory mem ==>
         val_in_memory rty v (w2n aw) mem)` by
        (qpat_assum `typed_copy_state_frame cu _ _ z bt` mp_tac >>
         qpat_assum `!mem. mem_agree_outside btn.t_mem bt.vs_memory mem ==> _` mp_tac >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[markerTheory.Abbrev_def, typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.lookup_var_def]) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t,G1,tn1) [] (OK bst,bG,btn)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) [] _ /\ _`
           drule >>
         qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] _`
           (qspec_then `DF H` mp_tac) >>
         qpat_assum `Abbrev (bst = _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         gvs[markerTheory.Abbrev_def] >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
      `alloca_history func bst` by
        (qpat_assum `compile_store_bytestring (Var src) (Var aq) cu = ((),cs)`
           (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
         map_every (fn q => qpat_assum q mp_tac)
           [`fn_has_code cu cs func`, `fn_inst_ids_distinct func`,
            `alloca_history func z`, `z.vs_current_bb = cu.cs_current_bb`,
            `z.vs_inst_idx = LENGTH cu.cs_current_insts`,
            `run_inst_seq (emitted_insts cu cs) z = OK bt`,
            `bst.vs_inst_idx = LENGTH cs.cs_current_insts`, `Abbrev (bst = _)`,
            `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ (at,aG,atn) [] _ /\ _`,
            `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         `alloca_inv z` by
           (qpat_x_assum `!H. _` drule >>
            simp[loweringPostsTheory.expr_post_def,
                 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
         `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cu cs)` by
           gvs[bytesCopyCodeTheory.bytes_copy_insts_def,
               venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
         `alloca_history func (bt with vs_inst_idx := LENGTH cs.cs_current_insts)` by
           (irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
            conj_tac >- first_assum ACCEPT_TAC >>
            qexistsl_tac [`emitted_insts cu cs`,`z`,`cu`] >>
            gvs[exprLoweringPropsTheory.same_blocks_def]) >>
         gvs[markerTheory.Abbrev_def]) >>
      `~bst.vs_halted` by
        (qpat_assum `typed_copy_state_frame cu _ _ z bst` mp_tac >>
         qpat_assum `~z.vs_halted` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
              venomStateTheory.venom_state_component_equality]) >>
      `!i. ~(w2n aw <= i /\ i < w2n aw + type_memory_size rty) ==>
         (i IN btn.t_mem <=> i IN tn'.t_mem)` by
        (qpat_assum `btn.t_mem = _` mp_tac >>
         qpat_assum `32+32*((len+31) DIV 32) <= type_memory_size rty` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >>
         eq_tac >> simp[] >> rpt strip_tac >> decide_tac) >>
      qexistsl_tac [`bst`,`bG`,`btn`,`type_memory_size rty`] >>
      conj_tac >- (irule arithmeticTheory.LE_TRANS >>
        qexists_tac `type_memory_bytes cenv dty` >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!p. not_fresh_at cu p ==> _ /\ _ /\ _` drule >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> disch_tac >>
      map_every (fn q => qpat_assum q mp_tac)
        [`type_widens_to (get_tenv cx) (expr_type e) dty`,
         `is_bytestring_type dty`,
         `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
         `post_value_type cenv e = expr_type e`,
         `value_has_type rty v`,
         `!mem. mem_agree_outside btn.t_mem bst.vs_memory mem ==> _`,
         `evaluate_type (get_tenv cx) dty = SOME rt`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
      Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
      Cases_on `b` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
      TRY (rename1 `is_bytestring_type (BaseT (BytesT dst_bound))` >>
        Cases_on `dst_bound` >> gvs[compileEnvTheory.is_bytestring_type_def,
          vyperValueTheory.evaluate_type_def]) >>
      Cases_on `expr_type e` >>
      gvs[vyperTypeSystemTheory.type_widens_to_def,
          vyperTypeSystemTheory.arg_type_fits_def] >>
      rename1 `expr_type e = BaseT bt` >>
      Cases_on `bt` >> gvs[vyperTypeSystemTheory.arg_type_fits_def,
          vyperValueTheory.evaluate_type_def] >>
      TRY (rename1 `expr_type e = BaseT (BytesT bound)` >>
        Cases_on `bound` >> gvs[vyperValueTheory.evaluate_type_def,
          compileEnvTheory.is_bytestring_type_def,
          vyperTypeSystemTheory.arg_type_fits_def]) >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
        valueEncodingDefsTheory.val_wf_def,
        valueEncodingDefsTheory.val_in_memory_def,
        valueEncodingTheory.type_memory_size_def, compileEnvTheory.type_memory_bytes_def,
        vfmConstantsTheory.word_size_def] >>
      TRY (decide_tac >> NO_TAC) >>
      TRY (rewrite_tac[GSYM contractABITheory.ceil32_def] >>
        qmatch_goalsub_rename_tac `contractABI$ceil32 cap` >>
        irule arithmeticTheory.LE_TRANS >> qexists_tac `cap` >>
        simp[contractABITheory.le_ceil32] >> decide_tac >> NO_TAC) >>
      FAIL_TAC "memory staging: bytestring representation widening") >>
  `vv_type vv = lowered_value_type cenv e` by
    (qpat_assum `!e dty ee ci vv cm. _` irule >>
     conj_tac >- (qexistsl_tac [`si`,`ci`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `dty` >> simp[]) >>
     qexists_tac `esi` >> first_assum ACCEPT_TAC) >>
  `~is_bytestring_type (expr_type e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `~is_bytestring_type dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
           metis_tac[valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >> strip_tac >>
     `well_typed_expr tenv e /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv.type_defs /\
      (!fid sig. FLOOKUP tenv.fn_sigs fid = SOME sig ==>
        cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
       (qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     drule exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
     disch_then (qspec_then `cenv` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`~is_word_type (expr_type e)`, `~is_bytestring_type (expr_type e)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[loweringPostsTheory.post_value_type_lowered,
         loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `value_has_type rty v /\ val_wf rty v` by
    (`value_has_type rty v` by
       (qpat_assum `!v. read_result cx tv mid = _ ==> value_has_type rty v` irule >>
        first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule memoryValueTypingTheory.value_has_type_val_wf >> first_assum ACCEPT_TAC) >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >>
     qpat_assum `expr_body_pre cenv cx tenv e esi` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
     rpt strip_tac >>
     metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >>
     qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `well_formed_type (get_tenv cx) (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
     strip_tac >- gvs[] >> strip_tac >> disj2_tac >>
     conj_tac >- (irule (CONJUNCT1 typedCopyCompatibilityTheory.arg_type_fits_trans) >>
       qexists_tac `expr_type e` >> simp[]) >> first_assum ACCEPT_TAC) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     qpat_assum `well_formed_type (get_tenv cx) (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeSystemTheory.type_widens_to_def,
          vyperTypeSystemTheory.well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `type_memory_bytes cenv dty = type_memory_size dtv /\
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty` by
    (conj_tac >> irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum drule >> qexistsl_tac [`tenv`,`esi`] >> first_assum ACCEPT_TAC) >>
  `value_has_type dtv v` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty`,
        `post_value_type cenv e = lowered_value_type cenv e`,
        `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
        `evaluate_type (get_tenv cx) dty = SOME dtv`, `value_has_type rty v`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[vyperTypeSystemTheory.type_widens_to_def] >>
     irule (CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type) >>
     goal_assum drule >> goal_assum drule >> goal_assum drule >> simp[]) >>
  `val_wf dtv v` by
    (irule memoryValueTypingTheory.value_has_type_val_wf >> first_assum ACCEPT_TAC) >>
  `(!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
       val_in_memory rty v (w2n sw) mem) /\ op_taint tn' op = {}` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`ptr_val_ok cx (post_value_type cenv e) v op G' tn' z`,
        `~is_word_type (post_value_type cenv e)`,
        `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
        `eval_operand op z = SOME sw`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
     metis_tac[]) >>
  reverse (Cases_on `type_memory_size rty = 0`)
  >- (`?src. op = Var src /\ lookup_var src z = SOME sw /\
         ptr_covers G' tn' src z (type_memory_size rty)` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z`,
            `~is_word_type (post_value_type cenv e)`, `eval_operand op z = SOME sw`,
            `op_taint tn' op = {}`, `type_memory_size rty <> 0`,
            `post_value_type cenv e = lowered_value_type cenv e`,
            `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty`] >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >>
         gvs[bodyPtrDefsTheory.ptr_buf_ok_def] >>
         simp[bodyPtrDefsTheory.ptr_covers_def] >>
         gvs[venomStateTheory.eval_operand_def]) >>
      `not_fresh_at cu src /\ not_fresh_at cu aq` by
        (conj_tac
         >- (`!x. vv_operand vv = Var x ==> not_fresh_at ca x` by
               (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
                qexists_tac `ci` >> simp[]) >>
             qpat_assum `unwrap_value cenv vv ca = (op,cu)`
               (mp_then Any mp_tac exprOperandVarTheory.compiler_unwrap_value_var) >>
             qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at ca x` mp_tac >>
             qpat_assum `op = Var src` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             Cases_on `vv` >> simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >>
         qpat_assum `ci_mono ca cu` mp_tac >>
         qpat_assum `not_fresh_at ca aq` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
      `acyclic_struct_metadata cenv.ce_struct_fields` by
        (qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[bodySimTheory.body_inv_def]) >>
      `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
       (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
         ALL_DISTINCT (MAP FST fields) /\
         EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
           sz = type_memory_size rt) fields)` by
        (qpat_assum `expr_sim_inv cenv cx tenv esi` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
      `z.vs_alloca_next < dimword (:256)` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[loweringPostsTheory.expr_post_def,
            stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
         metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >>
      `w2n sw + type_memory_size rty <= z.vs_alloca_next` by
        (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _` mp_tac >>
         map_every (fn q => qpat_assum q mp_tac)
           [`~is_word_type (post_value_type cenv e)`,
            `post_value_type cenv e = lowered_value_type cenv e`,
            `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty`,
            `eval_operand op z = SOME sw`, `type_memory_size rty <> 0`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      `w2n sw + type_memory_size rty < dimword (:256) /\
       w2n aw + type_memory_size dtv < dimword (:256)` by
        (map_every (fn q => qpat_assum q mp_tac)
           [`z.vs_alloca_next < dimword (:256)`,
            `w2n sw + type_memory_size rty <= z.vs_alloca_next`,
            `w2n aw + MAX 32 (type_memory_bytes cenv dty) <= z.vs_alloca_next`,
            `type_memory_bytes cenv dty = type_memory_size dtv`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      `w2n sw + type_memory_size rty <= w2n aw \/
       w2n aw + type_memory_size dtv <= w2n sw` by
        FAIL_TAC "aggregate store boundary: same-z unwrap source ownership must exclude ci.cs_next_id" >>
      FAIL_TAC "memory staging: aggregate nonzero store application") >>
  FAIL_TAC "memory staging: aggregate zero physical source"
QED


(* (a) Arguments and frame setup, at (DF H, lo).  The caller's code up to
   the INVOKE, then any code continuation kc, runs against the source up
   to push_function, then any source continuation f, on one witness: the
   arguments' judgments run their staging, and whatever runs the rest of
   the call and f from an intcall_entry_full state (source, memory and
   pointer facts at t) runs the whole call and f.  Supplied arguments and
   omitted defaults use their respective expression-list judgments. *)
Theorem intcall_args_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) ==>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
      (!v. storage_trace_frame (f v)) /\
      (!v. cs_appends (kc v)) /\
      comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
        kc sa = (out, sb) /\
      comp_bind
        (compile_expr cenv ty
           (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
        kc shadow_sa = (out, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        P es0 /\
      (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 s0 /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!H res ee gt r.
         expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
         R H res ee gt r) /\
      (!vv sm prev penv rtv es1 t G tn.
         compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
           (vv, sm) /\
         kc vv sm = (out, sb) /\
         (!H. valid_horizon cx st0 H es1.storage_trace ==>
            intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
              es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
              es1 t G tn) /\
         (?H. valid_horizon cx st0 H es1.storage_trace) /\
         gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
           P es1 ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
           Q R) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        (es0, s0, G0, tn0) Q R
Proof
  cheat
QED
