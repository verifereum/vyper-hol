(* A ternary at the joint judgments, on finite horizons: the condition's
   value, the JNZ into the selected arm's block, the arm (no copy, a
   bytestring widening copy, or a widened internal call's typed copy), the
   ASSIGN and the JMP.  The value judgment follows from the vv judgment by
   expr_sim_full_of_vv (bodyFullOfVV).

   The helper lemmas the arm steps take as premises are discharged here:
   the generic ALLOCA/bytestring ones from bodyFullAllocGeneric, the joint
   typed copy from typedCopyOriginPtr.

 *
 * TOP-LEVEL:
 *   ifexp_expr_full_ok -- bodyFullCases' IfExp case (body_ifexp_case_full)
 *)
Theory bodyFullIfExp
Ancestors
  bodyFullIfExpWiden bodyFullIfExpWidenCall
  bodyFullIfExpFinish bodyFullIfExpShadow bodyFullAllocGeneric typedCopyOriginPtr
  bodyFullIfExpPrepare bodyFullOfVV bodyFullUnwrap bodyFullPreds
  bodySimFull gasOutcomeFullCompose gasOutcomeFull gasOutcomeFullGuarded gasShadowCompile
  gasShadowCompileHelpers exprSimMemorySource exprSimIfExp exprSimDefs
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering exprLoweringProps
  typedCopyDomain vyperTypeSystem compileEnv context vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

(* Select the simulation field, without unfolding the child judgments. *)
fun use_ifexp_child child =
  qpat_assum child
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  qpat_x_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      _ ==> expr_sim_full _ _ _ _ _ _ /\ _` mp_tac >>
  metis_tac[];

Theorem ifexp_expr_full_ok_from_root[local]:
  (!c a b t cenv cx rty DF lo d ctx shadow_ctx PG func shadow_func es ty env.
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
       ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
       type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
       (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))) /\
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
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT BoolT) c es /\
    (!gs v es1.
      bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
      expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty a es1 /\
      expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty b es1 /\
      (!e gs' raw ee. (e = a \/ e = b) /\
        eval_expr cx e (es1 with gas_obs := gs') = (INL raw,ee) ==>
        eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
      !e gs' v' es2.
        (e = a \/ e = b) /\
        bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') = (INL v',es2) ==>
        value_has_type rty v' /\
        !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v') ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (IfExp t c a b) es) ==>
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  disch_then (assume_tac o GEN_ALL) >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac [bodyFullPredsTheory.body_expr_full_ok_def] >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> rpt (goal_assum (drule_at Any))) >>
  rpt gen_tac >> strip_tac >>
  drule ifexp_body_pre_children >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `?rty. evaluate_type (get_tenv cx) v5 = SOME rty` by
    (qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
       (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  reverse conj_asm2_tac
  >- (qpat_x_assum `!c a b t cenv cx rty DF lo d ctx shadow_ctx PG func shadow_func es ty env. _` irule >>
      simp[] >>
      conj_tac >- (rpt gen_tac >> strip_tac >>
        `expr_body_pre cenv cx env e es` by metis_tac[] >>
        drule ifexp_body_arm_kind >> gvs[]) >>
      conj_tac >- fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
      conj_tac >- (rpt strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
        fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
      conj_tac >- (strip_tac >>
        qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
          (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_copy_ok) >>
        simp[expr_type_def]) >>
      conj_tac >- fs[bodySimTheory.body_inv_def] >>
      conj_tac >- suspend "arms" >>
      conj_tac >- fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
      use_ifexp_child `body_expr_full_ok cx e1`) >>
  qpat_x_assum `!c a b t cenv cx rty DF lo d ctx shadow_ctx PG func shadow_func es ty env. _` kall_tac >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >>
  simp[post_value_type_def, expr_type_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
        (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_copy_ok) >>
      simp[expr_type_def]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) (es with gas_obs := gs)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `bind (eval_expr cx (IfExp v5 e1 e2 e3)) (read_result cx)
     (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) (_ with gas_obs := _)`
    (mp_then Any mp_tac exprSimIfExpTheory.ifexp_body_pre_read_typed) >>
  simp[expr_type_def] >> metis_tac[]
QED

Resume ifexp_expr_full_ok_from_root[arms]:
  qexists `env` >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env es1` by
    (qpat_assum `expr_body_pre _ _ _ e1 (_ with gas_obs := _)`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_eval) >>
     simp[] >> metis_tac[]) >>
  `well_typed_expr env e1` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env es1` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) _ _ = (_,es1)` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e2 es1 /\ expr_body_pre cenv cx env e3 es1` by metis_tac[] >>
  `body_expr_full_ok cx e2 /\ body_expr_full_ok cx e3` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  conj_tac >- use_ifexp_child `body_expr_full_ok cx e2` >>
  conj_tac >- use_ifexp_child `body_expr_full_ok cx e3` >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e (es1 with gas_obs := gs')` by
        metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es1 with gas_obs := gs')` by metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  (conj_tac
   >- (qpat_assum `expr_body_pre _ _ _ e (_ with gas_obs := _)`
         (mp_then Any mp_tac exprSimIfExpTheory.ifexp_body_pre_read_typed) >>
       simp[] >> metis_tac[]) >>
   `env.type_defs = get_tenv cx` by
     (qpat_assum `expr_body_pre _ _ _ e (_ with gas_obs := _)`
        (ACCEPT_TAC o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_env_type_defs)) >>
   qpat_assum `expr_body_pre _ _ _ e (_ with gas_obs := _)`
     (mp_then Any mp_tac exprSimHypsTheory.memory_rhs_read_post_typed) >>
   disch_then (qspecl_then [`v'`,`es2`] mp_tac) >>
   gvs[SF ETA_ss, vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
   strip_tac >> rpt strip_tac >> gvs[])
QED

Finalise ifexp_expr_full_ok_from_root

(* body_inv and expr_body_pre, the word agreement by the contrapositive of
   post_value_type_nonword. *)
Theorem ifexp_expr_full_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  match_mp_tac ifexp_expr_full_ok_from_root >>
  rpt gen_tac >> strip_tac >> irule ifexp_vv_full_root_uniform >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`env`,`rty`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule ifexp_selected_arm_step_full >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`e`,`env`,`rty`,`sm`,`ty`,`av`] >>
  simp[] >>
  qpat_x_assum `!e. e = a \/ e = b ==> _` (qspec_then `e` mp_tac) >>
  simp[] >> gvs[] >> metis_tac[]
QED
