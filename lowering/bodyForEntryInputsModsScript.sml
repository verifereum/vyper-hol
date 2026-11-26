(* Linked For entry: evaluator callbacks and the declared static frame. *)
Theory bodyForEntryInputsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullForFacts bodySimDeclCases
  bodyExprPreFacts bodyInvExecutionProps bodySim vyperState vyperInterpreter
  allocLimits finite_map

val _ = Parse.hide "body";

Theorem for_iterator_callback_mods:
  (!tenv s tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s =
       (INL tyv,t) ==>
     body_iterator_full_ok_mods mods exps cx it) /\
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  body_iterator_full_ok_mods mods exps cx it
Proof
  strip_tac >> first_x_assum irule >>
  simp[lift_option_type_def, return_def]
QED

(* The loop body is needed only after a successful read of the first result. *)
Theorem for_body_callback_mods:
  (!tenv s tyv t s1 vs t1 s2 u t2.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s =
       (INL tyv,t) /\
     eval_iterator cx it s1 = (INL vs,t1) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 =
       (INL u,t2) ==>
     body_for_full_ok_mods mods exps cx tyv id body vs) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  eval_iterator cx it es = (INL (r::rs),es1) /\
  compatible_bound (Dynamic n) (LENGTH (r::rs)) /\
  read_result cx r es1 = (INL v,es2) ==>
  body_stmts_full_ok_mods mods exps cx body
Proof
  strip_tac >>
  `body_for_full_ok_mods mods exps cx tyv id body (r::rs)` by
    (first_x_assum irule >>
     simp[lift_option_type_def, return_def, check_def, assert_def] >>
     metis_tac[]) >>
  fs[body_for_full_ok_mods_def] >> metis_tac[]
QED

Theorem for_declared_static_inputs_mods:
  !mods exps src tops ctx cenv cx bc id typ it n st st1 body env env' ret_ty
    DF lo d shadow_ctx PG func shadow_func RetQ.
    declare_local cenv id typ st = (bc,st1) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    same_frame cenv bc /\
    contract_inv mods exps ctx bc cx /\
    module_body_inv mods src tops bc cx /\
    stmts_exprs_ok bc body /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ bc ret_ty /\
    ?body_env'. type_stmts (extend_local env id typ F) ret_ty body = SOME body_env'
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  drule_then assume_tac contract_inv_alloca_locals >>
  `same_frame cenv bc` by (drule declare_local_same_frame >> simp[]) >>
  drule_all body_inv_same_frame_mods >> strip_tac >>
  drule_then assume_tac body_for_exprs_ok >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (drule_all for_declare_stmts_exprs_ok >> simp[]) >>
  conj_tac >- (drule_all ce_locals_declared_declare_local >> simp[]) >>
  conj_tac >-
    (`type_memory_bytes cenv typ < 2 ** 64` by
       (qpat_x_assum `stmt_exprs_ok _ (For _ _ _ _ _)` mp_tac >>
        simp[stmt_exprs_ok_def, alloc_limits_stmt_def, GSYM AND_IMP_INTRO]) >>
     drule_then assume_tac same_frame_struct_fields >>
     drule_all locals_alloc_ok_extend >> simp[]) >>
  reverse conj_tac >-
    (drule type_stmt_for_projection >> simp[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `frame_ret_ok_full_mods _ _ _ _ _ _` mp_tac >>
  simp[frame_ret_ok_full_mods_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED
