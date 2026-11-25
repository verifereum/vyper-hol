(* Source cuts for a linked StructLit's ordered field evaluation. *)
Theory bodyStructFieldsSourceMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprSimAggregateSource exprSimMemorySource
  exprSimHypsDefs exprSimDefs exprBodyPreProps exprBodyPreTypingProps
  exprBodyPreCallSafetyProps supportedExprTraverse
  vyperTypeCallStackSoundness vyperTypeCallGraph
  vyperTypeExprResult vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperTypeInvariants vyperTypeSystem
  allocLimits gasContext vyperInterpreter vyperState vyperAST stmtSimDefs
  list combin
Libs monadsyntax

Theorem struct_field_pre_mods:
  expr_body_pre_mods mods ce cx env (StructLit ann nsid fs) es /\
  MEM e (MAP SND fs) /\ expr_sim_inv_mods mods ce cx env mid ==>
  expr_body_pre_mods mods ce cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def] >>
  strip_tac >> drule_all_then strip_assume_tac aggregate_named_child_body_syntax >>
  `!p. supported_expr_exists p e ==>
       supported_expr_exists p (StructLit ann nsid fs)` by
    (rpt strip_tac >> simp[Once supported_expr_exists_def,
         supported_fields_exists_every, EXISTS_MEM, o_THM] >>
     gvs[MEM_MAP] >> disj2_tac >> qexists_tac `y` >> simp[]) >>
  simp[] >> rpt conj_tac
  >- (irule call_evaluation_safe_mono >>
      qexists_tac `int_calls_named_exprs fs` >> simp[])
  >- (qpat_x_assum `~expr_has_evm_run (StructLit _ _ _)` mp_tac >>
      simp[expr_has_evm_run_thm, EXISTS_MEM, o_THM] >>
      gvs[MEM_MAP] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[EVERY_MEM] >> metis_tac[])
QED

Theorem struct_fields_list_admissible_mods:
  gas_admissible (eval_expr cx (StructLit ann nsid fs)) expr_vv_res_ok es ==>
  gas_admissible (eval_exprs cx (MAP SND fs))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  drule aggregate_eval_struct >> disch_then (qspecl_then [`nsid`, `ann`] mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem struct_fields_eval_cons:
  eval_exprs cx (e::args) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem struct_fields_head_admissible_mods:
  expr_body_pre_mods mods ce cx env e es /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res`
  >- (rename1 `eval_expr cx e _ = (INL raw,ee)` >>
      `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
      drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
      qspecl_then [`cx`,`e`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`es with gas_obs := gs`,`INL raw`,`ee`] mp_tac) >>
      Cases_on `raw` >> fs[runtime_consistent_def, expr_vv_res_ok_def,
                           eval_result_typed_def]) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[struct_fields_eval_cons, bind_def, expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem struct_fields_tail_admissible[local]:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := marks ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) mid
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `marks ++ gs` mp_tac) >>
  simp[struct_fields_eval_cons, bind_def] >> metis_tac[]
QED

Theorem struct_fields_source_cuts_mods:
  body_exprs_full_ok_mods mods exps cx (e::args) /\
  expr_body_pre_mods mods ce cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!tail. eval_expr cx e (es with gas_obs := marks ++ tail) =
          (INL raw, mid with gas_obs := tail)) /\
  read_result cx raw mid = (INL v,mid) ==>
  body_exprs_full_ok_mods mods exps cx args /\
  expr_sim_inv_mods mods ce cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  value_runtime_typed env (expr_type e) v /\
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) mid
Proof
  strip_tac >>
  drule_then assume_tac read_result_gas_obs >>
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := marks ++ tail) = (INL v,mid with gas_obs := tail)` by
    simp[bind_def] >>
  drule_all_then assume_tac struct_fields_tail_admissible >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := marks) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := marks)` by simp[] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [])) >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  fs[] >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  first_x_assum irule >>
  qexistsl_tac [`es with gas_obs := marks`,`raw`,`mid with gas_obs := []`,
                `mid`,`v`,`mid`] >> simp[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))
QED
