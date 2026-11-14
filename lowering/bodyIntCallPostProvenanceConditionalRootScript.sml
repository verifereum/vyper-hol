(* Root routing is independent of the selected-arm implementation. *)
Theory bodyIntCallPostProvenanceConditionalRoot
Ancestors
  bodyIntCallPostProvenanceConditional exprSimIfExp
  vyperState vyperAST loweringPosts loweringStateRelDefs compileEnv
  exprLowering exprLoweringProps venomState finite_map exprSimDefs gasOutcome gasSummary
  fragGasMode fragGasPath gasContext fragExec list

Theorem intcall_ifexp_outcome_from_arm:
  !ctx func cenv cx ty t c a b es env sa sb vv s0.
    (!e es1 sa sm sb vv op u.
      post_value_type cenv e = expr_type e /\ well_typed_expr env e /\ ~expr_has_effect e /\
      (!sa sm vv u.
        compile_expr cenv ty e sa = (vv,sm) /\
        fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\
        gas_admissible (eval_expr cx e) expr_vv_res_ok es1 /\
        stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
        u.vs_current_bb = sa.cs_current_bb /\
        u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es1,u)
          (\res ee t. ?tv. res = INL tv /\
            vv_post ctx func cenv cx e es1 sa sm u ee tv vv t /\
            t.vs_current_bb = sm.cs_current_bb /\
            t.vs_inst_idx = LENGTH sm.cs_current_insts /\
            intcall_vv_provenance cenv cx (expr_type e) sa sm ee tv vv t)
          (\res ee r. expr_exit res r)) /\
      compile_expr cenv ty e sa = (vv,sm) /\
      compile_ifexp_arm cenv (expr_type e) (lowered_value_type cenv e) vv sm = (op,sb) /\
      (~is_word_type (expr_type e) ==>
        lowered_value_type cenv e = expr_type e \/
        is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
        arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
        same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
      (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
        ~is_word_type (expr_type e) ==>
        type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
        type_memory_size tvt < 2 ** 64) /\
      (!gs v es2. ~is_word_type (expr_type e) /\
        (do r <- eval_expr cx e; read_result cx r od)
          (es1 with gas_obs := gs) = (INL v,es2) ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v) /\
      gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es1 /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
      u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (bind (eval_expr cx e) (conditional_result cx)) (es1,u)
        (\res ee t. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
          expr_post ctx func cenv cx e es1 sa sb u ee v op t /\
          t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          (~is_word_type (expr_type e) ==>
            vv_at cenv cx (expr_type e) sa sb ee tv
              (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t /\
            intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv
              (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t))
        (\res ee r. expr_exit res r)) /\
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!e. (e = a \/ e = b) ==> well_typed_expr env e /\ ~expr_has_effect e /\
      post_value_type cenv e = expr_type e) /\
    (~is_word_type t ==> !e. (e = a \/ e = b) ==>
      lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
      same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
      type_memory_bytes cenv t = type_memory_size tvt /\ type_memory_size tvt < 2 ** 64) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
      (do result <- eval_expr cx c; read_result cx result od)
        (es with gas_obs := gs) = (INL tv,es1) ==>
      (!e sa sm vv u. (e = a \/ e = b) /\
        compile_expr cenv ty e sa = (vv,sm) /\ fn_has_code sa sm func /\
        fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
        gas_admissible (eval_expr cx e) expr_vv_res_ok es1 /\
        stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
        u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es1,u)
          (\res ee t. ?tv. res = INL tv /\
            vv_post ctx func cenv cx e es1 sa sm u ee tv vv t /\
            t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
            intcall_vv_provenance cenv cx (expr_type e) sa sm ee tv vv t)
          (\res ee r. expr_exit res r)) /\
      (!e gs' v es2. ~is_word_type t /\ (e = a \/ e = b) /\
        (do r <- eval_expr cx e; read_result cx r od)
          (es1 with gas_obs := gs') = (INL v,es2) ==>
        ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v)) /\
    compile_expr cenv ty (IfExp t c a b) sa = (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0)
      (\res ee u. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv vv u /\
        u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        intcall_vv_provenance cenv cx t sa sb ee tv vv u)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `?cop sc. lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
    fn_has_code sa sc func` by
    (drule_all ifexp_root_code_layout >> disch_then (qspec_then `T` mp_tac) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule ifexp_root_condition_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ c _` mp_tac >> rewrite_tac[expr_sim_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def, gas_summary_at_def])
  >- (gvs[] >>
      `!tail. bind (eval_expr cx c) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
      `?sel. v = BoolV sel` by (irule ifexp_root_condition_bool >> metis_tac[]) >>
      gvs[] >> suspend "selected")
  >- (irule ifexp_root_condition_exit >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[ifexp_root_condition_cert]
QED

Resume intcall_ifexp_outcome_from_arm[selected]:
  qmatch_asmsub_abbrev_tac `expr_post _ _ _ _ c es sa sc s0 mid` >>
  `bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL (BoolV sel),mid)` by
    (simp[Abbr `mid`] >> metis_tac[APPEND_NIL]) >>
  qpat_x_assum `!gs tv es1. _` (qspecl_then
    [`gas_explicit marks s0.vs_gas_readings`,`BoolV sel`,`mid`] mp_tac) >>
  fs[vyperStateTheory.bind_def] >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (irule ifexp_root_condition_scopes >> fs[vyperStateTheory.bind_def] >> metis_tac[]) >>
  `gas_admissible
    (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok mid` by
    (simp[Abbr `mid`] >> irule (SRULE [] ifexp_root_branch_admissible) >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  drule_all ifexp_root_code_layout >> disch_then (qspec_then `sel` strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e sa sb op. (e = a \/ e = b) /\ _ ==> _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (IfExp _ _ _ _) _ = _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (bind (eval_expr _ c) _) _ _` kall_tac >>
  gvs[] >> suspend "routed"
QED

Resume intcall_ifexp_outcome_from_arm[routed]:
  `~t'.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `gas_path ctx func t' 0 (OK (jump_to (if sel then tl else el) t'))` by
    (irule ifexp_root_jnz_path >> metis_tac[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code sj sn func` kall_tac >>
  qpat_x_assum `fn_has_code sa sb func` kall_tac >>
  qpat_x_assum `fn_has_code sa sc func` kall_tac >>
  `~expr_has_effect (IfExp (expr_type a) c a b) ==> ~expr_has_effect (if sel then a else b)` by
    (Cases_on `sel` >> rewrite_tac[expr_has_effect_thm, DE_MORGAN_THM] >>
     strip_tac >> asm_rewrite_tac[]) >>
  irule ifexp_root_selected_outcome_prefix >>
  qexistsl_tac [`marks`,`es_end`,`sel`,`t'`,`jump_to (if sel then tl else el) t'`] >>
  simp[] >>
  irule (SRULE [] intcall_ifexp_merge_outcome) >> simp[] >>
  qexistsl_tac [`cop`,`if sel then a else b`,`aop`,`sc`,`se`,`sx`,`sy`,`sz`,`BoolV sel`] >>
  simp[] >> conj_tac >- (Cases_on `sel` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx mid (jump_to (if sel then tl else el) t')` by
    (simp[stmt_state_rel_jump_to] >> fs[expr_post_def]) >>
  conj_tac >- (Cases_on `sel` >> simp[]) >>
  qpat_x_assum `!e es1 sa sm sb vv op u. _`
    (qspecl_then [`if sel then a else b`,`mid`] mp_tac) >>
  Cases_on `sel` >> gvs[] >> disch_then irule >>
  simp[jump_to_def] >>
  rpt conj_tac >> metis_tac[]
QED

Finalise intcall_ifexp_outcome_from_arm
