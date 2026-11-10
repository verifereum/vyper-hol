(* Source and gas composition for existing-local relayout. *)
Theory assignRelayoutFrag
Ancestors
  assignRelayoutContinue annassignRelayoutFrag annassignRelayoutCode
  stmtSimAssignMem stmtSimAssignCompose stmtSimAssignSource stmtSimAssignPath
  stmtSimDeclCompose gasOutcome gasSummary gasSummaryCompose gasExemptCert
  stmtSimDefs exprSimDefs loweringPosts stmtSimProps exprSimProps
  stmtLowering exprLowering exprLoweringProps emitHelperProps compileEnv loweringStateRelDefs
  context venomState venomInst vyperInterpreter vyperState vyperLookup
  localPtrsProps fragGasMode fragGasPath loweringSlice loweringHalt
  stmtFragPtr exprSimWordArgs list finite_map
  stmtSimAssign stmtSimAssignStore stmtLoweringMono fragExec
  annassignRelayoutContinue exprOpenTerminals exprOperandVar
Libs monadsyntax

Theorem assign_relayout_normal_continuation:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  post_value_type cenv e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\ ~is_word_type sty /\
  (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) /\
     lookup_scopes id es1.scopes = SOME entry ==>
     entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v /\
     val_wf stv v /\ val_wf dtv v /\ val_footprint stv v = type_memory_size stv) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_id <= sb.cs_next_id /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv sty < dimword (:256) /\
  compile_assign_value cenv (Var p) LocMemory op F loc dty sty info bytes sb = ((),sf) /\
  (loc = NONE \/ loc = SOME LocMemory) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?ff u. gas_marked_exec F (ctx,func) (write_place cx (MemoryPlace id []) v)
    (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
    stmt_post ctx func cx lctx cenv cenv sa sf es s0 (INL ()) ff u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v /\
   val_wf stv v /\ val_wf dtv v /\ val_footprint stv v = type_memory_size stv` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl_tac [`ee with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings ++ []`] >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[expr_post_def, stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `type_memory_size dtv <= cap` by
    (fs[expr_post_def, stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) s` by
    (irule expr_post_alloca_frame >> metis_tac[]) >>
  drule assign_relayout_store_post_path >>
  disch_then (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule >>
  disch_then (qspecl_then [`id`, `cap`, `pre`, `env`, `entry`, `rest`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexistsl_tac [`ee with scopes :=
    pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`, `t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac >-
    (qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (ee with scopes := scs) _` >>
     `ee with <|scopes := scs; gas_obs := []|> =
      (ee with scopes := scs) with gas_obs := []` by
       simp[evaluation_state_component_equality] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
     qpat_x_assum `ee with <|scopes := scs; gas_obs := []|> = _`
       (fn th => pure_once_rewrite_tac [th]) >>
     rewrite_tac[stmt_state_rel_gas_obs]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_post_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at sb x` by (irule not_fresh_at_mono >> metis_tac[]) >>
     `lookup_var x s = SOME w` by metis_tac[] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  irule alloca_frame_trans >>
  qexistsl_tac [`cenv`, `ee`, `s`, `sb`] >> simp[] >>
  conj_tac >-
    (qpat_x_assum `alloca_frame cenv es sa s0 cenv _ s` mp_tac >> simp[]) >>
  qpat_x_assum `alloca_frame cenv ee sb s cenv _ t` mp_tac >>
  qmatch_goalsub_abbrev_tac `ee with scopes := scs` >>
  `ee with <|scopes := scs; gas_obs := []|> =
   (ee with scopes := scs) with gas_obs := []` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => pure_once_rewrite_tac [th]) >> simp[]
QED

(* Assignment composition is independent of the representation of the value. *)
Theorem assign_local_store_rhs_outcome:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) Q
    (\res ee r. expr_exit res r) /\
  (!res ee t. Q res ee t ==> ?v. res = INL v) /\
  (!marks v ee t.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) marks (INL v) ee (OK t) /\ Q (INL v) (ee with gas_obs := []) t ==>
    ?ff u. gas_marked_exec F (ctx,func) (write_place cx (MemoryPlace id []) v)
      (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
      stmt_post ctx func cx lctx old c sa sf es s0 (INL ()) (ff with gas_obs := []) u) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
    (stmt_post ctx func cx lctx old c sa sf es s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          qpat_x_assum `!marks v ee t. _` drule >> simp[] >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[gas_exempt_cert_unforce_result]
QED

Theorem assign_local_relayout_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c,sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv,sV) /\
      unwrap_value cenv vv sV = (op,sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op,sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT et (Dynamic _) =>
          SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
         | _ => NONE) (type_memory_bytes cenv vtyp) sB = ((),sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op,sB)` >>
  simp[] >> strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,sB)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sf` by
    (`ci_mono sB sf` by metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  `fn_has_code sa sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >> gvs[]
QED

Theorem compile_assign_local_relayout_stmt_frag:
  !ctx func cx lctx RetQ cenv ret_ty id typ e es stv dtv p cap env.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    cenv.ce_var_type id = SOME typ /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e <> expr_type e /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    lowered_value_type cenv e <> typ /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) typ /\
    post_value_type cenv e = lowered_value_type cenv e /\
    evaluate_type (get_tenv cx) typ = SOME dtv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v /\
       val_wf stv v /\ val_wf dtv v /\ val_footprint stv v = type_memory_size stv) /\
    expr_body_pre cenv cx env e es /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_relayout_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
   ~block_is_terminated sV` by
    (irule residual_call_compile_location >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `~block_is_terminated sB` by (drule_all unwrap_value_open >> simp[]) >>
  `~block_is_terminated sb` by
    (drule compile_assign_memory_relayout_open >> simp[]) >>
  `sa.cs_next_var <= sB.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `sa.cs_next_id <= sB.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    (drule_then (drule_then assume_tac) compile_lower_value_var >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
      t.vs_current_bb = sB.cs_current_bb /\ t.vs_inst_idx = LENGTH sB.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_def] >> disch_then irule >> gvs[]) >>
  irule assign_local_store_rhs_outcome >>
  (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[stmt_post_end_gas_obs] >>
  irule assign_relayout_normal_continuation >> simp[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >> simp[] >> qexists_tac `marks` >>
  (conj_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
