(* General tuple assignment simulation. *)
Theory stmtSimAssignTupleTargets
Ancestors
  tupleAssignParts tupleTargetStoreRun tupleTargetStoreProps tupleAssignPrefix
  tupleAssignMemory tupleStageProps tupleLocalStoreProps stmtSimReturn stmtSimAssignTuple stmtSim
  exprSim exprLowering exprLoweringProps fragExec loweringSlice compileEnv freshWrites
  vyperInterpreter vyperState vyperValue vyperTyping vyperTypeDefaults valueEncoding stmtLowering
  list rich_list finite_map stmtSimDecl stmtSimDeclMem
Libs
  monadsyntax

Theorem stmt_frag_storage_maps_intro:
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
     stmt_frag ctx func cx lctx RetQ cenv m es res es') ==>
  stmt_frag ctx func cx lctx RetQ cenv m es res es'
Proof
  strip_tac >> rw[stmt_frag_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ /\ _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def]) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem tuple_target_aligned_sizes:
  !cenv cx g ty tv.
    tuple_target_aligned cenv cx g ty tv ==>
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    0 < type_memory_size tv
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac
  >- gvs[]
  >- (drule_all word_type_sizes >>
      disch_then (qspec_then `cenv` strip_assume_tac) >> simp[])
  >> drule_all word_type_sizes >>
  disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]
QED

Theorem assign_tuple_targets_success_run:
  !ctx func cx lctx cenv ty gs e es es' tys tvs sa sf s0.
    eval_stmt cx (Assign (TupleTarget gs) e) es = (INL (),es') /\
    gs <> [] /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (cenv,sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule eval_assign_tuple >> strip_tac >> Cases_on `r` >> gvs[] >>
  rename1 `assign_tuple_targets _ _ v es1 = (INL (),es')` >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  drule assign_tuple_target_list_length >> strip_tac >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[LIST_REL_LENGTH, values_have_types_length]) >>
  drule_all assign_tuple_targets_code_parts >> strip_tac >>
  suspend "prefix_setup"
QED

Resume assign_tuple_targets_success_run[prefix_setup]:
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `cs_extends su sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (qspecl_then [`sa`, `su`, `sf`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)` by
    (gen_tac >> disch_tac >> irule tuple_target_aligned_sizes >>
     qexists `EL i gs` >> first_x_assum irule >> decide_tac) >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (simp[LIST_REL_EL_EQN]) >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (simp[LIST_REL_EL_EQN]) >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl [`get_tenv cx`, `tys`] >>
     simp[] >> rpt strip_tac >>
     disj2_tac >> qexistsl [`EL i tys`, `EL i tvs`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  drule_all tuple_assignment_prefix_run >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "stores"
QED

Resume assign_tuple_targets_success_run[stores]:
  `!i. i < LENGTH gs ==> ?v. eval_operand (EL i elems) t = SOME v /\
    if is_word_type (EL i tys) then
      v = typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)` by
    (rpt strip_tac >> simp[]) >>
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (gen_tac >> disch_tac >> simp[] >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  `LENGTH elems = LENGTH vs /\ LENGTH gs = LENGTH tys` by decide_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`gs`, `T`] tuple_store_targets_run)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ es' _ /\ _`
    (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)) >>
  suspend "compose"
QED

Resume assign_tuple_targets_success_run[compose]:
  conj_tac >- simp[] >>
  qexists `sfv` >> simp[] >>
  suspend "vars"
QED

Resume assign_tuple_targets_success_run[vars]:
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists `sl` >> simp[]) >>
  simp[]
QED

Finalise assign_tuple_targets_success_run

Theorem compile_assign_tuple_targets_stmt_frag:
  !ctx func cx lctx RetQ cenv ty gs e es res es' tys tvs.
    eval_stmt cx (Assign (TupleTarget gs) e) es = (res,es') /\
    expr_type e = TupleT tys /\ LENGTH gs = LENGTH tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    gs <> [] /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e)) es res es'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_targets_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  Cases_on `res`
  >- (rename1 `eval_stmt _ _ _ = (INL u,_)` >> Cases_on `u` >>
      drule_all assign_tuple_targets_success_run >> strip_tac >>
      disj1_tac >> qexistsl [`t`, `cenv`] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]) >>
  rename1 `eval_stmt _ _ _ = (INR y,_)` >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INR y,es') /\
    expr_res_ok (INR y : value + exception)` by suspend "error_source" >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (qspecl_then [`sa`, `su`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  drule_all stmtSimDeclTheory.expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED

Resume compile_assign_tuple_targets_stmt_frag[error_source]:
  irule eval_assign_tuple_targets_error >>
  reverse conj_tac >- (qexists_tac `lctx` >> simp[]) >>
  qexists_tac `gs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `value_has_type (TupleTV tvs) v` by simp[] >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  qexists_tac `tvs` >> simp[GSYM values_have_types_LIST_REL] >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  simp[LIST_REL_EL_EQN] >> qx_gen_tac `i` >> strip_tac >>
  irule tuple_target_aligned_source >>
  qexistsl [`cenv`, `EL i tys`, `EL i vs`] >> simp[]
QED

Finalise compile_assign_tuple_targets_stmt_frag
