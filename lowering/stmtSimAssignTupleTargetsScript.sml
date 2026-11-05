(* General tuple assignment simulation. *)
Theory stmtSimAssignTupleTargets
Ancestors
  exprSimDefs exprSimProps exprSimStack exprOperandVar loweringPosts stmtSimDefs stmtSimProps
  stmtSimForced gasSummaryCompose fragGasMode
  tupleAssignParts tupleTargetStoreRun tupleTargetStoreProps tupleAssignPrefix
  tupleStageProps tupleLocalStoreProps stmtSimReturn stmtSimAssignTuple 
   exprLowering exprLoweringProps fragExec loweringSlice compileEnv freshWrites
  vyperInterpreter vyperState vyperValue vyperTyping vyperTypeDefaults valueEncoding stmtLowering
  list rich_list finite_map stmtSimDecl stmtSimDeclMem
Libs
  monadsyntax

Theorem stmt_frag_storage_maps_intro:
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
     stmt_frag ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  strip_tac >> rw[stmt_frag_def, stmt_framed_frag_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ /\ _ ==> stmt_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def, stmt_framed_frag_def]) >>
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

Theorem assign_tuple_targets_suffix[local]:
  !ctx func cx lctx cenv gs e es ee v tys tvs sa su sl ss sf op staged elems sv s0 flag.
    expr_post ctx func cenv cx e es sa su s0 ee v op sv /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts /\ ~sv.vs_halted /\
    ee.gas_obs = [] /\ value_has_type (TupleTV tvs) v /\
    gs <> [] /\ LENGTH gs = LENGTH tys /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs)
        (EL i (case v of ArrayV (TupleV vs) => vs | _ => []) )) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
    cs_extends sa su /\ sa.cs_next_var <= su.cs_next_var /\
    cs_extends su sl /\ cs_extends sl ss /\
    su.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= ss.cs_next_var /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    ?ee' t'.
      (!tail. assign_tuple_targets cx (TupleTarget gs) v (ee with gas_obs := tail) =
        (INL (), ee' with gas_obs := tail)) /\
      gas_marked_path F ctx func sv 0 (OK t') /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
        (ee' with gas_obs := []) t'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[LIST_REL_LENGTH, values_have_types_length]) >>
  `LIST_REL (tuple_source_target cx ee.scopes) gs tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule tuple_target_aligned_source >>
     qexistsl [`cenv`, `EL n tys`, `EL n vs`] >> simp[]) >>
  `LIST_REL value_has_type tvs vs` by simp[GSYM values_have_types_LIST_REL] >>
  `~cx.txn.is_static` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
  drule_all assign_tuple_targets_safe >> strip_tac >>
  rename1 `assign_tuple_targets _ _ _ ee = (INL (),ee')` >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "prefix"
QED

Resume assign_tuple_targets_suffix[prefix]:
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)` by
    (gen_tac >> disch_tac >> irule tuple_target_aligned_sizes >>
     qexists `EL i gs` >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl [`get_tenv cx`, `tys`] >>
     simp[] >> rpt strip_tac >>
     disj2_tac >> qexistsl [`EL i tys`, `EL i tvs`] >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> fs[cs_extends_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  `expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  drule_all tuple_assignment_prefix_path >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "stores"
QED

Resume assign_tuple_targets_suffix[stores]:
  `!i. i < LENGTH gs ==> ?v. eval_operand (EL i elems) t = SOME v /\
    if is_word_type (EL i tys) then
      v = typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (gen_tac >> disch_tac >> simp[] >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  `LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)` by
    (rpt strip_tac >> simp[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(if flag then _ else _) su = _` kall_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_val_rel _ (expr_type e) _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ (expr_type e) _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_rel _ (TupleT tys) _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ (TupleT tys) _ _ _ _ _ _` kall_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`gs`, `T`] tuple_store_targets_path)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ ee' _ /\ _`
    (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`ee'`, `sfv`] >> conj_tac
  >- (drule_all assign_tuple_target_list_gas_obs >>
      simp[Once evaluate_def]) >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  suspend "frame"
QED

Resume assign_tuple_targets_suffix[frame]:
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists `sl` >> simp[]) >>
  simp[]
QED

Finalise assign_tuple_targets_suffix

Theorem compile_assign_tuple_targets_stmt_frag:
  !ctx func cx lctx RetQ cenv ty gs e es tys tvs.
    expr_type e = TupleT tys /\ LENGTH gs = LENGTH tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!obs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := obs) = (INL v,es1) ==>
      value_has_type (TupleTV tvs) v) /\
    (!obs vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od)
        (es with gas_obs := obs) = (INL (ArrayV (TupleV vs)),es1) /\
      i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    gs <> [] /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_targets_code_parts >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  irule forced_then_stmt_outcome >>
  qexistsl [
    `\v ee t. expr_post ctx func cenv cx e es sa su s0 ee v op t /\
              t.vs_current_bb = su.cs_current_bb /\
              t.vs_inst_idx = LENGTH su.cs_current_insts`,
    `e`, `assign_tuple_targets cx (TupleTarget gs)`] >>
  reverse conj_tac
  >- (conj_tac >- simp[eval_assign_tuple_action] >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `su`, `op`, `s0`] mp_tac) >>
      (impl_tac >- (fs[] >> metis_tac[forced_then_admissible, eval_assign_tuple_action])) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs)
      (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))` by
    (drule_all tuple_type_value >> strip_tac >> gvs[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  drule_all assign_tuple_targets_suffix >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  qexistsl [`INL ()`, `ee'`, `OK t'`] >> simp[]
QED

