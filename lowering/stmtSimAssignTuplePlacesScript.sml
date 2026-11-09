(*
 * Statement simulation: a tuple assigned to places (#637, #851)
 *
 * (t1, ..., tn) = e where each ti is a base target of a value type that is
 * not inside an immutable: a local or a field or element of one, a storage
 * or transient variable or a field or element of one, or a mapping's
 * value.  The source evaluates e and reads its tuple value, then for each
 * ti in order evaluates its place and writes the element there
 * (assign_tuple_targets).  The lowering, in the same order, evaluates e,
 * loads every element (from a staged copy when e is a memory view with an
 * aggregate element), then for each ti computes its pointer
 * (compile_get_target_ptr, simulated by targetPlaceSim's target_sim) and
 * stores the element there (placeStore).  The elements are loaded at the
 * RHS's lowered type (an internal call's declared return type, which the
 * call site may annotate with a wider type), and each store converts from
 * that layout to its target's.
 *
 * TOP-LEVEL:
 *   compile_assign_tuple_places_stmt_frag — the statement for every outcome
 *)

Theory stmtSimAssignTuplePlaces
Ancestors
  supportedTargets placeStore targetPlaceSimCases targetPlaceSim targetPlaceSimDefs
  stmtSimDefs exprSimHypsDefs exprSimDefs loweringPosts
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperTypeSystem
  list tuplePlaceCodeParts tuplePlaceFlagUnpackOpen tuplePlaceRootReady
  stmtReasonVvMemory stmtSimAssignTuple stmtSimForced stmtSimProps
  gasSummaryCompose gasSummary fragGasPath fragGasMode freshWrites
Libs monadsyntax

Theorem compile_assign_tuple_places_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env tops gs e es tys tvs ltys ltvs.
    expr_type e = TupleT tys /\ gs <> [] /\
    LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    lowered_value_type cenv e = TupleT ltys /\ arg_types_fit ltys tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys ==>
      type_memory_size (TupleTV ltvs) < dimword (:256)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256) /\
      type_memory_size (EL i ltvs) + 64 < dimword (:256)) /\
    EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
                    target_case F ctx func cenv cx bt /\
                    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt)
      gs /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def, stmt_env_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[declare_stmt_local_def, comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule_all tuple_place_compile_parts_frames >> strip_tac >>
  `fn_has_code sa su func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[forced_then_admissible, eval_assign_tuple_action] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `su`, `op`, `s0`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rewrite_tac[eval_assign_tuple_action] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `res` >> fs[expr_exit_def] >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
   ?vs. v = ArrayV (TupleV vs) /\
     value_has_type (TupleTV ltvs) (ArrayV (TupleV vs))` by
    (mp_tac (Q.INST
      [`es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee` |-> `mid with gas_obs := []`] tuple_place_root_rhs_ready) >>
     simp[] >> metis_tac[]) >> gvs[] >>
  drule_all tuple_place_root_static_ready >> strip_tac >>
  drule_all tuple_place_root_layout_ready >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by simp[] >>
  drule_all (Q.INST [`ee` |-> `mid with gas_obs := []`]
    tuple_place_flag_unpack_outcome_open) >> strip_tac >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      Cases_on `res` >> fs[expr_exit_def] >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  fs[expr_post_def] >>
  rpt strip_tac >>
  `not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED
