(* Stack packaging for NoneT system actions, on the forced run's endpoint. *)
Theory bodyActionStackVVMods
Ancestors
  bodyScalarStackVVMods bodyFullPostsMods exprSimHypsDefs exprSimStack
  exprSimMemDefs loweringPosts bodyPtrDefs exprSimDefs valueEncoding context stmtSimProps
  vyperAST vyperValue vyperInterpreter vyperState compileEnv exprLowering

Theorem action_none_footprint[local]:
  val_footprint NoneTV v = 0
Proof
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

Theorem action_none_stack_post[local]:
  post_value_type cenv e = NoneT /\ expr_type e = NoneT /\
  expr_post_mods H ctx f cenv cx e es sa sb s0 ee v op u ==>
  vv_post_mods H ctx f cenv cx e es sa sb s0 ee (Value v) (StackValue a op) u /\
  vv_own cenv cx NoneT sa sb ee (Value v) (StackValue a op) u
Proof
  simp[expr_post_mods_def, expr_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_holds_def, vv_at_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       read_result_def, return_def, vv_storage_live_def, vv_own_def] >>
  strip_tac >> gvs[] >>
  gvs[expr_val_own_def, expr_val_rel_def, evaluate_type_def, action_none_footprint] >>
  first_assum ACCEPT_TAC
QED

Theorem action_stack_vv_full_mods:
  !DF lo d ctx sh PG f sf mods cenv cx env ty e es a args.
    e = Call NoneT a args NONE /\ MEM a [RawLog; RawRevert; SelfDestructTarget] /\
    expr_body_pre_mods mods cenv cx env e es /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?vt op sb. compile_expr cenv ty e sa = (StackValue vt op,sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv e = NoneT /\ expr_type e = NoneT /\
   lowered_value_type cenv e = NoneT` by
    gvs[post_value_type_def, lowered_value_type_def, expr_type_def] >>
  qpat_x_assum `e = _` kall_tac >>
  qpat_x_assum `MEM a _` kall_tac >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` kall_tac >>
  rw[expr_vv_sim_full_mods_def] >>
  qpat_x_assum `!sa. ?vt op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  drule_all_then assume_tac eval_expr_force_admissible >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (drule_all_then assume_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  irule stack_unforce_outcome_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all_then strip_assume_tac action_none_stack_post >>
      simp[ptr_vv_ok_def, vv_location_def, read_result_def, return_def] >>
      irule vv_store_bound_stack_value >> simp[evaluate_type_def, type_memory_size_def]) >>
  rpt strip_tac >> gvs[expr_exit_success_map, halt_exit_def] >>
  ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED
