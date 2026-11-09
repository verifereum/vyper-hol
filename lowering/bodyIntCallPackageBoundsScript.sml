(* Source traversal and graph obligations at the producer boundary. *)
Theory bodyIntCallPackageBounds
Ancestors
  bodyIntCallProducerBounds externalBodyWidths bodyIntCallJointInputs
  bodyIntCallActualEntryFields allocLimitsProps supportedProgram
  vyperTypeCallStackSoundness vyperTypeCallGraph vyperTypeInvariants bodySim
  compileVyper compileEnv list

Theorem callable_body_follows_graph:
  functions_follow_call_graph edges cx /\ get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,[],ret,ss) ==>
  calls_follow_call_graph edges (src,name) (int_calls_stmts ss)
Proof
  simp[functions_follow_call_graph_def, calls_follow_call_graph_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule >>
  simp[function_int_calls_def, int_calls_expr_def]
QED

Theorem internal_body_traversal_bounds:
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,ss) /\
  alloc_env_agree (build_compile_env tops Internal mut name args ret ss F) ce /\
  env_consistent env cx es /\ type_stmts env ret ss = SOME env' /\
  ~ce.ce_is_external ==>
  EVERY (stmt_exprs_ok ce) ss
Proof
  strip_tac >> drule_all fn_allocs_ok_body >> strip_tac >>
  `!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty` by
    metis_tac[consistent_var_types_well_formed] >>
  `!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt` by
    fs[env_consistent_def, env_context_consistent_def] >>
  drule_all type_stmts_excludes_bad_widths >> strip_tac >>
  irule stmt_exprs_ok_from_traversal_bounds >> simp[]
QED

Theorem declared_body_abi_targets:
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops ==>
  !target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
    occurs_abi_decode_target target tops
Proof
  simp[occurs_abi_decode_target_def, EXISTS_MEM] >> rpt strip_tac >>
  goal_assum (drule_at Any) >>
  fs[declaration_abi_decode_target_def]
QED
