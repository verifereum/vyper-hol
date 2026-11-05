(* Typed runtime immutable forcing and its actual global-name consumer. *)
Theory bodyToplevelAggregateMemory
Ancestors
  exprSimSource
  bodyImmutableUnwrapMemory bodyToplevelWordMemory bodyToplevelMemory
  bodyMemoryPreds bodyMemoryDefs exprSimHyps exprSimUnwrap exprSimDefs
  exprLowering exprLoweringProps compileEnv context fragExecMem fragExec
  vyperAST vyperValue vyperInterpreter vyperState loweringSlice exprSimLeaves
  accountsRelProps vyperTypeGlobalLookupSoundness vyperTypeSystem vyperTypeCallGraph
  vyperEvalExprPreservesScopesDom

Theorem body_location_code_aggregate_sim_mem:
  expr_body_pre cenv cx env e es /\
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  ~is_word_type (expr_type e) /\ ~cenv.ce_is_ctor /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
    !sa. ?p. compile_expr cenv ty e sa = (LocatedValue (expr_type e) p,sa) /\
      p.ptr_location = LocCode /\
      (!x. p.ptr_operand = Var x ==> not_fresh_at sa x)) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  cheat
QED

Theorem compile_toplevel_immutable_aggregate_runtime_sim_mem:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
    ~is_word_type ann /\ ~cenv.ce_is_ctor /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  cheat
QED

Theorem body_toplevel_immutable_mem_case:
  !cx ann src id ts.
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    body_expr_mem_ok cx (TopLevelName ann (src,id))
Proof
  cheat
QED

