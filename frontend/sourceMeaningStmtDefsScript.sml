Theory sourceMeaningStmtDefs
Ancestors
  sourceMeaningRuntime sourceModuleStmt sourceModuleDefs sourceSyntax
  sourceMeaningDefs vyperInterpreter vyperState vyperAST vyperValue vyperContext list

(* Independent body denotations. No runtime statement/expression evaluator is
   used here. Runtime store primitives retain errors, pointers and full state. *)
Datatype:
  source_body_meaning = SBM_Pass
    | SBM_Return (source_meaning option)
    | SBM_Expr source_meaning
    | SBM_Local string type source_meaning
    | SBM_Assign string source_meaning
    | SBM_If source_meaning (source_body_meaning list) (source_body_meaning list)
End

Definition source_meaning_run_def:
  source_meaning_run cx names SBM_Pass = return () /\
  source_meaning_run cx names (SBM_Return NONE) = raise (ReturnException NoneV) /\
  source_meaning_run cx names (SBM_Return (SOME e)) = do
    tv <- source_meaning_eval cx names e;
    v <- materialise cx tv;
    raise (ReturnException v)
  od /\
  source_meaning_run cx names (SBM_Expr e) = do
    tv <- source_meaning_eval cx names e;
    type_check (~is_HashMapRef tv) "Expr HashMapRef"
  od /\
  source_meaning_run cx names (SBM_Local id ty e) = do
    tyv <- lift_option_type (evaluate_type (get_tenv cx) ty) "AnnAssign evaluate_type";
    tv <- source_meaning_eval cx names e;
    v <- materialise cx tv;
    new_variable id tyv v
  od /\
  source_meaning_run cx names (SBM_Assign id e) = do
    sc <- get_scopes;
    type_check (IS_SOME (lookup_scopes id sc)) "NameTarget not in scope";
    tv <- source_meaning_eval cx names e;
    v <- materialise cx tv;
    assign_target cx (BaseTargetV (ScopedVar id) []) (Replace v);
    return ()
  od /\
  source_meaning_run cx names (SBM_If c yes no) = do
    tv <- source_meaning_eval cx names c;
    push_scope;
    finally (switch_BoolV tv
      (source_meaning_runs cx names yes) (source_meaning_runs cx names no)) pop_scope
  od /\
  source_meaning_runs cx names [] = return () /\
  source_meaning_runs cx names (s::ss) = do
    source_meaning_run cx names s;
    source_meaning_runs cx names ss
  od
Termination
  WF_REL_TAC `measure (\x. case x of INL (cx,names,s) => source_body_meaning_size s
    | INR (cx,names,ss) => list_size source_body_meaning_size ss)` >> simp[]
End

(* Original-source rules. The source type resolver is shared, not a runtime
   checker or elaboration success test. Locals are indexed by declaration path;
   the supported instance denotes local variables by LAST of that identity. *)
Inductive source_meaning_body:
[empty:]
  source_meaning_bodies types ctx ret [] [] types ctx
[cons:]
  source_meaning_body types ctx ret s m next_types next /\
  source_meaning_bodies next_types next ret ss ms last_types last ==>
  source_meaning_bodies types ctx ret (s::ss) (m::ms) last_types last
[pass:]
  source_meaning_body types ctx ret SS_Pass SBM_Pass types ctx
[return_none:]
  source_meaning_body types ctx ret (SS_Return NONE) (SBM_Return NONE) types ctx
[return_value:]
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants ret e em ==>
  source_meaning_body types ctx ret (SS_Return (SOME e)) (SBM_Return (SOME em)) types ctx
[declare_local:]
  source_module_type ctx annotation = SM_Ok ty /\
  source_module_interface_fields ctx annotation = NONE /\
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants ty e em ==>
  source_meaning_body types ctx ret (SS_AnnAssign name annotation (SOME e))
    (SBM_Local name ty em) ((ctx.sm_owner ++ [name],ty)::types)
    (source_module_local ctx name ty T)
[assign:]
  source_resolve_name ctx.sm_scopes ctx.sm_table [name] = SOME (path,SR_Dynamic) /\
  ALOOKUP types path = SOME ty /\
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants ty e em ==>
  source_meaning_body types ctx ret (SS_Assign (SX_Name name) e)
    (SBM_Assign (LAST path) em) types ctx
[branch:]
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants (BaseT BoolT) c cm /\
  source_meaning_bodies types ctx ret yes ym yt yc /\
  source_meaning_bodies types ctx ret no nm nt nc ==>
  source_meaning_body types ctx ret (SS_If c yes no) (SBM_If cm ym nm) types ctx
End
