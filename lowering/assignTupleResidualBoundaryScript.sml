(* Supported tuple destinations at the residual store boundary. *)
Theory assignTupleResidualBoundary
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim
  supportedStmts targetPlaceSim tupleTargetStoreProps vyperTyping
  vyperAST list stmtLowering loweringPosts compileEnv exprLowering
Libs
  monadsyntax

Theorem supported_target_local_live:
  !bt tops bindings cx id.
    supported_target tops bindings bt /\ target_root bt = NameTarget id ==>
    local_target_live cx id bt
Proof
  Cases >> simp[supported_target_def, target_root_def, local_target_live_def] >>
  rpt gen_tac >> Cases_on `b` >>
  simp[supported_target_def, target_root_def, local_target_live_def]
QED

Theorem supported_tuple_component:
  supported_assignment tops bindings (TupleTarget gs) e /\ MEM g gs ==>
  ?bt. g = BaseTarget bt /\ supported_target tops bindings bt
Proof
  simp[supported_assignment_def] >> strip_tac >>
  fs[EVERY_MEM] >> first_x_assum drule >> Cases_on `g` >> simp[]
QED

Theorem supported_target_sim_ptr_from_contract:
  (!bt env es.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    target_pre cenv cx env bt es /\
    (!id. target_root bt = NameTarget id ==> local_target_live cx id bt) ==>
    target_sim_ptr d ctx PG func cenv cx env bt es) /\
  body_inv tops ctx cenv cx /\
  supported_target tops bindings bt /\ body_base_target_ptr_ok cx bt /\
  target_pre cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env bt es
Proof
  strip_tac >> first_x_assum irule >> simp[] >>
  metis_tac[supported_target_local_live]
QED

Theorem supported_subscript_target_base:
  supported_target tops bindings (SubscriptTarget bt key) ==>
  ?nsid. bt = TopLevelNameTarget nsid /\
    supported_subscript_base tops nsid /\ supported_expr tops key
Proof
  Cases_on `bt` >> simp[supported_target_def]
QED

(* Preserve the actual lowered source type: annotated and ABI-return tuple
   layouts need not coincide. Staging and load decomposition follows later. *)
Theorem assign_tuple_residual_code_cut:
  stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (c,sf) ==>
  c = cenv /\
  ?vv sc op su.
    compile_expr cenv (expr_type e) e sa = (vv,sc) /\
    unwrap_value cenv vv sc = (op,su) /\
    compile_tuple_unpack cenv (lowered_value_type cenv e)
      (is_memory_view e /\ vv_location vv = SOME LocMemory) gs op su = ((),sf)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sc)` >> simp[] >>
  Cases_on `unwrap_value cenv vv sc` >>
  rename1 `unwrap_value _ _ _ = (op,su)` >> simp[] >>
  Cases_on `compile_tuple_unpack cenv (lowered_value_type cenv e)
    (is_memory_view e /\ vv_location vv = SOME LocMemory) gs op su` >>
  rename1 `_ = (u,sf1)` >> Cases_on `u` >> simp[] >>
  strip_tac >> gvs[]
QED
