(* Supported tuple destinations at the residual store boundary. *)
Theory assignTupleResidualBoundary
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim
  supportedStmts targetPlaceSim tupleTargetStoreProps vyperTyping
  vyperAST list stmtLowering loweringPosts compileEnv exprLowering
  vyperTypeSystem memoryLocalRhsProps exprSimHyps assignTuplePtrBodyTargets
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

(* Tuple annotations exclude the byte-producing special forms.  Internal
   calls retain their independently declared return-buffer layout. *)
Theorem tuple_rhs_post_lowered_type:
  !cenv env e ats.
    well_typed_expr env e /\ expr_type e = TupleT ats ==>
    post_value_type cenv e = lowered_value_type cenv e
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[expr_type_def, post_value_type_def, lowered_value_type_def]
  >- (Cases_on `b` >> simp[lowered_value_type_def] >>
      rpt strip_tac >> gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def])
  >- (Cases_on `t0` >> simp[lowered_value_type_def] >>
      rpt strip_tac >> gvs[well_typed_expr_def, type_builtin_result_ok_def, expr_type_def])
  >> Cases_on `c` >>
  simp[post_value_type_def, lowered_value_type_def,
       is_word_type_def, is_bytestring_type_def]
QED

Theorem tuple_rhs_lowered_resources:
  well_typed_expr env e /\ expr_type e = TupleT ats /\
  expr_post ctx func cenv cx e es sa su s0 ee v op sv ==>
  expr_val_rel cx (lowered_value_type cenv e) v op sv /\
  expr_val_at cenv cx (lowered_value_type cenv e) sa su ee v op sv /\
  (lowered_value_type cenv e <> expr_type e ==>
   expr_val_own cenv cx (lowered_value_type cenv e) sa su ee v op sv)
Proof
  strip_tac >> drule_all tuple_rhs_post_lowered_type >>
  strip_tac >> gvs[expr_post_def]
QED

(* An input-interface check, not a new runtime invariant: the suffix retains
   expr_post for its frames, and ptr_buf_ok for full lowered-buffer bounds.
   The annotation tuple ats and lowered type are deliberately independent. *)
Triviality tuple_residual_callsite_resources:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_sim_inv cenv cx env ee /\
  expr_post ctx func cenv cx e es sa su s0 ee v op sv ==>
  expr_body_pre cenv cx env e es /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v /\
  (?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
         value_has_type ltv v /\
         type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv) /\
  expr_val_rel cx (lowered_value_type cenv e) v op sv /\
  expr_val_at cenv cx (lowered_value_type cenv e) sa su ee v op sv /\
  (lowered_value_type cenv e <> expr_type e ==>
   expr_val_own cenv cx (lowered_value_type cenv e) sa su ee v op sv) /\
  (?ats. expr_type e = TupleT ats /\
         assignable_type env.type_defs (TupleT ats) /\
         LIST_REL (\g ty. well_typed_atarget env g ty) gs ats)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule tuple_rhs_body_pre_ptr >> metis_tac[]) >>
  `supported_expr tops e /\ supported_program tops /\
   get_module_code cx NONE = SOME tops /\
   cenv.ce_func_return_type = build_func_return_type tops` by
    gvs[body_inv_def, supported_stmt_def, supported_assignment_def] >>
  drule tuple_targets_typing >> strip_tac >>
  `value_runtime_typed env (expr_type e) v` by
    (irule memory_rhs_read_annotation_typed >> metis_tac[]) >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (irule memory_rhs_read_lowered_typed >> metis_tac[]) >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  drule_all tuple_rhs_lowered_resources >> strip_tac >>
  metis_tac[]
QED

(* Consumer recipe (without redundant exports):
   - memory_rhs_read_annotation_typed and memory_rhs_read_lowered_typed give
     the two independent runtime typings; memory_rhs_runtime_layout at the
     post-RHS expr_sim_inv gives evaluate_type, value_has_type and byte size.
   - In a TupleT sts lowered-dispatch branch, stmtSimReturn.tuple_type_value
     applied to these last facts gives TupleTV stvs, ArrayV (TupleV vs),
     LIST_REL of evaluate_type for sts/stvs, and values_have_types stvs vs.
     tuple_rhs_lowered_resources then describes that buffer at TupleT sts,
     never at annotation offsets. Other lowered-dispatch branches keep the
     generic runtime typing/layout facts; the code cut does not exclude them.
   - Rewrite the RHS pointer post's ptr_val_ok using
     tuple_rhs_post_lowered_type. Keep its ptr_buf_ok unchanged: by
     ptr_buf_ok_def, a nonzero lowered size and eval_operand op sv = SOME w
     give op = Var x, FLOOKUP G x = SOME (b,sz), b <= w2n w and
     w2n w + type_memory_bytes cenv (lowered_value_type cenv e) <= b + sz.
     No ownership of a fresh full-size allocation is inferred from this.
   - tuple_targets_typing is the annotation-indexed component typing relation;
     supported_tuple_component supplies the independent supported-target fact.
     Neither asserts source/destination alignment or preservation across later
     target effects. Those obligations belong to suffix execution. *)
