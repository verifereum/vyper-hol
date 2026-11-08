(* Storage aggregates have full-capacity footprints even with nested dynamic
   members: val_footprint only shortens top-level bytes and string values. *)
Theory assignBasePtrStorageExtent
Ancestors assignBasePtrStorageTypes exprSimHyps exprSimHypsDefs
  supportedTypes loweringPosts vyperValue vyperTyping exprLowering compileEnv bodySim supportedExprs
  stmtSimReturn assignBasePtrEndpointAudit words arithmetic

Theorem assign_base_nonbytes_footprint:
  !ty tenv tv v.
    ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
    val_footprint tv v = type_memory_size tv
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[is_bytestring_type_def] >>
  Cases_on `v` >> simp[val_footprint_def]
QED

Theorem assign_base_storage_rhs_footprint:
  !cenv e tops ctx cx env es tv v.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes cenv (lowered_value_type cenv e) = val_footprint tv v
Proof
  rpt strip_tac >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  drule assign_base_storage_not_bytestring >> strip_tac >>
  drule_all assign_base_nonbytes_footprint >> simp[]
QED

Theorem assign_base_storage_rhs_bound:
  !cenv e tops bctx cx env pre tv v ctx func es s sa sb op w.
    body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env pre /\
    expr_body_pre cenv cx env e pre /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx (expr_type e) sa sb es v op s /\
    eval_operand op s = SOME w ==>
    w2n w + type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)
Proof
  rpt strip_tac >>
  drule_all assign_base_storage_rhs_footprint >> strip_tac >>
  drule_all expr_val_at_bound >>
  qpat_x_assum `!v. _ = val_footprint tv v` (qspec_then `v` assume_tac) >>
  simp[]
QED

Theorem assign_base_storage_rhs_last_start:
  !cenv e tops bctx cx env pre tv v ctx func es s sa sb op w n.
    body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env pre /\
    expr_body_pre cenv cx env e pre /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
    (!elem k. expr_type e <> ArrayT elem (Dynamic k)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx (expr_type e) sa sb es v op s /\
    eval_operand op s = SOME w /\
    n = type_memory_bytes cenv (expr_type e) DIV 32 ==>
    w2n w + 32*(n-1) < dimword (:256)
Proof
  rpt strip_tac >>
  drule_all assign_base_storage_rhs_bound >> strip_tac >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  irule assign_base_footprint_last_start >>
  qexists_tac `type_memory_bytes cenv (expr_type e)` >> simp[] >>
  `32 * (type_memory_bytes cenv (expr_type e) DIV 32) <=
   type_memory_bytes cenv (expr_type e)` by
    (qspec_then `32` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `type_memory_bytes cenv (expr_type e)` mp_tac) >>
     decide_tac) >>
  gvs[] >> decide_tac
QED
