(* Diagnostic of the unstaged, equal-layout RHS ownership interface. *)
Theory assignTupleResidualDispatch
Ancestors
  assignTupleResidualBoundary stmtLowering loweringPosts exprLowering
  vyperAST vyperTypeSystem finite_map compileEnv
  tuplePlaceSnapshot tuplePlacePrefixCert

(* expr_post supplies expr_val_at, rather than unconditional ownership, for
   this equal-layout internal-call case.  Its local-region alternative is
   not excluded by the interface.  No runtime counterexample is asserted. *)
Triviality equal_layout_unstaged_ownership_diagnostic:
  lowered_value_type cenv (Call (TupleT tys) (IntCall fid) args drv) = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
  0 < val_footprint tv v /\
  (!aid b sz. FLOOKUP sv.vs_allocas aid = SOME (b,sz) /\
     sa.cs_next_id <= aid /\ aid < su.cs_next_id ==> F) ==>
  ~is_memory_view (Call (TupleT tys) (IntCall fid) args drv) /\
  post_value_type cenv (Call (TupleT tys) (IntCall fid) args drv) = TupleT tys /\
  ~expr_val_own cenv cx (TupleT tys) sa su ee v op sv
Proof
  simp[is_memory_view_def, post_value_type_def, is_word_type_def,
       is_bytestring_type_def] >>
  rpt strip_tac >> fs[expr_val_own_def, is_word_type_def] >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> metis_tac[]
QED

(* The call-site post selects the actual layout; only equal layouts may
   retain the borrowed alternative of the snapshot certificate. *)
Theorem tuple_rhs_snapshot_certificate:
  well_typed_expr env e /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = TupleT ltys /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  expr_post ctx func cenv cx e es sa su s0 ee (ArrayV (TupleV vs)) op sv /\
  eval_operand op sv = SOME w ==>
  tuple_place_snapshot cenv cx ee sa.cs_next_id su.cs_next_id
    tys ltys ltvs w sv
Proof
  strip_tac >> drule_all tuple_rhs_lowered_resources >> strip_tac >>
  Cases_on `ltys = tys`
  >- (gvs[] >> drule_all tuple_place_expr_snapshot_cases >>
      simp[tuple_place_snapshot_def, local_val_at_def] >>
      metis_tac[]) >>
  `expr_val_own cenv cx (TupleT ltys) sa su ee
    (ArrayV (TupleV vs)) op sv` by gvs[] >>
  drule_all tuple_place_expr_owned_snapshot >>
  simp[tuple_place_snapshot_def] >> metis_tac[]
QED
