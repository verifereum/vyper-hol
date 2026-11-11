(* Diagnostic of the unstaged, equal-layout RHS ownership interface. *)
Theory assignTupleResidualDispatch
Ancestors
  assignTupleResidualBoundary stmtLowering loweringPosts exprLowering
  vyperAST vyperTypeSystem finite_map compileEnv

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
