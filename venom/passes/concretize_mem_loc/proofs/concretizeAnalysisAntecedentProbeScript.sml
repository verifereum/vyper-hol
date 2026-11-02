(* Audit of the bounded examples: no complete stage counterexample claimed. *)
Theory concretizeAnalysisAntecedentProbe
Ancestors concretizeAnalysisBoundaryProbe o1PassContract
Libs wordsLib

Theorem boundary_loop_entry_mismatch:
  fn_entry_label boundary_loop <> SOME boundary_loop.fn_name
Proof
  EVAL_TAC
QED

Theorem boundary_late_entry_mismatch:
  fn_entry_label boundary_late <> SOME boundary_late.fn_name
Proof
  EVAL_TAC
QED

Theorem boundary_loop_not_stage_shape:
  ~o1_ctx_shape boundary_ctx
Proof
  simp[o1_ctx_shape_def, boundary_ctx_def,
       venomInstTheory.mk_venom_context_def, o1_fn_shape_def,
       unitShapeDefsTheory.fn_shape_ok_def, boundary_loop_entry_mismatch]
QED

Theorem boundary_late_not_stage_shape:
  ~o1_ctx_shape boundary_late_ctx
Proof
  simp[o1_ctx_shape_def, boundary_late_ctx_def,
       venomInstTheory.mk_venom_context_def, o1_fn_shape_def,
       unitShapeDefsTheory.fn_shape_ok_def, boundary_late_entry_mismatch]
QED
