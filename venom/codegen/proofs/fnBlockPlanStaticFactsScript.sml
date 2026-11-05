(* Small interfaces for block-prefix static reasoning. *)
Theory fnBlockPlanStaticFacts
Ancestors
  fnPlanPrefix stackPlanGen stackPlanOps stackPlanTypes

(* A unique available PHI source, once known to be on the join stack,
   excludes every PHI source from the spill map. *)
Theorem phi_unique_source_not_spilled:
  generated_plan_state_wf_marked spill_base ps /\
  (?!v. MEM (Var v) phi.inst_operands /\
         (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)) /\
  (?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) ps.ps_stack) ==>
  !v. MEM (Var v) phi.inst_operands ==> Var v NOTIN FDOM ps.ps_spilled
Proof
  rw[EXISTS_UNIQUE_THM, generated_plan_state_wf_marked_def] >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[]
QED

(* Without a path-local promise, cleanup on a non-must-halt path really
   removes its dead variables.  A RET consumer must establish the promise
   hypothesis as well as exclusion from must_halt_labels. *)
Theorem clean_stack_plan_non_halting_path:
  ~ps.ps_cleanup_promised /\
  ~MEM bb.bb_label (must_halt_labels cfg fn) /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb ==>
  clean_stack_plan liveness cfg fn bb ps =
  popmany_plan
    (MAP Var (FILTER (\v. ~MEM v
      (input_vars_from pred bb.bb_instructions
        (live_vars_at liveness bb.bb_label 0)))
      (live_vars_at liveness pred (LENGTH pred_bb.bb_instructions)))) ps
Proof
  strip_tac >>
  simp[clean_stack_plan_def, cleanup_elision_safe_def,
       cleanup_height_safe_def]
QED
