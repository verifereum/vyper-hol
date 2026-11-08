(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): the pointer twin of S1's
 * target_case_all (targetPlaceSimCases) for the targets a nested pop
 * reaches: a target meeting target_pre whose indices have their pointer
 * judgments (body_base_target_ptr_ok), rooted at a local whose base path
 * every index leaves live (local_target_live), or at a storage or
 * transient variable through pure indices, has target_sim_ptr.
 *
 * TOP-LEVEL:
 *   body_target_sim_ptr
 *)
Theory bodyPtrPopSeamTargetSim
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs
  targetPlaceSim targetPlaceLive vyperPureExpr vyperInterpreter vyperState
  vyperAST

(* Hints, not part of the statement:
   - By induction on the target (targetPlaceSimCasesBase's
     base_assignment_target_induct), as S1's target_case_all: a name
     (target_name_case), a module variable (target_toplevel_case), a
     field (target_attr_case) and an element (target_subscript_case,
     targetSubscriptCase).  The hypotheses hold of each prefix:
     body_base_target_ptr_ok, target_pre (targetPlaceSim's target_pre_sub),
     local_target_live and the indices' purity all recurse into the base.
   - An index's judgments: body_base_target_ptr_ok gives body_expr_ptr_ok
     for an index whose base evaluates, so expr_sim_ptr for the index
     (lower_value) from the base's end state, which meets expr_body_pre
     by target_indices_pre.
   - For a local root, the bounds check's MLOAD reads the length word of
     an array on the base's path, which local_target_live keeps in the
     local's value after the index ran; ghost_inv's val_in_memory for the
     local (whatever its tainted bytes hold) then makes that word
     untainted.  The element's or field's pointer is an ADD on the base's
     pointer, so it keeps the local's site (target_ptr_ok).
   - For a storage root, pure indices leave storage alone
     (targetPlaceLive's nested_pop_eval_base_pure_state,
     nested_pop_eval_base_live), so the length slot the bounds check reads
     is live and stor_taint_ok makes it untainted; a mapping's slot is a
     SHA3 output, with no provenance.
   - bodyPtrPopTargetFactor has the eval_base_place and
     compile_get_target_ptr cuts at a subscript. *)
Theorem body_target_sim_ptr:
  !bt tops ctx cenv cx env es d PG func.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    target_pre cenv cx env bt es /\
    (!id. target_root bt = NameTarget id ==> local_target_live cx id bt) /\
    (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
              EVERY pure_expr (target_indices bt)) ==>
    target_sim_ptr d ctx PG func cenv cx env bt es
Proof
  cheat
QED
