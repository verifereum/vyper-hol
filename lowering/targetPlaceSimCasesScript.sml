(*
 * The target/place judgment: fields, subscripts, every target (#636,
 * Places)
 *
 * The steps of targetPlaceSim's judgment.  A field adds its offset to the
 * base's pointer with one ADD: struct_field_offset bytes for a local's
 * place, struct_field_offset_slots slots for a storage one, where the
 * source extends the base's place by the field.  The shared facts and the
 * field step are in targetPlaceSimCasesBase; an element of an array or a
 * mapping is targetSubscriptCase's target_subscript_case.
 *
 * TOP-LEVEL:
 *   target_attr_case       — a field: the base's pointer plus the field's
 *                          byte offset (memory) or slot offset (storage)
 *   target_subscript_case  — an element of an array or a mapping
 *                          (targetSubscriptCase)
 *   target_case_all        — every target, by induction, from the indices'
 *                          judgments
 *   target_idx_case_ok     — the indices' judgments from
 *                          expr_ok, with no internal calls
 *   target_place_sim       — the judgment for eval_target_place: the place
 *                          of a target typed by a value type
 *   eval_base_place_sim_inv — expr_sim_inv after the target's evaluation
 *   place_ptr_rel_vars_frame, target_post_add — the pointer and the post
 *                          through code that writes only fresh variables
 *
 * Helpers: expr_exit_INR_type,
 *   alookup_fields_args, attribute_type_struct_field,
 *   extend_storage_place_attr, target_field_offset, target_field_type,
 *   compile_get_target_ptr_attr, extend_place_memory_attr,
 *   struct_field_slot_alookup, target_post_inst_idx, target_attr_add_frag,
 *   attr_place_step, base_assignment_target_induct
 *)

Theory targetPlaceSimCases
Ancestors
  targetSubscriptCase targetPlaceSimCasesBase targetPlaceLive
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs gasContext gasOutcome gasSummary gasExemptCert
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc
  venomState venomInst
Libs
  pairLib

(* ===== Every target ===== *)

Theorem target_case_all:
  !bt nocalls ctx func cenv cx.
    target_idx_case nocalls ctx func cenv cx bt ==>
    target_case nocalls ctx func cenv cx bt
Proof
  cheat
QED

(* With no internal calls, the indices' judgments follow from expr_ok, as
   compile_expr_sim's induction hypotheses give it. *)
Theorem target_idx_case_ok:
  !bt nocalls ctx func cenv cx.
    int_calls_target bt = [] /\
    (!e. MEM e (target_indices bt) ==> expr_ok cenv e) ==>
    target_idx_case nocalls ctx func cenv cx bt
Proof
  cheat
QED

(* ===== Places ===== *)

(* eval_target_place's results that lower to the target's code: a place,
   or an error the code raises too. *)
Definition target_place_res_ok_def:
  target_place_res_ok (res : place + exception) <=>
    (?p. res = INL p) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

(* eval_target_place reads the base's place. *)
Theorem eval_target_place_bind[local]:
  eval_target_place cx bt = bind (eval_base_place cx bt) get_place
Proof
  cheat
QED

(* The judgment for eval_target_place: a target typed by a value type
   evaluates to a place, at the pointer. *)
Theorem target_place_sim:
  !ctx func cenv cx env bt es ty sa sb r s0.
    target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_target_place cx bt) (es, s0)
      (\res ee t. ?p. res = INL p /\
        target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED
