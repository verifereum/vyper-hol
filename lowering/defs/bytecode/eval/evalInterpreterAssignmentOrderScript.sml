(* Interpreter regressions use the pinned compiler's source AST/layout exports.
   Expected values and storage slots were independently executed with py-evm;
   see assignment-order/oracle/evm-results.json. *)
Theory evalInterpreterAssignmentOrder
Ancestors
  evalAssignmentOrderFrontend vyperSmallStep vyperStorageBackend finite_map While
Libs
  finite_mapLib wordsLib cv_transLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem assignment_cont_pre[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`ss`,`st`,`DoneK`] mp_tac (cj 2 eval_cps_eq) >>
  rw[cont_def] >> CASE_TAC >> CASE_TAC >> gvs[] >>
  rw[Once OWHILE_THM]
QED

Definition assignment_run_def:
  assignment_run cx program st =
    eval_stmts cx (assignment_entry_body program) st
End
val () = cv_auto_trans (REWRITE_RULE [eval_stmts_eq_cont_cps] assignment_run_def);

Definition assignment_slot_def:
  assignment_slot cx st (slot:bytes32) =
    case get_storage_backend cx F st of
    | (INL storage,_) => lookup_storage slot storage
    | (INR _,_) => 0w
End
val () = cv_auto_trans assignment_slot_def;

Theorem assignment_rhs_side_effect_precedes_target:
  let (res,st) = assignment_run x04_assign_sideeffect_order_source_context
        x04_assign_sideeffect_order_source_program assignment_empty_state in
  res = INL () /\ assignment_slot x04_assign_sideeffect_order_source_context st 0w = 2w /\
  assignment_slot x04_assign_sideeffect_order_source_context st
    92458281274488595289803937127152923398167637295201432141969818930235769911599w = 0w /\
  assignment_slot x04_assign_sideeffect_order_source_context st
    105409183525425523237923285454331214386340807945685310246717412709691342439136w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_storage_read_is_delayed:
  let (res,st) = assignment_run assign_delayed_storage_read_source_context
        assign_delayed_storage_read_source_program assignment_empty_state in
  res = INL () /\ assignment_slot assign_delayed_storage_read_source_context st 0w = 1w /\
  assignment_slot assign_delayed_storage_read_source_context st
    92458281274488595289803937127152923398167637295201432141969818930235769911599w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_popped_element_remains_readable:
  FST (assignment_run assign_delayed_popped_read_source_context
    assign_delayed_popped_read_source_program assignment_empty_state) =
  INR (ReturnException (IntV 5))
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_nested_pop_reads_updated_snapshot:
  let (res,st) = assignment_run assign_nested_popped_read_source_context
        assign_nested_popped_read_source_program assignment_empty_state in
  res = INL () /\
  assignment_slot assign_nested_popped_read_source_context st
    24465873643947496235832446106509767096567058095563226156125564318740882468607w = 1w /\
  assignment_slot assign_nested_popped_read_source_context st
    24465873643947496235832446106509767096567058095563226156125564318740882468608w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_assignment_reads_before_rhs:
  let (res,st) = assignment_run g19_aug_rhs_modifies_target_source_context
        g19_aug_rhs_modifies_target_source_program assignment_empty_state in
  res = INL () /\ assignment_slot g19_aug_rhs_modifies_target_source_context st 0w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_storage_write_retains_resolved_slot:
  let initial = SND (set_storage_backend aug_storage_shrink_source_context F
        (update_storage 0w 1w (update_storage 1w 5w empty_storage)) assignment_empty_state) in
  let (res,st) = assignment_run aug_storage_shrink_source_context
        aug_storage_shrink_source_program initial in
  res = INL () /\ assignment_slot aug_storage_shrink_source_context st 0w = 0w /\
  assignment_slot aug_storage_shrink_source_context st 1w = 10w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_memory_shrink_succeeds:
  FST (assignment_run aug_memory_shrink_source_context
    aug_memory_shrink_source_program assignment_empty_state) =
  INR (ReturnException (IntV 0))
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_memory_append_overwrites_stale_slot:
  FST (assignment_run aug_memory_shrink_append_source_context
    aug_memory_shrink_append_source_program assignment_empty_state) =
  INR (ReturnException (IntV 7))
Proof
  CONV_TAC cv_eval
QED

Definition assignment_pop_argument_state_def:
  assignment_pop_argument_state =
    SND (push_scope_with_var "a" (BaseTV (UintT 256)) (IntV 5) assignment_empty_state)
End
val () = cv_auto_trans assignment_pop_argument_state_def;

Theorem assignment_pop_precedes_target_bounds_check:
  FST (assignment_run x03_assign_elem_from_pop_source_context
    x03_assign_elem_from_pop_source_program assignment_pop_argument_state) =
    INR (Error (RuntimeError "evaluate_subscripts array_index"))
Proof
  CONV_TAC cv_eval
QED
