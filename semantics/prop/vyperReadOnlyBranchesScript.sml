(* Branch boundaries for the read-only evaluator induction. *)
Theory vyperReadOnlyBranches
Ancestors
  vyperReadOnlyTargets vyperMachineFrame vyperCallOutcomeFrame
  vyperStatePreservation vyperInterpreter vyperState vyperTypeContract
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

Theorem machine_frame_return[simp]:
  state_rel_frame machine_frame (vyperState$return x)
Proof
  simp[state_rel_frame_def, return_def]
QED

(* A successful local target permits only a memory mutation. *)
Theorem machine_frame_local_place_effect:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) /\
  (!id path. state_rel_frame machine_frame (k (MemoryPlace id path))) ==>
  state_rel_frame machine_frame
    (do p <- eval_target_place cx bt; k p od)
Proof
  strip_tac >> match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[] >> rpt strip_tac >>
  drule_all eval_target_place_local >> strip_tac >> gvs[]
QED

Theorem machine_frame_stmt_assign:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_expr cx e) /\
  (!s r t. eval_expr cx e s = (INL r,t) ==>
     state_rel_frame machine_frame (eval_target_place cx bt)) ==>
  state_rel_frame machine_frame (eval_stmt cx (Assign (BaseTarget bt) e))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[] >> rpt strip_tac >> simp[] >>
  ho_match_mp_tac machine_frame_local_place_effect >> simp[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >>
  match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_write_memory_place]
QED

Theorem machine_frame_expr_pop:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) ==>
  state_rel_frame machine_frame (eval_expr cx (Pop ty bt))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  ho_match_mp_tac machine_frame_local_place_effect >>
  simp[machine_frame_pop_memory_place]
QED

Theorem machine_frame_abi_arguments:
  state_rel_frame machine_frame (eval_abi_exprs cx es) ==>
  state_rel_frame machine_frame
    (do mark <- mark_abi_captures;
        finally (do args <- eval_abi_exprs cx es; stage_abi_operands cx args od)
          (release_abi_captures mark)
     od)
Proof
  strip_tac >> match_mp_tac machine_frame_bind >> simp[machine_frame_abi] >>
  gen_tac >> irule state_rel_frame_finally >>
  simp[machine_frame_def, machine_frame_abi] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_abi]
QED

Theorem machine_frame_abi_expr_pop:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) ==>
  state_rel_frame machine_frame (eval_abi_expr cx (Pop ty bt))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  ho_match_mp_tac machine_frame_local_place_effect >> simp[] >>
  rpt gen_tac >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_abi_place] >> gen_tac >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_abi] >> gen_tac >>
  simp[ignore_bind_def] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_pop_memory_place, machine_frame_return]
QED

Theorem machine_frame_stmt_append:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) /\
  (!s p t. eval_target_place cx bt s = (INL p,t) ==>
     state_rel_frame machine_frame (eval_expr cx e)) ==>
  state_rel_frame machine_frame (eval_stmt cx (Append bt e))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[] >> rpt strip_tac >>
  drule_all eval_target_place_local >> strip_tac >> gvs[] >>
  match_mp_tac machine_frame_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_append_memory_place]
QED

Theorem machine_frame_stmt_augassign:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) /\
  (!s p t u cur w a ptv b.
     eval_target_place cx bt s = (INL p,t) /\
     read_place cx p u = (INL cur,w) /\
     place_type_value cx p a = (INL ptv,b) ==>
     state_rel_frame machine_frame (eval_expr cx e)) ==>
  state_rel_frame machine_frame (eval_stmt cx (AugAssign ty bt bop e))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[] >> rpt strip_tac >>
  drule_all eval_target_place_local >> strip_tac >> gvs[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[machine_frame_read_place] >> rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[machine_frame_place_type_value] >> rpt strip_tac >> simp[] >>
  match_mp_tac machine_frame_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_read_result] >>
  gen_tac >> simp[] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives, machine_frame_write_memory_place]
QED

Theorem machine_frame_assign_tuple_base:
  ~toplevel_target bt /\
  state_rel_frame machine_frame (eval_target_place cx bt) ==>
  state_rel_frame machine_frame (assign_tuple_targets cx (BaseTarget bt) v)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  ho_match_mp_tac machine_frame_local_place_effect >>
  simp[machine_frame_write_memory_place]
QED

Theorem machine_frame_stmt_tuple_assign:
  state_rel_frame machine_frame (eval_expr cx e) /\
  (!s r t u v w. eval_expr cx e s = (INL r,t) /\
     read_result cx r u = (INL v,w) ==>
     state_rel_frame machine_frame (assign_tuple_targets cx (TupleTarget gs) v)) ==>
  state_rel_frame machine_frame (eval_stmt cx (Assign (TupleTarget gs) e))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[] >> rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[machine_frame_read_result] >> rpt strip_tac >> metis_tac[]
QED

Theorem machine_frame_loop_cleanup:
  state_rel_frame machine_frame (eval_stmts cx body) ==>
  state_rel_frame machine_frame
    (finally (try (do eval_stmts cx body; return F od)
                  handle_loop_exception) pop_scope)
Proof
  strip_tac >> irule state_rel_frame_finally >>
  simp[machine_frame_def, machine_frame_primitives] >>
  irule state_rel_frame_try >> simp[machine_frame_def, machine_frame_handlers] >>
  irule machine_frame_sequence >> simp[]
QED

Theorem machine_frame_for_cons:
  (!s x t. push_scope_with_var nm tyv v s = (INL x,t) ==>
     state_rel_frame machine_frame (eval_stmts cx body)) /\
  (!s x t u broke w.
     push_scope_with_var nm tyv v s = (INL x,t) /\
     finally (try (do eval_stmts cx body; return F od)
                   handle_loop_exception) pop_scope u = (INL broke,w) /\
     ~broke ==> state_rel_frame machine_frame (eval_for cx tyv nm body vs)) ==>
  state_rel_frame machine_frame (eval_for cx tyv nm body (v::vs))
Proof
  strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >>
  suspend "loop_continuation"
QED

Resume machine_frame_for_cons[loop_continuation]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  conj_tac >- suspend "loop_tail" >>
  simp[machine_frame_def] >> irule (SRULE [ignore_bind_def] machine_frame_loop_cleanup) >>
  qpat_x_assum `!s x t. _ ==> state_rel_frame _ (eval_stmts _ _)` drule >> simp[]
QED

Resume machine_frame_for_cons[loop_tail]:
  rpt strip_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >>
  fs[ignore_bind_def] >> metis_tac[]
QED

Finalise machine_frame_for_cons

Theorem machine_frame_stmt_for:
  (!tenv s tyv t. tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) ==>
     state_rel_frame machine_frame (eval_iterator cx it)) /\
  (!tenv s tyv t u vs w a x b.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
     eval_iterator cx it u = (INL vs,w) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" a = (INL x,b) ==>
     state_rel_frame machine_frame (eval_for cx tyv id body vs)) ==>
  state_rel_frame machine_frame (eval_stmt cx (For id typ it n body))
Proof
  strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >>
  suspend "iterator_continuation"
QED

Resume machine_frame_stmt_for[iterator_continuation]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  conj_tac >- suspend "bound_continuation" >>
  simp[machine_frame_def] >> metis_tac[]
QED

Resume machine_frame_stmt_for[bound_continuation]:
  rpt strip_tac >> BETA_TAC >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> metis_tac[]
QED

Finalise machine_frame_stmt_for

Theorem machine_frame_custom_error_tail:
  state_rel_frame machine_frame (eval_exprs cx es) ==>
  state_rel_frame machine_frame
    (do vs <- eval_exprs cx es;
        data <- lift_option (build_custom_error_data (get_tenv cx) id tys vs)
                    "custom error encoding";
        raise (Error (RevertData data)) od)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]
QED

Theorem machine_frame_stmt_custom_error:
  (!id positional kwargs tops params es.
     err = CustomError id positional kwargs /\
     get_module_code cx (FST id) = SOME tops /\
     lookup_custom_error_args_in (SND id) tops = SOME params /\
     order_custom_error_args params err = SOME es ==>
     state_rel_frame machine_frame (eval_exprs cx es)) ==>
  state_rel_frame machine_frame (eval_stmt cx (Raise (RaiseCustomError err)))
Proof
  Cases_on `err` >> strip_tac >> simp[Once evaluate_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[machine_frame_primitives] >>
  irule machine_frame_custom_error_tail >> metis_tac[]
QED

Theorem machine_frame_push_function:
  state_rel_frame machine_frame (push_function src_fn sc cx)
Proof
  simp[state_rel_frame_def, push_function_def, return_def]
QED

Theorem machine_frame_pop_function:
  state_rel_frame machine_frame (pop_function prev)
Proof
  simp[pop_function_def, machine_frame_primitives]
QED

Theorem machine_frame_internal_lock:
  state_rel_frame machine_frame
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot T
     else return ())
Proof
  Cases_on `nr` >> simp[] >> Cases_on `cx.nonreentrant_slot` >>
  simp[machine_frame_view_lock, machine_frame_primitives]
QED

Theorem machine_frame_switch_BoolV:
  state_rel_frame machine_frame f /\ state_rel_frame machine_frame g ==>
  state_rel_frame machine_frame (switch_BoolV cx v f g)
Proof
  strip_tac >> simp[switch_BoolV_def] >>
  match_mp_tac machine_frame_bind >> conj_tac
  >- simp[machine_frame_read_result] >>
  gen_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> simp[machine_frame_primitives]
QED

Theorem machine_frame_reads:
  state_rel_frame machine_frame (lookup_global cx src id) /\
  state_rel_frame machine_frame (lookup_flag_mem cx nsid mid) /\
  state_rel_frame machine_frame (read_storage_slot cx tr slot ty) /\
  state_rel_frame machine_frame (result_array_length cx r)
Proof
  simp[state_rel_frame_result] >> metis_tac[lookup_global_state,
    lookup_flag_mem_state, read_storage_slot_state,
    result_array_length_state, machine_frame_refl]
QED

Theorem machine_frame_assign_tuple:
  (!vs. v = ArrayV (TupleV vs) ==>
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs)) ==>
  state_rel_frame machine_frame (assign_tuple_targets cx (TupleTarget gs) v)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[machine_frame_primitives] >>
  Cases_on `a` >> simp[machine_frame_primitives]
QED

Theorem machine_frame_assign_tuple_cons:
  state_rel_frame machine_frame (assign_tuple_targets cx g v) /\
  (!s r t. assign_tuple_targets cx g v s = (INL r,t) ==>
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs)) ==>
  state_rel_frame machine_frame (assign_tuple_target_list cx (g::gs) (v::vs))
Proof
  strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >> simp[] >> metis_tac[]
QED
