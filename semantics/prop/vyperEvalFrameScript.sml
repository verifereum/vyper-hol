(* Evaluator frame theorem.  A transitive relation R on evaluation states
 * that holds across every machine-invisible step (machine_frame) and across
 * each state-changing primitive the evaluator calls relates the start and end
 * states of every evaluator function. *)
Theory vyperEvalFrame
Ancestors
  pair vyperAST vyperMachineFrame vyperCallOutcomeFrame
  vyperCreateFrame vyperStatePreservation vyperInterpreter vyperState
Libs monadsyntax evalWalkLib

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem state_rel_frame_machine:
  (!s t. machine_frame s t ==> R s t) /\ state_rel_frame machine_frame f ==>
  state_rel_frame R f
Proof
  simp[state_rel_frame_def]
QED

val R_tm = mk_var ("R", type_of ``machine_frame``);

(* Each leaf is indexed under its conclusion with machine_frame generalised to
   R, and applied through state_rel_frame_machine. *)
val eval_frame_net =
  let
    val rules = [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally]
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads]
    fun leaf th = (subst [``machine_frame`` |-> R_tm] (concl th),
      MATCH_MP_TAC state_rel_frame_machine >> conj_tac >-
        first_assum ACCEPT_TAC >> MATCH_ACCEPT_TAC th)
  in evalWalkLib.walk_net (map SPEC_ALL rules)
       (map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;

val EVAL_FRAME_IH_TAC = evalWalkLib.IH_TAC {stop = K false,
  normalise = SIMP_RULE bool_ss
    [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
     lock_if_nr_def, unlock_if_nr_def]};

val EVAL_FRAME_STEP = evalWalkLib.STEP {net = eval_frame_net, at = RAND_CONV,
  unfolds = [switch_BoolV_def, ignore_bind_def],
  intros = [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac, conj_tac,
    CONV_TAC (RAND_CONV ETA_CONV),
    CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
      (pair_case_thm :: UNCURRY :: List.map ASSUME (List.filter is_eq asl)) (asl,w))],
  fallbacks = [EVAL_FRAME_IH_TAC, evalWalkLib.NORMALISE_IH_TAC EVAL_FRAME_IH_TAC]};

val EVAL_FRAME_CASE = evalWalkLib.EVAL_CASE (rpt strip_tac) EVAL_FRAME_STEP;

Theorem eval_state_rel_frame:
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s t. machine_frame s t ==> R s t) /\
  (!cx p v. state_rel_frame R (write_place cx p v)) /\
  (!cx p v. state_rel_frame R (append_place cx p v)) /\
  (!cx p. state_rel_frame R (pop_place cx p)) /\
  (!ev. state_rel_frame R (push_log ev)) /\
  (!a b n. state_rel_frame R (transfer_value a b n)) /\
  (!cx g vs. state_rel_frame R (eval_send cx g vs)) /\
  (!cx st sk sig opts vs. state_rel_frame R (eval_ext_call cx st sk sig opts vs)) /\
  (!cx fl a d m g. state_rel_frame R (eval_raw_call cx fl a d m g)) /\
  (!cx k h r ts vs cs. state_rel_frame R (eval_create cx k h r ts vs cs)) /\
  (!a n v. state_rel_frame R (acquire_nonreentrant_lock a n v)) /\
  (!a n. state_rel_frame R (release_nonreentrant_lock a n)) ==>
  (!cx s. state_rel_frame R (eval_stmt cx s)) /\
  (!cx ss. state_rel_frame R (eval_stmts cx ss)) /\
  (!cx it. state_rel_frame R (eval_iterator cx it)) /\
  (!cx tyv nm body vs. state_rel_frame R (eval_for cx tyv nm body vs)) /\
  (!cx e. state_rel_frame R (eval_expr cx e)) /\
  (!cx es. state_rel_frame R (eval_exprs cx es)) /\
  (!cx t. state_rel_frame R (eval_base_place cx t)) /\
  (!cx t. state_rel_frame R (eval_target_place cx t)) /\
  (!cx g v. state_rel_frame R (assign_tuple_targets cx g v)) /\
  (!cx gs vs. state_rel_frame R (assign_tuple_target_list cx gs vs)) /\
  (!cx es. state_rel_frame R (eval_expr_results cx es))
Proof
  strip_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- (EVAL_FRAME_CASE >> metis_tac[])
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >- EVAL_FRAME_CASE
  >> EVAL_FRAME_CASE
QED
