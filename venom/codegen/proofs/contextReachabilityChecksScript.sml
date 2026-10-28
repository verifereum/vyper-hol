(* Kernel probes for actual exec_block/run_blocks/run_context/INVOKE states.
   These are finite interface regressions, not a general reachability proof. *)
Theory contextReachabilityChecks
Ancestors
  contextReachability contextRawReachable contextCodegenRelProps contextCodegenRel
  venomExecSemantics venomInst
  venomState list finite_map words integer_word
Libs wordsLib

Definition check_assign_def:
  check_assign = instruction 0 ASSIGN [Lit 7w] ["x"]
End
Definition check_stop_def:
  check_stop = instruction 1 STOP [] []
End
Definition check_phi_def:
  check_phi = instruction 2 PHI [Label "entry"; Lit 9w] ["p"]
End
Definition check_jump_def:
  check_jump = instruction 3 JMP [Label "join"] []
End
Definition check_fn_def:
  check_fn = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions := [check_assign; check_jump] |>;
     <| bb_label := "join"; bb_instructions := [check_phi; check_stop] |>]
End
Definition check_ctx_def:
  check_ctx = mk_venom_context [check_fn] (SOME "main")
End
Definition check_start_def:
  check_start = init_venom_state "entry"
End
Definition check_next_def:
  check_next = (update_var "x" 7w check_start) with vs_inst_idx := 1
End
Definition check_join_def:
  check_join = check_next with
    <| vs_prev_bb := SOME "entry"; vs_current_bb := "join"; vs_inst_idx := 0 |>
End
Definition check_post_phi_def:
  check_post_phi = (update_var "p" 9w check_join) with vs_inst_idx := 1
End

Theorem assign_visited_states:
  active_inst check_fn check_assign check_start /\
  ~is_terminator check_assign.inst_opcode /\
  step_inst 0 check_ctx check_assign check_start =
    OK (update_var "x" 7w check_start) /\
  active_inst check_fn check_jump check_next /\
  ((update_var "x" 7w check_start) with
      vs_inst_idx := SUC check_start.vs_inst_idx) = check_next /\
  ~active_inst check_fn check_jump (update_var "x" 7w check_start)
Proof
  simp[active_inst_def, check_fn_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem closed_assign_postincrement:
  reachability_closed Inv check_ctx /\
  Inv check_ctx check_fn check_assign check_start ==>
  Inv check_ctx check_fn check_jump check_next
Proof
  strip_tac >>
  mp_tac assign_visited_states >> strip_tac >>
  metis_tac[reachability_closed_next]
QED

Theorem jump_and_phi_visited_states:
  active_inst check_fn check_jump check_next /\
  is_terminator check_jump.inst_opcode /\
  step_inst 0 check_ctx check_jump check_next = OK check_join /\
  ~check_join.vs_halted /\
  enters_block check_fn check_join check_post_phi /\
  active_inst check_fn check_stop check_post_phi /\
  ~active_inst check_fn check_phi check_post_phi /\
  lookup_var "p" check_post_phi = SOME 9w
Proof
  simp[active_inst_def, check_fn_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem closed_jump_post_phi:
  reachability_closed Inv check_ctx /\
  Inv check_ctx check_fn check_jump check_next ==>
  Inv check_ctx check_fn check_stop check_post_phi
Proof
  strip_tac >>
  mp_tac jump_and_phi_visited_states >> strip_tac >>
  drule_all reachability_closed_block >> simp[]
QED

(* A PHI failure, missing label, or empty block has no active entry point.
   The API does not demand an invariant at a PHI or at a failed step. *)
Theorem entry_failure_probes:
  ~(?s1. enters_block check_fn
    (check_join with vs_prev_bb := NONE) s1) /\
  ~(?s1. enters_block check_fn (init_venom_state "missing") s1) /\
  fn_entry_inv (\ctx fn inst s. F) check_ctx
    (mk_raw_function "empty" [<| bb_label := "empty"; bb_instructions := [] |>])
    (init_venom_state "empty")
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem initialized_entry_visited_state:
  enters_block check_fn check_start check_start /\
  active_inst check_fn check_assign check_start /\
  ((check_start with
      <| vs_prev_bb := SOME "stale"; vs_current_bb := "stale"; vs_inst_idx := 99 |>)
     with <| vs_prev_bb := NONE; vs_current_bb := "entry"; vs_inst_idx := 0 |>) =
    check_start
Proof
  simp[active_inst_def, check_fn_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem check_package_normalized:
  codegen_reachability_package Inv check_ctx
    (check_start with
      <| vs_prev_bb := prev; vs_current_bb := lbl; vs_inst_idx := idx |>) <=>
  reachability_closed Inv check_ctx /\ fn_entry_inv Inv check_ctx check_fn check_start
Proof
  simp[codegen_reachability_package_def, check_ctx_def, check_start_def,
       init_venom_state_def, mk_venom_context_def, lookup_function_def, FIND_thm,
       check_fn_def, mk_raw_function_def, fn_entry_label_def, entry_block_def]
QED

Theorem package_initialized_entry:
  codegen_reachability_package Inv check_ctx
    (check_start with
      <| vs_prev_bb := SOME "stale"; vs_current_bb := "stale"; vs_inst_idx := 99 |>)
  ==> Inv check_ctx check_fn check_assign check_start
Proof
  simp[check_package_normalized] >> strip_tac >>
  mp_tac initialized_entry_visited_state >> strip_tac >>
  drule_all fn_entry_inv_active >> simp[]
QED

(* A nonempty normal entry excludes the always-false invariant. An empty
   entry is intentionally permitted by the exact planned API. *)
Theorem package_false_normal_entry:
  ~codegen_reachability_package (\ctx fn inst s. F) check_ctx
    (check_start with
      <| vs_prev_bb := SOME "stale"; vs_current_bb := "stale"; vs_inst_idx := 99 |>)
Proof
  strip_tac >> drule package_initialized_entry >> simp[]
QED

(* The raw-reachable package is non-vacuous: from a stale initial position it
   reaches the post-PHI STOP through an ordinary step and a block entry. *)
Theorem raw_reachable_post_phi:
  raw_reachable
    (check_start with
      <| vs_prev_bb := SOME "stale"; vs_current_bb := "stale"; vs_inst_idx := 99 |>)
    check_ctx check_fn check_stop check_post_phi
Proof
  irule closed_jump_post_phi >> simp[raw_reachable_closed] >>
  irule closed_assign_postincrement >> simp[raw_reachable_closed] >>
  irule package_initialized_entry >>
  simp[raw_reachable_package_iff, check_ctx_def, mk_venom_context_def,
       lookup_function_def, FIND_thm, check_fn_def, mk_raw_function_def,
       fn_entry_label_def, entry_block_def]
QED

Theorem run_context_initialization_and_phi:
  run_context 2 check_ctx
    (check_start with
      <| vs_prev_bb := SOME "stale"; vs_current_bb := "stale"; vs_inst_idx := 99 |>) =
  Halt (check_post_phi with vs_halted := T)
Proof
  EVAL_TAC
QED

Definition check_ret_def:
  check_ret = instruction 4 RET [Lit 11w; Lit 0w] []
End
Definition check_callee_def:
  check_callee = mk_raw_function "callee"
    [<| bb_label := "callee_entry"; bb_instructions := [check_ret] |>]
End
Definition check_invoke_def:
  check_invoke = instruction 5 INVOKE [Label "callee"; Lit 0w] ["r"]
End
Definition check_caller_def:
  check_caller = mk_raw_function "caller"
    [<| bb_label := "caller_entry"; bb_instructions := [check_invoke; check_stop] |>]
End
Definition check_call_ctx_def:
  check_call_ctx = mk_venom_context [check_caller; check_callee] (SOME "caller")
End
Definition check_caller_state_def:
  check_caller_state = (init_venom_state "caller_entry") with
    <| vs_vars := FEMPTY |+ ("old",13w); vs_prev_bb := SOME "old_bb" |>
End
Definition check_callee_state_def:
  check_callee_state = (init_venom_state "callee_entry") with vs_params := [0w]
End
Definition check_returned_def:
  check_returned = update_var "r" 11w check_caller_state
End

Theorem callee_visited_states:
  active_inst check_caller check_invoke check_caller_state /\
  check_invoke.inst_opcode = INVOKE /\
  decode_invoke check_invoke = SOME ("callee",[Lit 0w]) /\
  lookup_function "callee" check_call_ctx.ctx_functions = SOME check_callee /\
  eval_operands [Lit 0w] check_caller_state = SOME [0w] /\
  setup_callee check_callee [0w] check_caller_state = SOME check_callee_state /\
  enters_block check_callee check_callee_state check_callee_state /\
  active_inst check_callee check_ret check_callee_state /\
  lookup_var "old" check_callee_state = NONE /\
  check_callee_state.vs_prev_bb = NONE
Proof
  simp[active_inst_def, check_callee_def, check_caller_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem closed_callee_entry:
  reachability_closed Inv check_call_ctx /\
  Inv check_call_ctx check_caller check_invoke check_caller_state ==>
  Inv check_call_ctx check_callee check_ret check_callee_state
Proof
  strip_tac >>
  mp_tac callee_visited_states >> strip_tac >>
  drule_all reachability_closed_callee >> strip_tac >>
  drule_all fn_entry_inv_active >> simp[]
QED

Theorem invoke_return_visited_states:
  active_inst check_caller check_invoke check_caller_state /\
  ~is_terminator check_invoke.inst_opcode /\
  step_inst 1 check_call_ctx check_invoke check_caller_state = OK check_returned /\
  active_inst check_caller check_stop (check_returned with vs_inst_idx := 1) /\
  (check_returned with vs_inst_idx := SUC check_caller_state.vs_inst_idx) =
    (check_returned with vs_inst_idx := 1) /\
  ~active_inst check_caller check_stop check_returned /\
  lookup_var "r" check_returned = SOME 11w /\
  lookup_var "old" check_returned = SOME 13w
Proof
  simp[active_inst_def, check_caller_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem exec_block_invoke_postincrement:
  exec_block 1 check_call_ctx (HD check_caller.fn_blocks) check_caller_state =
  Halt ((check_returned with vs_inst_idx := 1) with vs_halted := T)
Proof
  EVAL_TAC
QED

Theorem closed_invoke_postincrement:
  reachability_closed Inv check_call_ctx /\
  Inv check_call_ctx check_caller check_invoke check_caller_state ==>
  Inv check_call_ctx check_caller check_stop (check_returned with vs_inst_idx := 1)
Proof
  strip_tac >>
  mp_tac invoke_return_visited_states >> strip_tac >>
  metis_tac[reachability_closed_next]
QED

(* Exercise the least relation with the existing concrete execution witnesses. *)
Theorem raw_reachable_initialized_entry:
  raw_inst_reachable check_start check_ctx check_fn check_assign check_start
Proof
  irule raw_inst_reachable_entry >>
  mp_tac initialized_entry_visited_state >>
  simp[check_ctx_def, mk_venom_context_def, lookup_function_def, FIND_thm,
       check_fn_def, mk_raw_function_def, fn_entry_label_def, entry_block_def]
QED

Theorem raw_reachable_next_and_block:
  raw_inst_reachable check_start check_ctx check_fn check_jump check_next /\
  raw_inst_reachable check_start check_ctx check_fn check_stop check_post_phi
Proof
  `raw_inst_reachable check_start check_ctx check_fn check_jump check_next` by
    (irule closed_assign_postincrement >>
     simp[raw_inst_reachable_closed, raw_reachable_initialized_entry]) >>
  simp[] >> irule closed_jump_post_phi >> simp[raw_inst_reachable_closed]
QED

Theorem raw_reachable_call_entry:
  raw_inst_reachable check_caller_state check_call_ctx check_caller check_invoke
    (check_caller_state with vs_prev_bb := NONE)
Proof
  irule raw_inst_reachable_entry >>
  simp[check_call_ctx_def, mk_venom_context_def, lookup_function_def, FIND_thm,
       fn_entry_label_def, entry_block_def, active_inst_def, check_caller_def,
       check_callee_def, mk_raw_function_def,
       MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem raw_reachable_callee_and_return:
  raw_inst_reachable check_caller_state check_call_ctx check_callee check_ret
    check_callee_state /\
  raw_inst_reachable check_caller_state check_call_ctx check_caller check_stop
    (check_returned with <| vs_prev_bb := NONE; vs_inst_idx := 1 |>)
Proof
  conj_tac
  >- (irule raw_inst_reachable_callee >>
      simp[PULL_EXISTS] >>
      qexistsl_tac [`[0w]`, `check_caller`, `check_callee_state`, `check_invoke`,
        `"callee"`, `[Lit 0w]`, `check_caller_state with vs_prev_bb := NONE`] >>
      simp[raw_reachable_call_entry, active_inst_def, check_caller_def,
           check_callee_def, mk_raw_function_def, MEM,
           LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      EVAL_TAC >> simp[] >> EVAL_TAC >> simp[])
  >> `raw_inst_reachable check_caller_state check_call_ctx check_caller check_stop
        ((check_returned with vs_prev_bb := NONE) with vs_inst_idx :=
          SUC (check_caller_state with vs_prev_bb := NONE).vs_inst_idx)`
       suffices_by simp[check_caller_state_def, init_venom_state_def] >>
  irule raw_inst_reachable_next >>
  simp[PULL_EXISTS] >>
  qexistsl_tac [`1`, `check_invoke`] >>
  simp[raw_reachable_call_entry, active_inst_def, check_caller_def,
       mk_raw_function_def, MEM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >> EVAL_TAC
QED
