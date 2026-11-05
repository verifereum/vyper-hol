(*
 * The planner state partway through a block's instructions.
 *
 * generate_block_insts_plan takes each instruction's lookahead (the
 * liveness after it, whether the next one is a terminator) from the list
 * it is given, so planning a prefix of the instructions on its own plans
 * the prefix's last instruction as if it ended the block.  The prefix
 * planner below stops after j instructions but takes the lookahead from
 * the whole list, so its state is the one the block's plan reaches.
 *
 * Also generated_plan_state_wf_marked, the planner-state well-formedness
 * the block induction can keep: a cleanup elision (clean_stack_plan's
 * mark_dead_stack) leaves dead_stack_marker in several stack slots, so
 * generated_plan_state_wf's ALL_DISTINCT ps_stack fails after it.
 *
 * TOP-LEVEL:
 *   generate_block_insts_prefix      - the first j instructions' plan
 *   generate_block_insts_plan_split  - a block's plan is its prefix's plan
 *                                      followed by the rest's
 *   generated_plan_state_wf_marked   - generated_plan_state_wf, with
 *                                      repeated dead_stack_marker slots
 *   generated_plan_state_wf_marked_wf - generated_plan_state_wf implies it
 *)

Theory fnPlanPrefix
Ancestors
  genBlockSim stackPlanGen stackPlanTypes list arithmetic

Definition generate_block_insts_prefix_def:
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (0:num) insts ps =
    SOME ([] : stack_op list, ps) /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) [] ps = NONE /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) (inst :: rest) ps =
    let next_live =
      if rest = [] then live_vars_at liveness bb_label block_len
      else live_vars_at liveness bb_label (i + n_params + 1) in
    let next_is_term =
      case rest of
        [] => F
      | next_i :: _ => is_terminator next_i.inst_opcode in
    case generate_inst_plan liveness dfg cfg fn inst
           next_live is_halting next_is_term bb_label ps of
      NONE => NONE
    | SOME (step_ops, ps') =>
        case generate_block_insts_prefix liveness dfg cfg fn bb_label
               is_halting n_params block_len (i + 1) j rest ps' of
          NONE => NONE
        | SOME (rest_ops, ps'') => SOME (step_ops ++ rest_ops, ps'')
End

Theorem generate_block_insts_plan_split:
  !j insts liveness dfg cfg fn bb_label is_halting n_params block_len i ps
   ops ps_end.
    j <= LENGTH insts ==>
    (generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
       n_params block_len i insts ps = SOME (ops, ps_end) <=>
     ?pre ps_mid post.
       generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
         n_params block_len i j insts ps = SOME (pre, ps_mid) /\
       generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
         n_params block_len (i + j) (DROP j insts) ps_mid =
         SOME (post, ps_end) /\
       ops = pre ++ post)
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  gen_tac >> Cases_on `insts` >- simp[] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  disch_tac >> rpt gen_tac >> disch_tac >> gvs[] >>
  simp[Once generate_block_insts_plan_def, generate_block_insts_prefix_def,
       LET_THM, AllCaseEqs(), PULL_EXISTS] >>
  `i + SUC j = i + 1 + j` by simp[] >> pop_assum SUBST1_TAC >>
  eq_tac >> strip_tac >> gvs[] >>
  rpt (first_assum $ irule_at Any) >> simp[]
QED

Definition generated_plan_state_wf_marked_def:
  generated_plan_state_wf_marked base (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)
End

(* generated_plan_state_wf doesn't keep the marker out of the spill map,
   hence the second premise. *)
Theorem generated_plan_state_wf_marked_wf:
  !base ps.
    generated_plan_state_wf base ps /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled ==>
    generated_plan_state_wf_marked base ps
Proof
  rw[generated_plan_state_wf_def, generated_plan_state_wf_marked_def] >>
  irule FILTER_ALL_DISTINCT >> simp[]
QED
