Theory frameRawProjection
Ancestors frameExecutionPrefix contextRawReachable ptrDiscipline venomInstProofs
  venomInst list frameJointTransition frameOriginHistory frameOriginReachable

(* Each suspended prefix is tied to the precise setup entry of its child. *)
Definition matched_prefix_stack_def:
  (matched_prefix_stack vs0 ctx [] child entry <=> T) /\
  (matched_prefix_stack vs0 ctx (f::stk) child entry <=>
    ?parent_entry nm ops args.
      matched_prefix_stack vs0 ctx stk f.cf_fn parent_entry /\
      wf_function f.cf_fn /\
      execution_prefix ctx f.cf_fn parent_entry f.cf_inst f.cf_state /\
      raw_reachable vs0 ctx f.cf_fn f.cf_inst f.cf_state /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      f.cf_inst.inst_opcode = INVOKE /\
      decode_invoke f.cf_inst = SOME (nm,ops) /\
      lookup_function nm ctx.ctx_functions = SOME child /\
      eval_operands ops f.cf_state = SOME args /\
      setup_callee child args f.cf_state = SOME entry)
End

Theorem frame_reachable_prefix_stack:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    EVERY wf_function ctx.ctx_functions ==>
    ?entry. wf_function fn /\ execution_prefix ctx fn entry inst s /\
      raw_reachable vs0 ctx fn inst s /\
      matched_prefix_stack vs0 ctx stk fn entry
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      qexists `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>` >>
      simp[matched_prefix_stack_def] >>
      metis_tac[lookup_function_MEM, EVERY_MEM, execution_prefix_rules,
                raw_reachable_rules])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      qexists `entry` >> simp[] >>
      metis_tac[execution_prefix_rules, raw_reachable_rules])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      qexists `entry` >> simp[] >>
      metis_tac[execution_prefix_rules, raw_reachable_rules])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      qexists `cs` >> simp[matched_prefix_stack_def] >>
      conj_tac >- metis_tac[lookup_function_MEM, EVERY_MEM] >>
      conj_tac >- metis_tac[execution_prefix_rules] >>
      conj_tac >- metis_tac[raw_reachable_rules] >>
      qexists `entry` >> simp[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  fs[matched_prefix_stack_def] >>
  drule_all execution_prefix_return >> strip_tac >>
  drule_all frameInvokeReturnTheory.matched_run_invoke_return >> strip_tac >>
  qexists `parent_entry` >> simp[] >>
  `~is_terminator f.cf_inst.inst_opcode` by simp[is_terminator_def] >>
  conj_tac >- metis_tac[execution_prefix_rules] >>
  metis_tac[raw_reachable_rules]
QED

Theorem matched_prefix_stack_raw:
  !stk child entry.
    matched_prefix_stack vs0 ctx stk child entry ==>
    EVERY (\f. raw_reachable vs0 ctx f.cf_fn f.cf_inst f.cf_state) stk
Proof
  Induct >> simp[matched_prefix_stack_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem frame_reachable_raw:
  EVERY wf_function ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  raw_reachable vs0 ctx fn inst s
Proof
  metis_tac[frame_reachable_prefix_stack]
QED

Theorem frame_reachable_saved_raw:
  EVERY wf_function ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  EVERY (\f. raw_reachable vs0 ctx f.cf_fn f.cf_inst f.cf_state) stk
Proof
  metis_tac[frame_reachable_prefix_stack, matched_prefix_stack_raw]
QED

Theorem joint_config_raw:
  EVERY wf_function ctx.ctx_functions /\
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  raw_reachable vs0 ctx fn inst s
Proof
  simp[joint_config_reachable_def] >>
  metis_tac[joint_origin_history_erasure, origin_frame_erasure,
            frame_reachable_raw]
QED

Theorem joint_config_saved_raw:
  EVERY wf_function ctx.ctx_functions /\
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  EVERY (\f. raw_reachable vs0 ctx f.cf_fn f.cf_inst f.cf_state) stk
Proof
  simp[joint_config_reachable_def] >>
  metis_tac[joint_origin_history_erasure, origin_frame_erasure,
            frame_reachable_saved_raw]
QED
