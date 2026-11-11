Theory concretizeLayoutCallControl
Ancestors concretizeLayoutParameterSegments frameActivationSeparation
  frameRelocationOpaque venomExecSemantics venomInstProofs1 venomState list rich_list

Theorem paired_setup_control:
  setup_callee fn args s = SOME cs /\
  setup_callee fn' args' t = SOME ct /\
  (HD fn.fn_blocks).bb_label = (HD fn'.fn_blocks).bb_label ==>
  parameter_control cs = parameter_control ct /\
  cs.vs_vars = FEMPTY /\ ct.vs_vars = FEMPTY
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[parameter_control_def]
QED

Theorem bind_outputs_control[local]:
  bind_outputs outs vals s = SOME post ==>
  parameter_control post = parameter_control s
Proof
  strip_tac >> irule bind_outputs_preserves >>
  simp[parameter_control_def, update_var_def] >> metis_tac[]
QED

(* The caller's control is restored independently of the callee's control,
   returned values, and optional adopted FMP. *)
Theorem return_binding_control:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME post ==>
  parameter_control post = parameter_control caller
Proof
  strip_tac >> drule bind_outputs_control >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[parameter_control_def, adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem paired_return_next_control:
  parameter_control caller = parameter_control caller' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME post /\
  bind_outputs outs' ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' callee')) = SOME post' ==>
  parameter_control (post with vs_inst_idx := SUC caller.vs_inst_idx) =
    parameter_control (post' with vs_inst_idx := SUC caller'.vs_inst_idx)
Proof
  strip_tac >>
  `parameter_control post = parameter_control caller` by
    metis_tac[return_binding_control] >>
  `parameter_control post' = parameter_control caller'` by
    metis_tac[return_binding_control] >>
  gvs[parameter_control_def]
QED

(* Return values exclude the final logical return-PC token.  Neither these
   tokens nor the returned values need to be equal across the two runs. *)
Theorem paired_return_values:
  inst.inst_opcode = RET /\ inst'.inst_opcode = RET /\
  eval_operands inst.inst_operands s = SOME (xs ++ [token]) /\
  eval_operands inst'.inst_operands t = SOME (ys ++ [token']) /\
  LIST_REL Rel xs ys ==>
  ?ret ret'.
    step_inst fuel ctx inst s = IntRet ret s /\
    step_inst fuel' ctx' inst' t = IntRet ret' t /\
    LIST_REL Rel ret.iret_values ret'.iret_values /\
    ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE
Proof
  strip_tac >>
  `step_inst_base inst s =
    IntRet <|iret_values := xs; iret_adopt_fmp := NONE|> s` by
    (irule opaque_return_token_step >> simp[] >> goal_assum (drule_at Any)) >>
  `step_inst_base inst' t =
    IntRet <|iret_values := ys; iret_adopt_fmp := NONE|> t` by
    (irule opaque_return_token_step >> simp[] >> goal_assum (drule_at Any)) >>
  simp[step_inst_def]
QED
