Theory frameControlAgreement
Ancestors frameCfgBoundary venomExecProofs venomInstProps venomInstProofs1
  venomExecSemantics venomState contextCodegenRel

(* Only labels are synchronized: transformed instruction indices may differ. *)
Definition control_agree_def:
  control_agree s t <=>
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb
End

Theorem control_agree_refl[simp]:
  control_agree s s
Proof
  simp[control_agree_def]
QED

Theorem control_agree_index[simp]:
  control_agree (s with vs_inst_idx := i) (t with vs_inst_idx := j) <=>
  control_agree s t
Proof
  simp[control_agree_def]
QED

Theorem control_agree_jump:
  control_agree s t ==> control_agree (jump_to lbl s) (jump_to lbl t)
Proof
  simp[control_agree_def, jump_to_def]
QED

Theorem control_agree_step:
  control_agree s t /\
  step_inst fuel C inst s = OK post /\
  step_inst fuel' C' inst' t = OK post' /\
  ~is_terminator inst.inst_opcode /\ ~is_terminator inst'.inst_opcode ==>
  control_agree post post'
Proof
  metis_tac[control_agree_def, step_preserves_control_flow]
QED

Theorem control_agree_enters_block:
  control_agree s t /\ enters_block fn s post /\ enters_block fn' t post' ==>
  control_agree post post'
Proof
  metis_tac[control_agree_def, enters_block_control_labels]
QED

Theorem control_agree_phis:
  control_agree s t /\ eval_phis s insts = OK post /\
  eval_phis t insts' = OK post' ==> control_agree post post'
Proof
  metis_tac[control_agree_def, eval_phis_prev_bb, eval_phis_preserves_current_bb]
QED

Theorem control_agree_setup:
  setup_callee fn args s = SOME cs /\ setup_callee fn' args' t = SOME ct /\
  (HD fn.fn_blocks).bb_label = (HD fn'.fn_blocks).bb_label ==>
  control_agree cs ct
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[control_agree_def]
QED

Theorem control_agree_bind_outputs:
  control_agree s t /\ bind_outputs outs vals s = SOME post /\
  bind_outputs outs' vals' t = SOME post' ==> control_agree post post'
Proof
  strip_tac >>
  qspec_then `\u. (u.vs_current_bb,u.vs_prev_bb)` mp_tac bind_outputs_preserves >>
  (impl_tac >- simp[update_var_def]) >>
  simp[] >> strip_tac >>
  gvs[control_agree_def] >> metis_tac[]
QED

Theorem control_agree_restore:
  control_agree caller caller' ==>
  control_agree
    (adopt_return_fmp ret (merge_callee_state caller callee))
    (adopt_return_fmp ret' (merge_callee_state caller' callee'))
Proof
  Cases_on `ret.iret_adopt_fmp` >> Cases_on `ret'.iret_adopt_fmp` >>
  simp[control_agree_def, adopt_return_fmp_def, merge_callee_state_def]
QED

val _ = export_theory();
