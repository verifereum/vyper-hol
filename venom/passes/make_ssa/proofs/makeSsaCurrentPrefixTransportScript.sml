Theory makeSsaCurrentPrefixTransport
Ancestors
  makeSsaCurrentCopyPrefixRuntime venomExecSemantics list

Theorem current_prefix_steps_noninvoke_transport:
  !xs st done.
    EVERY (\inst. inst.inst_opcode <> INVOKE) xs ==>
    (current_prefix_steps fuel C xs st done <=>
     current_prefix_steps fuel' C' xs st done)
Proof
  Induct >> simp[current_prefix_steps_def, step_inst_non_invoke]
QED

Theorem current_copy_prefix_steps_transport:
  current_prefix_steps fuel C xs st done /\
  (!j. j < LENGTH xs ==>
    (EL j xs).inst_opcode = ASSIGN \/ (EL j xs).inst_opcode = NOP) ==>
  current_prefix_steps fuel' C' xs st done
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE) xs` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  metis_tac[current_prefix_steps_noninvoke_transport]
QED
