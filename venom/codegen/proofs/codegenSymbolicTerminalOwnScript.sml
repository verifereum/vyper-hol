(* Terminal fixed-step symbolic execution, uniformly in the own-code mode. *)
Theory codegenSymbolicTerminalOwn
Ancestors
  codegenSymRel finalizerContract finalizerContractOwn

Theorem sym_steps_mode_terminal_disciplined:
  !allow_own prog env own n as.
    asm_static_wf prog /\
    sym_terminal (sym_steps_mode allow_own prog env own n (sym_init as)) ==>
    if allow_own then label_disciplined_own env own prog as
    else label_disciplined env prog as
Proof
  rpt gen_tac >> strip_tac >>
  drule sym_steps_mode_terminal_run >>
  disch_then (qspec_then `0` mp_tac) >>
  Cases_on `allow_own` >> simp[] >> strip_tac >>
  metis_tac[sym_terminal_own_disciplined, sym_terminal_disciplined]
QED
