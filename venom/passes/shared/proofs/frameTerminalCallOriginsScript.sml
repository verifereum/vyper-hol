Theory frameTerminalCallOrigins
Ancestors frameTerminalOrigins frameExecutionPrefix venomExecSemantics
  frameFiniteExecution stepWriteFootprintForward

(* Single-block successful prefixes, including completed calls. *)
Definition terminal_call_edge_def:
  terminal_call_edge C bb s t <=>
    ?i p fuel. get_instruction bb s.vs_inst_idx = SOME i /\
      ~is_terminator i.inst_opcode /\ step_inst fuel C i s = OK p /\
      t = p with vs_inst_idx := SUC s.vs_inst_idx
End

Inductive terminal_call_prefix:
  (!C bb s. terminal_call_prefix C bb s s) /\
  (!C bb s p t. terminal_call_edge C bb s p /\
    terminal_call_prefix C bb p t ==> terminal_call_prefix C bb s t)
End

Theorem terminal_call_edge_no_normal:
  terminal_call_edge C bb s t /\
  (!fuel u. exec_block fuel C bb t <> OK u) ==>
  !fuel u. exec_block fuel C bb s <> OK u
Proof
  simp[terminal_call_edge_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `exec_block fuel' C bb s = OK u` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[] >>
  Cases_on `step_inst fuel' C i s` >> simp[] >>
  rename1 `step_inst fuel' C i s = OK q` >>
  `!e. step_inst fuel C i s <> Error e` by simp[] >>
  `!e. step_inst fuel' C i s <> Error e` by simp[] >>
  drule prefix_step_fuel_mono >>
  disch_then (qspec_then `fuel` assume_tac) >>
  qpat_x_assum `!e. step_inst fuel' C i s <> Error e` kall_tac >>
  drule prefix_step_fuel_mono >>
  disch_then (qspec_then `fuel'` assume_tac) >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem terminal_call_prefix_no_normal:
  !C bb s t. terminal_call_prefix C bb s t ==>
    (!fuel u. exec_block fuel C bb t <> OK u) ==>
    !fuel u. exec_block fuel C bb s <> OK u
Proof
  ho_match_mp_tac terminal_call_prefix_ind >> rpt strip_tac >>
  metis_tac[terminal_call_edge_no_normal]
QED

Theorem terminal_call_prefix_trans:
  !C bb s t. terminal_call_prefix C bb s t ==>
    !u. terminal_call_prefix C bb t u ==> terminal_call_prefix C bb s u
Proof
  ho_match_mp_tac terminal_call_prefix_ind >> rpt strip_tac >>
  metis_tac[terminal_call_prefix_rules]
QED

Theorem terminal_call_revert_no_normal:
  terminal_call_prefix C bb s t /\ revert_forward_at bb t.vs_inst_idx ==>
  !fuel u. exec_block fuel C bb s <> OK u
Proof
  metis_tac[terminal_call_prefix_no_normal, revert_forward_at_no_normal]
QED

Theorem terminal_call_revert_no_finite_ok:
  terminal_call_prefix C bb s t /\ revert_forward_at bb t.vs_inst_idx ==>
  ~finite_block C bb s (OK u)
Proof
  strip_tac >> drule_all terminal_call_revert_no_normal >>
  simp[finite_block_iff] >> metis_tac[]
QED

val _ = export_theory();
