Theory frameTerminalOrigins
Ancestors frameFiniteExecution stepWriteFootprintForward venomExecSemantics

(* Unlike an instruction-list run, these edges include the administrative
   increment and are independent of call-depth fuel.  INVOKE is excluded. *)
Definition terminal_origin_edge_def:
  terminal_origin_edge bb s t <=>
    ?i p. get_instruction bb s.vs_inst_idx = SOME i /\
      i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      step_inst_base i s = OK p /\
      t = p with vs_inst_idx := SUC s.vs_inst_idx
End

Inductive terminal_origin_prefix:
  (!bb s. terminal_origin_prefix bb s s) /\
  (!bb s p t. terminal_origin_edge bb s p /\ terminal_origin_prefix bb p t ==>
    terminal_origin_prefix bb s t)
End

Theorem terminal_origin_edge_no_normal:
  terminal_origin_edge bb s t /\
  (!fuel u. exec_block fuel C bb t <> OK u) ==>
  !fuel u. exec_block fuel C bb s <> OK u
Proof
  simp[terminal_origin_edge_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `exec_block fuel C bb s = OK u` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[step_inst_non_invoke]
QED

Theorem terminal_origin_prefix_no_normal:
  !bb s t. terminal_origin_prefix bb s t ==>
    (!fuel u. exec_block fuel C bb t <> OK u) ==>
    !fuel u. exec_block fuel C bb s <> OK u
Proof
  ho_match_mp_tac terminal_origin_prefix_ind >> rpt strip_tac >>
  metis_tac[terminal_origin_edge_no_normal]
QED

Theorem terminal_origin_prefix_trans:
  !bb s t. terminal_origin_prefix bb s t ==>
    !u. terminal_origin_prefix bb t u ==> terminal_origin_prefix bb s u
Proof
  ho_match_mp_tac terminal_origin_prefix_ind >> rpt strip_tac >>
  metis_tac[terminal_origin_prefix_rules]
QED

Theorem terminal_origin_revert_no_normal:
  terminal_origin_prefix bb s t /\ revert_forward_at bb t.vs_inst_idx ==>
  !fuel u. exec_block fuel C bb s <> OK u
Proof
  metis_tac[terminal_origin_prefix_no_normal, revert_forward_at_no_normal]
QED

Theorem terminal_origin_revert_no_finite_ok:
  terminal_origin_prefix bb s t /\ revert_forward_at bb t.vs_inst_idx ==>
  ~finite_block C bb s (OK u)
Proof
  strip_tac >> drule_all terminal_origin_revert_no_normal >>
  simp[finite_block_iff] >> metis_tac[]
QED

val _ = export_theory();
