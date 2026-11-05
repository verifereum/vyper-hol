Theory bodyPtrIntCallJoint
Ancestors
  fragExec exprLoweringProps instIdxIndep venomState venomExecSemantics
  list

(* Raw sequences leave the cursor alone.  Express their endpoints at the
   incoming cursor, so counted segments can be composed without pretending
   that an arbitrary path has a unique endpoint. *)
Theorem intcall_run_cursor_append:
  run_inst_seq a s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  run_inst_seq b u = OK (t with vs_inst_idx := u.vs_inst_idx) /\
  EVERY (\i. ~is_terminator i.inst_opcode) b ==>
  run_inst_seq (a ++ b) s = OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >> qpat_x_assum `run_inst_seq a s = _` (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `b` mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem intcall_run_cursor_witness:
  run_inst_seq code s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = s.vs_inst_idx + LENGTH code ==>
  ?u. run_inst_seq code s = OK u /\
      t = u with vs_inst_idx := s.vs_inst_idx + LENGTH code
Proof
  strip_tac >> qexists_tac `t with vs_inst_idx := s.vs_inst_idx` >>
  simp[venom_state_component_equality]
QED
