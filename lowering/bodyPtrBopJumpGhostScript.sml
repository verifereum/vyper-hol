Theory bodyPtrBopJumpGhost
Ancestors
  bodyPtrBopWordPathProbe typedCopyArrayPtr fragGasPathPtr fragExec
  ptrDiscipline venomExecProofs venomInst

Theorem bop_jump_edge_ghost:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = JMP /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME join /\
  phi_prefix_length join.bb_instructions = 0 ==>
  G' = G /\ tn' = tn
Proof
  rw[gas_path_ptr_edge_def] >> gvs[is_terminator_def]
  >>~- ([`exit_result _`], metis_tac[exit_result_def]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  drule_all entry_ghost_no_phi >> simp[]
QED
