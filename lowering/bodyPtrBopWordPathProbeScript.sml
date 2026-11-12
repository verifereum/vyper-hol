Theory bodyPtrBopWordPathProbe
Ancestors
  ptrSafeRun ptrDiscipline finite_map fragGasPathPtr fragExec venomInst
  exprLowering compileEnv typedCopyArrayPtr

Theorem bop_first_prov_none:
  EVERY (\op. op_prov G op = NONE) ops ==> first_prov G ops = NONE
Proof
  Induct_on `ops` >> simp[first_prov_def]
QED

Theorem bop_forward_step_prov_none:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/
   inst.inst_opcode = SUB) /\
  inst.inst_outputs = [z] /\
  EVERY (\op. op_prov G op = NONE) inst.inst_operands ==>
  FLOOKUP (step_prov PG G inst t) z = NONE
Proof
  strip_tac >> drule bop_first_prov_none >> strip_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem bop_forward_ghost_step_none:
  step_inst fuel ctx inst s = OK t /\
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/
   inst.inst_opcode = SUB) /\
  inst.inst_outputs = [z] /\
  EVERY (\op. op_prov G op = NONE) inst.inst_operands ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) z = NONE
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all ghost_step_non_invoke >> simp[] >>
  disch_then kall_tac >> irule bop_forward_step_prov_none >> simp[]
QED

(* This consumes the actual edge: it does not select a second execution. *)
Theorem bop_forward_edge_none:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/
   inst.inst_opcode = SUB) /\
  inst.inst_outputs = [z] /\
  EVERY (\op. op_prov G op = NONE) inst.inst_operands ==>
  FLOOKUP G' z = NONE
Proof
  rw[gas_path_ptr_edge_def] >>
  gvs[is_terminator_def, exit_result_def]
  >>~- ([`exit_result _`], metis_tac[exit_result_def]) >>
  qpat_x_assum `(G',tn') = _` mp_tac >>
  simp[Once ghost_step_def] >> strip_tac >> gvs[] >>
  irule bop_forward_step_prov_none >> simp[]
QED

(* Identity conversion emits nothing; the child's existing ghost is reused. *)
Theorem bop_identity_convert_prov:
  compile_type_convert op ConvIdentity sa = (out,sb) /\
  op_prov G op = NONE ==>
  sb = sa /\ op_prov G out = NONE
Proof
  simp[compile_type_convert_def, comp_return_def] >> rpt strip_tac >> gvs[]
QED

(* The selected arm's actual ASSIGN clears arbitrary old provenance at z.
   Entry into a PHI-free join preserves it; no fresh-name ghost premise. *)
Theorem bop_assign_join_prov:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [z] /\
  inst.inst_operands = [op] /\ op_prov G op = NONE /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME join /\
  phi_prefix_length join.bb_instructions = 0 ==>
  op_prov (entry_prov fn u G') (Var z) = NONE
Proof
  strip_tac >>
  `FLOOKUP G' z = NONE` by
    (drule bop_forward_edge_none >> simp[] >>
     disch_then drule_all >> simp[]) >>
  drule_all entry_ghost_no_phi >> simp[op_prov_def]
QED
