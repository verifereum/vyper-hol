(* Syntactic successor certificates for STOP observer regions. *)
Theory entryObserverCfg
Ancestors
  abiEncoderObserver venomExecProofs venomInstProofs opcodeClass
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem entry_cfg_observer_region_closed:
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
     (lbl,idx+1) IN R) \/
    (?dest target. inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
      lookup_block dest fn.fn_blocks = SOME target /\
      (dest,phi_prefix_length target.bb_instructions) IN R) \/
    (?cond yes no ybb nbb.
      inst.inst_opcode = JNZ /\ inst.inst_operands = [cond; Label yes; Label no] /\
      lookup_block yes fn.fn_blocks = SOME ybb /\
      lookup_block no fn.fn_blocks = SOME nbb /\
      (yes,phi_prefix_length ybb.bb_instructions) IN R /\
      (no,phi_prefix_length nbb.bb_instructions) IN R)) ==>
  observer_region_closed ctx fn cut R
Proof
  strip_tac >> rw[observer_region_closed_def, abi_observer_step_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[is_terminator_def]
  >- (drule_all step_preserves_control_flow >> strip_tac >> gvs[ADD1]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[]
QED

Theorem entry_cfg_observer_region_safe:
  (!bb. lookup_block (FST cut) fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (SND cut) = SOME (mk_inst id STOP [] [])) /\
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
     (lbl,idx+1) IN R) \/
    (?dest target. inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
      lookup_block dest fn.fn_blocks = SOME target /\
      (dest,phi_prefix_length target.bb_instructions) IN R) \/
    (?cond yes no ybb nbb.
      inst.inst_opcode = JNZ /\ inst.inst_operands = [cond; Label yes; Label no] /\
      lookup_block yes fn.fn_blocks = SOME ybb /\
      lookup_block no fn.fn_blocks = SOME nbb /\
      (yes,phi_prefix_length ybb.bb_instructions) IN R /\
      (no,phi_prefix_length nbb.bb_instructions) IN R)) ==>
  observer_region_safe fn cut R
Proof
  strip_tac >> rewrite_tac[observer_region_safe_def] >> conj_tac
  >- metis_tac[] >>
  map_every qx_gen_tac [`lbl`, `idx`, `bb`, `inst`] >> strip_tac >>
  first_x_assum drule_all >> disch_tac >>
  `inst.inst_opcode <> INVOKE /\
   (~is_terminator inst.inst_opcode \/ inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ)` by
    (gvs[] >> metis_tac[]) >>
  (simp[] >> conj_tac
   >- (rpt strip_tac >> drule step_inst_base_halt_opcodes >> strip_tac >>
       gvs[is_terminator_def]) >>
   rpt strip_tac >> drule venomExecProofsTheory.step_inst_base_OK_preserves_halted >> simp[])
QED
