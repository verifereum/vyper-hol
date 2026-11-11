(* Execution is unchanged by unreachable ALLOCA metadata and a no-call context. *)
Theory extcallReturnObserverRun
Ancestors
  extcallReturnObserver exprSimAbiGasBridge abiEncoderObserver abiDecoderLoop fragExec
  venomExecSemantics venomExecProofs venomInstProofs1 venomInstProps
  venomInst compileEnv list arithmetic unitShapeDefs

Theorem return_observer_block_context:
  !n s bb ctx ctx' fuel.
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions ==>
    exec_block fuel ctx bb s = exec_block fuel ctx' bb s
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once exec_block_def] >> simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by
    (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  once_rewrite_tac[exec_block_def] >> simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum irule >> gvs[get_instruction_def]
QED

Theorem return_observer_block_avoids_keep:
  !n s bb fuel ctx t keep.
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    EVERY (\i. i.inst_opcode <> INVOKE /\
               ~MEM (Label keep) i.inst_operands) bb.bb_instructions /\
    s.vs_current_bb <> keep /\ ~s.vs_halted /\
    exec_block fuel ctx bb s = OK t ==>
    t.vs_current_bb <> keep
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE /\ ~MEM (Label keep) inst.inst_operands` by
    (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >> simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  rename1 `step_inst_base inst s = OK middle` >>
  `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  IF_CASES_TAC >> simp[] >> strip_tac
  >- (gvs[] >>
      `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
        (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
         gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
      metis_tac[frag_observer_jump_no_reentry]) >>
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`bb`, `ctx`, `fuel`,
    `middle with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[get_instruction_def]
QED

Theorem return_observer_block_properties:
  EVERY P (fn_insts obs) /\ lookup_block lbl obs.fn_blocks = SOME bb ==>
  EVERY P bb.bb_instructions
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  fs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem return_observer_complete_run_blocks:
  !fuel s ctx ctx' func obs keep.
    EVERY (\i. i.inst_opcode <> INVOKE /\
               ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
    s.vs_current_bb <> keep /\ ~s.vs_halted ==>
    run_blocks fuel ctx (return_observer_complete func obs keep) s =
    run_blocks fuel ctx' obs s
Proof
  Induct_on `fuel` >- (once_rewrite_tac[run_blocks_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def] >>
  simp[return_observer_complete_lookup_off_keep] >>
  Cases_on `lookup_block s.vs_current_bb obs.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
       ~MEM (Label keep) i.inst_operands) bb.bb_instructions` by
    metis_tac[return_observer_block_properties] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions` by fs[EVERY_MEM] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[] >> rename1 `eval_phis s bb.bb_instructions = OK entered` >>
  `exec_block fuel ctx bb (entered with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   exec_block fuel ctx' bb (entered with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[return_observer_block_context] >> simp[] >>
  Cases_on `exec_block fuel ctx' bb
    (entered with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `exec_block fuel ctx' bb _ = OK middle` >>
  `~middle.vs_halted` by metis_tac[exec_block_OK_not_halted] >> simp[] >>
  first_x_assum irule >> simp[] >>
  irule return_observer_block_avoids_keep >>
  qexistsl_tac [`bb`, `ctx'`, `fuel`,
    `LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
    `entered with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[] >> metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted]
QED

Theorem return_observer_complete_run_from:
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
  s.vs_current_bb <> keep /\ ~s.vs_halted ==>
  run_from fuel ctx (return_observer_complete func obs keep) s =
  run_from fuel ctx' obs s
Proof
  strip_tac >> once_rewrite_tac[run_from_def] >>
  simp[return_observer_complete_lookup_off_keep] >>
  Cases_on `lookup_block s.vs_current_bb obs.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
       ~MEM (Label keep) i.inst_operands) bb.bb_instructions` by
    metis_tac[return_observer_block_properties] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions` by fs[EVERY_MEM] >>
  `exec_block fuel ctx bb s = exec_block fuel ctx' bb s` by
    metis_tac[return_observer_block_context] >> simp[] >>
  Cases_on `exec_block fuel ctx' bb s` >> simp[] >>
  rename1 `exec_block fuel ctx' bb s = OK middle` >>
  `~middle.vs_halted` by metis_tac[exec_block_OK_not_halted] >> simp[] >>
  irule return_observer_complete_run_blocks >> simp[] >>
  metis_tac[return_observer_block_avoids_keep]
QED

Theorem return_observer_complete_sim:
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
  s.vs_current_bb <> keep /\ ~s.vs_halted /\
  t.vs_current_bb <> keep /\ ~t.vs_halted /\
  abi_decode_sim ctx (return_observer_complete func obs keep) s t ==>
  abi_decode_sim ctx' obs s t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_sim _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decode_sim_def] >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  `run_from fuel ctx (return_observer_complete func obs keep) t = r` by
    metis_tac[return_observer_complete_run_from] >>
  `?fuel'. run_from fuel' ctx (return_observer_complete func obs keep) s = r` by
    metis_tac[] >>
  metis_tac[return_observer_complete_run_from]
QED
