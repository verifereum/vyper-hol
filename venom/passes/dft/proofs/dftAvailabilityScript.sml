(* SSA availability for a data-ready instruction, independently of its
   position in a reordered prefix. *)
Theory dftAvailability
Ancestors
  dftScheduleOrder dftCorrectness sccpCorrectnessProofs venomWf
  venomExecSemantics venomExecProofs venomState list finite_map

Theorem dft_ready_operand_defined:
  wf_ssa fn /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  strict_dom_vars_defined fn s /\
  (!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\
         MEM (Var v) inst.inst_operands /\
         id_before (MAP (\i. i.inst_id) bb.bb_instructions)
           d.inst_id inst.inst_id ==> v IN FDOM s.vs_vars) ==>
  !v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME inst) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  fs[def_available_at_def] >>
  Cases_on `def_bb.bb_label = bb.bb_label`
  >- (`def_bb = bb` by metis_tac[same_label_same_block] >>
      gvs[] >>
      qpat_x_assum `!d v. _` irule >>
      simp[] >> qexists_tac `EL i bb.bb_instructions` >> simp[] >>
      simp[id_before_def] >> qexistsl_tac [`i`, `j`] >>
      simp[EL_MAP]) >>
  fs[strict_dom_vars_defined_def] >> metis_tac[]
QED

Theorem dft_exec_block_initialized_outputs:
  exec_block fuel ctx bb s = OK t /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!i v. i < s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
         MEM v (EL i bb.bb_instructions).inst_outputs ==> v IN FDOM s.vs_vars)
  ==> !i v. i < LENGTH bb.bb_instructions /\
            ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
            MEM v (EL i bb.bb_instructions).inst_outputs ==>
            v IN FDOM t.vs_vars
Proof
  rpt strip_tac >> Cases_on `i < s.vs_inst_idx`
  >- (`v IN FDOM s.vs_vars` by metis_tac[] >>
      drule_all exec_block_fdom_mono >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  irule exec_block_output_in_fdom_aux >>
  qexistsl_tac [`bb`, `ctx`, `fuel`, `i`,
    `LENGTH bb.bb_instructions - s.vs_inst_idx`, `s`] >> simp[]
QED

Theorem dft_dominance_transfer:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb /\
  strict_dom_vars_defined fn s /\
  FDOM s.vs_vars SUBSET FDOM t.vs_vars /\
  (!inst v. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
            v IN FDOM t.vs_vars) ==>
  strict_dom_vars_defined fn t
Proof
  rw[strict_dom_vars_defined_def] >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- (`d_bb = bb` by metis_tac[same_label_same_block] >>
      gvs[] >> metis_tac[]) >>
  `fn_dominates fn d_bb.bb_label s.vs_current_bb` by
    metis_tac[fn_dominates_predecessor] >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem dft_successor_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s /\ EVERY inst_wf bb.bb_instructions /\
  run_block fuel ctx bb s = OK t /\ ~t.vs_halted ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     simp[] >> reverse conj_tac
     >- (fs[bb_well_formed_def] >> metis_tac[]) >>
     fs[bb_well_formed_def] >> rpt strip_tac >>
     spose_not_then assume_tac >>
     qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  irule dft_dominance_transfer >> simp[] >>
  qexistsl_tac [`bb`, `s`] >> simp[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  drule_all eval_phis_vars_grow >> strip_tac >>
  drule_all exec_block_fdom_mono >> simp[] >> strip_tac >>
  reverse conj_tac >- metis_tac[pred_setTheory.SUBSET_TRANS] >>
  rpt strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst`
    by metis_tac[MEM_EL] >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[terminator_no_outputs, EVERY_MEM, MEM] >>
  `!j w. j < phi_prefix_length bb.bb_instructions /\
         j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM s'.vs_vars` by
    (rpt strip_tac >> irule eval_phis_outputs_in_fdom_mem >>
     qexistsl_tac [`EL j bb.bb_instructions`, `bb.bb_instructions`, `s`] >>
     simp[] >> simp[MEM_EL] >> qexists_tac `j` >>
     simp[EL_TAKE, phi_prefix_length_le]) >>
  drule dft_exec_block_initialized_outputs >> simp[] >>
  disch_then (qspecl_then [`i`, `v`] mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >>
    qexists_tac `i'` >> simp[]) >> simp[]

QED
