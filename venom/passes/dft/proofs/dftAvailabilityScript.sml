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
