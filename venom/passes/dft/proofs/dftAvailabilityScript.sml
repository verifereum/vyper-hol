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
