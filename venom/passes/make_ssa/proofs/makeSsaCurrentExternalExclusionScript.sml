Theory makeSsaCurrentExternalExclusion
Ancestors
  makeSsaCurrentWfSsa venomExecProps list rich_list venomWfProps

(* ALL_DISTINCT of FLAT (MAP f xs) means shared elements identify their source *)
Triviality all_distinct_flat_map_unique:
  !f xs x y v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM x xs /\ MEM y xs /\ MEM v (f x) /\ MEM v (f y) ==>
    x = y
Proof
  gen_tac >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  Cases_on `x = h` >> Cases_on `y = h` >> gvs[] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED
Theorem current_wf_external_output_disjoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h renamed = SOME new /\
  MEM db renamed /\ MEM di db.bb_instructions /\ MEM z di.inst_outputs /\
  db.bb_label <> new.bb_label ==>
  !ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs
Proof
  rpt strip_tac >>
  drule_all current_wf_phi_context_ssa_form >> strip_tac >>
  `MEM new renamed` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
    bb.bb_instructions)) renamed))` by
    (fs[venomWfTheory.ssa_form_def, venomInstTheory.fn_insts_def,
      fn_insts_blocks_flat, listTheory.MAP_FLAT,
      FLAT_FLAT, listTheory.MAP_MAP_o, combinTheory.o_DEF]) >>
  `new = db` suffices_by metis_tac[] >>
  irule (Q.ISPEC `\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)`
           all_distinct_flat_map_unique) >>
  conj_tac >- (qexists_tac `renamed` >> simp[]) >>
  qexists_tac `z` >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_external_collapsed_phi_clear:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  current_wf_inserted_phi_at A renamed h q v /\
  simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var z]|> /\
  MEM db renamed /\ MEM di db.bb_instructions /\ MEM z di.inst_outputs /\
  db.bb_label <> new.bb_label ==>
  !oi. MEM oi old.bb_instructions /\ oi.inst_opcode = PHI ==> ~MEM v oi.inst_outputs
Proof
  rpt strip_tac >>
  `!ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs` by
    (rpt strip_tac >> drule_all current_wf_external_output_disjoint >>
     metis_tac[]) >>
  `?k. k < LENGTH old.bb_instructions /\ EL k old.bb_instructions = oi` by
    metis_tac[listTheory.MEM_EL] >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf oi` by metis_tac[venomWfTheory.fn_inst_wf_def,
    venomExecPropsTheory.lookup_block_MEM] >>
  `oi.inst_outputs = [v]` by
    (fs[venomWfTheory.inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >> gvs[]) >>
  `(EL k old.bb_instructions).inst_opcode = PHI /\
    (EL k old.bb_instructions).inst_outputs = [v]` by simp[] >>
  drule_all current_wf_exceptional_inserted_copy >> strip_tac >>
  `n = z` by fs[venomInstTheory.instruction_component_equality] >> gvs[] >>
  gvs[current_wf_original_phi_at_def] >>
  metis_tac[listTheory.EL_MEM]
QED
