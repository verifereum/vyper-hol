Theory loadElimReachableNormalize
Ancestors
  loadElimReachableSSA loadElimNormalizeAvailability simplifyCfgPhiRepair
  venomExecProofs dfgAnalysisProps dfgDefs venomWf venomInst
  simplifyCfgLabelProps

Theorem le_available_definition_reachable:
  wf_function fn /\ ssa_form fn /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  MEM u di.inst_outputs /\ def_available_at fn bb point u ==>
  fn_reachable fn db.bb_label
Proof
  strip_tac >> fs[def_available_at_def] >>
  `def_inst = di` by metis_tac[ssa_form_output_unique] >>
  `def_bb = db` by metis_tac[wf_function_instruction_block] >>
  metis_tac[fn_dominates_dom_reachable]
QED

Theorem le_reachable_normalize_operand_available:
  !dfg visited op v.
  dfg = dfg_build_function fn /\ wf_function fn /\ fn_inst_wf fn /\
  le_reachable_ssa fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  (!u. op = Var u ==> def_available_at fn bb point u) /\
  normalize_operand dfg visited op = Var v ==>
  def_available_at fn bb point v
Proof
  recInduct normalize_operand_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `MEM v visited` >- gvs[Once normalize_operand_def] >>
      Cases_on `FLOOKUP dfg.dfg_defs v` >- gvs[Once normalize_operand_def] >>
      rename1 `FLOOKUP dfg.dfg_defs v = SOME di` >>
      reverse (Cases_on `di.inst_opcode = ASSIGN`)
      >- gvs[Once normalize_operand_def] >>
      Cases_on `di.inst_operands` >- gvs[Once normalize_operand_def] >>
      Cases_on `t` >> gvs[Once normalize_operand_def] >>
      `normalize_operand (dfg_build_function fn) (v::visited) h = Var v'` by
        (qpat_x_assum `normalize_operand _ visited _ = _` mp_tac >>
         simp[Once normalize_operand_def]) >>
      first_x_assum irule >> simp[] >> rpt strip_tac >> gvs[] >>
      `dfg_get_def (dfg_build_function fn) v = SOME di` by simp[dfg_get_def_def] >>
      drule dfg_build_function_correct >> strip_tac >>
      `?db. MEM db fn.fn_blocks /\ MEM di db.bb_instructions` by
        (gvs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
      `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
      `fn_reachable fn db.bb_label` by
        (irule le_available_definition_reachable >> metis_tac[]) >>
      `def_available_at fn db (SOME di) u` by
        (irule le_reachable_ssa_ordinary_available >> simp[] >> metis_tac[]) >>
      irule le_available_via_definition >>
      metis_tac[])
  >- simp[normalize_operand_def]
  >- simp[normalize_operand_def]
QED

Theorem le_reachable_normalize_var_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_available_at fn bb point u /\
  normalize_operand (dfg_build_function fn) visited (Var u) = Var v ==>
  def_available_at fn bb point v
Proof
  strip_tac >> irule le_reachable_normalize_operand_available >> simp[] >>
  qexistsl [`Var u`, `visited`] >> simp[]
QED

Theorem le_reachable_normalize_ordinary_use_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  fn_reachable fn bb.bb_label /\
  inst.inst_opcode <> PHI /\ MEM addr inst.inst_operands /\
  normalize_operand (dfg_build_function fn) [] addr = Var v ==>
  def_available_at fn bb (SOME inst) v
Proof
  strip_tac >> irule le_reachable_normalize_operand_available >> simp[] >>
  qexistsl [`addr`, `[]`] >> simp[] >> rpt strip_tac >> gvs[] >>
  irule le_reachable_ssa_ordinary_available >> metis_tac[]
QED
