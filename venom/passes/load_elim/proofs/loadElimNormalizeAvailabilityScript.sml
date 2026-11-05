Theory loadElimNormalizeAvailability
Ancestors
  venomWf venomInst venomExecProofs dfgDefs dfgAnalysisProps
  simplifyCfgPhiRepair simplifyCfgStruct simplifyCfgWfssa simplifyCfgLabelProps
  list rich_list

Theorem le_path_append_prefix:
  !pre post. is_fn_path fn (pre ++ post) ==> is_fn_path fn pre
Proof
  Induct >> simp[is_fn_path_def] >> Cases_on `pre` >>
  gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem le_path_member_prefix:
  is_fn_path fn path /\ MEM d path ==>
  ?pre post. path = pre ++ [d] ++ post /\ is_fn_path fn (pre ++ [d])
Proof
  strip_tac >> qpat_x_assum `MEM d path` mp_tac >>
  rewrite_tac[MEM_SPLIT] >> strip_tac >>
  qexistsl [`l1`, `l2`] >> gvs[] >>
  irule le_path_append_prefix >> qexists `l2` >> asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

Theorem le_fn_dominates_trans:
  fn_dominates fn a b /\ fn_dominates fn b c ==>
  fn_dominates fn a c
Proof
  strip_tac >> simp[fn_dominates_def] >> conj_tac
  >- metis_tac[fn_dominates_def] >>
  rpt strip_tac >>
  `MEM b path` by metis_tac[fn_dominates_def] >>
  drule_all le_path_member_prefix >> strip_tac >>
  `HD (pre ++ [b]) = HD path` by (gvs[] >> Cases_on `pre` >> simp[]) >>
  `MEM a (pre ++ [b])` by
    (qpat_x_assum `fn_dominates fn a b` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem le_fn_dominates_antisym:
  fn_dominates fn a b /\ fn_dominates fn b a ==> a = b
Proof
  strip_tac >> Cases_on `a = b` >- simp[] >>
  `fn_reachable fn b` by metis_tac[fn_dominates_def] >>
  gvs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `MEM a (pre ++ [b])` by
    (qpat_x_assum `fn_dominates fn a b` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  `MEM a pre` by gvs[MEM_APPEND] >>
  `is_fn_path fn pre` by (irule le_path_append_prefix >> metis_tac[]) >>
  drule_all le_path_member_prefix >> strip_tac >>
  `HD (pre' ++ [a]) = entry` by
    (gvs[] >> Cases_on `pre'` >> gvs[]) >>
  `MEM b (pre' ++ [a])` by
    (qpat_x_assum `fn_dominates fn b a` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  gvs[MEM_APPEND]
QED

Theorem le_available_via_definition:
  wf_function fn /\ ssa_form fn /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  MEM u di.inst_outputs /\ def_available_at fn db (SOME di) v /\
  def_available_at fn bb point u ==>
  def_available_at fn bb point v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at fn bb point u` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `def_inst = di` by metis_tac[ssa_form_output_unique] >>
  `def_bb = db` by metis_tac[wf_function_instruction_block] >> gvs[] >>
  qpat_x_assum `def_available_at fn db (SOME di) v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  rename1 `MEM v vi.inst_outputs` >>
  `fn_dominates fn def_bb.bb_label bb.bb_label` by
    metis_tac[le_fn_dominates_trans] >>
  simp[def_available_at_def] >> qexistsl [`def_bb`, `vi`] >> simp[] >>
  strip_tac >> gvs[] >>
  `db.bb_label = bb.bb_label` by metis_tac[le_fn_dominates_antisym] >>
  `db = bb` by metis_tac[same_label_same_block] >> gvs[] >>
  Cases_on `point` >- simp[] >> gvs[] >>
  `j = i'` by (irule inst_ids_el_eq >> qexistsl [`bb`, `fn`] >>
    gvs[wf_function_def] >> metis_tac[]) >>
  qexistsl [`i`, `j'`] >> simp[]
QED

Theorem le_normalize_operand_available:
  !dfg visited op v.
  dfg = dfg_build_function fn /\ wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  MEM bb fn.fn_blocks /\
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
      `def_available_at fn db (SOME di) u` by
        (gvs[wf_ssa_def, def_dominates_uses_def] >>
         first_x_assum drule_all >> simp[]) >>
      irule le_available_via_definition >>
      gvs[wf_ssa_def] >> qexistsl [`db`, `di`, `v`] >> simp[])
  >- simp[normalize_operand_def]
  >- simp[normalize_operand_def]
QED

Theorem le_normalize_var_available:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  MEM bb fn.fn_blocks /\ def_available_at fn bb point u /\
  normalize_operand (dfg_build_function fn) visited (Var u) = Var v ==>
  def_available_at fn bb point v
Proof
  strip_tac >> irule le_normalize_operand_available >> simp[] >>
  qexistsl [`Var u`, `visited`] >> simp[]
QED

Theorem le_normalize_ordinary_use_available:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ MEM addr inst.inst_operands /\
  normalize_operand (dfg_build_function fn) [] addr = Var v ==>
  def_available_at fn bb (SOME inst) v
Proof
  strip_tac >> irule le_normalize_operand_available >> simp[] >>
  qexistsl [`addr`, `[]`] >> simp[] >>
  rpt strip_tac >> gvs[wf_ssa_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> simp[]
QED
