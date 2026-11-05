Theory makeSsaOriginInsert
Ancestors
  makeSsaOriginInvariant makeSsaCurrentDefs makeSsaCurrentProps
  makeSsaDefs venomWf venomInst irSupply o1PassContract list alist

Theorem origin_compute_defs_key:
  MEM v (MAP FST (compute_defs fn.fn_blocks)) ==>
  ?inst. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs
Proof
  simp[compute_defs_keys, block_assignments_def, fn_insts_def,
       fn_insts_blocks_MEM, MEM_nub, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_nub, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem origin_phi_operand_shape:
  !ops. phi_well_formed ops ==>
    !op. MEM op ops ==> ?x. op = Var x \/ op = Label x
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem origin_input_identity:
  fn_inst_wf fn /\ MEM i (fn_insts fn) ==>
  origin_before_cleanup fn I i
Proof
  rpt strip_tac >>
  Cases_on `i.inst_opcode = PHI`
  >- (`inst_wf i` by
        (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
      `LENGTH i.inst_outputs = 1 /\ phi_well_formed i.inst_operands` by
        gvs[inst_wf_def] >>
      `?w. i.inst_outputs = [w]` by
        (qpat_x_assum `LENGTH _ = 1` mp_tac >>
         simp[LENGTH_EQ_NUM_compute]) >>
      simp[origin_before_cleanup_def, origin_phi_def] >>
      disj2_tac >> qexists_tac `i` >>
      simp[] >> metis_tac[origin_phi_operand_shape]) >>
  simp[origin_before_cleanup_def, origin_ordinary_def] >>
  qexists_tac `i` >> simp[] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  Cases_on `EL x i.inst_operands` >> simp[]
QED

Theorem origin_init_coherent:
  origin_coherent orig (SND (init_current_rename_state defs))
Proof
  simp[init_current_rename_state_def, origin_coherent_def, MEM_MAP] >>
  rpt strip_tac >> gvs[]
QED

Theorem origin_init_covered:
  EVERY (\p. MEM (FST p) s.irs_used_vars) defs ==>
  origin_stacks_covered s (SND (init_current_rename_state defs))
Proof
  simp[init_current_rename_state_def, origin_stacks_covered_def,
       MEM_MAP, EVERY_MEM] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem origin_build_phi:
  (?inst. MEM inst (fn_insts fn) /\ MEM (orig v) inst.inst_outputs) ==>
  origin_before_cleanup fn orig (build_phi_inst_supply id v ls)
Proof
  simp[origin_before_cleanup_def, origin_phi_def, build_phi_inst_supply_def] >>
  rpt strip_tac >> disj2_tac >> qexists_tac `inst` >>
  simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem origin_insert_block:
  EVERY (origin_before_cleanup fn orig) bb.bb_instructions /\
  origin_before_cleanup fn orig phi ==>
  EVERY (origin_before_cleanup fn orig)
    (insert_phi_at_block phi bb).bb_instructions
Proof
  simp[insert_phi_at_block_def]
QED

Theorem origin_process_frontiers:
  !fs s v pm li bbs rest hp bbs' rest' hp' s' fn orig.
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') /\
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs /\
  (?inst. MEM inst (fn_insts fn) /\ MEM (orig v) inst.inst_outputs) ==>
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule >>
      disch_then (qspecl_then [`fn`, `orig`] mp_tac) >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule >>
      disch_then (qspecl_then [`fn`, `orig`] mp_tac) >> simp[] >> metis_tac[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  asm "ih" drule >>
  disch_then (qspecl_then [`fn`, `orig`] mp_tac) >>
  asm_x "ih" kall_tac >>
  qpat_x_assum `process_frontiers_supply _ _ _ _ _ _ _ _ = _` kall_tac >>
  (impl_tac >- (
    conj_tac
    >- (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
        Cases_on `bb.bb_label = h` >>
        gvs[insert_phi_at_block_def, EVERY_MEM] >>
        metis_tac[origin_build_phi]) >>
    metis_tac[])) >> simp[]
QED

Theorem origin_insert_phis_for_var:
  !s v df pm li bbs wl hp bbs' s' fn orig.
  insert_phis_for_var_supply s v df pm li bbs wl hp = (bbs',s') /\
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs /\
  (?inst. MEM inst (fn_insts fn) /\ MEM (orig v) inst.inst_outputs) ==>
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`fn`, `orig`] irule) >>
  conj_tac >- metis_tac[] >>
  drule origin_process_frontiers >>
  disch_then (qspecl_then [`fn`, `orig`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem origin_add_phi_nodes:
  !defs s df pm li bbs bbs' s' fn orig.
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs /\
  EVERY (\p. ?inst. MEM inst (fn_insts fn) /\
                    MEM (orig (FST p)) inst.inst_outputs) defs ==>
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (qspecl_then [`fn`, `orig`] irule) >>
  simp[] >> drule origin_insert_phis_for_var >>
  disch_then (qspecl_then [`fn`, `orig`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem origin_input_blocks:
  fn_inst_wf fn ==>
  EVERY (\bb. EVERY (origin_before_cleanup fn I) bb.bb_instructions) fn.fn_blocks
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> irule origin_input_identity >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem origin_compute_defs_outputs:
  EVERY (\p. ?inst. MEM inst (fn_insts fn) /\ MEM (FST p) inst.inst_outputs)
    (compute_defs fn.fn_blocks)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> irule origin_compute_defs_key >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem origin_operand_vars_mem:
  !ops v. MEM v (venomInst$operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct >- simp[venomInstTheory.operand_vars_def] >> Cases_on `h` >>
  simp[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >> metis_tac[]
QED

Theorem origin_inst_covered_iff:
  origin_inst_covered s i <=> ssa_vars_covered s (inst_ir_vars i)
Proof
  simp[origin_inst_covered_def, ssa_vars_covered_def, inst_ir_vars_def,
       inst_uses_def, EVERY_MEM, origin_operand_vars_mem] >> metis_tac[]
QED

Theorem origin_blocks_covered_iff:
  EVERY (\bb. EVERY (origin_inst_covered s) bb.bb_instructions) bbs <=>
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs))
Proof
  simp[block_ir_vars_def, ssa_vars_covered_def,
       EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM, GSYM ssa_vars_covered_def, GSYM origin_inst_covered_iff]
QED
