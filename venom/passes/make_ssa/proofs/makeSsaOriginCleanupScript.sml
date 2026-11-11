Theory makeSsaOriginCleanup
Ancestors
  makeSsaOriginInvariant makeSsaDefs venomInst list

Theorem origin_before_after:
  origin_before_cleanup fn orig i ==> origin_after_cleanup fn orig i
Proof
  simp[origin_before_cleanup_def, origin_after_cleanup_def] >> metis_tac[]
QED

Theorem origin_phi_change_id:
  origin_phi fn orig i ==> origin_phi fn orig (i with inst_id := id)
Proof
  simp[origin_phi_def]
QED

Theorem origin_remove_self_member:
  !out ops op. MEM op (remove_current_phi_self out ops) ==> MEM op ops
Proof
  ho_match_mp_tac remove_current_phi_self_ind >>
  simp[remove_current_phi_self_def] >> rpt strip_tac >>
  gvs[] >> Cases_on `out' = out` >> gvs[] >> metis_tac[]
QED

Theorem origin_phi_values_member:
  !ops vs. current_phi_values ops = SOME vs ==>
  !v. MEM v vs ==> MEM (Var v) ops
Proof
  ho_match_mp_tac current_phi_values_ind >>
  simp[current_phi_values_def] >> rpt gen_tac >>
  rpt CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem origin_simplify_raw:
  i.inst_opcode = PHI /\ origin_phi fn orig i ==>
  ((simplify_current_phi_raw i).inst_opcode = NOP /\
   (simplify_current_phi_raw i).inst_outputs = [] /\
   (simplify_current_phi_raw i).inst_operands = []) \/
  (((simplify_current_phi_raw i).inst_opcode = PHI \/
    (simplify_current_phi_raw i).inst_opcode = ASSIGN) /\
   origin_phi fn orig (simplify_current_phi_raw i))
Proof
  rpt strip_tac >> simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output i.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x i.inst_operands)` >> simp[] >>
  Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[] >>
  simp[origin_phi_def] >>
  gvs[origin_phi_def] >> qexists_tac `inst` >> simp[] >>
  `MEM (Var h) i.inst_operands` by
    (irule origin_remove_self_member >>
     qexists_tac `x` >>
     drule origin_phi_values_member >> simp[]) >>
  metis_tac[]
QED

Theorem origin_simplify_phi:
  i.inst_opcode = PHI /\ origin_before_cleanup fn orig i ==>
  !id. origin_after_cleanup fn orig (simplify_current_phi i with inst_id := id)
Proof
  rpt strip_tac >>
  `origin_phi fn orig i` by
    (gvs[origin_before_cleanup_def, origin_ordinary_def]) >>
  drule_all origin_simplify_raw >> strip_tac >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[origin_after_cleanup_def] >>
  metis_tac[origin_phi_change_id]
QED

Theorem origin_reassign_suffix:
  !ids pre suffix. LENGTH ids = LENGTH pre ==>
    reassign_current_inst_ids (ids ++ MAP (\i. i.inst_id) suffix) (pre ++ suffix) =
    reassign_current_inst_ids ids pre ++ suffix
Proof
  Induct >> Cases_on `pre` >> simp[reassign_current_inst_ids_def] >>
  Induct_on `suffix` >> simp[reassign_current_inst_ids_def]
QED

Theorem origin_reassign_every:
  !insts ids. EVERY (\i. !id. origin_after_cleanup fn orig (i with inst_id := id)) insts ==>
  EVERY (origin_after_cleanup fn orig) (reassign_current_inst_ids ids insts)
Proof
  Induct >> Cases_on `ids` >> simp[reassign_current_inst_ids_def] >>
  rpt strip_tac >> simp[] >>
  `origin_after_cleanup fn orig h` by
    (qpat_x_assum `!id. _` (qspec_then `h.inst_id` mp_tac) >> simp[]) >>
  simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i insts ==> _` drule >>
  disch_then (qspec_then `e.inst_id` mp_tac) >> simp[]
QED

Theorem origin_cleanup_parts:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
  EVERY (origin_before_cleanup fn orig) insts ==>
  ?pre suffix changed.
    insts = pre ++ suffix /\ ordinary = changed ++ suffix /\
    LENGTH pre = LENGTH phis + LENGTH changed /\
    EVERY (\i. !id. origin_after_cleanup fn orig (i with inst_id := id)) (phis ++ changed) /\
    EVERY (origin_before_cleanup fn orig) suffix
Proof
  Induct
  >- (simp[simplify_current_phi_prefix_parts_def] >> rpt strip_tac >> gvs[] >>
      qexistsl [`[]`, `[]`, `[]`] >> simp[]) >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> rpt strip_tac >> gvs[] >>
      qexistsl [`[]`, `h::insts`, `[]`] >> simp[]) >>
  simp[simplify_current_phi_prefix_parts_def] >> pairarg_tac >> gvs[] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  simp[] >> rpt strip_tac >> gvs[]
  >- (qexistsl [`h::pre`, `suffix`, `changed`] >>
      simp[] >> irule origin_simplify_phi >> simp[]) >>
  qexistsl [`h::pre`, `suffix`, `simplify_current_phi h::changed`] >>
  simp[] >> irule origin_simplify_phi >> simp[]
QED

Theorem origin_cleanup_prefix:
  EVERY (origin_before_cleanup fn orig) insts ==>
  EVERY (origin_after_cleanup fn orig) (simplify_current_phi_prefix insts)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >>
  pairarg_tac >> gvs[] >> drule_all origin_cleanup_parts >> strip_tac >>
  gvs[MAP_APPEND] >>
  `LENGTH (MAP (\i. i.inst_id) pre) = LENGTH (phis ++ changed)` by simp[] >>
  `phis ++ (changed ++ suffix) = (phis ++ changed) ++ suffix` by simp[] >>
  simp[GSYM APPEND_ASSOC, origin_reassign_suffix] >>
  conj_tac
  >- (irule origin_reassign_every >> simp[]) >>
  gvs[EVERY_MEM] >> metis_tac[origin_before_after]
QED

Theorem origin_cleanup_block:
  EVERY (origin_before_cleanup fn orig) bb.bb_instructions ==>
  EVERY (origin_after_cleanup fn orig)
    (simplify_current_phi_block bb).bb_instructions
Proof
  simp[simplify_current_phi_block_def] >>
  Cases_on `bb.bb_instructions` >> simp[] >>
  IF_CASES_TAC >> simp[origin_cleanup_prefix] >>
  gvs[EVERY_MEM] >> metis_tac[origin_before_after]
QED

Theorem origin_cleanup_blocks:
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (origin_after_cleanup fn orig) bb.bb_instructions)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> Cases_on `blocks_have_leading_phi bbs` >>
  simp[simplify_current_phis_if_def, simplify_current_phis_def, EVERY_MAP] >>
  rpt strip_tac >>
  gvs[EVERY_MEM] >>
  metis_tac[SRULE [EVERY_MEM] origin_cleanup_block, origin_before_after]
QED
