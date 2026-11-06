Theory makeSsaOriginRename
Ancestors
  makeSsaOriginInsert makeSsaOriginInvariant makeSsaCurrentDefs
  makeSsaCurrentProps makeSsaCurrentInduct irSupply venomInst list alist

Theorem origin_rename_operands:
  !ops rs orig. origin_coherent orig (SND rs) ==>
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    (rename_current_operands rs ops) =
  MAP (\op. case op of Var u => Var (orig u) | _ => op) ops
Proof
  Induct >- simp[rename_current_operands_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[rename_current_operands_def] >> rpt strip_tac >>
  metis_tac[origin_latest_current_name]
QED

Theorem origin_rename_outputs:
  !outs s rs rs' s' outs' orig.
  rename_current_outputs s rs outs = (rs',s',outs') /\
  ssa_vars_covered s outs /\ origin_coherent orig (SND rs) /\
  origin_stacks_covered s (SND rs) ==>
  ?orig'. origin_agrees s orig orig' /\ MAP orig' outs' = MAP orig outs /\
    origin_coherent orig' (SND rs') /\
    origin_stacks_covered s' (SND rs') /\
    ssa_vars_covered s' outs' /\ ssa_supply_extends s s'
Proof
  Induct
  >- (simp[rename_current_outputs_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `orig` >> simp[origin_agrees_refl, ssa_supply_extends_refl,
                                ssa_vars_covered_def]) >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  gvs[ssa_vars_covered_def] >>
  drule_all origin_push_current_name >> strip_tac >>
  `ssa_vars_covered s'' outs` by
    (gvs[ssa_vars_covered_def, EVERY_MEM, ssa_supply_extends_def] >> metis_tac[]) >>
  `MEM name s''.irs_used_vars` by
    (irule (cj 2 push_current_name_covered) >>
     metis_tac[origin_stacks_values_covered]) >>
  asm "ih" drule >> disch_then (qspec_then `orig'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `orig''` >>
  `MAP orig' outs = MAP orig outs` by
    (irule MAP_CONG >> simp[] >> gvs[origin_agrees_def, EVERY_MEM]) >>
  asm_x "ih" kall_tac >>
  gvs[origin_agrees_def, ssa_vars_covered_def, ssa_supply_extends_def,
      EVERY_MEM] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem origin_mapped_var_member:
  !ops orig v.
  MEM (Var v) (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops) <=>
  ?u. MEM (Var u) ops /\ orig u = v
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >> metis_tac[]
QED

Theorem origin_mapped_operand_shape:
  !ops orig.
  (!op. MEM op (MAP (\op. case op of Var u => Var (orig u) | _ => op) ops) ==>
     ?x. op = Var x \/ op = Label x) <=>
  (!op. MEM op ops ==> ?x. op = Var x \/ op = Label x)
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem origin_phi_same_image:
  origin_phi fn orig i /\ i'.inst_opcode = i.inst_opcode /\
  MAP orig' i'.inst_outputs = MAP orig i.inst_outputs /\
  MAP (\op. case op of Var u => Var (orig' u) | _ => op) i'.inst_operands =
  MAP (\op. case op of Var u => Var (orig u) | _ => op) i.inst_operands /\
  i.inst_opcode = PHI ==>
  origin_phi fn orig' i'
Proof
  simp[origin_phi_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `inst` >> simp[] >> conj_tac
  >- (qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
      metis_tac[origin_mapped_operand_shape]) >>
  rpt strip_tac >>
  `MEM (Var (orig' u))
    (MAP (\op. case op of Var x => Var (orig' x) | _ => op) i'.inst_operands)` by
    (simp[origin_mapped_var_member] >> metis_tac[]) >>
  qpat_x_assum `MAP _ _ = MAP _ _` (fn th => fs[th]) >>
  gvs[origin_mapped_var_member] >> metis_tac[]
QED

Theorem origin_before_cleanup_same_image:
  origin_before_cleanup fn orig i /\
  i'.inst_id = i.inst_id /\ i'.inst_opcode = i.inst_opcode /\
  MAP orig' i'.inst_outputs = MAP orig i.inst_outputs /\
  MAP (\op. case op of Var u => Var (orig' u) | _ => op) i'.inst_operands =
  MAP (\op. case op of Var u => Var (orig u) | _ => op) i.inst_operands ==>
  origin_before_cleanup fn orig' i'
Proof
  simp[origin_before_cleanup_def] >> rpt strip_tac
  >- (disj1_tac >> gvs[origin_ordinary_def] >> metis_tac[]) >>
  disj2_tac >> simp[] >> irule origin_phi_same_image >> metis_tac[]
QED

Theorem origin_rename_inst:
  rename_current_inst s rs i = (rs',s',i') /\
  origin_inst_covered s i /\ origin_before_cleanup fn orig i /\
  origin_coherent orig (SND rs) /\ origin_stacks_covered s (SND rs) ==>
  ?orig'. origin_agrees s orig orig' /\
    origin_before_cleanup fn orig' i' /\ origin_inst_covered s' i' /\
    origin_coherent orig' (SND rs') /\ origin_stacks_covered s' (SND rs') /\
    ssa_supply_extends s s'
Proof
  rpt strip_tac >>
  `ssa_vars_covered s (inst_ir_vars i)` by metis_tac[origin_inst_covered_iff] >>
  `ssa_stacks_covered s (SND rs)` by metis_tac[origin_stacks_values_covered] >>
  drule_all rename_current_inst_covered >> strip_tac >>
  `ssa_vars_covered s i.inst_outputs` by
    gvs[inst_ir_vars_def, ssa_vars_covered_def] >>
  qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all origin_rename_outputs >> strip_tac >>
  qexists_tac `orig'` >> simp[origin_inst_covered_iff] >>
  irule origin_before_cleanup_same_image >>
  qexistsl [`i`, `orig`] >> simp[] >>
  `origin_coherent orig' (SND rs)` by metis_tac[origin_coherent_transport] >>
  simp[origin_rename_operands] >> metis_tac[origin_map_operands_agree]
QED

Theorem origin_inst_covered_extends:
  ssa_supply_extends s s' /\ origin_inst_covered s i ==>
  origin_inst_covered s' i
Proof
  simp[origin_inst_covered_def, ssa_supply_extends_def] >> metis_tac[]
QED

Theorem origin_rename_insts:
  !insts s rs rs' s' insts' fn orig.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  EVERY (origin_inst_covered s) insts /\
  EVERY (origin_before_cleanup fn orig) insts /\
  origin_coherent orig (SND rs) /\ origin_stacks_covered s (SND rs) ==>
  ?orig'. origin_agrees s orig orig' /\
    EVERY (origin_inst_covered s') insts' /\
    EVERY (origin_before_cleanup fn orig') insts' /\
    origin_coherent orig' (SND rs') /\ origin_stacks_covered s' (SND rs') /\
    ssa_supply_extends s s'
Proof
  Induct
  >- (simp[rename_current_block_insts_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `orig` >> simp[origin_agrees_refl, ssa_supply_extends_refl]) >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all origin_rename_inst >> strip_tac >>
  gvs[] >>
  `EVERY (origin_inst_covered s'') insts` by
    (gvs[EVERY_MEM] >> metis_tac[origin_inst_covered_extends]) >>
  `EVERY (origin_before_cleanup fn orig') insts` by
    metis_tac[origin_before_cleanup_list_transport] >>
  asm "ih" drule >> disch_then (qspecl_then [`fn`, `orig'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "ih" kall_tac >>
  qexists_tac `orig''` >> simp[] >>
  rpt conj_tac
  >- metis_tac[origin_agrees_trans, origin_agrees_restrict]
  >- metis_tac[origin_inst_covered_extends]
  >- metis_tac[origin_before_cleanup_transport] >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem origin_update_phi_operands:
  !rs cur ops orig. origin_coherent orig (SND rs) ==>
  MAP (\op. case op of Var u => Var (orig u) | _ => op)
    (update_current_phi_for_pred rs cur ops) =
  MAP (\op. case op of Var u => Var (orig u) | _ => op) ops
Proof
  ho_match_mp_tac update_current_phi_for_pred_ind >>
  simp[update_current_phi_for_pred_def] >> rpt strip_tac >>
  gvs[] >> simp[origin_latest_current_name] >>
  Cases_on `l = cur` >> simp[origin_latest_current_name]
QED

Theorem origin_replace_block_every:
  EVERY P bbs /\ P bb ==> EVERY P (replace_block lbl bb bbs)
Proof
  simp[cfgTransformTheory.replace_block_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem origin_update_phi_inst:
  origin_coherent orig (SND rs) /\ origin_before_cleanup fn orig i ==>
  origin_before_cleanup fn orig
    (if i.inst_opcode <> PHI then i else
      i with inst_operands := update_current_phi_for_pred rs cur i.inst_operands)
Proof
  rpt strip_tac >> IF_CASES_TAC >- simp[] >>
  irule origin_before_cleanup_same_image >>
  qexistsl [`i`, `orig`] >> simp[origin_update_phi_operands]
QED

Theorem origin_update_succ_phis:
  !succs bbs. origin_coherent orig (SND rs) /\
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions)
    (update_current_succ_phis rs cur bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  irule origin_replace_block_every >> simp[] >>
  `MEM x bbs` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  irule origin_update_phi_inst >> metis_tac[]
QED

Theorem origin_update_succ_phis_covered:
  EVERY (\bb. EVERY (origin_inst_covered s) bb.bb_instructions) bbs /\
  origin_stacks_covered s (SND rs) ==>
  EVERY (\bb. EVERY (origin_inst_covered s) bb.bb_instructions)
    (update_current_succ_phis rs cur bbs succs)
Proof
  simp[origin_blocks_covered_iff] >> rpt strip_tac >>
  irule update_current_succ_phis_vars_covered >>
  metis_tac[origin_stacks_values_covered]
QED

Theorem origin_rename_tree:
  (!tree s rs bbs sm ctrs' s' bbs' fn orig.
    rename_current_blocks s rs bbs sm tree = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs /\
    EVERY (\bb. EVERY (origin_inst_covered s) bb.bb_instructions) bbs /\
    origin_coherent orig (SND rs) /\ origin_stacks_covered s (SND rs) ==>
    ?orig'. origin_agrees s orig orig' /\ ssa_supply_extends s s' /\
      EVERY (\bb. EVERY (origin_before_cleanup fn orig') bb.bb_instructions) bbs' /\
      EVERY (\bb. EVERY (origin_inst_covered s') bb.bb_instructions) bbs') /\
  (!trees s ctrs stacks bbs sm ctrs' s' bbs' fn orig.
    rename_current_children s ctrs stacks bbs sm trees = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY (origin_before_cleanup fn orig) bb.bb_instructions) bbs /\
    EVERY (\bb. EVERY (origin_inst_covered s) bb.bb_instructions) bbs /\
    origin_coherent orig stacks /\ origin_stacks_covered s stacks ==>
    ?orig'. origin_agrees s orig orig' /\ ssa_supply_extends s s' /\
      EVERY (\bb. EVERY (origin_before_cleanup fn orig') bb.bb_instructions) bbs' /\
      EVERY (\bb. EVERY (origin_inst_covered s') bb.bb_instructions) bbs')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- suspend "node"
  >- (simp[rename_current_blocks_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `orig` >> simp[origin_agrees_refl, ssa_supply_extends_refl]) >>
  suspend "children"
QED

Resume origin_rename_tree[node]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[rename_current_blocks_def] >>
  Cases_on `lookup_block lbl bbs` >> simp[]
  >- (rpt strip_tac >> gvs[] >> qexists_tac `orig` >>
      simp[origin_agrees_refl, ssa_supply_extends_refl]) >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  `MEM x bbs` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `EVERY (origin_before_cleanup fn orig) x.bb_instructions /\
   EVERY (origin_inst_covered s) x.bb_instructions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all origin_rename_insts >> strip_tac >>
  `EVERY (\bb. EVERY (origin_before_cleanup fn orig') bb.bb_instructions) bbs` by
    (gvs[EVERY_MEM] >> metis_tac[origin_before_cleanup_transport]) >>
  `EVERY (\bb. EVERY (origin_inst_covered s1) bb.bb_instructions) bbs` by
    (gvs[EVERY_MEM] >> metis_tac[origin_inst_covered_extends]) >>
  qabbrev_tac `bs1 = replace_block lbl (x with bb_instructions := insts') bbs` >>
  `EVERY (\bb. EVERY (origin_before_cleanup fn orig') bb.bb_instructions) bs1` by
    (simp[Abbr `bs1`] >> irule origin_replace_block_every >> simp[]) >>
  `EVERY (\bb. EVERY (origin_inst_covered s1) bb.bb_instructions) bs1` by
    (simp[Abbr `bs1`] >> irule origin_replace_block_every >> simp[]) >>
  qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl bs1 succs` >>
  `EVERY (\bb. EVERY (origin_before_cleanup fn orig') bb.bb_instructions)
      (update_current_succ_phis rs1 lbl bs1 succs)` by
    (irule origin_update_succ_phis >> simp[]) >>
  `EVERY (\bb. EVERY (origin_inst_covered s1) bb.bb_instructions)
      (update_current_succ_phis rs1 lbl bs1 succs)` by
    (irule origin_update_succ_phis_covered >> simp[]) >>
  first_x_assum drule >> disch_then (qspecl_then [`fn`, `orig'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `orig''` >> simp[] >>
  metis_tac[origin_agrees_trans, origin_agrees_restrict, ssa_supply_extends_trans]
QED

Resume origin_rename_tree[children]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s rs bbs sm ctrs' s' bbs' fn orig.
    rename_current_blocks _ _ _ _ _ = _ /\ _ ==> _` $ mk_asm "child" >>
  qpat_x_assum `!s ctrs stacks bbs sm ctrs' s' bbs' fn orig.
    rename_current_children _ _ _ _ _ _ = _ /\ _ ==> _` $ mk_asm "rest" >>
  rpt gen_tac >> simp[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  asm "child" drule >> disch_then (qspecl_then [`fn`, `orig`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `origin_coherent orig' stacks` by metis_tac[origin_coherent_transport] >>
  `origin_stacks_covered s'' stacks` by metis_tac[origin_stacks_covered_extends] >>
  asm "rest" drule >> disch_then (qspecl_then [`fn`, `orig'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "child" kall_tac >> asm_x "rest" kall_tac >>
  qexists_tac `orig''` >> simp[] >>
  metis_tac[origin_agrees_trans, origin_agrees_restrict, ssa_supply_extends_trans]
QED

Finalise origin_rename_tree
