Theory makeSsaCurrentPlacement
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaDefs venomInst list alist

Definition current_frontier_edge_def:
  current_frontier_edge df d f <=>
    ?fs. ALOOKUP df d = SOME fs /\ MEM f fs
End

Definition current_placement_live_def:
  current_placement_live li v f <=>
    ?vs. ALOOKUP li f = SOME vs /\ MEM v vs
End

Definition current_phi_prefix_def:
  current_phi_prefix pm vars old new <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      EVERY (\i. ?id v. MEM v vars /\
        i = build_phi_inst_supply id v
          (case ALOOKUP pm old.bb_label of SOME ps => ps | NONE => [])) pre
End

Definition current_var_prefix_def:
  current_var_prefix pm li v hp old new <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      LENGTH pre <= 1 /\
      (pre <> [] ==> ~MEM old.bb_label hp /\
        current_placement_live li v old.bb_label) /\
      EVERY (\i. ?id. i = build_phi_inst_supply id v
        (case ALOOKUP pm old.bb_label of SOME ps => ps | NONE => [])) pre
End

Theorem current_var_prefix_refl[simp]:
  current_var_prefix pm li v hp bb bb
Proof
  simp[current_var_prefix_def] >> qexists_tac `[]` >> simp[]
QED

Theorem current_var_prefix_label:
  current_var_prefix pm li v hp old new ==> new.bb_label = old.bb_label
Proof
  simp[current_var_prefix_def] >> rpt strip_tac >> gvs[]
QED

Theorem current_var_prefix_provenance:
  current_var_prefix pm li v hp old new ==>
  current_phi_prefix pm [v] old new
Proof
  simp[current_var_prefix_def, current_phi_prefix_def] >> rpt strip_tac >>
  qexists_tac `pre` >> simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_var_prefix_insert:
  ~MEM bb.bb_label hp /\ current_placement_live li v bb.bb_label ==>
  current_var_prefix pm li v hp bb
    (insert_phi_at_block (build_phi_inst_supply id v
      (case ALOOKUP pm bb.bb_label of SOME ps => ps | NONE => [])) bb)
Proof
  rpt strip_tac >> simp[current_var_prefix_def, insert_phi_at_block_def] >>
  qexists_tac `[build_phi_inst_supply id v
      (case ALOOKUP pm bb.bb_label of SOME ps => ps | NONE => [])]` >> simp[] >>
  qexists_tac `id` >> simp[]
QED

Theorem current_var_prefix_map_insert:
  ~MEM f hp /\ current_placement_live li v f ==>
  LIST_REL (current_var_prefix pm li v hp) bbs
    (MAP (\bb. if bb.bb_label = f then
      insert_phi_at_block (build_phi_inst_supply id v
        (case ALOOKUP pm f of SOME ps => ps | NONE => [])) bb else bb) bbs)
Proof
  Induct_on `bbs` >> simp[] >> strip_tac >>
  Cases_on `h.bb_label = f` >> gvs[current_var_prefix_insert]
QED

Theorem current_process_frontiers_processed:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s v pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    !x. MEM x hp' <=> MEM x hp \/ MEM x fs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[] >> metis_tac[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >> simp[] >> metis_tac[]
QED

Theorem current_process_dead_frontier:
  ~MEM f hp /\ ~current_placement_live li v f ==>
  process_frontiers_supply s v pm li bbs rest hp [f] =
    (bbs,rest,f::hp,s)
Proof
  simp[current_placement_live_def, process_frontiers_supply_def] >>
  Cases_on `ALOOKUP li f` >> simp[]
QED

Theorem current_process_duplicate_frontier:
  process_frontiers_supply s v pm li bbs rest hp [f;f] =
  process_frontiers_supply s v pm li bbs rest hp [f]
Proof
  simp[process_frontiers_supply_def] >>
  Cases_on `MEM f hp` >> simp[process_frontiers_supply_def] >>
  Cases_on `ALOOKUP li f` >> simp[process_frontiers_supply_def] >>
  Cases_on `MEM v x` >> simp[process_frontiers_supply_def] >>
  rpt CASE_TAC >> simp[process_frontiers_supply_def] >>
  pairarg_tac >> simp[process_frontiers_supply_def]
QED

Theorem current_var_prefix_processed:
  current_var_prefix pm li v hp old new /\ MEM old.bb_label hp ==>
  new = old
Proof
  simp[current_var_prefix_def] >> rpt strip_tac >>
  Cases_on `pre` >> gvs[]
QED

Theorem current_var_prefix_weaken:
  current_var_prefix pm li v hp' old new /\
  (!x. MEM x hp ==> MEM x hp') ==>
  current_var_prefix pm li v hp old new
Proof
  simp[current_var_prefix_def] >> rpt strip_tac >>
  qexists_tac `pre` >> simp[] >> metis_tac[]
QED

Theorem current_var_prefix_compose:
  current_var_prefix pm li v hp a b /\
  current_var_prefix pm li v hp' b c /\
  (!x. MEM x hp ==> MEM x hp') /\
  (a <> b ==> MEM a.bb_label hp') ==>
  current_var_prefix pm li v hp a c
Proof
  rpt strip_tac >> Cases_on `a = b`
  >- (gvs[] >> metis_tac[current_var_prefix_weaken]) >>
  `b.bb_label = a.bb_label` by metis_tac[current_var_prefix_label] >>
  `c = b` by metis_tac[current_var_prefix_processed] >> simp[]
QED
