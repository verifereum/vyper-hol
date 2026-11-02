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

Theorem current_var_prefix_list_weaken:
  LIST_REL (\a b. current_var_prefix pm li v hp' a b /\
    (a <> b ==> MEM a.bb_label done')) xs ys /\
  (!x. MEM x hp ==> MEM x hp') /\
  (!x. MEM x done' ==> MEM x done) ==>
  LIST_REL (\a b. current_var_prefix pm li v hp a b /\
    (a <> b ==> MEM a.bb_label done)) xs ys
Proof
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >>
  simp[] >> rpt strip_tac >>
  irule current_var_prefix_weaken >> qexists_tac `hp'` >> simp[]
QED

Theorem current_var_prefix_list_compose:
  LIST_REL (\a b. current_var_prefix pm li v hp a b /\
    (a <> b ==> MEM a.bb_label mid)) xs ys /\
  LIST_REL (\a b. current_var_prefix pm li v mid a b /\
    (a <> b ==> MEM a.bb_label done)) ys zs /\
  (!x. MEM x hp ==> MEM x mid) /\
  (!x. MEM x mid ==> MEM x done) ==>
  LIST_REL (\a b. current_var_prefix pm li v hp a b /\
    (a <> b ==> MEM a.bb_label done)) xs zs
Proof
  map_every qid_spec_tac [`zs`, `ys`] >>
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >> simp[] >>
  rpt strip_tac
  >- metis_tac[current_var_prefix_compose]
  >- metis_tac[current_var_prefix_label]
  >> metis_tac[]
QED

Theorem current_var_prefix_map_step:
  ~MEM f hp /\ current_placement_live li v f ==>
  LIST_REL (\a b. current_var_prefix pm li v hp a b /\
    (a <> b ==> MEM a.bb_label (f::hp))) bbs
    (MAP (\bb. if bb.bb_label = f then
      insert_phi_at_block (build_phi_inst_supply id v
        (case ALOOKUP pm f of SOME ps => ps | NONE => [])) bb else bb) bbs)
Proof
  Induct_on `bbs` >> simp[] >> strip_tac >>
  Cases_on `h.bb_label = f` >> gvs[current_var_prefix_insert]
QED

Theorem current_placement_live_lookup:
  current_placement_live li v f =
    (case ALOOKUP li f of NONE => F | SOME vs => MEM v vs)
Proof
  Cases_on `ALOOKUP li f` >> simp[current_placement_live_def]
QED

Theorem current_process_frontiers_prefix:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s v pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    LIST_REL (\a b. current_var_prefix pm li v hp a b /\
      (a <> b ==> MEM a.bb_label hp')) bbs bbs'
Proof
  Induct >- simp[process_frontiers_supply_def, LIST_REL_EL_EQN] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[process_frontiers_supply_def, GSYM current_placement_live_lookup] >>
  Cases_on `MEM h hp` >> simp[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  Cases_on `current_placement_live li v h` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      drule current_process_frontiers_processed >> strip_tac >>
      asm "ih" drule >> strip_tac >>
      irule current_var_prefix_list_compose >>
      qexists_tac `h::hp` >>
      goal_assum $ drule_at Any >> simp[] >>
      irule (SRULE [] current_var_prefix_map_step) >> simp[]) >>
  strip_tac >> asm "ih" drule >> strip_tac >>
  irule current_var_prefix_list_weaken >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem current_var_prefix_list_then:
  LIST_REL (\a b. current_var_prefix pm li v hp a b /\
    (a <> b ==> MEM a.bb_label mid)) xs ys /\
  LIST_REL (current_var_prefix pm li v mid) ys zs /\
  (!x. MEM x hp ==> MEM x mid) ==>
  LIST_REL (current_var_prefix pm li v hp) xs zs
Proof
  map_every qid_spec_tac [`zs`, `ys`] >>
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >> simp[] >>
  rpt strip_tac >- metis_tac[current_var_prefix_compose] >> metis_tac[]
QED

Theorem current_insert_var_prefix:
  !s v df pm li bbs roots hp bbs' s'.
    insert_phis_for_var_supply s v df pm li bbs roots hp = (bbs',s') ==>
    LIST_REL (current_var_prefix pm li v hp) bbs bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >> rpt strip_tac
  >- gvs[insert_phis_for_var_supply_def, LIST_REL_EL_EQN] >>
  gvs[Once insert_phis_for_var_supply_def] >>
  pairarg_tac >> gvs[] >>
  drule current_process_frontiers_prefix >> strip_tac >>
  drule current_process_frontiers_processed >> strip_tac >>
  irule current_var_prefix_list_then >>
  goal_assum $ drule_at Any >> goal_assum $ drule_at Any >> simp[]
QED
