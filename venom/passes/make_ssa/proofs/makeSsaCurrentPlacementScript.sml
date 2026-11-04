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

Inductive current_pruned_reach:
  (!d f. MEM d roots /\ current_frontier_edge df d f /\
     current_placement_live li v f ==>
     current_pruned_reach df li v roots f) /\
  (!d f. current_pruned_reach df li v roots d /\
     current_frontier_edge df d f /\ current_placement_live li v f ==>
     current_pruned_reach df li v roots f)
End

Definition current_pruned_closed_def:
  current_pruned_closed df li v roots inserted <=>
    !d f. (MEM d roots \/ MEM d inserted) /\
      current_frontier_edge df d f /\ current_placement_live li v f ==>
      MEM f inserted
End

Theorem current_pruned_reach_live:
  !f. current_pruned_reach df li v roots f ==>
    current_placement_live li v f
Proof
  ho_match_mp_tac current_pruned_reach_ind >> simp[]
QED

Theorem current_pruned_reach_least:
  current_pruned_closed df li v roots inserted ==>
  !f. current_pruned_reach df li v roots f ==> MEM f inserted
Proof
  strip_tac >> ho_match_mp_tac current_pruned_reach_ind >>
  gvs[current_pruned_closed_def] >> metis_tac[]
QED

Theorem current_pruned_reach_closed:
  (!f. MEM f inserted <=> current_pruned_reach df li v roots f) ==>
  current_pruned_closed df li v roots inserted
Proof
  simp[current_pruned_closed_def] >> rpt strip_tac >>
  metis_tac[current_pruned_reach_rules]
QED

Theorem current_frontier_work_needed:
  frontier_work_needed df hp d <=>
    ?f. current_frontier_edge df d f /\ ~MEM f hp
Proof
  Cases_on `ALOOKUP df d` >>
  simp[frontier_work_needed_def, current_frontier_edge_def, EXISTS_MEM]
QED

Theorem current_process_frontiers_pending:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s v pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    !x. MEM x rest' <=> MEM x rest \/
      (MEM x fs /\ ~MEM x hp /\ current_placement_live li v x)
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[process_frontiers_supply_def, GSYM current_placement_live_lookup] >>
  Cases_on `MEM h hp` >> simp[]
  >- (strip_tac >> asm "ih" drule >> simp[] >> metis_tac[]) >>
  Cases_on `current_placement_live li v h` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      asm "ih" drule >> simp[] >> metis_tac[]) >>
  strip_tac >> asm "ih" drule >> simp[] >> metis_tac[]
QED

Definition current_placement_seed_def:
  current_placement_seed li v roots hp d <=>
    MEM d roots \/ (MEM d hp /\ current_placement_live li v d)
End

Definition current_frontiers_done_def:
  current_frontiers_done df hp d <=>
    !f. current_frontier_edge df d f ==> MEM f hp
End

Definition current_placement_work_inv_def:
  current_placement_work_inv df li v roots hp work <=>
    (!f. MEM f hp /\ current_placement_live li v f ==>
      current_pruned_reach df li v roots f) /\
    (!f. MEM f hp ==> ?d. current_placement_seed li v roots hp d /\
      current_frontier_edge df d f) /\
    (!d. current_placement_seed li v roots hp d ==>
      MEM d work \/ current_frontiers_done df hp d) /\
    (!d. MEM d work ==> current_placement_seed li v roots hp d)
End

Theorem current_placement_work_inv_initial:
  current_placement_work_inv df li v roots [] roots
Proof
  simp[current_placement_work_inv_def, current_placement_seed_def]
QED

Theorem current_placement_seed_mono:
  (!x. MEM x hp ==> MEM x hp') ==>
  !d. current_placement_seed li v roots hp d ==>
    current_placement_seed li v roots hp' d
Proof
  simp[current_placement_seed_def] >> metis_tac[]
QED

Theorem current_frontiers_done_mono:
  (!x. MEM x hp ==> MEM x hp') ==>
  !d. current_frontiers_done df hp d ==> current_frontiers_done df hp' d
Proof
  simp[current_frontiers_done_def] >> metis_tac[]
QED

Theorem current_frontiers_done_filter:
  MEM d work ==>
  MEM d (FILTER (frontier_work_needed df hp) work) \/
    current_frontiers_done df hp d
Proof
  simp[MEM_FILTER, current_frontier_work_needed, current_frontiers_done_def] >>
  metis_tac[]
QED

Theorem current_placement_work_inv_filter:
  current_placement_work_inv df li v roots hp work ==>
  current_placement_work_inv df li v roots hp
    (FILTER (frontier_work_needed df hp) work)
Proof
  simp[current_placement_work_inv_def] >> rpt strip_tac >>
  metis_tac[current_frontiers_done_filter, MEM_FILTER]
QED

Theorem current_placement_work_inv_final:
  current_placement_work_inv df li v roots hp [] ==>
  current_pruned_closed df li v roots
    (FILTER (current_placement_live li v) hp) /\
  (!f. MEM f (FILTER (current_placement_live li v) hp) <=>
    current_pruned_reach df li v roots f)
Proof
  strip_tac >>
  `current_pruned_closed df li v roots
     (FILTER (current_placement_live li v) hp)` by
    (gvs[current_placement_work_inv_def, current_pruned_closed_def,
      current_placement_seed_def, current_frontiers_done_def, MEM_FILTER] >>
     metis_tac[]) >>
  simp[] >> drule current_pruned_reach_least >>
  gvs[current_placement_work_inv_def, MEM_FILTER] >> metis_tac[]
QED

Theorem current_placement_work_inv_step:
  current_placement_work_inv df li v roots hp (d::rest) /\
  (!f. MEM f hp' <=> MEM f hp \/ current_frontier_edge df d f) /\
  (!f. MEM f work' <=> MEM f rest \/
    (current_frontier_edge df d f /\ ~MEM f hp /\
      current_placement_live li v f)) ==>
  current_placement_work_inv df li v roots hp' work'
Proof
  strip_tac >>
  `!x. MEM x hp ==> MEM x hp'` by metis_tac[] >>
  `!x. current_placement_seed li v roots hp x ==>
       current_placement_seed li v roots hp' x` by
    metis_tac[current_placement_seed_mono] >>
  `!x. current_frontiers_done df hp x ==>
       current_frontiers_done df hp' x` by
    metis_tac[current_frontiers_done_mono] >>
  `current_placement_seed li v roots hp d` by
    gvs[current_placement_work_inv_def] >>
  gvs[current_placement_work_inv_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `MEM f hp \/ current_frontier_edge df d f` by metis_tac[] >>
      Cases_on `MEM f hp` >- metis_tac[] >>
      gvs[current_placement_seed_def] >>
      metis_tac[current_pruned_reach_rules]) >>
  conj_tac
  >- (rpt strip_tac >>
      `MEM f hp \/ current_frontier_edge df d f` by metis_tac[] >>
      Cases_on `MEM f hp` >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `current_placement_seed li v roots hp d'`
      >- (Cases_on `d' = d` >>
          gvs[current_frontiers_done_def] >> metis_tac[]) >>
      gvs[current_placement_seed_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[current_placement_seed_def] >> metis_tac[]
QED

Theorem current_process_frontiers_distinct:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s v pm li bbs rest hp fs =
      (bbs',rest',hp',s') /\ ALL_DISTINCT hp ==> ALL_DISTINCT hp'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[process_frontiers_supply_def, GSYM current_placement_live_lookup] >>
  Cases_on `MEM h hp` >> simp[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  Cases_on `current_placement_live li v h` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      asm "ih" drule >> simp[]) >>
  strip_tac >> asm "ih" drule >> simp[]
QED

Theorem current_process_frontiers_work_inv:
  process_frontiers_supply s v pm li bbs rest hp fs =
    (bbs',rest',hp',s') /\
  (!f. MEM f fs <=> current_frontier_edge df d f) /\
  current_placement_work_inv df li v roots hp (d::rest) ==>
  current_placement_work_inv df li v roots hp' rest'
Proof
  rpt strip_tac >>
  drule current_process_frontiers_pending >> strip_tac >>
  drule current_process_frontiers_processed >> strip_tac >>
  irule current_placement_work_inv_step >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem current_frontier_edge_lookup:
  MEM f (case ALOOKUP df d of NONE => [] | SOME fs => fs) <=>
  current_frontier_edge df d f
Proof
  Cases_on `ALOOKUP df d` >> simp[current_frontier_edge_def]
QED

Theorem current_insert_var_work_inv:
  !s v df pm li bbs work hp bbs' s'.
    insert_phis_for_var_supply s v df pm li bbs work hp = (bbs',s') /\
    current_placement_work_inv df li v roots hp work /\ ALL_DISTINCT hp ==>
    ?final. current_placement_work_inv df li v roots final [] /\
      ALL_DISTINCT final /\ (!x. MEM x hp ==> MEM x final)
Proof
  recInduct insert_phis_for_var_supply_ind >> rpt strip_tac
  >- (qexists_tac `has_phi` >> simp[]) >>
  gvs[Once insert_phis_for_var_supply_def] >>
  pairarg_tac >> gvs[] >>
  drule_all current_process_frontiers_distinct >> strip_tac >>
  `current_placement_work_inv dom_frontiers live_in var roots has_phi' rest'` by
    (irule current_process_frontiers_work_inv >>
     goal_assum $ drule_at Any >> qexists_tac `d` >>
     simp[current_frontier_edge_lookup]) >>
  drule current_placement_work_inv_filter >> strip_tac >>
  drule current_process_frontiers_processed >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `final` >> simp[]
QED

Theorem current_insert_var_closure:
  insert_phis_for_var_supply s v df pm li bbs roots [] = (bbs',s') ==>
  ?inserted. ALL_DISTINCT inserted /\
    current_pruned_closed df li v roots inserted /\
    (!f. MEM f inserted <=> current_pruned_reach df li v roots f)
Proof
  strip_tac >> drule current_insert_var_work_inv >>
  disch_then (qspec_then `roots` mp_tac) >>
  simp[current_placement_work_inv_initial] >> strip_tac >>
  drule current_placement_work_inv_final >> strip_tac >>
  qexists_tac `FILTER (current_placement_live li v) final` >>
  simp[FILTER_ALL_DISTINCT]
QED

Definition current_var_mark_def:
  current_var_mark li v hp done old new <=>
    new.bb_label = old.bb_label /\
    (old <> new <=> ~MEM old.bb_label hp /\ MEM old.bb_label done /\
      current_placement_live li v old.bb_label)
End

Theorem current_var_mark_refl:
  current_var_mark li v hp hp bb bb
Proof
  simp[current_var_mark_def] >> metis_tac[]
QED

Theorem current_var_mark_compose:
  current_var_mark li v hp mid a b /\
  current_var_mark li v mid done b c /\
  (!x. MEM x hp ==> MEM x mid) /\
  (!x. MEM x mid ==> MEM x done) ==>
  current_var_mark li v hp done a c
Proof
  simp[current_var_mark_def] >> rpt strip_tac >>
  Cases_on `a = b` >- (gvs[] >> metis_tac[]) >>
  `b = c` by metis_tac[] >> metis_tac[]
QED

Theorem current_var_mark_list_compose:
  LIST_REL (current_var_mark li v hp mid) xs ys /\
  LIST_REL (current_var_mark li v mid done) ys zs /\
  (!x. MEM x hp ==> MEM x mid) /\
  (!x. MEM x mid ==> MEM x done) ==>
  LIST_REL (current_var_mark li v hp done) xs zs
Proof
  map_every qid_spec_tac [`zs`, `ys`] >>
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >> simp[] >>
  rpt strip_tac >- metis_tac[current_var_mark_compose] >> metis_tac[]
QED

Theorem current_insert_phi_changes:
  insert_phi_at_block phi bb <> bb
Proof
  simp[insert_phi_at_block_def, basic_block_component_equality] >>
  strip_tac >>
  qpat_x_assum `_ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  simp[]
QED

Theorem current_insert_phi_label[simp]:
  (insert_phi_at_block phi bb).bb_label = bb.bb_label
Proof
  simp[insert_phi_at_block_def]
QED

Theorem current_var_mark_map_step:
  ~MEM f hp /\ current_placement_live li v f ==>
  LIST_REL (current_var_mark li v hp (f::hp)) bbs
    (MAP (\bb. if bb.bb_label = f then insert_phi_at_block phi bb else bb) bbs)
Proof
  Induct_on `bbs` >> simp[] >> strip_tac >>
  Cases_on `h.bb_label = f` >>
  gvs[current_var_mark_def, current_insert_phi_changes] >>
  metis_tac[current_insert_phi_changes]
QED
