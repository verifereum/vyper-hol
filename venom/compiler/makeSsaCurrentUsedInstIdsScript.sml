(*
 * MakeSSA never reads the supply's used instruction ids: fresh_inst_id
 * takes irs_next_inst and only records the id.  So running
 * make_ssa_current_fn from a supply whose used ids are replaced gives the
 * same function, and a supply that differs only in its used ids.
 *)
Theory makeSsaCurrentUsedInstIds
Ancestors
  makeSsaDefs makeSsaCurrentInduct irSupply

Theorem fresh_inst_id_used_inst_ids:
  fresh_inst_id s = (id,s') ==>
  fresh_inst_id (s with irs_used_inst_ids := ids) =
    (id,s' with irs_used_inst_ids := id::ids)
Proof
  rw[fresh_inst_id_def] >> simp[]
QED

Theorem fresh_ir_var_used_inst_ids:
  fresh_ir_var s = (name,s') ==>
  fresh_ir_var (s with irs_used_inst_ids := ids) =
    (name,s' with irs_used_inst_ids := ids)
Proof
  simp[fresh_ir_var_def] >> CASE_TAC >> rw[] >> simp[]
QED

Theorem process_frontiers_supply_used_inst_ids:
  !fs s ids var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    ?ids'.
      process_frontiers_supply (s with irs_used_inst_ids := ids)
        var pm li bbs rest hp fs =
        (bbs',rest',hp',s' with irs_used_inst_ids := ids')
Proof
  Induct >> simp[process_frontiers_supply_def] >> rpt gen_tac
  >- metis_tac[] >>
  Cases_on `fresh_inst_id s` >>
  drule fresh_inst_id_used_inst_ids >>
  disch_then (qspec_then `ids` assume_tac) >> simp[] >>
  rw[] >> metis_tac[]
QED

Theorem insert_phis_for_var_supply_used_inst_ids:
  !s var df pm li bbs wl hp ids bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    ?ids'.
      insert_phis_for_var_supply (s with irs_used_inst_ids := ids)
        var df pm li bbs wl hp =
        (bbs',s' with irs_used_inst_ids := ids')
Proof
  recInduct insert_phis_for_var_supply_ind >> rpt conj_tac >>
  rpt gen_tac
  >- (simp[insert_phis_for_var_supply_def] >> rw[] >>
      qexists_tac `ids` >> simp[]) >>
  strip_tac >> rpt gen_tac >>
  simp[Once insert_phis_for_var_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule process_frontiers_supply_used_inst_ids >>
  disch_then (qspec_then `ids` strip_assume_tac) >>
  simp[Once insert_phis_for_var_supply_def] >>
  first_x_assum drule_all >> strip_tac >> fs[] >> metis_tac[]
QED

Theorem add_phi_nodes_supply_used_inst_ids:
  !defs s ids df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    ?ids'.
      add_phi_nodes_supply (s with irs_used_inst_ids := ids) df pm li bbs
        defs = (bbs',s' with irs_used_inst_ids := ids')
Proof
  Induct >> simp[add_phi_nodes_supply_def] >> rpt gen_tac
  >- metis_tac[] >>
  PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_used_inst_ids >>
  disch_then (qspec_then `ids` strip_assume_tac) >> simp[] >>
  metis_tac[]
QED

Theorem push_current_name_used_inst_ids:
  push_current_name s rs v = (rs',s',name) ==>
  push_current_name (s with irs_used_inst_ids := ids) rs v =
    (rs',s' with irs_used_inst_ids := ids,name)
Proof
  PairCases_on `rs` >> simp[push_current_name_def] >>
  Cases_on `fresh_ir_var s` >>
  drule fresh_ir_var_used_inst_ids >>
  disch_then (qspec_then `ids` assume_tac) >> simp[] >>
  rw[] >> simp[]
QED

Theorem rename_current_outputs_used_inst_ids:
  !vs s ids rs rs' s' outs.
    rename_current_outputs s rs vs = (rs',s',outs) ==>
    rename_current_outputs (s with irs_used_inst_ids := ids) rs vs =
      (rs',s' with irs_used_inst_ids := ids,outs)
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule push_current_name_used_inst_ids >>
  disch_then (qspec_then `ids` assume_tac) >>
  first_x_assum drule >>
  disch_then (qspec_then `ids` assume_tac) >> gvs[]
QED

Theorem rename_current_inst_used_inst_ids:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  rename_current_inst (s with irs_used_inst_ids := ids) rs inst =
    (rs',s' with irs_used_inst_ids := ids,inst')
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >> simp[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_outputs_used_inst_ids >>
  disch_then (qspec_then `ids` assume_tac) >> gvs[]
QED

Theorem rename_current_block_insts_used_inst_ids:
  !insts s ids rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    rename_current_block_insts (s with irs_used_inst_ids := ids) rs insts =
      (rs',s' with irs_used_inst_ids := ids,insts')
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_inst_used_inst_ids >>
  disch_then (qspec_then `ids` assume_tac) >>
  first_x_assum drule >>
  disch_then (qspec_then `ids` assume_tac) >> gvs[]
QED

Theorem rename_current_blocks_used_inst_ids:
  (!t s ids rs bbs sm ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     rename_current_blocks (s with irs_used_inst_ids := ids) rs bbs sm t =
       (ctrs,s' with irs_used_inst_ids := ids,bbs')) /\
  (!ts s ids ctrs stacks bbs sm ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     rename_current_children (s with irs_used_inst_ids := ids) ctrs stacks
       bbs sm ts = (ctrs',s' with irs_used_inst_ids := ids,bbs'))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()] >>
      `?a b c. rename_current_block_insts s rs bb.bb_instructions = (a,b,c)`
        by metis_tac[pairTheory.PAIR] >>
      drule rename_current_block_insts_used_inst_ids >>
      disch_then (qspec_then `ids` assume_tac) >> gvs[] >>
      first_x_assum drule >> simp[])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >>
  gvs[rename_current_blocks_def] >>
  `?a b c. rename_current_blocks s (ctrs,stacks) bbs sm t = (a,b,c)`
    by metis_tac[pairTheory.PAIR] >>
  gvs[] >>
  first_x_assum drule >>
  disch_then (qspec_then `ids` assume_tac) >>
  first_x_assum drule >>
  disch_then (qspec_then `ids` assume_tac) >> gvs[]
QED

Theorem make_ssa_current_fn_used_inst_ids:
  make_ssa_current_fn s fn = (fn',s') ==>
  ?ids'.
    make_ssa_current_fn (s with irs_used_inst_ids := ids) fn =
      (fn',s' with irs_used_inst_ids := ids')
Proof
  simp[make_ssa_current_fn_def] >> CASE_TAC >> simp[]
  >- (rw[] >> qexists_tac `ids` >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule add_phi_nodes_supply_used_inst_ids >>
  disch_then (qspec_then `ids` strip_assume_tac) >> simp[] >>
  drule (CONJUNCT1 rename_current_blocks_used_inst_ids) >>
  disch_then (qspec_then `ids'` assume_tac) >> simp[] >>
  metis_tac[]
QED
