(*
 * Memory SSA Analysis — Proofs
 *
 * Proves safety properties of the memory SSA construction.
 * Consumed by memSSAPropsScript.sml via ACCEPT_TAC.
 *)

Theory memSSAProofs
Ancestors
  memSSADefs
  dominatorAnalysisProps
  cfgAnalysisProps
  cfgHelpers
  memAliasProps
Libs
  listTheory rich_listTheory finite_mapTheory pairTheory pred_setTheory
  memSSAProofsLib

(* ==========================================================================
   Well-formedness: sub-predicates
   ========================================================================== *)

Definition mem_ssa_ids_valid_def:
  mem_ssa_ids_valid ms ⇔
    (∀lbl aids aid.
       (FLOOKUP ms.ms_block_defs lbl = SOME aids ∨
        FLOOKUP ms.ms_block_uses lbl = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM ms.ms_nodes) ∧
    (∀lbl phi_id.
       FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
       phi_id ∈ FDOM ms.ms_nodes)
End

Definition mem_ssa_edges_valid_def:
  mem_ssa_edges_valid ms ⇔
    (∀aid rd.
       FLOOKUP ms.ms_reaching aid = SOME rd ⇒
       rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒
       rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
End

Definition mem_ssa_inst_maps_consistent_def:
  mem_ssa_inst_maps_consistent ms ⇔
    (∀iid aid.
       FLOOKUP ms.ms_inst_def iid = SOME aid ⇒
       ∃blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid blk loc)) ∧
    (∀iid aid.
       FLOOKUP ms.ms_inst_use iid = SOME aid ⇒
       ∃blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnUse iid blk loc))
End

Definition mem_ssa_reaching_complete_def:
  mem_ssa_reaching_complete ms ⇔
    ∀aid node.
      FLOOKUP ms.ms_nodes aid = SOME node ∧
      (∀blk. node ≠ MnPhi blk) ⇒
      ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd
End

Definition wf_mem_ssa_def:
  wf_mssa ms ⇔
    mem_ssa_ids_valid ms ∧
    mem_ssa_edges_valid ms ∧
    mem_ssa_inst_maps_consistent ms ∧
    mem_ssa_reaching_complete ms
End

(* ==========================================================================
   Phase 3 toolkit: connect_all only modifies ms_reaching
   ========================================================================== *)

Triviality connect_list_fields:
  ∀aids ms dom fn fuel.
    (mem_ssa_connect_list ms dom fn fuel aids).ms_nodes = ms.ms_nodes ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_block_defs = ms.ms_block_defs ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_block_uses = ms.ms_block_uses ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_block_phis = ms.ms_block_phis ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_inst_def = ms.ms_inst_def ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_inst_use = ms.ms_inst_use ∧
    (mem_ssa_connect_list ms dom fn fuel aids).ms_next_id = ms.ms_next_id
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[]
QED

Triviality connect_all_fields:
  ∀lbls ms dom fn fuel.
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_nodes = ms.ms_nodes ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_block_defs = ms.ms_block_defs ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_block_uses = ms.ms_block_uses ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_block_phis = ms.ms_block_phis ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_inst_def = ms.ms_inst_def ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_inst_use = ms.ms_inst_use ∧
    (mem_ssa_connect_all ms dom fn fuel lbls).ms_next_id = ms.ms_next_id
Proof
  Induct >> simp[mem_ssa_connect_all_def] >>
  rpt gen_tac >> simp[connect_list_fields]
QED

(* ==========================================================================
   Phase 2 toolkit: insert_phis preserves reaching, block_defs/uses, inst_def/use
   ========================================================================== *)

Triviality insert_phi_at_fields:
  ∀ms cfg dom fuel lbl ms' inserted.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    ms'.ms_reaching = ms.ms_reaching ∧
    ms'.ms_block_defs = ms.ms_block_defs ∧
    ms'.ms_block_uses = ms.ms_block_uses ∧
    ms'.ms_inst_def = ms.ms_inst_def ∧
    ms'.ms_inst_use = ms.ms_inst_use
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[]
QED

Triviality process_frontiers_fields:
  ∀fronts ms cfg dom fuel ms' wl.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    ms'.ms_reaching = ms.ms_reaching ∧
    ms'.ms_block_defs = ms.ms_block_defs ∧
    ms'.ms_block_uses = ms.ms_block_uses ∧
    ms'.ms_inst_def = ms.ms_inst_def ∧
    ms'.ms_inst_use = ms.ms_inst_use
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule insert_phi_at_fields >> strip_tac >> res_tac >> simp[]
QED

Triviality insert_phis_fields:
  ∀ms cfg dom ef fuel wl.
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_reaching = ms.ms_reaching ∧
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_defs = ms.ms_block_defs ∧
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_uses = ms.ms_block_uses ∧
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_inst_def = ms.ms_inst_def ∧
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_inst_use = ms.ms_inst_use
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >>
  simp[Once mem_ssa_insert_phis_def] >>
  pairarg_tac >> simp[] >>
  drule process_frontiers_fields >> strip_tac >> fs[]
QED

(* ==========================================================================
   Phase 1 toolkit: process_blocks preserves reaching, phi_ops, block_phis
   ========================================================================== *)

Triviality process_inst_fields:
  ∀bp addr_sp lbl ms inst.
    (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_reaching = ms.ms_reaching ∧
    (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_phis = ms.ms_block_phis
Proof
  rpt gen_tac >> simp[mem_ssa_process_inst_def] >>
  COND_CASES_TAC >> simp[] >>
  COND_CASES_TAC >> simp[]
QED

Triviality process_block_fields:
  ∀insts bp addr_sp lbl ms.
    (mem_ssa_process_block bp addr_sp lbl ms insts).ms_reaching = ms.ms_reaching ∧
    (mem_ssa_process_block bp addr_sp lbl ms insts).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_phis = ms.ms_block_phis
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> simp[process_inst_fields]
QED

Triviality process_blocks_fields:
  ∀lbls bp addr_sp fn ms.
    (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_reaching = ms.ms_reaching ∧
    (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_phis = ms.ms_block_phis
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[process_block_fields]
QED

Triviality process_inst_no_new_phi:
  !bp addr_sp lbl ms inst id blk.
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes id =
      SOME (MnPhi blk) ==>
    FLOOKUP ms.ms_nodes id = SOME (MnPhi blk)
Proof
  rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  rpt COND_CASES_TAC >> simp[FLOOKUP_UPDATE] >>
  rpt COND_CASES_TAC >> simp[]
QED

Triviality process_block_no_new_phi:
  !insts bp addr_sp lbl ms id blk.
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes id =
      SOME (MnPhi blk) ==>
    FLOOKUP ms.ms_nodes id = SOME (MnPhi blk)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  metis_tac[process_inst_no_new_phi]
QED

Triviality process_blocks_no_new_phi:
  !lbls bp addr_sp fn ms id blk.
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes id =
      SOME (MnPhi blk) ==>
    FLOOKUP ms.ms_nodes id = SOME (MnPhi blk)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  metis_tac[process_block_no_new_phi]
QED

(* ==========================================================================
   Phase 4 toolkit: remove_redundant_phis only modifies ms_block_phis
   ========================================================================== *)

(* All non-block_phis fields are preserved *)
Triviality remove_redundant_phis_fields:
  ∀ms pairs.
    (mem_ssa_remove_redundant_phis ms pairs).ms_nodes = ms.ms_nodes ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_reaching = ms.ms_reaching ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_phi_ops = ms.ms_phi_ops ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_block_defs = ms.ms_block_defs ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_block_uses = ms.ms_block_uses ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_inst_def = ms.ms_inst_def ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_inst_use = ms.ms_inst_use ∧
    (mem_ssa_remove_redundant_phis ms pairs).ms_next_id = ms.ms_next_id
Proof
  Induct_on `pairs` >> simp[mem_ssa_remove_redundant_phis_def] >>
  Cases >> simp[mem_ssa_remove_redundant_phis_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  Cases_on `mem_ssa_phi_redundant x` >> simp[]
QED

(* block_phis only shrinks: FDOM only loses entries *)
Triviality remove_redundant_phis_block_phis_subseteq:
  ∀pairs ms lbl phi_id.
    FLOOKUP (mem_ssa_remove_redundant_phis ms pairs).ms_block_phis lbl = SOME phi_id ⇒
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id
Proof
  Induct >> simp[mem_ssa_remove_redundant_phis_def] >>
  Cases >> rpt gen_tac >>
  simp[mem_ssa_remove_redundant_phis_def] >>
  CASE_TAC >> simp[] >>
  Cases_on `mem_ssa_phi_redundant x` >> simp[] >> strip_tac >> res_tac >>
  fs[finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED

(* Key soundness: surviving phis are not redundant *)
Triviality remove_redundant_phis_sound:
  ∀pairs ms lbl phi_id ops.
    FLOOKUP (mem_ssa_remove_redundant_phis ms pairs).ms_block_phis lbl = SOME phi_id ∧
    MEM (lbl, phi_id) pairs ∧
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
    ops ≠ [] ⇒
    ¬mem_ssa_phi_redundant ops
Proof
  Induct >> simp[mem_ssa_remove_redundant_phis_def] >>
  Cases >> rpt gen_tac >>
  simp[mem_ssa_remove_redundant_phis_def] >>
  Cases_on `FLOOKUP ms.ms_phi_ops r` >> simp[]
  >- (
    strip_tac >> gvs[] >> first_x_assum irule >> metis_tac[]
  ) >>
  Cases_on `mem_ssa_phi_redundant x` >> fs[]
  >- (
    strip_tac >> gvs[]
    >- (
      drule_all remove_redundant_phis_block_phis_subseteq >>
      simp[finite_mapTheory.DOMSUB_FLOOKUP_THM]
    ) >>
    first_x_assum (qspecl_then
      [`ms with ms_block_phis := ms.ms_block_phis \\ q`,
       `lbl`, `phi_id`, `ops`] mp_tac) >>
    simp[]
  ) >>
  strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

(* Non-redundant phis survive Phase 4 *)
Triviality remove_redundant_phis_non_redundant_preserved:
  ∀pairs ms lbl phi_id.
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ∧
    (∀pid ops. MEM (lbl, pid) pairs ∧
              FLOOKUP ms.ms_phi_ops pid = SOME ops ⇒
              ¬mem_ssa_phi_redundant ops) ⇒
    FLOOKUP (mem_ssa_remove_redundant_phis ms pairs).ms_block_phis lbl =
      SOME phi_id
Proof
  Induct >> simp[mem_ssa_remove_redundant_phis_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  rename [`(lbl', pid')::rest`] >>
  simp[mem_ssa_remove_redundant_phis_def] >>
  Cases_on `FLOOKUP ms.ms_phi_ops pid'` >> simp[]
  >- ((* NONE: state unchanged *)
    first_x_assum irule >> simp[] >> metis_tac[])
  >- ((* SOME ops' *)
    rename [`FLOOKUP ms.ms_phi_ops pid' = SOME ops'`] >>
    Cases_on `mem_ssa_phi_redundant ops'` >> simp[]
    >- ((* redundant: lbl' removed from block_phis *)
      (* lbl' ≠ lbl because our precondition says lbl's phi is non-redundant *)
      `lbl' <> lbl` by (
        CCONTR_TAC >> gvs[] >>
        `phi_id = pid'` by fs[finite_mapTheory.FLOOKUP_DEF] >>
        gvs[] >> metis_tac[MEM]) >>
      first_x_assum irule >>
      simp[finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
      metis_tac[])
    >- ((* non-redundant: state unchanged *)
      first_x_assum irule >> simp[] >> metis_tac[]))
QED

(* ==========================================================================
   Composite preservation: wf_mssa through phases 3+4
   ========================================================================== *)

(* Phase 3 preserves all non-reaching properties *)
Triviality connect_list_preserves_ids_valid:
  ∀ms dom fn fuel aids.
    mem_ssa_ids_valid ms ⇒
    mem_ssa_ids_valid (mem_ssa_connect_list ms dom fn fuel aids)
Proof
  rw[mem_ssa_ids_valid_def, connect_list_fields]
QED

Triviality connect_list_preserves_inst_maps:
  ∀ms dom fn fuel aids.
    mem_ssa_inst_maps_consistent ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_connect_list ms dom fn fuel aids)
Proof
  rw[mem_ssa_inst_maps_consistent_def, connect_list_fields]
QED

Triviality connect_all_preserves_ids_valid:
  ∀ms dom fn fuel lbls.
    mem_ssa_ids_valid ms ⇒
    mem_ssa_ids_valid (mem_ssa_connect_all ms dom fn fuel lbls)
Proof
  rw[mem_ssa_ids_valid_def, connect_all_fields]
QED

Triviality connect_all_preserves_inst_maps:
  ∀ms dom fn fuel lbls.
    mem_ssa_inst_maps_consistent ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_connect_all ms dom fn fuel lbls)
Proof
  rw[mem_ssa_inst_maps_consistent_def, connect_all_fields]
QED

(* Phase 4 preserves wf_mssa (combined — all 4 sub-predicates) *)
Triviality remove_phis_preserves_wf:
  ∀ms pairs. wf_mssa ms ⇒ wf_mssa (mem_ssa_remove_redundant_phis ms pairs)
Proof
  simp[wf_mem_ssa_def] >> rpt gen_tac >> strip_tac >> rpt conj_tac >>
  fs[mem_ssa_ids_valid_def, mem_ssa_edges_valid_def,
     mem_ssa_inst_maps_consistent_def, mem_ssa_reaching_complete_def,
     remove_redundant_phis_fields] >>
  metis_tac[remove_redundant_phis_block_phis_subseteq]
QED

(* ==========================================================================
   Phase 1 establishment: inst_maps_consistent
   ========================================================================== *)

(* ==========================================================================
   Freshness invariant: all node IDs < ms_next_id
   Required by nodes_mono, inst_maps, ids_valid across phases
   ========================================================================== *)

Definition nodes_fresh_def:
  nodes_fresh ms ⇔ ∀aid. aid ∈ FDOM ms.ms_nodes ⇒ aid < ms.ms_next_id
End

(* process_inst preserves freshness *)
Triviality process_inst_preserves_fresh:
  ∀bp addr_sp lbl ms inst.
    nodes_fresh ms ⇒
    nodes_fresh (mem_ssa_process_inst bp addr_sp lbl ms inst)
Proof
  rw[mem_ssa_process_inst_def, nodes_fresh_def] >>
  rpt (COND_CASES_TAC >> gvs[finite_mapTheory.FDOM_FUPDATE]) >>
  res_tac >> DECIDE_TAC
QED

Triviality process_block_preserves_fresh:
  ∀insts bp addr_sp lbl ms.
    nodes_fresh ms ⇒
    nodes_fresh (mem_ssa_process_block bp addr_sp lbl ms insts)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  metis_tac[process_inst_preserves_fresh]
QED

Triviality process_blocks_preserves_fresh:
  ∀lbls bp addr_sp fn ms.
    nodes_fresh ms ⇒
    nodes_fresh (mem_ssa_process_blocks bp addr_sp fn ms lbls)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  metis_tac[process_block_preserves_fresh]
QED

(* process_inst monotonically increases next_id *)
Triviality process_inst_next_id_mono:
  ∀bp addr_sp lbl ms inst.
    ms.ms_next_id ≤ (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_next_id
Proof
  rw[mem_ssa_process_inst_def] >>
  rpt (COND_CASES_TAC >> gvs[]) >> DECIDE_TAC
QED

Triviality process_block_next_id_mono:
  ∀insts bp addr_sp lbl ms.
    ms.ms_next_id ≤ (mem_ssa_process_block bp addr_sp lbl ms insts).ms_next_id
Proof
  Induct >> simp[mem_ssa_process_block_def] >> rpt gen_tac >>
  `ms.ms_next_id ≤
     (mem_ssa_process_inst bp addr_sp lbl ms h).ms_next_id` by
    simp[process_inst_next_id_mono] >>
  first_x_assum
    (qspecl_then [`bp`,`addr_sp`,`lbl`,
                  `mem_ssa_process_inst bp addr_sp lbl ms h`] mp_tac) >>
  DECIDE_TAC
QED

(* General: adding a matching pair to index+nodes preserves inst_maps *)
(* General helper: FLOOKUP_UPDATE-based map extension preserves consistency.
   Pattern: new index entry (iid↦nid) + new node entry (nid↦MnXxx iid ...).
   Old entries preserved because nid is fresh (not in FDOM ms.ms_nodes). *)
Triviality inst_maps_extend_def:
  ∀ms iid nid blk loc.
    mem_ssa_inst_maps_consistent ms ∧ nid ∉ FDOM ms.ms_nodes ⇒
    mem_ssa_inst_maps_consistent
      (ms with <| ms_inst_def := ms.ms_inst_def |+ (iid, nid);
                  ms_nodes := ms.ms_nodes |+ (nid, MnDef iid blk loc) |>)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ms.ms_nodes nid = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  fs[mem_ssa_inst_maps_consistent_def] >>
  simp[mem_ssa_inst_maps_consistent_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  rpt (COND_CASES_TAC >> gvs[]) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  COND_CASES_TAC >> gvs[] >>
  strip_tac >> res_tac >> gvs[]
QED

Triviality inst_maps_extend_use:
  ∀ms iid nid blk loc.
    mem_ssa_inst_maps_consistent ms ∧ nid ∉ FDOM ms.ms_nodes ⇒
    mem_ssa_inst_maps_consistent
      (ms with <| ms_inst_use := ms.ms_inst_use |+ (iid, nid);
                  ms_nodes := ms.ms_nodes |+ (nid, MnUse iid blk loc) |>)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ms.ms_nodes nid = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  fs[mem_ssa_inst_maps_consistent_def] >>
  simp[mem_ssa_inst_maps_consistent_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  rpt (COND_CASES_TAC >> gvs[]) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  COND_CASES_TAC >> gvs[] >>
  strip_tac >> res_tac >> gvs[]
QED

(* Updating fields that inst_maps doesn't mention is invisible *)
Triviality inst_maps_irrelevant_fields:
  ∀ms bd bu bp pp nid r.
    mem_ssa_inst_maps_consistent ms ⇒
    mem_ssa_inst_maps_consistent
      (ms with <| ms_block_defs := bd; ms_block_uses := bu;
                  ms_block_phis := bp; ms_phi_ops := pp;
                  ms_next_id := nid; ms_reaching := r |>)
Proof
  rw[mem_ssa_inst_maps_consistent_def] >> res_tac >> gvs[]
QED

(* inst_maps_consistent only depends on inst_def, inst_use, nodes *)
Triviality inst_maps_cong:
  ∀ms1 ms2.
    ms1.ms_inst_def = ms2.ms_inst_def ∧
    ms1.ms_inst_use = ms2.ms_inst_use ∧
    ms1.ms_nodes = ms2.ms_nodes ⇒
    (mem_ssa_inst_maps_consistent ms1 ⇔ mem_ssa_inst_maps_consistent ms2)
Proof
  rw[mem_ssa_inst_maps_consistent_def]
QED

(* process_inst preserves + extends inst_maps_consistent *)
Triviality process_inst_preserves_inst_maps:
  ∀bp addr_sp lbl ms inst.
    mem_ssa_inst_maps_consistent ms ∧ nodes_fresh ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_process_inst bp addr_sp lbl ms inst)
Proof
  rpt gen_tac >> strip_tac >>
  `ms.ms_next_id ∉ FDOM ms.ms_nodes` by
    (fs[nodes_fresh_def] >> strip_tac >> res_tac >> DECIDE_TAC) >>
  `FLOOKUP ms.ms_nodes ms.ms_next_id = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  `ms.ms_next_id + 1 ∉ FDOM ms.ms_nodes` by
    (fs[nodes_fresh_def] >> strip_tac >> res_tac >> DECIDE_TAC) >>
  `FLOOKUP ms.ms_nodes (ms.ms_next_id + 1) = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  fs[mem_ssa_inst_maps_consistent_def] >>
  simp[mem_ssa_process_inst_def, mem_ssa_inst_maps_consistent_def] >>
  rpt COND_CASES_TAC >> simp[] >>
  rpt strip_tac >>
  (* Two kinds of goals:
     A) assumption has plain FLOOKUP (inst unchanged, nodes grew)
     B) assumption has FLOOKUP (map |+ ...) (inst grew too) *)
  TRY (
    res_tac >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >>
    rpt (COND_CASES_TAC >> gvs[]) >>
    fs[finite_mapTheory.FLOOKUP_DEF] >> NO_TAC) >>
  qpat_x_assum `FLOOKUP (_ |+ _) _ = SOME _` mp_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  COND_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  res_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (COND_CASES_TAC >> gvs[])
QED

Triviality process_block_preserves_inst_maps:
  ∀insts bp addr_sp lbl ms.
    mem_ssa_inst_maps_consistent ms ∧ nodes_fresh ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_process_block bp addr_sp lbl ms insts)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  metis_tac[process_inst_preserves_inst_maps,
            process_inst_preserves_fresh]
QED

Triviality process_blocks_preserves_inst_maps:
  ∀lbls bp addr_sp fn ms.
    mem_ssa_inst_maps_consistent ms ∧ nodes_fresh ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_process_blocks bp addr_sp fn ms lbls)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  metis_tac[process_block_preserves_inst_maps,
            process_block_preserves_fresh]
QED

(* ==========================================================================
   MnDef node → iid ∈ FDOM inst_def (weaker than full reverse, but sufficient)
   Holds because process_inst adds iid to FDOM inst_def when creating MnDef,
   and |+ never removes keys from FDOM.
   ========================================================================== *)

Triviality process_inst_MnDef_in_inst_def:
  !bp addr_sp lbl ms inst aid iid blk loc.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      i IN FDOM ms.ms_inst_def) /\
    nodes_fresh ms /\
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    iid IN FDOM (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_inst_def
Proof
  rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  rpt COND_CASES_TAC >> simp[FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  rpt strip_tac >>
  TRY (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
       rpt IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
       res_tac >> simp[] >> NO_TAC) >>
  res_tac
QED

Triviality process_block_MnDef_in_inst_def:
  !insts bp addr_sp lbl ms aid iid blk loc.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      i IN FDOM ms.ms_inst_def) /\
    nodes_fresh ms /\
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    iid IN FDOM (mem_ssa_process_block bp addr_sp lbl ms insts).ms_inst_def
Proof
  Induct >> simp[mem_ssa_process_block_def]
  >- metis_tac[]
  >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `aid`, `iid`, `blk`, `loc`]
    mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  conj_tac
  >- (rpt strip_tac >>
      match_mp_tac (GEN_ALL process_inst_MnDef_in_inst_def) >>
      metis_tac[])
  >- metis_tac[process_inst_preserves_fresh]
QED

Triviality process_blocks_MnDef_in_inst_def:
  !lbls bp addr_sp fn ms aid iid blk loc.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      i IN FDOM ms.ms_inst_def) /\
    nodes_fresh ms /\
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    iid IN FDOM (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_inst_def
Proof
  Induct >> simp[mem_ssa_process_blocks_def]
  >- metis_tac[]
  >> rpt gen_tac >> Cases_on `lookup_block h fn.fn_blocks` >>
  simp[mem_ssa_process_blocks_def]
  >- metis_tac[]
  >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
    `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`,
    `aid`, `iid`, `blk`, `loc`] mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  conj_tac
  >- (rpt strip_tac >>
      match_mp_tac (GEN_ALL process_block_MnDef_in_inst_def) >>
      metis_tac[])
  >- metis_tac[process_block_preserves_fresh]
QED

(* --------------------------------------------------------------------------
   Full reverse inst_def: nodes aid = MnDef iid ... ==> inst_def iid = SOME aid
   Requires collision-free precondition (no two instructions share an inst_id).
   -------------------------------------------------------------------------- *)

Triviality process_inst_inst_def_reverse:
  !bp addr_sp lbl ms inst aid iid blk loc.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      FLOOKUP ms.ms_inst_def i = SOME a) /\
    nodes_fresh ms /\
    (!a b l. FLOOKUP ms.ms_nodes a = SOME (MnDef inst.inst_id b l) ==> F) /\
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_inst_def iid =
      SOME aid
Proof
  rpt gen_tac >> strip_tac >>
  `ms.ms_next_id NOTIN FDOM ms.ms_nodes` by
    (fs[nodes_fresh_def] >> strip_tac >> res_tac >> DECIDE_TAC) >>
  `FLOOKUP ms.ms_nodes ms.ms_next_id = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  `ms.ms_next_id + 1 NOTIN FDOM ms.ms_nodes` by
    (fs[nodes_fresh_def] >> strip_tac >> res_tac >> DECIDE_TAC) >>
  `FLOOKUP ms.ms_nodes (ms.ms_next_id + 1) = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  qpat_x_assum `FLOOKUP (mem_ssa_process_inst _ _ _ _ _).ms_nodes _ = _` mp_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  rpt COND_CASES_TAC >> simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  rpt IF_CASES_TAC >> gvs[]
QED

(* Any MnDef in process_inst output either came from ms or has inst.inst_id *)
Triviality process_inst_MnDef_old_or_new:
  !bp addr_sp lbl ms inst a iid blk loc.
    nodes_fresh ms /\
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes a =
      SOME (MnDef iid blk loc) ==>
    FLOOKUP ms.ms_nodes a = SOME (MnDef iid blk loc) \/
    iid = inst.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FLOOKUP (mem_ssa_process_inst _ _ _ _ _).ms_nodes _ = _` mp_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  rpt COND_CASES_TAC >> simp[FLOOKUP_UPDATE] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  rpt IF_CASES_TAC >> gvs[]
QED

Triviality process_block_inst_def_reverse:
  !insts bp addr_sp lbl ms aid iid blk loc.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      FLOOKUP ms.ms_inst_def i = SOME a) /\
    nodes_fresh ms /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!a j b l. FLOOKUP ms.ms_nodes a = SOME (MnDef j b l) /\
      MEM j (MAP (\i. i.inst_id) insts) ==> F) /\
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_inst_def iid =
      SOME aid
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `aid`, `iid`, `blk`, `loc`]
    mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  rpt conj_tac
  >- (rpt strip_tac >>
      irule process_inst_inst_def_reverse >> simp[] >> metis_tac[])
  >- metis_tac[process_inst_preserves_fresh]
  >- (rpt strip_tac >>
      drule_all process_inst_MnDef_old_or_new >> strip_tac >> gvs[] >>
      metis_tac[])
QED

(* --- Helpers moved here for scope: needed by process_blocks_inst_def_reverse --- *)

Triviality lookup_block_props:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl /\ MEM bb bbs
Proof
  Induct_on `bbs` >>
  simp[venomInstTheory.lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = lbl` >> simp[] >>
  simp[GSYM venomInstTheory.lookup_block_def] >>
  strip_tac >> gvs[] >> res_tac >> simp[]
QED

Triviality fn_inst_ids_block_distinct:
  !fn bb.
    fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  fs[venomWfTheory.fn_inst_ids_distinct_def] >>
  qsuff_tac `!ls. ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) ls)) /\
                   MEM bb ls ==>
                   ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`
  >- metis_tac[] >>
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

Triviality ALL_DISTINCT_FLAT_MAP_UNIQUE:
  !f ls a b x.
    ALL_DISTINCT (FLAT (MAP f ls)) /\ MEM a ls /\ MEM b ls /\
    MEM x (f a) /\ MEM x (f b) ==> a = b
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

(* --- End moved helpers --- *)

(* If two blocks share an inst_id, they must be the same block *)
Triviality fn_inst_ids_distinct_unique_block:
  !fn bb1 bb2 iid.
    fn_inst_ids_distinct fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM iid (MAP (\i. i.inst_id) bb1.bb_instructions) /\
    MEM iid (MAP (\i. i.inst_id) bb2.bb_instructions) ==>
    bb1 = bb2
Proof
  rpt strip_tac >>
  fs[venomWfTheory.fn_inst_ids_distinct_def] >>
  mp_tac (ISPEC ``\(bb:basic_block). MAP (\i. i.inst_id) bb.bb_instructions``
           ALL_DISTINCT_FLAT_MAP_UNIQUE) >>
  simp[] >> metis_tac[]
QED

(* Any MnDef in process_block output either came from ms or has iid from
   this block's instructions *)
Triviality process_block_MnDef_old_or_new:
  !insts bp addr_sp lbl ms a iid blk loc.
    nodes_fresh ms /\
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes a =
      SOME (MnDef iid blk loc) ==>
    FLOOKUP ms.ms_nodes a = SOME (MnDef iid blk loc) \/
    MEM iid (MAP (\i. i.inst_id) insts)
Proof
  Induct >> simp[mem_ssa_process_block_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `a`, `iid`, `blk`, `loc`]
    mp_tac) >> simp[] >>
  impl_tac >- metis_tac[process_inst_preserves_fresh] >>
  strip_tac >> gvs[] >>
  drule_all process_inst_MnDef_old_or_new >> metis_tac[]
QED

(* process_blocks_inst_def_reverse:
   IH invariant = the property itself + collision-free with remaining blocks.
   Preconditions:
   1) IH property: MnDef nodes have correct inst_def entries
   2) nodes_fresh
   3) fn_inst_ids_distinct
   4) No existing MnDef has inst_id from any block in lbls *)
Triviality process_blocks_inst_def_reverse:
  !lbls bp addr_sp fn ms.
    (!a i b l. FLOOKUP ms.ms_nodes a = SOME (MnDef i b l) ==>
      FLOOKUP ms.ms_inst_def i = SOME a) /\
    nodes_fresh ms /\
    fn_inst_ids_distinct fn /\
    ALL_DISTINCT lbls /\
    (!a j b l lbl bb.
      FLOOKUP ms.ms_nodes a = SOME (MnDef j b l) /\
      MEM lbl lbls /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM j (MAP (\i. i.inst_id) bb.bb_instructions) ==> F) ==>
    !aid iid blk loc.
      FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid =
        SOME (MnDef iid blk loc) ==>
      FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_inst_def iid =
        SOME aid
Proof
  Induct >- simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> DISCH_TAC >>
  simp[mem_ssa_process_blocks_def] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[]
  >- ((* lookup_block h = NONE: skip h, apply IH directly *)
      first_x_assum match_mp_tac >>
      qpat_x_assum `_ /\ _ /\ _ /\ _ /\ _` strip_assume_tac >>
      rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC)
      >- (gvs[ALL_DISTINCT]) >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[MEM])
  >> rename [`lookup_block h fn.fn_blocks = SOME bb`] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
    `mem_ssa_process_block bp addr_sp h ms bb.bb_instructions`] mp_tac) >>
  impl_tac
  >- (
    qpat_x_assum `_ /\ _ /\ _ /\ _ /\ _` strip_assume_tac >>
    `ALL_DISTINCT lbls /\ ~MEM h lbls` by
      (gvs[ALL_DISTINCT]) >>
    rpt conj_tac
    >- ((* IH property: MnDef in process_block => inst_def maps back *)
        rpt strip_tac >>
        match_mp_tac process_block_inst_def_reverse >>
        qexistsl_tac [`b`, `l`] >> simp[] >>
        conj_tac >- (irule fn_inst_ids_block_distinct >>
                      metis_tac[lookup_block_props]) >>
        rpt strip_tac >> first_x_assum irule >> metis_tac[MEM])
    >- metis_tac[process_block_preserves_fresh]
    >- simp[]
    >- simp[]
    >- ((* Collision-free for remaining blocks *)
        rpt strip_tac >>
        drule (REWRITE_RULE [GSYM AND_IMP_INTRO]
                (GEN_ALL process_block_MnDef_old_or_new)) >>
        disch_then drule >> strip_tac
        >- (first_x_assum irule >> metis_tac[MEM])
        >- (`MEM bb fn.fn_blocks` by metis_tac[lookup_block_props] >>
            `MEM bb' fn.fn_blocks` by metis_tac[lookup_block_props] >>
            `bb = bb'` by
              metis_tac[fn_inst_ids_distinct_unique_block, lookup_block_props] >>
            `h = lbl` by metis_tac[lookup_block_props] >> gvs[])))
  >> disch_then (qspecl_then [`aid`, `iid`, `blk`, `loc`] mp_tac) >> simp[]
QED

(* ==========================================================================
   Phase 2 establishment: nodes monotonicity (only adds, never overwrites)
   ========================================================================== *)

(* insert_phi_at only adds to nodes at ms.ms_next_id (fresh key) *)
Triviality insert_phi_at_nodes_mono:
  ∀ms cfg dom fuel lbl ms' inserted aid node.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    aid < ms.ms_next_id ⇒
    FLOOKUP ms'.ms_nodes aid = SOME node
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  COND_CASES_TAC >> gvs[]
QED

(* insert_phi_at monotonically increases next_id *)
Triviality insert_phi_at_next_id_mono:
  ∀ms cfg dom fuel lbl ms' inserted.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    ms.ms_next_id ≤ ms'.ms_next_id
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[]
QED

(* insert_phi_at preserves freshness *)
Triviality insert_phi_at_preserves_fresh:
  ∀ms cfg dom fuel lbl ms' inserted.
    nodes_fresh ms ∧
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    nodes_fresh ms'
Proof
  rw[nodes_fresh_def] >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >>
  gvs[mem_ssa_insert_phi_at_def] >>
  fs[finite_mapTheory.FDOM_FUPDATE] >>
  rpt strip_tac >> gvs[] >>
  res_tac >> DECIDE_TAC
QED

Triviality insert_phi_at_preserves_zero_not_in_nodes:
  !ms cfg dom fuel lbl ms' inserted.
    0 NOTIN FDOM ms.ms_nodes /\
    ms.ms_next_id > 0 /\
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ==>
    0 NOTIN FDOM ms'.ms_nodes /\ ms'.ms_next_id > 0
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >>
  gvs[mem_ssa_insert_phi_at_def, FDOM_FUPDATE]
QED

Triviality insert_phi_at_preserves_block_defs_are_defs:
  !ms cfg dom fuel lbl ms' inserted.
    nodes_fresh ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ==>
    (!lbl' aid. MEM aid (fmap_lookup_list ms'.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms'.ms_nodes aid = SOME (MnDef iid lbl' loc))
Proof
  rpt gen_tac >>
  simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  (* SOME case: ms' = ms, trivial *)
  TRY (rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  (* NONE case: block_defs unchanged, nodes extended with fresh MnPhi *)
  rpt strip_tac >>
  `?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)` by
    (first_x_assum match_mp_tac >> simp[]) >>
  `aid IN FDOM ms.ms_nodes` by fs[FLOOKUP_DEF] >>
  `aid < ms.ms_next_id` by (
    qpat_x_assum `nodes_fresh ms`
      (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >> res_tac) >>
  simp[FLOOKUP_UPDATE]
QED

Triviality process_frontiers_nodes_mono:
  ∀fronts ms cfg dom fuel ms' wl aid node.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    nodes_fresh ms ⇒
    FLOOKUP ms'.ms_nodes aid = SOME node
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `nodes_fresh ms1` by metis_tac[insert_phi_at_preserves_fresh] >>
  `ms.ms_next_id ≤ ms1.ms_next_id` by metis_tac[insert_phi_at_next_id_mono] >>
  `aid < ms.ms_next_id` by
    (fs[nodes_fresh_def, finite_mapTheory.FLOOKUP_DEF] >>
     res_tac >> DECIDE_TAC) >>
  `FLOOKUP ms1.ms_nodes aid = SOME node` by
    metis_tac[insert_phi_at_nodes_mono] >>
  metis_tac[]
QED

Triviality process_frontiers_next_id_mono:
  ∀fronts ms cfg dom fuel ms' wl.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    ms.ms_next_id ≤ ms'.ms_next_id
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `ms.ms_next_id ≤ ms1.ms_next_id` by metis_tac[insert_phi_at_next_id_mono] >>
  `ms1.ms_next_id ≤ ms'.ms_next_id` by metis_tac[] >>
  DECIDE_TAC
QED

Triviality process_frontiers_preserves_fresh:
  ∀fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms ∧
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    nodes_fresh ms'
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  metis_tac[insert_phi_at_preserves_fresh]
QED

Triviality insert_phis_preserves_fresh:
  ∀ms cfg dom ef fuel wl.
    nodes_fresh ms ⇒
    nodes_fresh (mem_ssa_insert_phis ms cfg dom ef fuel wl)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum irule >>
  metis_tac[process_frontiers_preserves_fresh]
QED

Triviality process_frontiers_preserves_zero_not_in_nodes:
  !fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms /\
    0 NOTIN FDOM ms.ms_nodes /\ ms.ms_next_id > 0 /\
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ==>
    0 NOTIN FDOM ms'.ms_nodes /\ ms'.ms_next_id > 0
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  metis_tac[insert_phi_at_preserves_fresh,
            insert_phi_at_preserves_zero_not_in_nodes]
QED

Triviality insert_phis_preserves_zero_not_in_nodes:
  !ms cfg dom ef fuel wl.
    nodes_fresh ms /\
    0 NOTIN FDOM ms.ms_nodes /\ ms.ms_next_id > 0 ==>
    0 NOTIN FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes /\
    (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_next_id > 0
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >> rpt conj_tac >>
  TRY (rpt gen_tac >> strip_tac >> simp[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum irule >>
  metis_tac[process_frontiers_preserves_fresh,
            process_frontiers_preserves_zero_not_in_nodes]
QED

Triviality insert_phis_nodes_mono:
  ∀ms cfg dom ef fuel wl aid node.
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    nodes_fresh ms ⇒
    FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum irule >>
  `nodes_fresh ms'` by metis_tac[process_frontiers_preserves_fresh] >>
  metis_tac[process_frontiers_nodes_mono]
QED

(* Phase 2 preserves inst_maps_consistent (inst_def/use unchanged, nodes only grow) *)
Triviality insert_phis_preserves_inst_maps:
  ∀ms cfg dom ef fuel wl.
    mem_ssa_inst_maps_consistent ms ∧ nodes_fresh ms ⇒
    mem_ssa_inst_maps_consistent (mem_ssa_insert_phis ms cfg dom ef fuel wl)
Proof
  rpt strip_tac >>
  fs[mem_ssa_inst_maps_consistent_def] >>
  simp[insert_phis_fields] >>
  rpt strip_tac >> res_tac >>
  qexistsl_tac [`blk`, `loc`] >>
  match_mp_tac insert_phis_nodes_mono >>
  simp[]
QED

(* ==========================================================================
   Phase 1+2 establishment: ids_valid
   ========================================================================== *)

(* process_inst preserves + extends ids_valid (defs/uses part only) *)
Triviality process_inst_preserves_ids_valid_du:
  ∀bp addr_sp lbl ms inst.
    (∀l aids aid.
       (FLOOKUP ms.ms_block_defs l = SOME aids ∨
        FLOOKUP ms.ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒ aid ∈ FDOM ms.ms_nodes) ⇒
    (∀l aids aid.
       (FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs l = SOME aids ∨
        FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[mem_ssa_process_inst_def] >>
  rpt COND_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
  fs[cfgDefsTheory.fmap_lookup_list_def,
     finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FDOM_FUPDATE] >>
  rpt strip_tac >> gvs[listTheory.MEM_SNOC] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* Remaining: if-then-else in assumption *)
  Cases_on `lbl = l` >> gvs[listTheory.MEM_SNOC]
  >- (Cases_on `FLOOKUP ms.ms_block_uses l` >> gvs[] >> res_tac >> gvs[])
  >- (res_tac >> simp[])
  >- (Cases_on `FLOOKUP ms.ms_block_defs l` >> gvs[] >> res_tac >> gvs[])
  >- (res_tac >> simp[])
  >- (Cases_on `FLOOKUP ms.ms_block_defs l` >> gvs[] >> res_tac >> gvs[])
  >- (res_tac >> simp[])
  >- (Cases_on `FLOOKUP ms.ms_block_uses l` >> gvs[] >> res_tac >> gvs[])
  >- (res_tac >> simp[])
QED

Triviality process_block_preserves_ids_valid_du:
  ∀insts bp addr_sp lbl ms.
    (∀l aids aid.
       (FLOOKUP ms.ms_block_defs l = SOME aids ∨
        FLOOKUP ms.ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒ aid ∈ FDOM ms.ms_nodes) ⇒
    (∀l aids aid.
       (FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs l = SOME aids ∨
        FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac process_inst_preserves_ids_valid_du >>
  first_assum ACCEPT_TAC
QED

Triviality process_blocks_preserves_ids_valid_du:
  ∀lbls bp addr_sp fn ms.
    (∀l aids aid.
       (FLOOKUP ms.ms_block_defs l = SOME aids ∨
        FLOOKUP ms.ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒ aid ∈ FDOM ms.ms_nodes) ⇒
    (∀l aids aid.
       (FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs l = SOME aids ∨
        FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  TRY (match_mp_tac process_block_preserves_ids_valid_du) >>
  first_assum ACCEPT_TAC
QED

(* Phase 2: insert_phi_at preserves ids_valid (phis part) and adds its own phi *)
Triviality insert_phi_at_preserves_ids_valid_phis:
  ∀ms cfg dom fuel lbl ms' inserted.
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM ms.ms_nodes) ∧
    nodes_fresh ms ∧
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    (∀l phi_id. FLOOKUP ms'.ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM ms'.ms_nodes)
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >> rpt strip_tac >>
  fs[finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FDOM_FUPDATE] >>
  Cases_on `lbl = l` >> gvs[] >>
  `phi_id ∈ FDOM ms.ms_nodes` by (res_tac >> simp[]) >>
  fs[nodes_fresh_def, finite_mapTheory.FDOM_FUPDATE]
QED

Triviality process_frontiers_preserves_ids_valid_phis:
  ∀fronts ms cfg dom fuel ms' wl.
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM ms.ms_nodes) ∧
    nodes_fresh ms ∧
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    (∀l phi_id. FLOOKUP ms'.ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM ms'.ms_nodes)
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >>
  TRY (strip_tac >> simp[] >> NO_TAC) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`ms1`,`cfg`,`dom`,`fuel`,`ms'`,`rest`] mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  metis_tac[insert_phi_at_preserves_fresh,
            insert_phi_at_preserves_ids_valid_phis]
QED

Triviality insert_phis_preserves_ids_valid_phis:
  ∀ms cfg dom ef fuel wl.
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM ms.ms_nodes) ∧
    nodes_fresh ms ⇒
    (∀l phi_id. FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_phis l = SOME phi_id ⇒
                phi_id ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >> gvs[mem_ssa_insert_phis_def] >>
  TRY (res_tac >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  `(∀l' phi_id'. FLOOKUP ms'.ms_block_phis l' = SOME phi_id' ⇒
                 phi_id' ∈ FDOM ms'.ms_nodes) ∧ nodes_fresh ms'` by
    metis_tac[process_frontiers_preserves_ids_valid_phis,
              process_frontiers_preserves_fresh] >>
  res_tac
QED

(* Corollary: FDOM monotonicity for insert_phis (used by multiple preservation lemmas) *)
Triviality insert_phis_fdom_nodes_mono:
  ∀ms cfg dom ef fuel wl aid.
    aid ∈ FDOM ms.ms_nodes ∧ nodes_fresh ms ⇒
    aid ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes
Proof
  rpt strip_tac >>
  `∃node. FLOOKUP ms.ms_nodes aid = SOME node` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  `FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node` by
    (match_mp_tac insert_phis_nodes_mono >> simp[]) >>
  fs[finite_mapTheory.FLOOKUP_DEF]
QED

(* Phase 2 preserves ids_valid du part (block_defs/uses unchanged) *)
Triviality insert_phis_preserves_ids_valid_du:
  ∀ms cfg dom ef fuel wl.
    (∀l aids aid.
       (FLOOKUP ms.ms_block_defs l = SOME aids ∨
        FLOOKUP ms.ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒ aid ∈ FDOM ms.ms_nodes) ∧
    nodes_fresh ms ⇒
    (∀l aids aid.
       (FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_defs l = SOME aids ∨
        FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_uses l = SOME aids) ∧
       MEM aid aids ⇒
       aid ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes)
Proof
  rpt strip_tac >> gvs[insert_phis_fields] >>
  `aid ∈ FDOM ms.ms_nodes` by (res_tac >> simp[]) >>
  metis_tac[insert_phis_fdom_nodes_mono]
QED

(* ==========================================================================
   Phase 2: phi_ops edges validity
   ========================================================================== *)

(* get_exit_def returns 0 or a valid node id when ids_valid holds *)
Triviality get_exit_def_valid:
  ∀ms dom fuel lbl.
    mem_ssa_ids_valid ms ⇒
    let rd = mem_ssa_get_exit_def ms dom fuel lbl in
    rd = 0 ∨ rd ∈ FDOM ms.ms_nodes
Proof
  Induct_on `fuel` >> simp[mem_ssa_get_exit_def_def] >>
  rpt strip_tac >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl ≠ []` >> gvs[] >>
  TRY (
    DISJ2_TAC >>
    fs[mem_ssa_ids_valid_def, cfgDefsTheory.fmap_lookup_list_def] >>
    CASE_TAC >> gvs[] >>
    first_x_assum (qspecl_then [`lbl`, `x`, `LAST x`] mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    simp[rich_listTheory.MEM_LAST_NOT_NIL] >> NO_TAC
  ) >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >> simp[] >>
  TRY (Cases_on `idom_of dom lbl` >> simp[] >> NO_TAC) >>
  DISJ2_TAC >> fs[mem_ssa_ids_valid_def] >> res_tac
QED

(* insert_phi_at preserves phi_ops validity.
   New phi_ops entries have rd from get_exit_def (valid by get_exit_def_valid).
   Old entries survive because FDOM ms.ms_nodes ⊆ FDOM ms'.ms_nodes. *)
Triviality insert_phi_at_preserves_phi_ops_valid:
  ∀ms cfg dom fuel lbl ms' inserted.
    mem_ssa_ids_valid ms ∧ nodes_fresh ms ∧
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒ rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀phi_id ops rd blk.
       FLOOKUP ms'.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒ rd = 0 ∨ rd ∈ FDOM ms'.ms_nodes)
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  (* SOME case handled inline, NONE case continues *)
  TRY (rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  rpt strip_tac >>
  (* Goal: rd = 0 ∨ rd = ms.ms_next_id ∨ rd ∈ FDOM ms.ms_nodes *)
  Cases_on `phi_id = ms.ms_next_id` >> gvs[finite_mapTheory.FLOOKUP_UPDATE, MEM_MAP] >>
  TRY (res_tac >> simp[] >> NO_TAC) >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
            (Q.SPECL [`ms`, `dom`, `fuel`, `blk`] get_exit_def_valid)) >>
  simp[] >> metis_tac[]
QED

(* process_frontiers preserves phi_ops validity *)
(* Combined ids_valid preservation for insert_phi_at *)
Triviality insert_phi_at_preserves_ids_valid:
  ∀ms cfg dom fuel lbl ms' inserted.
    mem_ssa_ids_valid ms ∧ nodes_fresh ms ∧
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    mem_ssa_ids_valid ms'
Proof
  rpt strip_tac >> simp[mem_ssa_ids_valid_def] >> rpt conj_tac >>
  rpt strip_tac
  (* du part: block_defs/uses fields preserved, nodes only grow *)
  >> TRY (
    `ms'.ms_block_defs = ms.ms_block_defs ∧
     ms'.ms_block_uses = ms.ms_block_uses` by metis_tac[insert_phi_at_fields] >>
    `aid ∈ FDOM ms.ms_nodes` by
      (fs[mem_ssa_ids_valid_def] >> res_tac >> gvs[]) >>
    `∃node. FLOOKUP ms.ms_nodes aid = SOME node` by
      metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
    `FLOOKUP ms'.ms_nodes aid = SOME node` by
      (match_mp_tac insert_phi_at_nodes_mono >>
       qexistsl_tac [`ms`, `cfg`, `dom`, `fuel`, `lbl`] >>
       fs[nodes_fresh_def]) >>
    fs[finite_mapTheory.FLOOKUP_DEF] >> NO_TAC
  )
  (* phis part *)
  >> metis_tac[insert_phi_at_preserves_ids_valid_phis, mem_ssa_ids_valid_def]
QED

(* Combined ids_valid preservation for process_frontiers *)
Triviality process_frontiers_preserves_ids_valid:
  ∀fronts ms cfg dom fuel ms' wl.
    mem_ssa_ids_valid ms ∧ nodes_fresh ms ∧
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    mem_ssa_ids_valid ms'
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`] >> simp[] >>
  metis_tac[insert_phi_at_preserves_ids_valid, insert_phi_at_preserves_fresh]
QED

(* process_frontiers preserves phi_ops validity *)
Triviality process_frontiers_preserves_phi_ops_valid:
  ∀fronts ms cfg dom fuel ms' wl.
    mem_ssa_ids_valid ms ∧ nodes_fresh ms ∧
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒ rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀phi_id ops rd blk.
       FLOOKUP ms'.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒ rd = 0 ∨ rd ∈ FDOM ms'.ms_nodes)
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  TRY (rpt gen_tac >> strip_tac >> first_x_assum ACCEPT_TAC >> NO_TAC) >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`] >> simp[] >>
  metis_tac[insert_phi_at_preserves_ids_valid, insert_phi_at_preserves_fresh,
            insert_phi_at_preserves_phi_ops_valid]
QED

(* insert_phis preserves phi_ops validity *)
Triviality insert_phis_preserves_phi_ops_valid:
  ∀ms cfg dom ef fuel wl.
    mem_ssa_ids_valid ms ∧ nodes_fresh ms ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒ rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀phi_id ops rd blk.
       FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_phi_ops phi_id = SOME ops ∧
       MEM (rd, blk) ops ⇒
       rd = 0 ∨ rd ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >> gvs[mem_ssa_insert_phis_def] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  (* Discharge the IH premise *)
  `mem_ssa_ids_valid ms' ∧ nodes_fresh ms'` by
    metis_tac[process_frontiers_preserves_ids_valid,
              process_frontiers_preserves_fresh] >>
  `∀phi_id ops rd blk.
     FLOOKUP ms'.ms_phi_ops phi_id = SOME ops ∧ MEM (rd, blk) ops ⇒
     rd = 0 ∨ rd ∈ FDOM ms'.ms_nodes` by
    metis_tac[process_frontiers_preserves_phi_ops_valid] >>
  (* Apply IH *)
  res_tac >> gvs[]
QED

(* ==========================================================================
   Property 5: No redundant phis after construction
   ========================================================================== *)

Theorem mem_ssa_no_redundant_phis:
  ∀cfg dom bp fn addr_sp ms lbl phi_id ops.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_block_phis lbl = SOME phi_id ∧
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops ∧
    ops ≠ [] ⇒
    ¬mem_ssa_phi_redundant ops
Proof
  rpt gen_tac >> strip_tac >> gvs[mem_ssa_build_def] >>
  (* Abbreviate the inner state (before remove_redundant_phis) *)
  qmatch_asmsub_abbrev_tac
    `mem_ssa_remove_redundant_phis ms0 _` >>
  (* Get: FLOOKUP ms0.ms_block_phis lbl = SOME phi_id *)
  `FLOOKUP ms0.ms_block_phis lbl = SOME phi_id` by
    metis_tac[remove_redundant_phis_block_phis_subseteq] >>
  (* Get: MEM (lbl, phi_id) (fmap_to_alist ms0.ms_block_phis) *)
  `MEM (lbl, phi_id) (fmap_to_alist ms0.ms_block_phis)` by
    simp[alistTheory.MEM_fmap_to_alist_FLOOKUP] >>
  (* Get: FLOOKUP ms0.ms_phi_ops phi_id = SOME ops *)
  `FLOOKUP ms0.ms_phi_ops phi_id = SOME ops` by
    fs[remove_redundant_phis_fields, Abbr `ms0`] >>
  (* Apply soundness *)
  metis_tac[remove_redundant_phis_sound]
QED

(* ==========================================================================
   Phase 3 establishment: edges_valid + reaching_complete
   ========================================================================== *)

(* find_prev_def returns NONE or a value from ms_inst_def *)
Triviality find_prev_def_valid:
  ∀ms insts target d.
    mem_ssa_inst_maps_consistent ms ∧
    mem_ssa_find_prev_def ms insts target = SOME d ⇒
    d ∈ FDOM ms.ms_nodes
Proof
  Induct_on `insts` >> simp[mem_ssa_find_prev_def_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_id = target` >> gvs[] >>
  Cases_on `mem_ssa_find_prev_def ms insts target` >> gvs[]
  >- (
    (* recursive call returned NONE, result is FLOOKUP ms.ms_inst_def h.inst_id *)
    fs[mem_ssa_inst_maps_consistent_def] >>
    Cases_on `FLOOKUP ms.ms_inst_def h.inst_id` >> gvs[] >>
    res_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]
  ) >>
  (* recursive call returned SOME → apply IH *)
  res_tac
QED

(* reaching_in_block returns 0 or a valid node id *)
Triviality reaching_in_block_valid:
  ∀ms dom fn fuel inst_id blk_lbl.
    mem_ssa_ids_valid ms ∧ mem_ssa_inst_maps_consistent ms ⇒
    let rd = mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl in
    rd = 0 ∨ rd ∈ FDOM ms.ms_nodes
Proof
  rpt strip_tac >> simp[mem_ssa_reaching_in_block_def] >>
  Cases_on `lookup_block blk_lbl fn.fn_blocks` >> simp[] >>
  Cases_on `mem_ssa_find_prev_def ms x.bb_instructions inst_id` >> simp[] >>
  (* SOME case: find_prev_def returned a def_id *)
  TRY (
    DISJ2_TAC >> match_mp_tac find_prev_def_valid >>
    qexistsl_tac [`x.bb_instructions`, `inst_id`] >> simp[] >> NO_TAC
  ) >>
  (* NONE case: check phis, then idom *)
  Cases_on `FLOOKUP ms.ms_block_phis blk_lbl` >> simp[] >>
  TRY (DISJ2_TAC >> fs[mem_ssa_ids_valid_def] >> res_tac >> NO_TAC) >>
  Cases_on `idom_of dom blk_lbl` >> simp[] >>
  mp_tac (Q.SPECL [`ms`, `dom`, `fuel`, `x'`] get_exit_def_valid) >> simp[]
QED

(* connect_list preserves edges_valid for reaching entries.
   Uses separate S parameter to decouple node set from ms_reaching updates. *)
Triviality connect_list_reaching_valid:
  ∀aids ms dom fn fuel.
    mem_ssa_ids_valid ms ∧ mem_ssa_inst_maps_consistent ms ∧
    (∀aid rd. FLOOKUP ms.ms_reaching aid = SOME rd ⇒
              rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀aid rd. FLOOKUP (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching aid = SOME rd ⇒
              rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof
  Induct_on `aids`
  >- (simp[mem_ssa_connect_list_def] >> rpt strip_tac >> res_tac)
  >> rpt gen_tac >> strip_tac
  >> Cases_on `FLOOKUP ms.ms_nodes h` >> fs[mem_ssa_connect_list_def]
  (* NONE case: IH applies directly *)
  >> TRY apply_forall_ih_tac
  >> Cases_on `x` >> simp[]
  (* MnPhi case: IH applies directly *)
  >> TRY apply_forall_ih_tac
  (* MnDef/MnUse: apply IH to updated state *)
  >> qmatch_goalsub_abbrev_tac `mem_ssa_connect_list ms'`
  >> first_x_assum (qspecl_then [`ms'`, `dom`, `fn`, `fuel`] mp_tac)
  >> UNABBREV_ALL_TAC >> simp[mem_ssa_ids_valid_def, mem_ssa_inst_maps_consistent_def]
  >> disch_then match_mp_tac
  >> fs[mem_ssa_ids_valid_def, mem_ssa_inst_maps_consistent_def]
  >> rpt strip_tac
  >> TRY (res_tac >> simp[] >> NO_TAC)
  >> fs[finite_mapTheory.FLOOKUP_UPDATE]
  >> Cases_on `h = aid` >> gvs[]
  >> TRY (res_tac >> gvs[] >> NO_TAC)
  >> match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM] reaching_in_block_valid)
  >> simp[mem_ssa_ids_valid_def, mem_ssa_inst_maps_consistent_def]
  >> metis_tac[]
QED

(* Per-label step: connect_list twice preserves reaching validity *)
Triviality connect_one_label_reaching_valid:
  ∀ms dom fn fuel uses defs.
    mem_ssa_ids_valid ms ∧ mem_ssa_inst_maps_consistent ms ∧
    (∀aid rd. FLOOKUP ms.ms_reaching aid = SOME rd ⇒
              rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀aid rd. FLOOKUP (mem_ssa_connect_list
      (mem_ssa_connect_list ms dom fn fuel uses) dom fn fuel defs
    ).ms_reaching aid = SOME rd ⇒ rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof
  rpt strip_tac >>
  (* First application: reaching entries of connect_list ms ... uses point into ms.ms_nodes *)
  mp_tac (Q.SPECL [`uses`, `ms`, `dom`, `fn`, `fuel`] connect_list_reaching_valid) >>
  simp[] >> strip_tac >>
  (* Second application: reaching entries of connect_list ms1 ... defs point into ms1.ms_nodes *)
  mp_tac (Q.SPECL [`defs`, `mem_ssa_connect_list ms dom fn fuel uses`, `dom`, `fn`, `fuel`]
            connect_list_reaching_valid) >>
  simp[connect_list_preserves_ids_valid, connect_list_preserves_inst_maps] >>
  (* ms1.ms_nodes = ms.ms_nodes by connect_list_fields *)
  simp[connect_list_fields] >>
  metis_tac[]
QED

(* connect_all preserves reaching entry validity *)
Triviality connect_all_reaching_valid:
  ∀lbls ms dom fn fuel.
    mem_ssa_ids_valid ms ∧ mem_ssa_inst_maps_consistent ms ∧
    (∀aid rd. FLOOKUP ms.ms_reaching aid = SOME rd ⇒
              rd = 0 ∨ rd ∈ FDOM ms.ms_nodes) ⇒
    (∀aid rd. FLOOKUP (mem_ssa_connect_all ms dom fn fuel lbls).ms_reaching aid = SOME rd ⇒
              rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof
  Induct >> simp[mem_ssa_connect_all_def] >>
  rpt gen_tac >> strip_tac >>
  (* IH has shadowed ms — use qspecl_then pattern *)
  qmatch_goalsub_abbrev_tac `mem_ssa_connect_all ms' dom fn fuel lbls` >>
  first_x_assum (qspecl_then [`ms'`, `dom`, `fn`, `fuel`] mp_tac) >>
  UNABBREV_ALL_TAC >>
  simp[connect_list_preserves_ids_valid, connect_list_preserves_inst_maps,
       connect_list_fields] >>
  disch_then match_mp_tac >>
  match_mp_tac connect_one_label_reaching_valid >>
  rpt conj_tac >> first_x_assum ACCEPT_TAC
QED

(* connect_list preserves existing reaching entries *)
Triviality connect_list_preserves_reaching:
  ∀aids ms dom fn fuel aid.
    (∃rd. FLOOKUP ms.ms_reaching aid = SOME rd) ⇒
    (∃rd. FLOOKUP (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching aid = SOME rd)
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >>
  Cases_on `FLOOKUP ms.ms_nodes h` >> simp[] >>
  Cases_on `x` >> simp[] >>
  (* MnDef/MnUse case: ms' = ms with reaching |+ (h, rd) *)
  strip_tac >>
  first_x_assum match_mp_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* connect_list sets reaching for every MnDef/MnUse in the list *)
Triviality connect_list_sets_reaching:
  ∀aids ms dom fn fuel aid node.
    MEM aid aids ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃rd. FLOOKUP (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching aid = SOME rd
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  (* Case 1: aid = h — connect_list processes it *)
  TRY (
    simp[connect_list_fields] >>
    Cases_on `node` >> gvs[] >>
    match_mp_tac connect_list_preserves_reaching >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >> NO_TAC
  ) >>
  (* Case 2: MEM aid aids — IH handles via case split on node at h *)
  Cases_on `FLOOKUP ms.ms_nodes h` >> simp[] >>
  Cases_on `x` >> simp[]
QED

(* reaching_in_block, find_prev_def, and get_exit_def only depend on
   ms_nodes, ms_inst_def, ms_block_defs, ms_block_phis — NOT ms_reaching.
   So updating ms_reaching doesn't change their results. *)
Triviality find_prev_def_reaching_indep:
  ∀insts ms r target.
    mem_ssa_find_prev_def (ms with ms_reaching := r) insts target =
    mem_ssa_find_prev_def ms insts target
Proof
  Induct >> simp[mem_ssa_find_prev_def_def]
QED

Triviality get_exit_def_reaching_indep:
  ∀fuel ms dom r lbl.
    mem_ssa_get_exit_def (ms with ms_reaching := r) dom fuel lbl =
    mem_ssa_get_exit_def ms dom fuel lbl
Proof
  Induct >> simp[mem_ssa_get_exit_def_def, LET_THM,
    find_prev_def_reaching_indep]
QED

Triviality reaching_in_block_reaching_indep:
  ∀ms dom fn fuel iid blk r.
    mem_ssa_reaching_in_block (ms with ms_reaching := r) dom fn fuel iid blk =
    mem_ssa_reaching_in_block ms dom fn fuel iid blk
Proof
  simp[mem_ssa_reaching_in_block_def, find_prev_def_reaching_indep,
       get_exit_def_reaching_indep]
QED

(* General congruence: reaching_in_block only depends on inst_def, block_defs,
   block_phis fields of ms. Works for connect_list output via connect_list_fields. *)
Triviality find_prev_def_cong:
  ∀insts ms ms' target.
    ms'.ms_inst_def = ms.ms_inst_def ⇒
    mem_ssa_find_prev_def ms' insts target =
    mem_ssa_find_prev_def ms insts target
Proof
  Induct >> simp[mem_ssa_find_prev_def_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Triviality get_exit_def_cong:
  ∀fuel ms ms' dom lbl.
    ms'.ms_block_defs = ms.ms_block_defs ∧
    ms'.ms_block_phis = ms.ms_block_phis ⇒
    mem_ssa_get_exit_def ms' dom fuel lbl =
    mem_ssa_get_exit_def ms dom fuel lbl
Proof
  Induct >> simp[mem_ssa_get_exit_def_def, LET_THM] >>
  rpt strip_tac >> res_tac >> fs[]
QED

Triviality reaching_in_block_cong:
  ∀ms ms' dom fn fuel iid blk.
    ms'.ms_inst_def = ms.ms_inst_def ∧
    ms'.ms_block_defs = ms.ms_block_defs ∧
    ms'.ms_block_phis = ms.ms_block_phis ⇒
    mem_ssa_reaching_in_block ms' dom fn fuel iid blk =
    mem_ssa_reaching_in_block ms dom fn fuel iid blk
Proof
  rpt strip_tac >>
  simp[mem_ssa_reaching_in_block_def] >>
  CASE_TAC >> simp[] >>
  `∀insts t. mem_ssa_find_prev_def ms' insts t =
             mem_ssa_find_prev_def ms insts t` by
    (rpt strip_tac >> match_mp_tac find_prev_def_cong >> simp[]) >>
  `∀f d l. mem_ssa_get_exit_def ms' d f l =
           mem_ssa_get_exit_def ms d f l` by
    (rpt strip_tac >> match_mp_tac get_exit_def_cong >> simp[]) >>
  simp[]
QED

(* Characterization: every reaching entry in connect_list output is either
   from the input or from reaching_in_block for a node in the list. *)
Triviality connect_list_reaching_characterize:
  ∀aids ms dom fn fuel aid rd.
    FLOOKUP (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching aid = SOME rd ⇒
    FLOOKUP ms.ms_reaching aid = SOME rd ∨
    (∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ∧
       rd = mem_ssa_reaching_in_block ms dom fn fuel
              (mn_inst_id node) (mn_block node))
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >>
  Cases_on `FLOOKUP ms.ms_nodes h` >> simp[] >>
  Cases_on `x` >> simp[]
  (* MnDef/MnUse: ms' = ms with reaching |+ (h, reaching_in_block ...) *)
  >> TRY (
    strip_tac >>
    first_x_assum drule >>
    simp[FLOOKUP_UPDATE, reaching_in_block_reaching_indep] >>
    strip_tac >> (
      (* Case 1: from old reaching - check if aid = h *)
      (Cases_on `aid = h` >> gvs[] >> DISJ2_TAC >> metis_tac[])
      ORELSE
      (* Case 2: from new reaching_in_block *)
      (DISJ2_TAC >> metis_tac[])
    ) >> NO_TAC)
QED

(* connect_all achieves reaching_complete when all MnDef/MnUse are covered *)
Triviality connect_all_reaching_complete:
  ∀lbls ms dom fn fuel.
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
      (∃lbl. MEM lbl lbls ∧
        (MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ∨
         MEM aid (fmap_lookup_list ms.ms_block_uses lbl))) ∨
      (∃rd. FLOOKUP ms.ms_reaching aid = SOME rd)) ⇒
    mem_ssa_reaching_complete (mem_ssa_connect_all ms dom fn fuel lbls)
Proof
  Induct >> simp[mem_ssa_connect_all_def] >>
  (* Base: [] — all MnDef/MnUse already have reaching *)
  TRY (rpt strip_tac >> simp[mem_ssa_reaching_complete_def] >>
       rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  (* Step: h::lbls — connect uses then defs for h, recurse on lbls *)
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  simp[connect_list_fields] >>
  rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  (* aid in defs of h: connect_list for defs covers it *)
  TRY (
    DISJ2_TAC >>
    match_mp_tac connect_list_sets_reaching >>
    simp[connect_list_fields] >>
    qexistsl_tac [`node`] >> simp[] >> NO_TAC
  ) >>
  (* aid in uses of h: connect_list for uses, preserved by defs *)
  TRY (
    DISJ2_TAC >>
    match_mp_tac connect_list_preserves_reaching >>
    match_mp_tac connect_list_sets_reaching >>
    qexistsl_tac [`node`] >> simp[] >> NO_TAC
  ) >>
  (* aid in some other lbl in lbls → pass to IH *)
  TRY (DISJ1_TAC >> qexists_tac `lbl` >> simp[] >> NO_TAC) >>
  (* aid already had reaching → preserved *)
  DISJ2_TAC >> metis_tac[connect_list_preserves_reaching]
QED

(* Phase 1 locality: process_inst/block/blocks only modify block_defs/uses at
   the processed label. This lets us derive MEM l order from du_covered. *)
Triviality process_inst_defs_uses_local:
  ∀bp addr_sp lbl ms inst l.
    l ≠ lbl ⇒
    fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs l =
      fmap_lookup_list ms.ms_block_defs l ∧
    fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_uses l =
      fmap_lookup_list ms.ms_block_uses l
Proof
  rpt strip_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_UPDATE]
QED

Triviality process_block_defs_uses_local:
  ∀insts bp addr_sp lbl ms l.
    l ≠ lbl ⇒
    fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs l =
      fmap_lookup_list ms.ms_block_defs l ∧
    fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_uses l =
      fmap_lookup_list ms.ms_block_uses l
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `l`] mp_tac) >>
  simp[process_inst_defs_uses_local]
QED

Triviality process_blocks_defs_uses_local:
  ∀lbls bp addr_sp fn ms l.
    ¬MEM l lbls ⇒
    fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs l =
      fmap_lookup_list ms.ms_block_defs l ∧
    fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_uses l =
      fmap_lookup_list ms.ms_block_uses l
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >> CASE_TAC >> simp[] >> (
    TRY (first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`, `ms`, `l`] mp_tac) >>
         simp[] >> NO_TAC) >>
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`, `l`] mp_tac) >>
    simp[process_block_defs_uses_local]
  )
QED

(* Phase 1: non-phi node inst_id comes from processed instruction *)
Triviality process_inst_node_inst_id:
  ∀bp addr_sp lbl ms inst aid node.
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ∧
    FLOOKUP ms.ms_nodes aid = NONE ⇒
    mn_inst_id node = inst.inst_id ∧ mn_block node = lbl
Proof
  rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[FLOOKUP_UPDATE, mn_inst_id_def, mn_block_def] >>
  strip_tac >> gvs[] >>
  rpt (pop_assum mp_tac) >> rpt COND_CASES_TAC >> gvs[mn_inst_id_def, mn_block_def] >>
  rpt strip_tac >> gvs[mn_inst_id_def, mn_block_def]
QED

(* Existing nodes are preserved through process_inst/block *)
Triviality process_inst_preserves_node:
  ∀bp addr_sp lbl ms inst aid node.
    FLOOKUP ms.ms_nodes aid = SOME node ∧ nodes_fresh ms ⇒
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid = SOME node
Proof
  rpt gen_tac >> strip_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[FLOOKUP_UPDATE] >>
  fs[nodes_fresh_def, flookup_thm] >>
  rpt COND_CASES_TAC >> gvs[] >> res_tac >> gvs[]
QED

Triviality process_block_preserves_node:
  ∀insts bp addr_sp lbl ms aid node.
    FLOOKUP ms.ms_nodes aid = SOME node ∧ nodes_fresh ms ⇒
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid = SOME node
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_preserves_node, process_inst_preserves_fresh]
QED

Triviality process_block_node_inst_id:
  ∀insts bp addr_sp lbl ms aid node.
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ∧
    FLOOKUP ms.ms_nodes aid = NONE ∧
    nodes_fresh ms ⇒
    MEM (mn_inst_id node) (MAP (λi. i.inst_id) insts) ∧ mn_block node = lbl
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms h).ms_nodes aid`
  >- (
    (* aid not in process_inst output → from later insts via IH *)
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
      `mem_ssa_process_inst bp addr_sp lbl ms h`, `aid`, `node`] mp_tac) >>
    simp[] >>
    impl_tac >- metis_tac[process_inst_preserves_fresh] >>
    strip_tac >> simp[])
  >> rename [`FLOOKUP _ aid = SOME node'`] >>
  (* aid was created by process_inst h (since FLOOKUP ms = NONE) *)
  (* process_inst only creates MnDef/MnUse, never MnPhi *)
  `!blk. node' <> MnPhi blk` by (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `FLOOKUP (mem_ssa_process_inst _ _ _ _ _).ms_nodes _ = _`
      (mp_tac o REWRITE_RULE [mem_ssa_process_inst_def, LET_THM]) >>
    Cases_on `bp_get_read_location bp h addr_sp = ml_empty` >>
    Cases_on `bp_get_write_location bp h addr_sp = ml_empty` >>
    gvs[FLOOKUP_UPDATE] >>
    rpt COND_CASES_TAC >> gvs[] >>
    fs[nodes_fresh_def, flookup_thm] >> res_tac >> gvs[]) >>
  drule_all process_inst_node_inst_id >> strip_tac >>
  (* node' preserved through rest of process_block *)
  `nodes_fresh (mem_ssa_process_inst bp addr_sp lbl ms h)` by
    metis_tac[process_inst_preserves_fresh] >>
  `FLOOKUP (mem_ssa_process_block bp addr_sp lbl
     (mem_ssa_process_inst bp addr_sp lbl ms h) insts).ms_nodes aid = SOME node'` by
    metis_tac[process_block_preserves_node] >>
  `node = node'` by fs[] >> gvs[]
QED


(* Existing nodes preserved through process_blocks *)
Triviality process_blocks_preserves_node:
  ∀lbls bp addr_sp fn ms aid node.
    FLOOKUP ms.ms_nodes aid = SOME node ∧ nodes_fresh ms ⇒
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid = SOME node
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_block_preserves_node, process_block_preserves_fresh]
QED

(* Non-phi node created by process_blocks: inst_id is in corresponding block *)
Triviality process_blocks_node_inst_id:
  ∀lbls bp addr_sp fn ms aid node.
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ∧
    FLOOKUP ms.ms_nodes aid = NONE ∧
    nodes_fresh ms ⇒
    ∃bb. lookup_block (mn_block node) fn.fn_blocks = SOME bb ∧
         MEM (mn_inst_id node) (MAP (λi. i.inst_id) bb.bb_instructions)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block h fn.fn_blocks` >> fs[]
  >- (first_x_assum match_mp_tac >> metis_tac[])
  >>
  rename [`lookup_block h _ = SOME bb`] >>
  Cases_on `FLOOKUP (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_nodes aid`
  >- (
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms bb.bb_instructions`,
      `aid`, `node`] mp_tac) >>
    simp[] >>
    disch_then match_mp_tac >>
    metis_tac[process_block_preserves_fresh])
  >>
  rename [`FLOOKUP _ aid = SOME node'`] >>
  (* First show node' is preserved to the final result as node *)
  `nodes_fresh (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions)` by
    metis_tac[process_block_preserves_fresh] >>
  `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn
     (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_nodes
     aid = SOME node'` by
    metis_tac[process_blocks_preserves_node] >>
  (* So node = node', and node is non-phi (given) *)
  `node = node'` by fs[] >> gvs[] >>
  drule_all process_block_node_inst_id >> strip_tac >>
  qexists_tac `bb` >>
  imp_res_tac lookup_block_props >> gvs[]
QED

(* Phase 1 invariant: every MnDef/MnUse created is in some block's list. *)

(* Helper: insert_phis only adds MnPhi nodes *)
Triviality insert_phi_at_only_adds_phi:
  ∀ms cfg dom fuel lbl ms' inserted aid node.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    FLOOKUP ms'.ms_nodes aid = SOME node ∧
    FLOOKUP ms.ms_nodes aid = NONE ⇒
    ∃blk. node = MnPhi blk
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `ms.ms_next_id = aid` >> gvs[]
QED

Triviality process_frontiers_only_adds_phi:
  ∀fronts ms cfg dom fuel ms' wl aid node.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    FLOOKUP ms'.ms_nodes aid = SOME node ∧
    FLOOKUP ms.ms_nodes aid = NONE ∧
    nodes_fresh ms ⇒
    ∃blk. node = MnPhi blk
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  TRY (rpt strip_tac >> gvs[] >> NO_TAC) >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `nodes_fresh ms1` by metis_tac[insert_phi_at_preserves_fresh] >>
  Cases_on `FLOOKUP ms1.ms_nodes aid` >> gvs[] >>
  (* NONE case: IH applies directly — aid was added by process_frontiers ms1 *)
  TRY (first_x_assum (qspecl_then [`ms1`,`cfg`,`dom`,`fuel`,`ms'`,`rest`,`aid`,`node`] mp_tac) >>
       simp[] >> NO_TAC) >>
  (* SOME case: aid was added by insert_phi_at — must be MnPhi *)
  `∃blk. x = MnPhi blk` by
    (match_mp_tac (GEN_ALL insert_phi_at_only_adds_phi) >>
     MAP_EVERY qexists_tac [`ms`, `cfg`, `dom`, `fuel`, `h`, `ms1`, `inserted`, `aid`] >>
     simp[]) >>
  gvs[] >>
  (* node = MnPhi blk in ms1, preserved to ms' by process_frontiers_nodes_mono *)
  `FLOOKUP ms'.ms_nodes aid = SOME (MnPhi blk)` by
    (match_mp_tac (GEN_ALL process_frontiers_nodes_mono) >>
     MAP_EVERY qexists_tac [`fronts`, `ms1`, `cfg`, `dom`, `fuel`, `rest`] >>
     simp[]) >>
  gvs[]
QED

Triviality insert_phis_only_adds_phi:
  ∀ms cfg dom ef fuel wl aid node.
    FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
    FLOOKUP ms.ms_nodes aid = NONE ∧
    nodes_fresh ms ⇒
    ∃blk. node = MnPhi blk
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >> gvs[mem_ssa_insert_phis_def] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  `nodes_fresh ms'` by metis_tac[process_frontiers_preserves_fresh] >>
  Cases_on `FLOOKUP ms'.ms_nodes aid` >> gvs[] >>
  (* NONE case: node added by recursive insert_phis — apply IH *)
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* SOME case: node added by process_frontiers — must be MnPhi *)
  `∃blk. x = MnPhi blk` by
    (match_mp_tac (GEN_ALL process_frontiers_only_adds_phi) >>
     MAP_EVERY qexists_tac
       [`frontier_of dom b`, `ms`, `cfg`, `dom`, `ef`, `ms'`,
        `new_wl`, `aid`] >> simp[]) >>
  gvs[] >>
  `FLOOKUP (mem_ssa_insert_phis ms' cfg dom ef fuel (new_wl ++ wl)).ms_nodes aid = SOME (MnPhi blk)` by
    (match_mp_tac insert_phis_nodes_mono >> simp[]) >>
  gvs[]
QED

(* Phase 1+2: MnDef node ⇒ iid ∈ FDOM inst_def *)
Triviality phase12_MnDef_in_inst_def:
  !bp addr_sp fn order cfg dom ef fuel wl aid iid blk loc.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME (MnDef iid blk loc) ==>
    iid IN FDOM (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_inst_def
Proof
  rpt gen_tac >> strip_tac >>
  simp[insert_phis_fields] >>
  `nodes_fresh (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)`
    by simp[process_blocks_preserves_fresh, mem_ssa_init_def,
            nodes_fresh_def, FDOM_FEMPTY] >>
  Cases_on `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
      order).ms_nodes aid`
  >- (drule_all insert_phis_only_adds_phi >> strip_tac >> gvs[]) >>
  drule_all insert_phis_nodes_mono >>
  disch_then (qspecl_then [`cfg`,`dom`,`ef`,`fuel`,`wl`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL process_blocks_MnDef_in_inst_def) >>
  qexistsl_tac [`aid`, `blk`, `loc`] >>
  simp[mem_ssa_init_def, nodes_fresh_def, FDOM_FEMPTY, FLOOKUP_DEF]
QED

(* Strong reverse: MnDef in phase12 output => inst_def maps iid to aid *)
Triviality phase12_inst_def_reverse:
  !bp addr_sp fn order cfg dom ef fuel wl aid iid blk loc.
    wf_function fn /\ ALL_DISTINCT order /\
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME (MnDef iid blk loc) ==>
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_inst_def iid = SOME aid
Proof
  rpt gen_tac >> strip_tac >>
  simp[insert_phis_fields] >>
  `nodes_fresh (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)`
    by simp[process_blocks_preserves_fresh, mem_ssa_init_def,
            nodes_fresh_def, FDOM_FEMPTY] >>
  Cases_on `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
      order).ms_nodes aid`
  >- (drule_all insert_phis_only_adds_phi >> strip_tac >> gvs[]) >>
  drule_all insert_phis_nodes_mono >>
  disch_then (qspecl_then [`cfg`,`dom`,`ef`,`fuel`,`wl`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`order`, `bp`, `addr_sp`, `fn`, `mem_ssa_init`]
    mp_tac process_blocks_inst_def_reverse >>
  simp[mem_ssa_init_def, nodes_fresh_def, FDOM_FEMPTY, FLOOKUP_DEF] >>
  (impl_tac >- gvs[venomWfTheory.wf_function_def]) >>
  disch_then (qspecl_then [`aid`, `iid`, `blk`, `loc`] mp_tac) >>
  (impl_tac >- fs[mem_ssa_init_def, FLOOKUP_DEF]) >>
  simp[]
QED

(* Phase 1: process_inst creates new nodes ONLY in block_defs/uses *)
Triviality process_inst_du_covered:
  ∀bp addr_sp lbl ms inst.
    nodes_fresh ms ∧
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list ms.ms_block_defs l) ∨
          MEM aid (fmap_lookup_list ms.ms_block_uses l)) ⇒
    (∀aid node. FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid = SOME node ∧
                (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs l) ∨
          MEM aid (fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_uses l))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[mem_ssa_process_inst_def, LET_THM, FLOOKUP_UPDATE,
      cfgDefsTheory.fmap_lookup_list_def] >> (
    (* Split on whether aid is a new or old node *)
    TRY (Cases_on `ms.ms_next_id + 1 = aid` >> gvs[]) >>
    TRY (Cases_on `ms.ms_next_id = aid` >> gvs[]) >> (
      (* New node: witness is lbl *)
      TRY (qexists_tac `lbl` >> simp[MEM_SNOC] >> NO_TAC) >>
      (* Old node: use IH *)
      first_x_assum drule >> simp[] >> strip_tac >>
      qexists_tac `l` >>
      Cases_on `lbl = l` >> gvs[MEM_SNOC]
    )
  )
QED

Triviality process_block_du_covered:
  ∀insts bp addr_sp lbl ms.
    nodes_fresh ms ∧
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list ms.ms_block_defs l) ∨
          MEM aid (fmap_lookup_list ms.ms_block_uses l)) ⇒
    (∀aid node. FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid = SOME node ∧
                (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs l) ∨
          MEM aid (fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_uses l))
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_du_covered, process_inst_preserves_fresh]
QED

Triviality process_blocks_du_covered:
  ∀lbls bp addr_sp fn ms.
    nodes_fresh ms ∧
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list ms.ms_block_defs l) ∨
          MEM aid (fmap_lookup_list ms.ms_block_uses l)) ⇒
    (∀aid node. FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid = SOME node ∧
                (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs l) ∨
          MEM aid (fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_uses l))
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  rpt strip_tac >> (
    (* NONE case: skip h, process_blocks ms lbls *)
    TRY (first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`, `ms`] mp_tac) >>
         simp[] >> disch_then drule >> simp[] >> NO_TAC) >>
    (* SOME case: process_block then process_blocks *)
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >>
    metis_tac[process_block_du_covered, process_block_preserves_fresh]
  )
QED

Triviality insert_phis_preserves_du_covered:
  ∀ms cfg dom ef fuel wl.
    nodes_fresh ms ∧
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list ms.ms_block_defs l) ∨
          MEM aid (fmap_lookup_list ms.ms_block_uses l)) ⇒
    (∀aid node.
       FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
       (∀blk. node ≠ MnPhi blk) ⇒
      ∃l. MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_defs l) ∨
          MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_uses l))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP ms.ms_nodes aid` >> gvs[insert_phis_fields] >> (
    (* NONE: new node must be phi — contradicts assumption *)
    TRY (metis_tac[insert_phis_only_adds_phi] >> NO_TAC) >>
    (* SOME x: insert_phis_nodes_mono gives FLOOKUP result = SOME x *)
    `FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME x`
      by (match_mp_tac insert_phis_nodes_mono >> simp[]) >>
    gvs[]
  )
QED

(* ==========================================================================
   Property 1: Construction produces well-formed state
   ========================================================================== *)

(* Helper: nodes_fresh for Phase 1 output *)
Triviality phase1_fresh:
  ∀bp addr_sp fn order.
    nodes_fresh (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
Proof
  rpt gen_tac >> match_mp_tac process_blocks_preserves_fresh >>
  simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY]
QED

(* Non-phi node in Phase 1+2 output: inst_id is in corresponding block *)
Triviality phase12_node_inst_id_in_block:
  ∀bp addr_sp fn order cfg dom ef fuel wl aid node.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃bb. lookup_block (mn_block node) fn.fn_blocks = SOME bb ∧
         MEM (mn_inst_id node) (MAP (λi. i.inst_id) bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_nodes aid`
  >- (
    `∃blk. node = MnPhi blk` by (
      match_mp_tac (GEN_ALL insert_phis_only_adds_phi) >>
      MAP_EVERY qexists_tac [`mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order`,
        `cfg`, `dom`, `ef`, `fuel`, `wl`, `aid`] >>
      simp[phase1_fresh]) >>
    metis_tac[])
  >>
  rename [`FLOOKUP _ aid = SOME node'`] >>
  `FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME node'` by (
    match_mp_tac insert_phis_nodes_mono >> simp[phase1_fresh]) >>
  `node = node'` by gvs[] >> gvs[] >>
  match_mp_tac (GEN_ALL process_blocks_node_inst_id) >>
  MAP_EVERY qexists_tac [`order`, `bp`, `addr_sp`, `mem_ssa_init`, `aid`] >>
  simp[mem_ssa_init_def, FLOOKUP_DEF, nodes_fresh_def]
QED

Triviality phase12_ids_valid:
  ∀bp addr_sp fn order cfg dom ef fuel wl.
    mem_ssa_ids_valid
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl)
Proof
  rpt strip_tac >> simp[mem_ssa_ids_valid_def] >>
  conj_tac
  >- (match_mp_tac (GEN_ALL (SIMP_RULE std_ss [AND_IMP_INTRO]
        insert_phis_preserves_ids_valid_du)) >>
      simp[phase1_fresh] >>
      match_mp_tac (GEN_ALL process_blocks_preserves_ids_valid_du) >>
      simp[mem_ssa_init_def, FLOOKUP_DEF])
  >- (match_mp_tac (GEN_ALL (SIMP_RULE std_ss [AND_IMP_INTRO]
        insert_phis_preserves_ids_valid_phis)) >>
      simp[mem_ssa_init_def, FLOOKUP_DEF, process_blocks_fields, phase1_fresh])
QED

Triviality phase12_inst_maps:
  ∀bp addr_sp fn order cfg dom ef fuel wl.
    mem_ssa_inst_maps_consistent
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl)
Proof
  rpt strip_tac >>
  match_mp_tac (GEN_ALL (SIMP_RULE std_ss [AND_IMP_INTRO]
    insert_phis_preserves_inst_maps)) >>
  simp[phase1_fresh] >>
  match_mp_tac (GEN_ALL (SIMP_RULE std_ss [AND_IMP_INTRO]
    process_blocks_preserves_inst_maps)) >>
  simp[mem_ssa_init_def, mem_ssa_inst_maps_consistent_def, nodes_fresh_def,
       FLOOKUP_DEF, FDOM_FEMPTY]
QED

Triviality phase1_ids_valid:
  ∀bp addr_sp fn order.
    mem_ssa_ids_valid
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
Proof
  rpt strip_tac >> simp[mem_ssa_ids_valid_def] >> conj_tac
  >- (match_mp_tac (GEN_ALL process_blocks_preserves_ids_valid_du) >>
      simp[mem_ssa_init_def, FLOOKUP_DEF])
  >- simp[process_blocks_fields, mem_ssa_init_def, FLOOKUP_DEF]
QED

Triviality phase12_phi_ops_valid:
  ∀bp addr_sp fn order cfg dom ef fuel wl phi_id ops rd blk.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_phi_ops phi_id = SOME ops ∧
    MEM (rd, blk) ops ⇒
    rd = 0 ∨ rd ∈ FDOM (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order`,
                    `cfg`, `dom`, `ef`, `fuel`, `wl`]
    insert_phis_preserves_phi_ops_valid) >>
  impl_tac
  >- (simp[phase1_fresh, phase1_ids_valid,
           process_blocks_fields, mem_ssa_init_def, FLOOKUP_DEF])
  >- (disch_then match_mp_tac >> metis_tac[])
QED

Triviality phase12_du_covered:
  ∀bp addr_sp fn order cfg dom ef fuel wl aid node.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃lbl.
      MEM aid (fmap_lookup_list
        (mem_ssa_insert_phis
          (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
          cfg dom ef fuel wl).ms_block_defs lbl) ∨
      MEM aid (fmap_lookup_list
        (mem_ssa_insert_phis
          (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
          cfg dom ef fuel wl).ms_block_uses lbl)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order`,
                    `cfg`, `dom`, `ef`, `fuel`, `wl`]
    insert_phis_preserves_du_covered) >>
  impl_tac
  >- (simp[phase1_fresh] >>
      match_mp_tac process_blocks_du_covered >>
      simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY, FLOOKUP_DEF,
           cfgDefsTheory.fmap_lookup_list_def])
  >- (disch_then match_mp_tac >> metis_tac[])
QED

(* MnDef nodes are always in block_defs at their block label *)
Triviality process_inst_MnDef_in_block_defs:
  !bp addr_sp lbl ms inst.
    nodes_fresh ms /\
    (!aid iid blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list ms.ms_block_defs blk)) ==>
    (!aid iid blk loc.
       FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid =
         SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list
         (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs blk))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[mem_ssa_process_inst_def, LET_THM, FLOOKUP_UPDATE,
      cfgDefsTheory.fmap_lookup_list_def] >> (
    TRY (Cases_on `ms.ms_next_id + 1 = aid` >> gvs[]) >>
    TRY (Cases_on `ms.ms_next_id = aid` >> gvs[]) >> (
      (* New MnDef: witness is lbl *)
      TRY (simp[MEM_SNOC] >> NO_TAC) >>
      (* New MnUse: contradicts MnDef *)
      TRY (fs[nodes_fresh_def] >> res_tac >> gvs[FLOOKUP_DEF] >> NO_TAC) >>
      (* Old node: use IH *)
      first_x_assum drule >> strip_tac >>
      Cases_on `lbl = blk` >> gvs[MEM_SNOC]
    )
  )
QED

Triviality process_block_MnDef_in_block_defs:
  !insts bp addr_sp lbl ms.
    nodes_fresh ms /\
    (!aid iid blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list ms.ms_block_defs blk)) ==>
    (!aid iid blk loc.
       FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid =
         SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list
         (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs blk))
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_MnDef_in_block_defs, process_inst_preserves_fresh]
QED

Triviality process_blocks_MnDef_in_block_defs:
  !lbls bp addr_sp fn ms.
    nodes_fresh ms /\
    (!aid iid blk loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list ms.ms_block_defs blk)) ==>
    (!aid iid blk loc.
       FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid =
         SOME (MnDef iid blk loc) ==>
       MEM aid (fmap_lookup_list
         (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs blk))
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  rpt strip_tac >> (
    TRY (first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`, `ms`] mp_tac) >>
         simp[] >> disch_then drule >> simp[] >> NO_TAC) >>
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >>
    metis_tac[process_block_MnDef_in_block_defs,
              process_block_preserves_fresh]
  )
QED

Triviality phase12_MnDef_in_block_defs:
  !bp addr_sp fn order cfg dom ef fuel wl aid iid blk loc.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME (MnDef iid blk loc) ==>
    MEM aid (fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_defs blk)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM aid (fmap_lookup_list
     (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_block_defs
     blk)` by (
    Cases_on `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_nodes aid`
    >- (metis_tac[insert_phis_only_adds_phi, phase1_fresh,
                  TypeBase.distinct_of ``:mem_ssa_node``])
    >> `FLOOKUP (mem_ssa_insert_phis
           (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
           cfg dom ef fuel wl).ms_nodes aid = SOME x` by
         (match_mp_tac insert_phis_nodes_mono >> simp[phase1_fresh]) >>
       gvs[] >>
       irule (GEN_ALL process_blocks_MnDef_in_block_defs) >>
       simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY, FLOOKUP_DEF,
            cfgDefsTheory.fmap_lookup_list_def]) >>
  gvs[insert_phis_fields]
QED

Triviality phase12_MnDef_block_defs_nonempty:
  !bp addr_sp fn order cfg dom ef fuel wl aid iid blk loc.
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes aid = SOME (MnDef iid blk loc) ==>
    fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_defs blk <> []
Proof
  rpt gen_tac >> strip_tac >>
  drule phase12_MnDef_in_block_defs >> strip_tac >>
  Cases_on `fmap_lookup_list
    (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_block_defs blk` >> gvs[]
QED

Triviality build_MnDef_in_block_defs:
  !cfg dom bp fn addr_sp aid iid blk loc.
    FLOOKUP (mem_ssa_build cfg dom bp fn addr_sp).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    MEM aid (fmap_lookup_list
      (mem_ssa_build cfg dom bp fn addr_sp).ms_block_defs blk)
Proof
  rpt gen_tac >> strip_tac >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  drule phase12_MnDef_in_block_defs >> simp[insert_phis_fields]
QED

(* Reverse direction: nodes in block_defs are MnDef *)
Triviality process_inst_block_defs_are_defs:
  !bp addr_sp lbl ms inst.
    nodes_fresh ms /\
    (!aid lbl'. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) ==>
    (!aid lbl'. MEM aid (fmap_lookup_list
       (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP
         (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes aid =
           SOME (MnDef iid lbl' loc))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM,
       cfgHelpersTheory.fmap_lookup_list_update] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  simp[] >> strip_tac >>
  Cases_on `lbl = lbl'` >>
  gvs[MEM_SNOC, cfgHelpersTheory.fmap_lookup_list_update] >>
  (* New node case: aid = ms.ms_next_id (or +1), trivial *)
  simp[FLOOKUP_UPDATE] >> (
    (* Old node case: use IH then nodes_fresh *)
    first_x_assum drule >> strip_tac >>
    qexistsl_tac [`iid`, `loc`] >>
    sg `aid < ms.ms_next_id`
    >- (gvs[nodes_fresh_def] >> res_tac >> gvs[flookup_thm]) >>
    simp[FLOOKUP_UPDATE])
QED

Triviality process_block_block_defs_are_defs:
  !insts bp addr_sp lbl ms.
    nodes_fresh ms /\
    (!aid lbl'. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) ==>
    (!aid lbl'. MEM aid (fmap_lookup_list
       (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP
         (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid =
           SOME (MnDef iid lbl' loc))
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_block_defs_are_defs, process_inst_preserves_fresh]
QED

Triviality process_blocks_block_defs_are_defs:
  !lbls bp addr_sp fn ms.
    nodes_fresh ms /\
    (!aid lbl'. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) ==>
    (!aid lbl'. MEM aid (fmap_lookup_list
       (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP
         (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid =
           SOME (MnDef iid lbl' loc))
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  rpt strip_tac >> (
    TRY (first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`, `ms`] mp_tac) >>
         simp[] >> disch_then drule >> simp[] >> NO_TAC) >>
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >>
    metis_tac[process_block_block_defs_are_defs,
              process_block_preserves_fresh]
  )
QED

Triviality build_block_defs_are_defs:
  !fn bp addr_sp aid lbl.
    MEM aid (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl) ==>
    ?iid loc. FLOOKUP
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_nodes aid = SOME (MnDef iid lbl loc)
Proof
  rpt gen_tac >> strip_tac >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields, insert_phis_fields] >>
  mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`, `fn`,
    `mem_ssa_init`] process_blocks_block_defs_are_defs) >>
  (impl_tac
   >- simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY, FLOOKUP_DEF,
           cfgDefsTheory.fmap_lookup_list_def]) >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`iid`, `loc`] >>
  match_mp_tac (GEN_ALL insert_phis_nodes_mono) >>
  simp[] >> match_mp_tac process_blocks_preserves_fresh >>
  simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY]
QED

Triviality phase12_block_defs_are_defs:
  !bp addr_sp fn order cfg dom ef fuel wl aid lbl.
    MEM aid (fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_defs lbl) ==>
    ?iid loc. FLOOKUP
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_nodes aid = SOME (MnDef iid lbl loc)
Proof
  rpt gen_tac >> strip_tac >>
  fs[insert_phis_fields] >>
  mp_tac (Q.SPECL [`order`, `bp`, `addr_sp`, `fn`,
    `mem_ssa_init`] process_blocks_block_defs_are_defs) >>
  (impl_tac
   >- simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY, FLOOKUP_DEF,
           cfgDefsTheory.fmap_lookup_list_def]) >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`iid`, `loc`] >>
  match_mp_tac (GEN_ALL insert_phis_nodes_mono) >>
  simp[] >> match_mp_tac process_blocks_preserves_fresh >>
  simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY]
QED

Triviality build_MnDef_block_defs_nonempty:
  !cfg dom bp fn addr_sp aid iid blk loc.
    FLOOKUP (mem_ssa_build cfg dom bp fn addr_sp).ms_nodes aid =
      SOME (MnDef iid blk loc) ==>
    fmap_lookup_list
      (mem_ssa_build cfg dom bp fn addr_sp).ms_block_defs blk <> []
Proof
  rpt gen_tac >> strip_tac >>
  drule build_MnDef_in_block_defs >> strip_tac >>
  Cases_on `fmap_lookup_list
    (mem_ssa_build cfg dom bp fn addr_sp).ms_block_defs blk` >> gvs[]
QED

(* The ms_block_defs field of mem_ssa_build equals that of the phase12 state.
   connect_all and remove_redundant_phis preserve ms_block_defs. *)
Triviality build_block_defs_eq:
  !cfg dom bp fn addr_sp.
    (mem_ssa_build cfg dom bp fn addr_sp).ms_block_defs =
    (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init cfg.cfg_dfs_pre)
      cfg dom (LENGTH (fn_labels fn))
      (LENGTH (fn_labels fn) * LENGTH (fn_labels fn))
      (MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init cfg.cfg_dfs_pre).
          ms_block_defs))).ms_block_defs
Proof
  rpt gen_tac >>
  simp[mem_ssa_build_def, LET_THM,
       remove_redundant_phis_fields, connect_all_fields]
QED

(* Labels with non-empty block_defs/uses are in the processed order *)
Triviality phase12_defs_uses_local:
  ∀bp addr_sp fn order cfg dom ef fuel wl l.
    ¬MEM l order ⇒
    fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_defs l = [] ∧
    fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_uses l = []
Proof
  rpt strip_tac >> simp[insert_phis_fields] >>
  mp_tac (Q.SPECL [`order`, `bp`, `addr_sp`, `fn`, `mem_ssa_init`, `l`]
            process_blocks_defs_uses_local) >>
  simp[mem_ssa_init_def, cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_DEF]
QED

(* block_defs entries are always non-empty (SNOC creates non-empty lists) *)
Triviality process_inst_block_defs_nonempty:
  ∀bp addr_sp lbl ms inst b v.
    (∀k v. FLOOKUP ms.ms_block_defs k = SOME v ⇒ v <> []) ⇒
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs b = SOME v ⇒
    v <> []
Proof
  rpt strip_tac >>
  fs[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[FLOOKUP_UPDATE] >>
  Cases_on `lbl = b` >> gvs[SNOC_APPEND] >>
  res_tac
QED

Triviality process_block_block_defs_nonempty:
  ∀insts bp addr_sp lbl ms b v.
    (∀k v. FLOOKUP ms.ms_block_defs k = SOME v ⇒ v <> []) ⇒
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs b = SOME v ⇒
    v <> []
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  `∀k v'. FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms h).ms_block_defs k =
          SOME v' ⇒ v' <> []` by metis_tac[process_inst_block_defs_nonempty] >>
  metis_tac[]
QED

Triviality process_blocks_block_defs_nonempty:
  ∀lbls bp addr_sp fn ms b v.
    (∀k v. FLOOKUP ms.ms_block_defs k = SOME v ⇒ v <> []) ⇒
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs b = SOME v ⇒
    v <> []
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >> CASE_TAC >> strip_tac >> first_x_assum match_mp_tac >>
  TRY (first_x_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  metis_tac[process_block_block_defs_nonempty]
QED

(* block_defs monotonicity: process_inst only adds to block_defs[lbl] via SNOC *)
Triviality process_inst_block_defs_mono:
  ∀bp addr_sp lbl ms inst did.
    MEM did (fmap_lookup_list ms.ms_block_defs lbl) ⇒
    MEM did (fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs lbl)
Proof
  rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM,
       cfgDefsTheory.fmap_lookup_list_def] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  simp[FLOOKUP_UPDATE, MEM_SNOC] >>
  Cases_on `FLOOKUP ms.ms_block_defs lbl` >> simp[MEM_SNOC]
QED

Triviality process_block_block_defs_mono:
  ∀insts bp addr_sp lbl ms did.
    MEM did (fmap_lookup_list ms.ms_block_defs lbl) ⇒
    MEM did (fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs lbl)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac process_inst_block_defs_mono >> simp[]
QED

(* block_defs ALL_DISTINCT: nodes_fresh implies distinct block_defs entries *)
Triviality process_inst_block_defs_all_distinct:
  !bp addr_sp lbl ms inst.
    nodes_fresh ms /\
    ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs lbl) /\
    (!aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ==>
       aid IN FDOM ms.ms_nodes) ==>
    ALL_DISTINCT (fmap_lookup_list
      (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs lbl) /\
    (!aid. MEM aid (fmap_lookup_list
      (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs lbl) ==>
       aid IN FDOM (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes)
Proof
  rpt gen_tac >> strip_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  simp[cfgHelpersTheory.fmap_lookup_list_update,
       ALL_DISTINCT_SNOC, MEM_SNOC, FDOM_FUPDATE] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  TRY (fs[nodes_fresh_def] >> res_tac >> res_tac >> DECIDE_TAC)
QED

Triviality process_block_block_defs_all_distinct:
  !insts bp addr_sp lbl ms.
    nodes_fresh ms /\
    ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs lbl) /\
    (!aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ==>
       aid IN FDOM ms.ms_nodes) ==>
    ALL_DISTINCT (fmap_lookup_list
      (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs lbl)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_block_defs_all_distinct,
            process_inst_preserves_fresh]
QED

(* Strengthened version: ALL_DISTINCT + FDOM membership for all labels *)
Triviality process_block_block_defs_all_distinct_strong:
  !insts bp addr_sp lbl ms.
    nodes_fresh ms /\
    (!l. ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list ms.ms_block_defs l) ==>
       aid IN FDOM ms.ms_nodes) ==>
    (!l. ALL_DISTINCT (fmap_lookup_list
      (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list
      (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs l) ==>
       aid IN FDOM (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`] mp_tac) >>
  impl_tac >> rpt conj_tac
  >- metis_tac[process_inst_preserves_fresh]
  >- (rpt strip_tac >> Cases_on `l = lbl`
      >- metis_tac[process_inst_block_defs_all_distinct]
      >> simp[process_inst_defs_uses_local])
  >- (rpt strip_tac >> Cases_on `l = lbl`
      >- metis_tac[process_inst_block_defs_all_distinct]
      >> gvs[process_inst_defs_uses_local] >>
         res_tac >> metis_tac[process_inst_preserves_node, flookup_thm])
  >> simp[]
QED

Triviality process_blocks_block_defs_all_distinct:
  !lbls bp addr_sp fn ms lbl.
    nodes_fresh ms /\
    (!l. ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list ms.ms_block_defs l) ==>
       aid IN FDOM ms.ms_nodes) ==>
    ALL_DISTINCT (fmap_lookup_list
      (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  TRY (simp[]) >>
  metis_tac[process_block_block_defs_all_distinct_strong,
            process_block_preserves_fresh]
QED

Triviality build_block_defs_all_distinct:
  !fn bp addr_sp lbl.
    ALL_DISTINCT (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl)
Proof
  rpt gen_tac >>
  simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
       connect_all_fields, insert_phis_fields] >>
  match_mp_tac process_blocks_block_defs_all_distinct >>
  simp[mem_ssa_init_def, cfgDefsTheory.fmap_lookup_list_def,
       FLOOKUP_DEF, nodes_fresh_def, FDOM_FEMPTY]
QED

(* block_defs inst_ids form a sublist of instruction inst_ids.
   Key property: process_block processes instructions left-to-right,
   SNOCing def node IDs for instructions that write memory. *)
Triviality process_block_block_defs_iids_sublist:
  !insts bp addr_sp lbl ms.
    nodes_fresh ms ==>
    sublist
      (MAP (\aid. mn_inst_id (THE (FLOOKUP
         (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid)))
           (fmap_lookup_list
         (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs lbl))
      (MAP (\aid. mn_inst_id (THE (FLOOKUP
         (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes aid)))
           (fmap_lookup_list ms.ms_block_defs lbl) ++
       MAP (\i. i.inst_id) insts)
Proof
  Induct >>
  simp[mem_ssa_process_block_def, rich_listTheory.sublist_refl] >>
  rpt strip_tac >>
  (* Step case: process_block(process_inst(ms, h), insts) *)
  (* Case split on whether h writes memory *)
  Cases_on `bp_get_write_location bp h addr_sp = ml_empty` >-
  (
    (* Case A: no write. block_defs unchanged by process_inst *)
    (* IH on process_block(ms1, insts) where ms1.block_defs(lbl) = ms.block_defs(lbl) *)
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
      `mem_ssa_process_inst bp addr_sp lbl ms h`] mp_tac) >>
    impl_tac >- metis_tac[process_inst_preserves_fresh] >>
    (* IH conclusion: sublist (MAP f ms'.bd) (MAP f ms1.bd ++ MAP iid insts) *)
    (* ms1.bd(lbl) = ms.bd(lbl) since no write *)
    strip_tac >>
    (* Need: sublist (MAP f ms'.bd) (MAP f ms.bd ++ h.iid :: MAP iid insts) *)
    (* From IH: sublist (MAP f ms'.bd) (MAP f ms1.bd ++ MAP iid insts) *)
    (* ms1.bd(lbl) = ms.bd(lbl) → sublist (MAP f ms'.bd) (MAP f ms.bd ++ MAP iid insts) *)
    (* Then insertion: sublist X (A ++ B) ⇒ sublist X (A ++ c::B) *)
    match_mp_tac (GEN_ALL rich_listTheory.sublist_trans) >>
    qexists_tac `MAP
      (\aid. mn_inst_id (THE (FLOOKUP
        (mem_ssa_process_block bp addr_sp lbl
          (mem_ssa_process_inst bp addr_sp lbl ms h) insts).ms_nodes aid)))
      (fmap_lookup_list
        (mem_ssa_process_inst bp addr_sp lbl ms h).ms_block_defs lbl) ++
      MAP (\i. i.inst_id) insts` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    (* Now need: sublist (MAP f ms1.bd ++ MAP iid insts) (MAP f ms.bd ++ h.iid :: MAP iid insts) *)
    (* ms1.bd(lbl) = ms.bd(lbl) since no write at lbl *)
    sg `fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms h).ms_block_defs lbl =
        fmap_lookup_list ms.ms_block_defs lbl` >-
    (
      simp[mem_ssa_process_inst_def, LET_THM, cfgDefsTheory.fmap_lookup_list_def] >>
      Cases_on `bp_get_read_location bp h addr_sp = ml_empty` >>
      simp[FLOOKUP_UPDATE]
    ) >>
    simp[] >>
    (* sublist (MAP f ms.bd ++ MAP iid insts) (MAP f ms.bd ++ h.iid :: MAP iid insts) *)
    ONCE_REWRITE_TAC [GSYM rich_listTheory.sublist_prefix] >>
    match_mp_tac rich_listTheory.sublist_cons_include >>
    simp[rich_listTheory.sublist_refl]
  ) >>
  (* Case B: write. block_defs gets SNOC'd *)
  (* First establish what process_inst does to block_defs and nodes *)
  sg `?did wloc.
    fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms h).ms_block_defs lbl =
      SNOC did (fmap_lookup_list ms.ms_block_defs lbl) /\
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms h).ms_nodes did =
      SOME (MnDef h.inst_id lbl wloc)` >-
  (
    simp[mem_ssa_process_inst_def, LET_THM, cfgDefsTheory.fmap_lookup_list_def] >>
    Cases_on `bp_get_read_location bp h addr_sp = ml_empty` >>
    simp[FLOOKUP_UPDATE] >>
    Cases_on `FLOOKUP ms.ms_block_defs lbl` >> simp[]
  ) >>
  (* Establish that FLOOKUP is preserved through the remaining process_block *)
  sg `FLOOKUP (mem_ssa_process_block bp addr_sp lbl
    (mem_ssa_process_inst bp addr_sp lbl ms h) insts).ms_nodes did =
    SOME (MnDef h.inst_id lbl wloc)` >-
  (
    match_mp_tac process_block_preserves_node >>
    metis_tac[process_inst_preserves_fresh]
  ) >>
  (* Establish MAP equality: MAP f ms1.bd = MAP f ms.bd ++ [h.inst_id] *)
  (* where f = \aid. mn_inst_id(THE(FLOOKUP ms'.nodes aid)) *)
  qabbrev_tac `ms' = mem_ssa_process_block bp addr_sp lbl
    (mem_ssa_process_inst bp addr_sp lbl ms h) insts` >>
  sg `MAP (\aid. mn_inst_id (THE (FLOOKUP ms'.ms_nodes aid)))
        (fmap_lookup_list
          (mem_ssa_process_inst bp addr_sp lbl ms h).ms_block_defs lbl) =
      MAP (\aid. mn_inst_id (THE (FLOOKUP ms'.ms_nodes aid)))
        (fmap_lookup_list ms.ms_block_defs lbl) ++ [h.inst_id]` >-
  (
    qpat_x_assum `fmap_lookup_list _ _ = SNOC _ _` (fn th => REWRITE_TAC [th]) >>
    simp[MAP_SNOC, SNOC_APPEND, mn_inst_id_def]
  ) >>
  (* Now apply IH *)
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`] mp_tac) >>
  impl_tac >- metis_tac[process_inst_preserves_fresh] >>
  (* IH gives: sublist (MAP f ms'.bd) (MAP f ms1.bd ++ MAP iid insts) *)
  (* Substitute MAP f ms1.bd = MAP f ms.bd ++ [h.inst_id] *)
  simp[Abbr `ms'`] >>
  (* Goal becomes: sublist X (MAP f ms.bd ++ [h.iid] ++ MAP iid insts) *)
  (* = sublist X (MAP f ms.bd ++ h.iid :: MAP iid insts) = target *)
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

(* Lift to process_blocks: block_defs inst_ids are sublist of instruction inst_ids.
   Requires: ALL_DISTINCT lbls, lbl in lbls, empty initial block_defs. *)
Triviality sublist_MAP_eq:
  !(f:'a -> 'b) g l r.
    (!x. MEM x l ==> f x = g x) /\ sublist (MAP g l) r ==>
    sublist (MAP f l) r
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  sg `f h = g h` >- simp[] >>
  sg `MAP f l = MAP g l` >- (match_mp_tac MAP_CONG >> simp[]) >>
  gvs[rich_listTheory.sublist_def]
QED

(* Helper for h=lbl case of process_blocks_block_defs_iids_sublist *)
Triviality process_blocks_block_defs_iids_sublist_base:
  !lbls bp addr_sp fn ms bb h.
    nodes_fresh ms /\
    ~MEM h lbls /\
    lookup_block h fn.fn_blocks = SOME bb /\
    fmap_lookup_list ms.ms_block_defs h = [] /\
    (!l. ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list ms.ms_block_defs l) ==>
       aid IN FDOM ms.ms_nodes) ==>
    sublist
      (MAP (\aid. mn_inst_id (THE (FLOOKUP
         (mem_ssa_process_blocks bp addr_sp fn
           (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_nodes aid)))
           (fmap_lookup_list
         (mem_ssa_process_blocks bp addr_sp fn
           (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_block_defs h))
      (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  (* block_defs for h preserved through process_blocks since ~MEM h lbls *)
  sg `fmap_lookup_list
    (mem_ssa_process_blocks bp addr_sp fn
      (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_block_defs h =
    fmap_lookup_list
      (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_block_defs h` >-
  (
    mp_tac (Q.SPECL [`lbls`, `bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms bb.bb_instructions`, `h`]
      process_blocks_defs_uses_local) >>
    simp[]
  ) >>
  simp[] >>
  match_mp_tac sublist_MAP_eq >>
  qexists_tac `\aid. mn_inst_id (THE (FLOOKUP
    (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_nodes aid))` >>
  reverse conj_tac >- (
    (* Sublist conjunct (was second, now first after reverse) *)
    mp_tac (Q.SPECL [`bb.bb_instructions`, `bp`, `addr_sp`, `h`, `ms`]
      process_block_block_defs_iids_sublist) >>
    simp[]
  ) >>
  (* Equality conjunct *)
  BETA_TAC >> rpt strip_tac >>
  sg `x IN FDOM (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_nodes` >-
  (
    mp_tac (Q.SPECL [`bb.bb_instructions`, `bp`, `addr_sp`, `h`, `ms`]
      process_block_block_defs_all_distinct_strong) >>
    simp[] >> strip_tac >> res_tac
  ) >>
  sg `?nd. FLOOKUP (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_nodes x = SOME nd` >-
    metis_tac[flookup_thm] >>
  sg `nodes_fresh (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions)` >-
  (match_mp_tac process_block_preserves_fresh >> simp[]) >>
  mp_tac (Q.SPECL [`lbls`, `bp`, `addr_sp`, `fn`,
    `mem_ssa_process_block bp addr_sp h ms bb.bb_instructions`,
    `x`, `nd`] process_blocks_preserves_node) >>
  simp[]
QED

Triviality process_blocks_block_defs_iids_sublist:
  !lbls bp addr_sp fn ms lbl bb.
    nodes_fresh ms /\
    ALL_DISTINCT lbls /\
    MEM lbl lbls /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    fmap_lookup_list ms.ms_block_defs lbl = [] /\
    (!l. ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list ms.ms_block_defs l) ==>
       aid IN FDOM ms.ms_nodes) ==>
    sublist
      (MAP (\aid. mn_inst_id (THE (FLOOKUP
         (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid)))
           (fmap_lookup_list
         (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl))
      (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >- (
    gvs[] >> match_mp_tac process_blocks_block_defs_iids_sublist_base >>
    simp[] >> metis_tac[]
  ) >>
  sg `lbl <> h` >- (CCONTR_TAC >> gvs[]) >>
  CASE_TAC >> simp[] >>
  first_x_assum match_mp_tac >> simp[] >>
  TRY (metis_tac[process_block_preserves_fresh,
            process_block_defs_uses_local,
            process_block_block_defs_all_distinct_strong])
QED

(* block_defs elements are in FDOM after process_blocks *)
Triviality process_blocks_block_defs_in_fdom:
  !lbls bp addr_sp fn ms lbl aid.
    nodes_fresh ms /\
    (!l. ALL_DISTINCT (fmap_lookup_list ms.ms_block_defs l)) /\
    (!l aid. MEM aid (fmap_lookup_list ms.ms_block_defs l) ==>
       aid IN FDOM ms.ms_nodes) /\
    MEM aid (fmap_lookup_list
      (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl) ==>
    aid IN FDOM (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >- metis_tac[] >>
  rpt gen_tac >> CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  metis_tac[process_block_block_defs_all_distinct_strong,
            process_block_preserves_fresh]
QED

(* Build-level wrapper: block_defs inst_ids form a sublist of bb instruction inst_ids *)
Triviality build_block_defs_iids_sublist:
  !fn bp addr_sp lbl bb.
    wf_function fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    sublist
      (MAP (\aid. mn_inst_id (THE (FLOOKUP
         (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
            bp fn addr_sp).ms_nodes aid)))
           (fmap_lookup_list
         (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
            bp fn addr_sp).ms_block_defs lbl))
      (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[mem_ssa_build_def, LET_THM] >> BETA_TAC >>
  simp[remove_redundant_phis_fields, connect_all_fields,
       insert_phis_fields] >>
  qmatch_goalsub_abbrev_tac `mem_ssa_insert_phis ms_pb _ _ _ _ _` >>
  match_mp_tac sublist_MAP_eq >>
  qexists_tac `\aid. mn_inst_id (THE (FLOOKUP ms_pb.ms_nodes aid))` >>
  reverse conj_tac >- (
    mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`,
      `fn`, `mem_ssa_init`, `lbl`, `bb`]
      process_blocks_block_defs_iids_sublist) >>
    simp[Abbr `ms_pb`, mem_ssa_init_def, cfgDefsTheory.fmap_lookup_list_def,
         FLOOKUP_DEF, nodes_fresh_def, FDOM_FEMPTY,
         cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct]
  ) >>
  BETA_TAC >> rpt strip_tac >>
  sg `x IN FDOM ms_pb.ms_nodes` >- (
    mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`,
      `fn`, `mem_ssa_init`, `lbl`, `x`] process_blocks_block_defs_in_fdom) >>
    simp[Abbr `ms_pb`, mem_ssa_init_def, cfgDefsTheory.fmap_lookup_list_def,
         nodes_fresh_def, FDOM_FEMPTY]
  ) >>
  sg `?nd. FLOOKUP ms_pb.ms_nodes x = SOME nd` >- metis_tac[flookup_thm] >>
  sg `nodes_fresh ms_pb` >- (
    simp[Abbr `ms_pb`] >>
    match_mp_tac process_blocks_preserves_fresh >>
    simp[mem_ssa_init_def, nodes_fresh_def, FDOM_FEMPTY]
  ) >>
  mp_tac (insert_phis_nodes_mono
    |> Q.SPECL [`ms_pb`, `cfg_analyze fn`,
       `dom_analyze (cfg_analyze fn) fn`,
       `LENGTH (fn_labels fn)`,
       `(LENGTH (fn_labels fn)) * (LENGTH (fn_labels fn))`,
       `MAP FST (fmap_to_alist ms_pb.ms_block_defs)`,
       `x`, `nd`]) >>
  simp[]
QED

(* inst_def locality: process_inst only modifies inst_def at the processed inst's id *)
Triviality process_inst_inst_def_local:
  ∀bp addr_sp lbl ms inst iid.
    iid <> inst.inst_id ⇒
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_inst_def iid =
      FLOOKUP ms.ms_inst_def iid
Proof
  rpt strip_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  simp[FLOOKUP_UPDATE] >> DECIDE_TAC
QED

Triviality process_block_inst_def_local:
  ∀insts bp addr_sp lbl ms iid.
    ~MEM iid (MAP (\i. i.inst_id) insts) ⇒
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_inst_def iid =
      FLOOKUP ms.ms_inst_def iid
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `iid`] mp_tac) >>
  simp[process_inst_inst_def_local]
QED

(* process_blocks: inst_def for iid not in block lbl2's instructions is unchanged by processing lbl2 *)
Triviality process_blocks_inst_def_local:
  ∀lbls bp addr_sp fn ms iid.
    (∀lbl bb. MEM lbl lbls ∧ lookup_block lbl fn.fn_blocks = SOME bb ⇒
       ~MEM iid (MAP (\i. i.inst_id) bb.bb_instructions)) ⇒
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_inst_def iid =
      FLOOKUP ms.ms_inst_def iid
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  CASE_TAC >> simp[]
  >- (first_x_assum match_mp_tac >> metis_tac[])
  >> first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`, `iid`] mp_tac) >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  simp[process_block_inst_def_local]
QED

(* lookup_block returns a matching block *)
(* process_inst: new inst_def entries map to block_defs at the processing label *)
(* Comprehensive: any inst_def entry from process_inst is in block_defs OR pre-existing *)
Triviality process_inst_inst_def_block_defs:
  ∀bp addr_sp lbl ms inst iid did.
    FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_inst_def iid = SOME did ⇒
    MEM did (fmap_lookup_list (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_block_defs lbl) ∨
    FLOOKUP ms.ms_inst_def iid = SOME did
Proof
  rpt gen_tac >>
  simp[mem_ssa_process_inst_def, LET_THM] >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  simp[cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_UPDATE, MEM_SNOC] >>
  rpt strip_tac >> Cases_on `inst.inst_id = iid` >> gvs[]
QED

(* Chain to process_block level *)
Triviality process_block_inst_def_block_defs:
  ∀insts bp addr_sp lbl ms iid did.
    FLOOKUP (mem_ssa_process_block bp addr_sp lbl ms insts).ms_inst_def iid = SOME did ⇒
    MEM did (fmap_lookup_list (mem_ssa_process_block bp addr_sp lbl ms insts).ms_block_defs lbl) ∨
    FLOOKUP ms.ms_inst_def iid = SOME did
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `iid`, `did`] mp_tac) >>
  simp[] >> disch_tac >>
  Cases_on `MEM did (fmap_lookup_list
    (mem_ssa_process_block bp addr_sp lbl
       (mem_ssa_process_inst bp addr_sp lbl ms h) insts).ms_block_defs lbl)` >>
  simp[] >>
  `FLOOKUP (mem_ssa_process_inst bp addr_sp lbl ms h).ms_inst_def iid =
   SOME did` by metis_tac[] >>
  (* process_inst gives: in block_defs[lbl] OR pre-existing *)
  drule process_inst_inst_def_block_defs >> strip_tac >> gvs[] >>
  (* If in process_inst's block_defs, then in process_block's too — contradiction *)
  metis_tac[process_block_block_defs_mono]
QED

(* Key lemma: after process_blocks with unique inst_ids,
   inst_def[iid] = SOME did implies did ∈ block_defs[lbl]
   where lbl is the block containing iid *)
Triviality process_blocks_inst_def_block_defs:
  ∀lbls bp addr_sp fn ms lbl bb iid did.
    fn_inst_ids_distinct fn ∧
    ALL_DISTINCT lbls ∧
    MEM lbl lbls ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) ∧
    FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_inst_def iid = SOME did ∧
    FLOOKUP ms.ms_inst_def iid = NONE ⇒
    MEM did (fmap_lookup_list
      (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl)
Proof
  Induct_on `lbls` >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[Once mem_ssa_process_blocks_def] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  Cases_on `lbl = h` >> fs[] >| [
    (* Goal 1: lbl = h, lookup_block h = SOME x *)
    gvs[] >>
    `∀lbl' bb'. MEM lbl' lbls ∧ lookup_block lbl' fn.fn_blocks = SOME bb' ⇒
       ~MEM iid (MAP (\i. i.inst_id) bb'.bb_instructions)` by (
      rpt strip_tac >>
      `bb' = bb` by metis_tac[fn_inst_ids_distinct_unique_block, lookup_block_props] >>
      `bb'.bb_label = lbl'` by metis_tac[lookup_block_props] >>
      `bb.bb_label = h` by metis_tac[lookup_block_props] >>
      gvs[]) >>
    `FLOOKUP (mem_ssa_process_blocks bp addr_sp fn
       (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_inst_def iid =
     FLOOKUP (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_inst_def iid` by (
      match_mp_tac process_blocks_inst_def_local >> simp[] >>
      rpt strip_tac >> res_tac) >>
    `FLOOKUP (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_inst_def iid =
     SOME did` by fs[Once mem_ssa_process_blocks_def] >>
    drule process_block_inst_def_block_defs >> strip_tac >> gvs[] >>
    `fmap_lookup_list
       (mem_ssa_process_blocks bp addr_sp fn
          (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions) lbls).ms_block_defs h =
     fmap_lookup_list
       (mem_ssa_process_block bp addr_sp h ms bb.bb_instructions).ms_block_defs h` by (
      mp_tac (Q.SPECL [`lbls`, `bp`, `addr_sp`, `fn`,
        `mem_ssa_process_block bp addr_sp h ms bb.bb_instructions`, `h`]
        process_blocks_defs_uses_local) >>
      simp[]) >>
    fs[],
    (* Goal 2: lbl ≠ h, lookup_block h = NONE *)
    qpat_x_assum `FLOOKUP (mem_ssa_process_blocks _ _ _ ms (h::_)).ms_inst_def _ = SOME _`
      (mp_tac o SIMP_RULE (srw_ss()) [Once mem_ssa_process_blocks_def]) >>
    simp[] >> strip_tac >>
    first_x_assum irule >> simp[] >> metis_tac[],
    (* Goal 3: lbl ≠ h, lookup_block h = SOME x *)
    rename [`lookup_block h _ = SOME bb_h`] >>
    `~MEM iid (MAP (\i. i.inst_id) bb_h.bb_instructions)` by (
      strip_tac >>
      `bb = bb_h` by metis_tac[fn_inst_ids_distinct_unique_block, lookup_block_props] >>
      `bb.bb_label = lbl` by metis_tac[lookup_block_props] >>
      `bb_h.bb_label = h` by metis_tac[lookup_block_props] >>
      gvs[]) >>
    `FLOOKUP (mem_ssa_process_block bp addr_sp h ms bb_h.bb_instructions).ms_inst_def iid =
     FLOOKUP ms.ms_inst_def iid` by (
      match_mp_tac process_block_inst_def_local >> simp[]) >>
    (* Unfold h::lbls in assumption to match goal *)
    qpat_x_assum `FLOOKUP (mem_ssa_process_blocks _ _ _ ms (h::_)).ms_inst_def _ = SOME _`
      (mp_tac o SIMP_RULE (srw_ss()) [Once mem_ssa_process_blocks_def]) >>
    simp[] >> strip_tac >>
    first_x_assum irule >> simp[] >> metis_tac[]
  ]
QED

(* Phase 1+2 composition: inst_def entries map to block_defs entries *)
Triviality phase12_inst_def_block_defs:
  ∀bp addr_sp fn order cfg dom ef fuel wl lbl bb iid did.
    wf_function fn ∧
    ALL_DISTINCT order ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    MEM iid (MAP (λi. i.inst_id) bb.bb_instructions) ∧
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_inst_def iid = SOME did ⇒
    MEM did (fmap_lookup_list
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl).ms_block_defs lbl)
Proof
  rpt strip_tac >>
  fs[insert_phis_fields] >>
  `fn_inst_ids_distinct fn` by fs[venomWfTheory.wf_function_def] >>
  `FLOOKUP mem_ssa_init.ms_inst_def iid = NONE` by simp[mem_ssa_init_def] >>
  `MEM lbl order` by (
    CCONTR_TAC >> fs[] >>
    mp_tac (Q.SPECL [`order`, `bp`, `addr_sp`, `fn`, `mem_ssa_init`, `iid`]
      process_blocks_inst_def_local) >>
    impl_tac
    >- (rpt strip_tac >>
        spose_not_then assume_tac >> gvs[] >>
        imp_res_tac lookup_block_props >>
        metis_tac[fn_inst_ids_distinct_unique_block]) >>
    simp[mem_ssa_init_def]) >>
  match_mp_tac process_blocks_inst_def_block_defs >>
  qexistsl_tac [`bb`, `iid`] >> simp[]
QED

Triviality phase3_edges_valid:
  ∀ms2 dom fn fuel order.
    mem_ssa_ids_valid ms2 ∧
    mem_ssa_inst_maps_consistent ms2 ∧
    (∀aid rd. FLOOKUP ms2.ms_reaching aid = SOME rd ⇒
       rd = 0 ∨ rd ∈ FDOM ms2.ms_nodes) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms2.ms_phi_ops phi_id = SOME ops ∧ MEM (rd,blk) ops ⇒
       rd = 0 ∨ rd ∈ FDOM ms2.ms_nodes) ⇒
    mem_ssa_edges_valid (mem_ssa_connect_all ms2 dom fn fuel order)
Proof
  rpt strip_tac >>
  simp[mem_ssa_edges_valid_def, connect_all_fields] >>
  conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`order`, `ms2`, `dom`, `fn`, `fuel`]
                connect_all_reaching_valid) >>
      simp[] >> metis_tac[])
  >- metis_tac[]
QED

Triviality phase3_wf:
  ∀ms2 dom fn fuel order.
    mem_ssa_ids_valid ms2 ∧
    mem_ssa_inst_maps_consistent ms2 ∧
    (∀aid rd. FLOOKUP ms2.ms_reaching aid = SOME rd ⇒
       rd = 0 ∨ rd ∈ FDOM ms2.ms_nodes) ∧
    (∀phi_id ops rd blk.
       FLOOKUP ms2.ms_phi_ops phi_id = SOME ops ∧ MEM (rd,blk) ops ⇒
       rd = 0 ∨ rd ∈ FDOM ms2.ms_nodes) ∧
    (∀aid node. FLOOKUP ms2.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
       (∃lbl. MEM lbl order ∧
         (MEM aid (fmap_lookup_list ms2.ms_block_defs lbl) ∨
          MEM aid (fmap_lookup_list ms2.ms_block_uses lbl)))) ⇒
    wf_mssa (mem_ssa_connect_all ms2 dom fn fuel order)
Proof
  rpt strip_tac >>
  simp[wf_mem_ssa_def] >> rpt conj_tac
  >- metis_tac[connect_all_preserves_ids_valid]
  >- metis_tac[phase3_edges_valid]
  >- metis_tac[connect_all_preserves_inst_maps]
  >- (match_mp_tac connect_all_reaching_complete >>
      rpt strip_tac >> DISJ1_TAC >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexists_tac `lbl` >> simp[])
QED

Theorem mem_ssa_build_wf:
  ∀cfg dom bp fn addr_sp.
    wf_function fn ⇒
    wf_mssa (mem_ssa_build cfg dom bp fn addr_sp)
Proof
  rpt strip_tac >>
  simp[mem_ssa_build_def, LET_THM] >>
  match_mp_tac remove_phis_preserves_wf >>
  qmatch_goalsub_abbrev_tac `wf_mssa (mem_ssa_connect_all ms2 _ _ _ _)` >>
  match_mp_tac phase3_wf >>
  qunabbrev_tac `ms2` >>
  simp[phase12_ids_valid, phase12_inst_maps] >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[insert_phis_fields, process_blocks_fields, mem_ssa_init_def])
  >- metis_tac[phase12_phi_ops_valid]
  >- (rpt strip_tac >>
      drule phase12_du_covered >> simp[] >> strip_tac >>
      qexists_tac `lbl` >> simp[insert_phis_fields] >>
      CCONTR_TAC >> gvs[] >>
      imp_res_tac phase12_defs_uses_local >> gvs[])
QED

(* ==========================================================================
   Property 2: Reaching def validity and completeness
   ========================================================================== *)

Theorem mem_ssa_reaching_def_exists_and_valid:
  ∀cfg dom bp fn addr_sp ms aid node.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    ∃rd. FLOOKUP ms.ms_reaching aid = SOME rd ∧
         (rd = 0 ∨ rd ∈ FDOM ms.ms_nodes)
Proof
  rpt strip_tac >>
  `wf_mssa ms` by (gvs[] >> irule mem_ssa_build_wf >> simp[]) >>
  gvs[wf_mem_ssa_def, mem_ssa_reaching_complete_def, mem_ssa_edges_valid_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists_tac `rd` >> simp[] >>
  qpat_x_assum `∀aid rd. FLOOKUP _ aid = SOME rd ⇒ _` drule >>
  simp[]
QED

(* ==========================================================================
   Property 3: Reaching def dominates use — Infrastructure
   ========================================================================== *)

(* Block-correctness: nodes referenced by block_defs/uses/phis have the right mn_block *)
Definition block_maps_correct_def:
  block_maps_correct ms ⇔
    (* defs at label lbl have mn_block = lbl *)
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (* uses at label lbl have mn_block = lbl *)
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (* phis at label lbl are MnPhi lbl *)
    (∀lbl phi_id. FLOOKUP ms.ms_block_phis lbl = SOME phi_id ⇒
       FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi lbl))
End

(* --- Phase 1 chain for defs/uses parts of block_maps_correct --- *)

Triviality process_inst_block_maps_du:
  ∀bp addr_sp blk_lbl ms inst.
    nodes_fresh ms ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ⇒
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_inst bp addr_sp blk_lbl ms inst).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_inst bp addr_sp blk_lbl ms inst).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_inst bp addr_sp blk_lbl ms inst).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_inst bp addr_sp blk_lbl ms inst).ms_nodes aid = SOME node ∧
              mn_block node = lbl)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `bp_get_read_location bp inst addr_sp = ml_empty` >>
  Cases_on `bp_get_write_location bp inst addr_sp = ml_empty` >>
  gvs[mem_ssa_process_inst_def, LET_THM, FLOOKUP_UPDATE,
      cfgDefsTheory.fmap_lookup_list_def] >> (
    (* Split on whether lbl = blk_lbl and whether aid is new *)
    TRY (Cases_on `blk_lbl = lbl` >> gvs[MEM_SNOC]) >>
    TRY (Cases_on `ms.ms_next_id + 1 = aid` >> gvs[mn_block_def]) >>
    TRY (Cases_on `ms.ms_next_id = aid` >> gvs[mn_block_def]) >>
    (* Old node at different label: use IH + freshness for FLOOKUP_UPDATE *)
    TRY (res_tac >> gvs[] >>
         `aid < ms.ms_next_id` by (fs[nodes_fresh_def, FLOOKUP_DEF] >> res_tac) >>
         simp[] >> NO_TAC) >>
    (* Fresh id in old block_defs/uses → contradiction via IH + nodes_fresh *)
    first_x_assum drule >> strip_tac >>
    fs[nodes_fresh_def, FLOOKUP_DEF] >> res_tac >> gvs[]
  )
QED

Triviality process_block_block_maps_du:
  ∀insts bp addr_sp blk_lbl ms.
    nodes_fresh ms ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ⇒
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_block bp addr_sp blk_lbl ms insts).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_block bp addr_sp blk_lbl ms insts).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_block bp addr_sp blk_lbl ms insts).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_block bp addr_sp blk_lbl ms insts).ms_nodes aid = SOME node ∧
              mn_block node = lbl)
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_inst_block_maps_du, process_inst_preserves_fresh]
QED

Triviality process_blocks_block_maps_du:
  ∀lbls bp addr_sp fn ms.
    nodes_fresh ms ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ⇒
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes aid = SOME node ∧
              mn_block node = lbl)
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  rpt strip_tac >> (
    (* NONE case: skip label, pass ms directly *)
    TRY (first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`, `ms`] mp_tac) >>
         simp[] >> NO_TAC) >>
    (* SOME case: process_block then process_blocks *)
    first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
      `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >>
    metis_tac[process_block_block_maps_du, process_block_preserves_fresh]
  )
QED

(* Phase 2 preserves defs/uses parts (block_defs/uses unchanged, nodes only grow) *)
Triviality insert_phis_preserves_block_maps_du:
  ∀ms cfg dom ef fuel wl.
    nodes_fresh ms ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ mn_block node = lbl) ⇒
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
    (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
              mn_block node = lbl)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[insert_phis_fields] >>
  res_tac >>
  `FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes aid = SOME node`
    by (match_mp_tac insert_phis_nodes_mono >> simp[FLOOKUP_DEF]) >>
  metis_tac[]
QED

(* Phase 2 establishes phis part *)
Triviality insert_phi_at_block_phis_correct:
  ∀ms cfg dom fuel lbl ms' inserted.
    nodes_fresh ms ∧
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
       FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi l)) ∧
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ⇒
    (∀l phi_id. FLOOKUP ms'.ms_block_phis l = SOME phi_id ⇒
       FLOOKUP ms'.ms_nodes phi_id = SOME (MnPhi l))
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  fs[FLOOKUP_UPDATE] >>
  Cases_on `lbl = l` >> gvs[] >>
  (* old phi: preserved by FUPDATE at a fresh key *)
  res_tac >>
  `phi_id < ms.ms_next_id` by (fs[nodes_fresh_def, FLOOKUP_DEF] >> res_tac) >>
  simp[FLOOKUP_UPDATE]
QED

Triviality process_frontiers_block_phis_correct:
  ∀fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms ∧
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
       FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi l)) ∧
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ⇒
    (∀l phi_id. FLOOKUP ms'.ms_block_phis l = SOME phi_id ⇒
       FLOOKUP ms'.ms_nodes phi_id = SOME (MnPhi l))
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`] >> simp[] >>
  metis_tac[insert_phi_at_block_phis_correct,
            insert_phi_at_preserves_fresh]
QED

Triviality insert_phis_block_phis_correct:
  ∀ms cfg dom ef fuel wl.
    nodes_fresh ms ∧
    (∀l phi_id. FLOOKUP ms.ms_block_phis l = SOME phi_id ⇒
       FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi l)) ⇒
    (∀l phi_id. FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_phis l = SOME phi_id ⇒
       FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes phi_id = SOME (MnPhi l))
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >>
  fs[Once mem_ssa_insert_phis_def] >>
  TRY (res_tac >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `_ = (_,_)` (assume_tac o GSYM) >>
  `nodes_fresh ms'` by (
    match_mp_tac (GEN_ALL process_frontiers_preserves_fresh) >>
    metis_tac[]) >>
  `∀l' phi_id'. FLOOKUP ms'.ms_block_phis l' = SOME phi_id' ⇒
     FLOOKUP ms'.ms_nodes phi_id' = SOME (MnPhi l')` by (
    match_mp_tac (GEN_ALL process_frontiers_block_phis_correct) >>
    metis_tac[]) >>
  res_tac
QED

Triviality phase1_block_maps_correct:
  ∀bp addr_sp fn order.
    block_maps_correct
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
Proof
  rpt strip_tac >> simp[block_maps_correct_def] >>
  `(∀lbl aid. MEM aid (fmap_lookup_list
       (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
   (∀lbl aid. MEM aid (fmap_lookup_list
       (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order).ms_nodes aid = SOME node ∧
              mn_block node = lbl)` by (
    match_mp_tac (GEN_ALL process_blocks_block_maps_du) >>
    simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY,
         cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_DEF]) >>
  simp[process_blocks_fields, mem_ssa_init_def, FLOOKUP_DEF]
QED

(* Phase 1+2 output has block_maps_correct *)
Triviality phase12_block_maps_correct:
  ∀bp addr_sp fn order cfg dom ef fuel wl.
    block_maps_correct
      (mem_ssa_insert_phis
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
        cfg dom ef fuel wl)
Proof
  rpt strip_tac >> simp[block_maps_correct_def] >>
  qabbrev_tac `ms1 = mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order` >>
  `nodes_fresh ms1` by simp[Abbr `ms1`, phase1_fresh] >>
  `(∀lbl aid. MEM aid (fmap_lookup_list ms1.ms_block_defs lbl) ⇒
       ∃node. FLOOKUP ms1.ms_nodes aid = SOME node ∧ mn_block node = lbl) ∧
   (∀lbl aid. MEM aid (fmap_lookup_list ms1.ms_block_uses lbl) ⇒
       ∃node. FLOOKUP ms1.ms_nodes aid = SOME node ∧ mn_block node = lbl)` by (
    simp[Abbr `ms1`] >>
    match_mp_tac (GEN_ALL process_blocks_block_maps_du) >>
    simp[nodes_fresh_def, mem_ssa_init_def, FDOM_FEMPTY,
         cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_DEF]) >>
  `(∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms1 cfg dom ef fuel wl).ms_block_defs lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_insert_phis ms1 cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
              mn_block node = lbl) ∧
   (∀lbl aid. MEM aid (fmap_lookup_list (mem_ssa_insert_phis ms1 cfg dom ef fuel wl).ms_block_uses lbl) ⇒
       ∃node. FLOOKUP (mem_ssa_insert_phis ms1 cfg dom ef fuel wl).ms_nodes aid = SOME node ∧
              mn_block node = lbl)` by (
    match_mp_tac (GEN_ALL insert_phis_preserves_block_maps_du) >> simp[]) >>
  simp[] >>
  simp[Abbr `ms1`] >>
  match_mp_tac (GEN_ALL (SIMP_RULE std_ss [AND_IMP_INTRO]
    insert_phis_block_phis_correct)) >>
  simp[process_blocks_fields, mem_ssa_init_def, FLOOKUP_DEF]
QED

(* Non-phi nodes in phase12 output are at cfg-reachable labels *)
Triviality phase12_non_phi_reachable:
  ∀bp addr_sp fn order cfg dom ef fuel wl a node.
    wf_function fn ∧ order = (cfg_analyze fn).cfg_dfs_pre ∧
    FLOOKUP (mem_ssa_insert_phis
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order)
      cfg dom ef fuel wl).ms_nodes a = SOME node ∧
    (∀blk. node ≠ MnPhi blk) ⇒
    cfg_reachable_of (cfg_analyze fn) (mn_block node)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `order = _` SUBST_ALL_TAC >>
  drule phase12_du_covered >> simp[] >> disch_then (qx_choose_then `lbl` assume_tac) >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (CCONTR_TAC >> imp_res_tac phase12_defs_uses_local >> gvs[]) >>
  assume_tac (Q.SPECL [`bp`, `addr_sp`, `fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `cfg`, `dom`, `ef`, `fuel`, `wl`]
    phase12_block_maps_correct) >>
  fs[block_maps_correct_def] >>
  res_tac >> gvs[mn_block_def] >>
  imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
  gvs[EXTENSION]
QED

(* idom of a reachable label dominates it and is reachable *)
Triviality idom_dominates:
  ∀fn lbl x.
    wf_function fn ∧
    cfg_reachable_of (cfg_analyze fn) lbl ∧
    idom_of (dom_analyze (cfg_analyze fn) fn) lbl = SOME x ⇒
    cfg_reachable_of (cfg_analyze fn) x ∧
    dominates (dom_analyze (cfg_analyze fn) fn) x lbl
Proof
  rpt strip_tac
  >- (
    `strict_dominates (dom_analyze (cfg_analyze fn) fn) x lbl` by (
      mp_tac (Q.SPECL [`fn`, `lbl`, `x`]
        (SIMP_RULE (srw_ss()) [LET_THM] idom_is_immediate)) >> simp[]) >>
    fs[dominatorDefsTheory.strict_dominates_def] >>
    match_mp_tac (SIMP_RULE (srw_ss()) [] dominates_reachable) >>
    qexists_tac `lbl` >> simp[])
  >> mp_tac (Q.SPECL [`fn`, `lbl`, `x`]
       (SIMP_RULE (srw_ss()) [LET_THM] idom_is_immediate)) >>
  simp[dominatorDefsTheory.strict_dominates_def]
QED

(* Simplified dominates_trans: chain two dominance facts *)
Triviality dominates_chain:
  ∀fn a b c.
    wf_function fn ∧
    cfg_reachable_of (cfg_analyze fn) c ∧
    dominates (dom_analyze (cfg_analyze fn) fn) a b ∧
    dominates (dom_analyze (cfg_analyze fn) fn) b c ⇒
    dominates (dom_analyze (cfg_analyze fn) fn) a c
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM, AND_IMP_INTRO,
    GSYM CONJ_ASSOC] dominates_trans) >>
  disch_then (qspecl_then [`fn`, `a`, `b`, `c`] mp_tac) >> simp[]
QED

(* find_prev_def returns a value from ms_inst_def for some instruction in the list *)
Triviality find_prev_def_from_inst_def:
  ∀ms insts target d.
    mem_ssa_find_prev_def ms insts target = SOME d ⇒
    ∃iid. MEM iid (MAP (λi. i.inst_id) insts) ∧
          FLOOKUP ms.ms_inst_def iid = SOME d
Proof
  Induct_on `insts` >> simp[mem_ssa_find_prev_def_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_id = target` >> gvs[] >>
  Cases_on `mem_ssa_find_prev_def ms insts target` >> gvs[]
  >- (
    Cases_on `FLOOKUP ms.ms_inst_def h.inst_id` >> gvs[] >>
    qexists_tac `h.inst_id` >> simp[])
  >> res_tac >> qexists_tac `iid` >> simp[]
QED

(* find_prev_def result is in block_defs and has mn_block = blk_lbl *)
Triviality find_prev_def_in_block:
  ∀ms insts blk_lbl target d.
    block_maps_correct ms ∧
    mem_ssa_find_prev_def ms insts target = SOME d ∧
    (∀iid did. MEM iid (MAP (λi. i.inst_id) insts) ∧
               FLOOKUP ms.ms_inst_def iid = SOME did ⇒
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) ⇒
    d ∈ FDOM ms.ms_nodes ∧
    mn_block (THE (FLOOKUP ms.ms_nodes d)) = blk_lbl
Proof
  rpt strip_tac >>
  drule find_prev_def_from_inst_def >> strip_tac >>
  `MEM d (fmap_lookup_list ms.ms_block_defs blk_lbl)` by metis_tac[] >>
  fs[block_maps_correct_def] >> res_tac >> gvs[] >> fs[flookup_thm]
QED

(* Block defs/phis self-dominance helpers *)
Triviality block_defs_dom_self:
  ∀ms fn lbl d.
    block_maps_correct ms ∧ wf_function fn ∧ MEM lbl (fn_labels fn) ∧
    MEM d (fmap_lookup_list ms.ms_block_defs lbl) ⇒
    d ∈ FDOM ms.ms_nodes ∧
    dominates (dom_analyze (cfg_analyze fn) fn)
              (mn_block (THE (FLOOKUP ms.ms_nodes d))) lbl
Proof
  rpt strip_tac >> fs[block_maps_correct_def] >> res_tac >> gvs[] >>
  fs[flookup_thm] >> match_mp_tac dom_self >> simp[]
QED

Triviality block_phis_dom_self:
  ∀ms fn lbl d.
    block_maps_correct ms ∧ wf_function fn ∧ MEM lbl (fn_labels fn) ∧
    FLOOKUP ms.ms_block_phis lbl = SOME d ⇒
    d ∈ FDOM ms.ms_nodes ∧
    dominates (dom_analyze (cfg_analyze fn) fn)
              (mn_block (THE (FLOOKUP ms.ms_nodes d))) lbl
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ms.ms_nodes d = SOME (MnPhi lbl)` by (
    fs[block_maps_correct_def] >> res_tac >> fs[]) >>
  simp[memSSADefsTheory.mn_block_def] >>
  conj_tac >- fs[flookup_thm] >>
  match_mp_tac dom_self >> simp[]
QED

(* Dom set at idom is a proper subset of dom set at lbl *)
Triviality dom_set_shrinks_at_idom:
  ∀fn cfg lbl d.
    wf_function fn ∧ cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg lbl ∧
    idom_of (dom_analyze cfg fn) lbl = SOME d ⇒
    set (fmap_lookup_list (dom_analyze cfg fn).da_dominators d) ⊂
    set (fmap_lookup_list (dom_analyze cfg fn).da_dominators lbl)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qabbrev_tac `dom = dom_analyze (cfg_analyze fn) fn` >>
  `MEM lbl (fn_labels fn)` by
    metis_tac[cfg_analyze_reachable_in_labels] >>
  imp_res_tac idom_dominates >>
  mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `lbl`] idom_is_immediate) >>
  simp[LET_THM] >> strip_tac >>
  simp[PSUBSET_DEF] >> conj_tac
  >- (
    rw[SUBSET_DEF] >>
    simp[GSYM dominatorDefsTheory.dominates_def] >>
    `dominates dom x d` by fs[dominatorDefsTheory.dominates_def] >>
    `dominates dom d lbl` by
      fs[dominatorDefsTheory.strict_dominates_def] >>
    mp_tac dominates_trans >>
    disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `x`, `d`, `lbl`] mp_tac) >>
    simp[LET_THM])
  >- (
    SPOSE_NOT_THEN ASSUME_TAC >>
    `dominates dom lbl lbl` by
      (simp[Abbr `dom`] >> match_mp_tac dom_self >> simp[]) >>
    `MEM lbl (fmap_lookup_list dom.da_dominators lbl)` by
      fs[dominatorDefsTheory.dominates_def] >>
    `MEM lbl (fmap_lookup_list dom.da_dominators d)` by
      metis_tac[EXTENSION] >>
    `dominates dom lbl d` by fs[dominatorDefsTheory.dominates_def] >>
    `dominates dom d lbl` by fs[dominatorDefsTheory.strict_dominates_def] >>
    `lbl = d` by (
      mp_tac dominates_antisym >>
      disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `lbl`, `d`] mp_tac) >>
      gvs[LET_THM]) >>
    fs[dominatorDefsTheory.strict_dominates_def])
QED

(* CARD of dom set is bounded by LENGTH of fn_labels *)
Triviality dom_set_card_bounded:
  ∀fn cfg lbl.
    wf_function fn ∧ cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    CARD (set (fmap_lookup_list (dom_analyze cfg fn).da_dominators lbl)) ≤
    LENGTH (fn_labels fn)
Proof
  rpt strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  `set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl) ⊆
   set (fn_labels fn)` by (
    rw[SUBSET_DEF] >>
    mp_tac dom_labels_bounded >>
    disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `lbl`, `x`] mp_tac) >>
    simp[LET_THM]) >>
  `CARD (set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)) ≤
   CARD (set (fn_labels fn))` by (
    irule CARD_SUBSET >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  `CARD (set (fn_labels fn)) = LENGTH (fn_labels fn)` by
    simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  DECIDE_TAC
QED

(* If d strictly dominates lbl, then d dominates every predecessor of lbl. *)
Triviality sdom_dominates_preds:
  ∀fn cfg d lbl p.
    wf_function fn ∧ cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg lbl ∧
    strict_dominates (dom_analyze cfg fn) d lbl ∧
    MEM p (cfg_preds_of cfg lbl) ⇒
    dominates (dom_analyze cfg fn) d p
Proof
  rpt gen_tac >> strip_tac >>
  `d <> lbl` by fs[dominatorDefsTheory.strict_dominates_def] >>
  `dominates (dom_analyze cfg fn) d lbl` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  `MEM d (fmap_lookup_list (dom_analyze cfg fn).da_dominators lbl)` by
    fs[dominatorDefsTheory.dominates_def] >>
  `?bb. entry_block fn = SOME bb` by (
    simp[venomInstTheory.entry_block_def] >>
    fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
    Cases_on `fn.fn_blocks` >> gvs[]) >>
  `lbl <> bb.bb_label` by (
    CCONTR_TAC >> gvs[] >>
    mp_tac dom_entry_self >>
    disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `bb`] mp_tac) >>
    simp[] >> strip_tac >>
    fs[dominatorDefsTheory.dominates_def] >>
    `d IN set (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators bb.bb_label)` by
      fs[] >>
    gvs[]) >>
  `cfg_preds_of (cfg_analyze fn) lbl <> []` by (
    CCONTR_TAC >> gvs[] >>
    `MEM p []` by metis_tac[] >> gvs[]) >>
  mp_tac dom_fixpoint_equation >>
  disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `bb`, `lbl`] mp_tac) >>
  simp[LET_THM] >> (impl_tac >- gvs[]) >> strip_tac >>
  `d IN set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)` by
    gvs[] >>
  `d IN BIGINTER (IMAGE (\p'. set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p'))
      (set (cfg_preds_of (cfg_analyze fn) lbl)))` by (
    qpat_x_assum `set _ = _` (fn eq => fs[eq]) >>
    fs[]) >>
  fs[IN_BIGINTER, IN_IMAGE] >>
  first_x_assum (qspec_then `set (fmap_lookup_list
    (dom_analyze (cfg_analyze fn) fn).da_dominators p)` mp_tac) >>
  impl_tac >- (qexists_tac `p` >> gvs[]) >>
  simp[dominatorDefsTheory.dominates_def]
QED

(* Helper: get_exit_def ≠ 0 with CARD-based fuel bound.
   The actual theorem (below) derives this from fuel ≥ LENGTH. *)
Triviality get_exit_def_nonzero_aux:
  ∀n ms fn fuel lbl c.
    n = CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)) ∧
    wf_function fn ∧
    mem_ssa_ids_valid ms ∧ 0 ∉ FDOM ms.ms_nodes ∧
    cfg_reachable_of (cfg_analyze fn) lbl ∧
    dominates (dom_analyze (cfg_analyze fn) fn) c lbl ∧
    fuel ≥ n ∧
    (fmap_lookup_list ms.ms_block_defs c ≠ [] ∨
     c ∈ FDOM ms.ms_block_phis) ⇒
    mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel lbl ≠ 0
Proof
  completeInduct_on `n` >>
  rpt gen_tac >> disch_tac >> fs[] >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  qabbrev_tac `dom = dom_analyze (cfg_analyze fn) fn` >>
  `dominates dom lbl lbl` by
    (simp[Abbr `dom`] >> match_mp_tac dom_self >> simp[]) >>
  `MEM lbl (fmap_lookup_list dom.da_dominators lbl)` by
    fs[dominatorDefsTheory.dominates_def] >>
  `0 < n` by
    (`set (fmap_lookup_list dom.da_dominators lbl) <> {}` by
       (simp[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
     `CARD (set (fmap_lookup_list dom.da_dominators lbl)) <> 0` by
       simp[CARD_EQ_0, FINITE_LIST_TO_SET] >>
     DECIDE_TAC) >>
  `fuel <> 0` by DECIDE_TAC >>
  Cases_on `fuel` >> fs[] >>
  simp[mem_ssa_get_exit_def_def, LET_THM] >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl <> []` >> simp[]
  >- (
    `LAST (fmap_lookup_list ms.ms_block_defs lbl) ∈ FDOM ms.ms_nodes` by (
      fs[mem_ssa_ids_valid_def, cfgDefsTheory.fmap_lookup_list_def] >>
      CASE_TAC >> gvs[] >>
      first_x_assum (qspecl_then [`lbl`, `x`, `LAST x`] mp_tac) >>
      simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
    metis_tac[])
  >> Cases_on `FLOOKUP ms.ms_block_phis lbl` >> simp[]
  >- (
    `c <> lbl` by (
      CCONTR_TAC >> gvs[] >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
    `?bb. entry_block fn = SOME bb` by (
      simp[venomInstTheory.entry_block_def] >>
      fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
      Cases_on `fn.fn_blocks` >> gvs[]) >>
    `lbl <> bb.bb_label` by (
      CCONTR_TAC >> gvs[] >>
      mp_tac dom_entry_self >>
      disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `bb`] mp_tac) >>
      simp[] >> strip_tac >>
      fs[dominatorDefsTheory.dominates_def] >>
      `c ∈ set (fmap_lookup_list dom.da_dominators bb.bb_label)` by fs[] >>
      gvs[]) >>
    `?d. idom_of dom lbl = SOME d` by
      (simp[Abbr `dom`] >> irule idom_exists >> simp[]) >>
    simp[] >>
    `cfg_reachable_of (cfg_analyze fn) d ∧ dominates dom d lbl` by (
      mp_tac idom_dominates >>
      disch_then (qspecl_then [`fn`, `lbl`, `d`] mp_tac) >>
      simp[Abbr `dom`]) >>
    `strict_dominates dom c lbl` by
      fs[dominatorDefsTheory.strict_dominates_def] >>
    `dominates dom c d` by (
      Cases_on `c = d`
      >- (simp[Abbr `dom`] >> match_mp_tac dom_self >>
          simp[] >> metis_tac[cfg_analyze_reachable_in_labels])
      >> mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `lbl`] idom_is_immediate) >>
      simp[Abbr `dom`, LET_THM] >> strip_tac >>
      first_x_assum match_mp_tac >>
      fs[dominatorDefsTheory.strict_dominates_def]) >>
    `set (fmap_lookup_list dom.da_dominators d) ⊂
     set (fmap_lookup_list dom.da_dominators lbl)` by
      (simp[Abbr `dom`] >> irule dom_set_shrinks_at_idom >> simp[]) >>
    `CARD (set (fmap_lookup_list dom.da_dominators d)) <
     CARD (set (fmap_lookup_list dom.da_dominators lbl))` by
      (irule CARD_PSUBSET >> simp[FINITE_LIST_TO_SET]) >>
    qpat_x_assum `!m. m < _ ==> _`
      (qspec_then `CARD (set (fmap_lookup_list dom.da_dominators d))` mp_tac) >>
    simp[Abbr `dom`] >>
    disch_then (qspecl_then [`ms`, `fn`, `n'`, `d`, `c`] mp_tac) >>
    impl_tac >- (simp[] >> DECIDE_TAC) >>
    simp[])
  >- (
    qpat_x_assum `!m. _` kall_tac >>
    `x ∈ FDOM ms.ms_nodes` by (
      fs[mem_ssa_ids_valid_def] >> res_tac) >>
    metis_tac[])
QED

(* If an ancestor block has defs/phi, get_exit_def returns nonzero. *)
Triviality get_exit_def_nonzero:
  ∀ms dom fn fuel lbl c cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    mem_ssa_ids_valid ms ∧ 0 ∉ FDOM ms.ms_nodes ∧
    cfg_reachable_of cfg lbl ∧
    dominates dom c lbl ∧
    fuel ≥ LENGTH (fn_labels fn) ∧
    (fmap_lookup_list ms.ms_block_defs c ≠ [] ∨
     c ∈ FDOM ms.ms_block_phis) ⇒
    mem_ssa_get_exit_def ms dom fuel lbl ≠ 0
Proof
  rpt gen_tac >> disch_tac >> fs[] >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  irule get_exit_def_nonzero_aux >>
  simp[] >>
  conj_tac
  >- (`MEM lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
      `CARD (set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)) ≤
       LENGTH (fn_labels fn)` by
        (mp_tac dom_set_card_bounded >>
         disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `lbl`] mp_tac) >>
         simp[]) >>
      DECIDE_TAC)
  >> qexists_tac `c` >> simp[]
QED

(* get_exit_def returns a phi only at blocks with empty block_defs.
   Requires block_defs entries are all MnDef (true of build output). *)
Triviality get_exit_def_phi_has_no_defs:
  !fuel ms dom lbl blk.
    block_maps_correct ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_get_exit_def ms dom fuel lbl <> 0 /\
    FLOOKUP ms.ms_nodes (mem_ssa_get_exit_def ms dom fuel lbl) =
      SOME (MnPhi blk) ==>
    fmap_lookup_list ms.ms_block_defs blk = []
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_ssa_get_exit_def_def]
  >> fs[mem_ssa_get_exit_def_def, LET_THM] >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl <> []` >> fs[]
  >- (
    `MEM (LAST (fmap_lookup_list ms.ms_block_defs lbl))
         (fmap_lookup_list ms.ms_block_defs lbl)` by
      metis_tac[MEM_LAST_NOT_NIL] >>
    first_x_assum drule >> strip_tac >> gvs[]) >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >> fs[]
  >- (
    Cases_on `idom_of dom lbl` >> fs[] >>
    first_x_assum (qspecl_then [`ms`, `dom`, `x`] mp_tac) >>
    simp[]) >>
  `FLOOKUP ms.ms_nodes x = SOME (MnPhi lbl)` by
    fs[block_maps_correct_def] >>
  gvs[]
QED

(* get_exit_def: if result is non-phi at block B with block_defs(B) <> [],
   then result = LAST(block_defs(B)). *)
Triviality get_exit_def_nonphi_is_last:
  !fuel ms dom lbl r rnode.
    block_maps_correct ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_get_exit_def ms dom fuel lbl = r /\
    r <> 0 /\
    FLOOKUP ms.ms_nodes r = SOME rnode /\
    (!b. rnode <> MnPhi b) /\
    fmap_lookup_list ms.ms_block_defs (mn_block rnode) <> [] ==>
    r = LAST (fmap_lookup_list ms.ms_block_defs (mn_block rnode))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_ssa_get_exit_def_def] >>
  fs[mem_ssa_get_exit_def_def, LET_THM] >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl <> []` >> fs[]
  >- (
    (* block_defs(lbl) <> []: r = LAST(block_defs(lbl)).
       By block_maps_correct, LAST is at lbl, so mn_block rnode = lbl. *)
    `MEM r (fmap_lookup_list ms.ms_block_defs lbl)` by
      metis_tac[MEM_LAST_NOT_NIL] >>
    first_x_assum (qspecl_then [`lbl`, `r`] mp_tac) >>
    simp[] >> strip_tac >> gvs[mn_block_def]) >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >> fs[]
  >- (
    Cases_on `idom_of dom lbl` >> fs[] >>
    first_x_assum (qspecl_then [`ms`, `dom`, `x`] mp_tac) >>
    simp[]) >>
  (* phi case: r = x (phi_id), but rnode is non-phi — contradiction *)
  `FLOOKUP ms.ms_nodes x = SOME (MnPhi lbl)` by
    fs[block_maps_correct_def] >>
  gvs[]
QED

(* get_exit_def returns 0 or a node that dominates lbl *)
Triviality get_exit_def_dominates:
  ∀ms dom fn fuel lbl d cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    block_maps_correct ms ∧
    cfg_reachable_of cfg lbl ∧
    mem_ssa_get_exit_def ms dom fuel lbl = d ∧ d ≠ 0 ⇒
    d ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes d))) lbl
Proof
  Induct_on `fuel` >> rpt gen_tac >> disch_tac
  >- (fs[mem_ssa_get_exit_def_def])
  >> fs[mem_ssa_get_exit_def_def, LET_THM] >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  qpat_x_assum `dom = _` (SUBST_ALL_TAC) >>
  qpat_x_assum `cfg = _` (SUBST_ALL_TAC) >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl <> []` >> fs[]
  >- (
    `MEM d (fmap_lookup_list ms.ms_block_defs lbl)` by
      metis_tac[MEM_LAST_NOT_NIL] >>
    metis_tac[block_defs_dom_self])
  >> Cases_on `FLOOKUP ms.ms_block_phis lbl` >> fs[]
  >- (
    Cases_on `idom_of (dom_analyze (cfg_analyze fn) fn) lbl` >> fs[] >>
    drule_all idom_dominates >> strip_tac >>
    last_x_assum (qspecl_then [`ms`, `fn`, `x`] mp_tac) >>
    simp[] >> strip_tac >>
    match_mp_tac dominates_chain >> qexists_tac `x` >> simp[])
  >> gvs[] >> metis_tac[block_phis_dom_self]
QED

(* If c strictly dominates lbl and idom(lbl) = d, then c dominates d.
   This follows from the definition of immediate dominator. *)
Triviality sdom_dom_idom:
  !fn lbl c d.
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) c lbl /\
    idom_of (dom_analyze (cfg_analyze fn) fn) lbl = SOME d ==>
    dominates (dom_analyze (cfg_analyze fn) fn) c d
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] idom_is_immediate) >>
  disch_then (qspecl_then [`fn`, `lbl`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `c = d`
  >- metis_tac[SIMP_RULE (srw_ss()) [] dom_self,
               cfg_analyze_reachable_in_labels,
               SIMP_RULE (srw_ss()) [] dominates_reachable,
               dominatorDefsTheory.strict_dominates_def]
  >> first_x_assum match_mp_tac >>
  fs[dominatorDefsTheory.strict_dominates_def]
QED

(* If c dominates lbl and c has defs/phis, get_exit_def from lbl
   returns a node whose block is dominated by c.
   (Complementary to get_exit_def_dominates — together they give
    c dom block(d) dom lbl.) *)
Triviality get_exit_def_dominated_by_ancestor:
  ∀ms dom fn fuel lbl d c cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    block_maps_correct ms ∧
    cfg_reachable_of cfg lbl ∧
    dominates dom c lbl ∧
    (fmap_lookup_list ms.ms_block_defs c ≠ [] ∨
     c ∈ FDOM ms.ms_block_phis) ∧
    mem_ssa_get_exit_def ms dom fuel lbl = d ∧ d ≠ 0 ⇒
    dominates dom c (mn_block (THE (FLOOKUP ms.ms_nodes d)))
Proof
  Induct_on `fuel` >> rpt gen_tac >> disch_tac
  >- fs[mem_ssa_get_exit_def_def]
  >> fs[mem_ssa_get_exit_def_def, LET_THM] >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  Cases_on `fmap_lookup_list ms.ms_block_defs lbl <> []` >> fs[]
  >- (
    Q_TAC SUFF_TAC `mn_block (THE (FLOOKUP ms.ms_nodes d)) = lbl`
    >- simp[]
    >> `MEM d (fmap_lookup_list ms.ms_block_defs lbl)` by
         metis_tac[MEM_LAST_NOT_NIL] >>
    fs[block_maps_correct_def] >> res_tac >> fs[mn_block_def])
  >> Cases_on `FLOOKUP ms.ms_block_phis lbl` >> fs[]
  >- (
    Cases_on `idom_of (dom_analyze (cfg_analyze fn) fn) lbl` >> fs[] >>
    `c <> lbl` by (
      CCONTR_TAC >> gvs[] >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
    `strict_dominates (dom_analyze (cfg_analyze fn) fn) c lbl` by
      fs[dominatorDefsTheory.strict_dominates_def] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) c x` by
      metis_tac[sdom_dom_idom] >>
    `cfg_reachable_of (cfg_analyze fn) x` by
      metis_tac[SIMP_RULE (srw_ss()) [] idom_dominates] >>
    first_x_assum (qspecl_then [`ms`, `fn`, `x`, `c`] mp_tac) >>
    simp[])
  >> gvs[] >>
  `FLOOKUP ms.ms_nodes d = SOME (MnPhi lbl)` by (
    fs[block_maps_correct_def]) >>
  simp[mn_block_def]
QED

(* reaching_in_block returns 0 or a node that dominates blk_lbl *)
Triviality reaching_in_block_dominates:
  ∀ms dom fn fuel inst_id blk_lbl d cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    block_maps_correct ms ∧
    cfg_reachable_of cfg blk_lbl ∧
    (* inst_defs for instructions in blk_lbl map to block_defs blk_lbl *)
    (∀bb iid did.
       lookup_block blk_lbl fn.fn_blocks = SOME bb ∧
       MEM iid (MAP (λi. i.inst_id) bb.bb_instructions) ∧
       FLOOKUP ms.ms_inst_def iid = SOME did ⇒
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) ∧
    mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl = d ∧ d ≠ 0 ⇒
    d ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes d))) blk_lbl
Proof
  rpt gen_tac >> strip_tac >>
  `MEM blk_lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  qpat_x_assum `dom = _` (SUBST_ALL_TAC) >>
  qpat_x_assum `cfg = _` (SUBST_ALL_TAC) >>
  fs[mem_ssa_reaching_in_block_def] >>
  Cases_on `lookup_block blk_lbl fn.fn_blocks` >> gvs[] >>
  Cases_on `mem_ssa_find_prev_def ms x.bb_instructions inst_id` >> gvs[]
  >- (
    (* NONE case: find_prev_def not found, check block_phis *)
    Cases_on `FLOOKUP ms.ms_block_phis blk_lbl` >> gvs[]
    >- (
      (* block_phis = NONE: use idom *)
      Cases_on `idom_of (dom_analyze (cfg_analyze fn) fn) blk_lbl` >> gvs[] >>
      drule_all idom_dominates >> strip_tac >>
      qabbrev_tac `ged = mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel x'` >>
      `ged ∈ FDOM ms.ms_nodes ∧
       dominates (dom_analyze (cfg_analyze fn) fn)
         (mn_block (THE (FLOOKUP ms.ms_nodes ged))) x'` by (
        UNABBREV_ALL_TAC >>
        match_mp_tac (SIMP_RULE (srw_ss()) [] get_exit_def_dominates) >> simp[]) >>
      conj_tac >- simp[] >>
      match_mp_tac dominates_chain >> qexists_tac `x'` >> simp[])
    >> (* block_phis = SOME x': use block_phis_dom_self *)
    metis_tac[block_phis_dom_self])
  >> (* SOME x': find_prev_def found a def *)
  qpat_x_assum `mem_ssa_find_prev_def _ _ _ = SOME _`
    (mp_tac o MATCH_MP find_prev_def_from_inst_def) >>
  strip_tac >>
  `MEM x' (fmap_lookup_list ms.ms_block_defs blk_lbl)` by metis_tac[] >>
  metis_tac[block_defs_dom_self]
QED

(* reaching_in_block returns a phi only at blk_lbl or at a block
   with empty block_defs (via get_exit_def). *)
Triviality reaching_in_block_phi_not_at_defs_block:
  !ms dom fn fuel inst_id blk_lbl b.
    block_maps_correct ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    (!bb iid did.
       lookup_block blk_lbl fn.fn_blocks = SOME bb /\
       MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
       FLOOKUP ms.ms_inst_def iid = SOME did ==>
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) /\
    mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl <> 0 /\
    FLOOKUP ms.ms_nodes
      (mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl) =
      SOME (MnPhi b) ==>
    b = blk_lbl \/ fmap_lookup_list ms.ms_block_defs b = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ <> 0` mp_tac >>
  qpat_x_assum `FLOOKUP _ _ = SOME (MnPhi _)` mp_tac >>
  simp[mem_ssa_reaching_in_block_def] >>
  Cases_on `lookup_block blk_lbl fn.fn_blocks` >> simp[] >>
  Cases_on `mem_ssa_find_prev_def ms x.bb_instructions inst_id` >> simp[]
  (* NONE find_prev_def: continue to block_phis / idom *)
  >- (Cases_on `FLOOKUP ms.ms_block_phis blk_lbl` >> simp[]
      (* NONE block_phis: idom / get_exit_def *)
      >- (Cases_on `idom_of dom blk_lbl` >> simp[] >>
          rpt strip_tac >> gvs[] >>
          disj2_tac >>
          metis_tac[get_exit_def_phi_has_no_defs])
      (* SOME block_phis: b = blk_lbl *)
      >> rpt strip_tac >> gvs[] >>
      sg `FLOOKUP ms.ms_nodes x' = SOME (MnPhi blk_lbl)`
      >- fs[block_maps_correct_def] >>
      gvs[])
  (* SOME find_prev_def: returned a def — contradicts MnPhi *)
  >> rpt strip_tac >>
  drule find_prev_def_from_inst_def >> strip_tac >>
  sg `MEM x' (fmap_lookup_list ms.ms_block_defs blk_lbl)`
  >- metis_tac[] >>
  res_tac >> gvs[]
QED

(* If reaching_in_block returns a non-phi result at a DIFFERENT block
   with non-empty block_defs, then result = LAST(block_defs).
   Cross-block reaching goes through get_exit_def, which returns LAST. *)
Triviality reaching_in_block_cross_block_nonphi_is_last:
  !ms dom fn fuel inst_id blk_lbl r rnode.
    block_maps_correct ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    (!bb iid did.
       lookup_block blk_lbl fn.fn_blocks = SOME bb /\
       MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
       FLOOKUP ms.ms_inst_def iid = SOME did ==>
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) /\
    mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl = r /\
    r <> 0 /\
    FLOOKUP ms.ms_nodes r = SOME rnode /\
    (!b. rnode <> MnPhi b) /\
    mn_block rnode <> blk_lbl /\
    fmap_lookup_list ms.ms_block_defs (mn_block rnode) <> [] ==>
    r = LAST (fmap_lookup_list ms.ms_block_defs (mn_block rnode))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  simp[mem_ssa_reaching_in_block_def] >>
  rpt CASE_TAC >> simp[] >>
  rpt strip_tac >> gvs[] >>
  (* Resolve phi contradiction cases *)
  TRY (fs[block_maps_correct_def] >> res_tac >> gvs[] >> NO_TAC) >>
  (* Resolve find_prev_def same-block cases *)
  TRY (imp_res_tac find_prev_def_in_block >> gvs[] >> NO_TAC) >>
  (* Remaining: get_exit_def case *)
  irule get_exit_def_nonphi_is_last >> metis_tac[]
QED

(* If c strictly dominates blk_lbl and c has defs/phis,
   reaching_in_block returns a node whose block is dominated by c. *)
Triviality reaching_in_block_dominated_by_ancestor:
  !ms dom fn fuel inst_id blk_lbl d c cfg.
    wf_function fn /\ cfg = cfg_analyze fn /\ dom = dom_analyze cfg fn /\
    block_maps_correct ms /\
    cfg_reachable_of cfg blk_lbl /\
    strict_dominates dom c blk_lbl /\
    (fmap_lookup_list ms.ms_block_defs c <> [] \/
     c IN FDOM ms.ms_block_phis) /\
    (!bb iid did.
       lookup_block blk_lbl fn.fn_blocks = SOME bb /\
       MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
       FLOOKUP ms.ms_inst_def iid = SOME did ==>
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) /\
    mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl = d /\ d <> 0 ==>
    dominates dom c (mn_block (THE (FLOOKUP ms.ms_nodes d)))
Proof
  rpt gen_tac >> DISCH_TAC >> fs[] >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  `MEM blk_lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) c blk_lbl` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  qpat_x_assum `_ = d` mp_tac >>
  qpat_x_assum `d <> 0` mp_tac >>
  simp[mem_ssa_reaching_in_block_def] >>
  Cases_on `lookup_block blk_lbl fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `mem_ssa_find_prev_def ms bb.bb_instructions inst_id` >> simp[] >>
  Cases_on `FLOOKUP ms.ms_block_phis blk_lbl` >> simp[] >>
  Cases_on `idom_of (dom_analyze (cfg_analyze fn) fn) blk_lbl` >> simp[] >>
  rpt strip_tac >> gvs[]
  (* Goal 1: idom case — use sdom_dom_idom then get_exit_def_dominated_by_ancestor *)
  >- (
    `dominates (dom_analyze (cfg_analyze fn) fn) c x` by
      metis_tac[sdom_dom_idom] >>
    `cfg_reachable_of (cfg_analyze fn) x` by
      metis_tac[SIMP_RULE (srw_ss()) [] idom_dominates] >>
    match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
      get_exit_def_dominated_by_ancestor) >>
    simp[] >> metis_tac[])
  (* Goals 2-3: phi case *)
  >- (`FLOOKUP ms.ms_nodes d = SOME (MnPhi blk_lbl)` by
        fs[block_maps_correct_def] >>
      simp[memSSADefsTheory.mn_block_def])
  >- (`FLOOKUP ms.ms_nodes d = SOME (MnPhi blk_lbl)` by
        fs[block_maps_correct_def] >>
      simp[memSSADefsTheory.mn_block_def])
  (* Goals 4-7: find_prev_def case *)
  >> (
    qpat_x_assum `mem_ssa_find_prev_def _ _ _ = SOME _`
      (mp_tac o MATCH_MP find_prev_def_from_inst_def) >>
    strip_tac >>
    `MEM d (fmap_lookup_list ms.ms_block_defs blk_lbl)` by res_tac >>
    `mn_block (THE (FLOOKUP ms.ms_nodes d)) = blk_lbl` by (
      fs[block_maps_correct_def] >> res_tac >>
      gvs[memSSADefsTheory.mn_block_def]) >>
    simp[])
QED

(* Same characterization for connect_all *)
Triviality connect_all_reaching_characterize:
  ∀order ms dom fn fuel aid rd.
    FLOOKUP (mem_ssa_connect_all ms dom fn fuel order).ms_reaching aid = SOME rd ⇒
    FLOOKUP ms.ms_reaching aid = SOME rd ∨
    (∃node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ∧
       rd = mem_ssa_reaching_in_block ms dom fn fuel
              (mn_inst_id node) (mn_block node))
Proof
  Induct >> simp[mem_ssa_connect_all_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[connect_list_fields, connect_all_fields] >> strip_tac
  >- (
    drule connect_list_reaching_characterize >>
    simp[connect_list_fields] >> strip_tac
    >- (
      drule connect_list_reaching_characterize >> simp[] >> strip_tac >>
      simp[] >>
      DISJ2_TAC >> qexists_tac `node` >> simp[])
    >> DISJ2_TAC >> qexists_tac `node` >> simp[] >>
    match_mp_tac reaching_in_block_cong >> simp[connect_list_fields])
  >> DISJ2_TAC >> qexists_tac `node` >> simp[connect_list_fields] >>
  match_mp_tac reaching_in_block_cong >> simp[connect_list_fields]
QED

(* connect_all preserves: all reaching entries satisfy dominance *)
Triviality connect_all_reaching_dominates:
  ∀order ms dom fn fuel cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    block_maps_correct ms ∧ mem_ssa_inst_maps_consistent ms ∧
    mem_ssa_ids_valid ms ∧
    (* existing reaching entries already satisfy dominance *)
    (∀aid rd. FLOOKUP ms.ms_reaching aid = SOME rd ∧ rd ≠ 0 ⇒
       rd ∈ FDOM ms.ms_nodes ∧
       dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes rd)))
                     (mn_block (THE (FLOOKUP ms.ms_nodes aid)))) ∧
    (* every label in order is reachable *)
    (∀lbl. MEM lbl order ⇒ cfg_reachable_of cfg lbl) ∧
    (* every non-phi node is at a label in order *)
    (∀aid node. FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
       MEM (mn_block node) order) ∧
    (* inst_defs at any label map to block_defs at that label *)
    (∀lbl bb iid did.
       lookup_block lbl fn.fn_blocks = SOME bb ∧
       MEM iid (MAP (λi. i.inst_id) bb.bb_instructions) ∧
       FLOOKUP ms.ms_inst_def iid = SOME did ⇒
       MEM did (fmap_lookup_list ms.ms_block_defs lbl)) ⇒
    ∀aid rd. FLOOKUP (mem_ssa_connect_all ms dom fn fuel order).ms_reaching aid = SOME rd ∧
             rd ≠ 0 ∧ aid ∈ FDOM ms.ms_nodes ⇒
    rd ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes rd)))
                  (mn_block (THE (FLOOKUP ms.ms_nodes aid)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  rpt gen_tac >> strip_tac >>
  drule connect_all_reaching_characterize >> strip_tac
  (* Case 1: old entry from ms.ms_reaching *)
  >- (first_x_assum (qspecl_then [`aid`, `rd`] mp_tac) >> simp[])
  (* Case 2: new entry from reaching_in_block *)
  >> gvs[] >>
  match_mp_tac (SIMP_RULE (srw_ss()) [] reaching_in_block_dominates) >>
  simp[] >>
  `MEM (mn_block node) order` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  metis_tac[]
QED

Theorem mem_ssa_reaching_def_dominates:
  ∀cfg dom bp fn addr_sp ms use_id def_id.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    FLOOKUP ms.ms_reaching use_id = SOME def_id ∧
    def_id ≠ 0 ∧
    use_id ∈ FDOM ms.ms_nodes ⇒
    def_id ∈ FDOM ms.ms_nodes ∧
    dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes def_id)))
                  (mn_block (THE (FLOOKUP ms.ms_nodes use_id)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ms = _` SUBST_ALL_TAC >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  qmatch_asmsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  `block_maps_correct ms2 ∧ mem_ssa_inst_maps_consistent ms2 ∧
   mem_ssa_ids_valid ms2` by
    simp[Abbr `ms2`, phase12_block_maps_correct, phase12_inst_maps,
         phase12_ids_valid] >>
  `∀aid rd. FLOOKUP ms2.ms_reaching aid = SOME rd ∧ rd ≠ 0 ⇒
     rd ∈ FDOM ms2.ms_nodes ∧
     dominates (dom_analyze (cfg_analyze fn) fn)
       (mn_block (THE (FLOOKUP ms2.ms_nodes rd)))
       (mn_block (THE (FLOOKUP ms2.ms_nodes aid)))` by
    (simp[Abbr `ms2`, insert_phis_fields, process_blocks_fields,
          mem_ssa_init_def]) >>
  `∀lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre ⇒
     cfg_reachable_of (cfg_analyze fn) lbl` by
    (rpt strip_tac >>
     imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     fs[pred_setTheory.EXTENSION]) >>
  `∀aid node. FLOOKUP ms2.ms_nodes aid = SOME node ∧
     (∀blk. node ≠ MnPhi blk) ⇒
     MEM (mn_block node) (cfg_analyze fn).cfg_dfs_pre` by (
    UNABBREV_ALL_TAC >> rpt strip_tac >>
    drule phase12_du_covered >> simp[] >> strip_tac >>
    `mn_block node = lbl` by (
      fs[block_maps_correct_def] >> res_tac >> gvs[]) >>
    gvs[] >> CCONTR_TAC >> gvs[] >>
    imp_res_tac phase12_defs_uses_local >> gvs[]) >>
  `∀lbl bb iid did.
     lookup_block lbl fn.fn_blocks = SOME bb ∧
     MEM iid (MAP (λi. i.inst_id) bb.bb_instructions) ∧
     FLOOKUP ms2.ms_inst_def iid = SOME did ⇒
     MEM did (fmap_lookup_list ms2.ms_block_defs lbl)` by
    (UNABBREV_ALL_TAC >> rpt strip_tac >>
     match_mp_tac phase12_inst_def_block_defs >>
     simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
     metis_tac[]) >>
  mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `ms2`,
    `dom_analyze (cfg_analyze fn) fn`, `fn`,
    `LENGTH (fn_labels fn)`, `cfg_analyze fn`]
    connect_all_reaching_dominates) >>
  impl_tac >- (rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qspecl_then [`use_id`, `def_id`] mp_tac) >> simp[]
QED

(* ==========================================================================
   Property 4: Phi placement at dominance frontiers
   ========================================================================== *)

(* block_phis FDOM monotonicity at each level *)
Triviality insert_phi_at_block_phis_mono:
  ∀ms cfg dom fuel lbl ms' inserted l.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    l ∈ FDOM ms.ms_block_phis ⇒
    l ∈ FDOM ms'.ms_block_phis
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[]
QED

Triviality process_frontiers_block_phis_mono:
  ∀fronts ms cfg dom fuel ms' wl l.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    l ∈ FDOM ms.ms_block_phis ⇒
    l ∈ FDOM ms'.ms_block_phis
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`, `rest`] >> simp[] >>
  metis_tac[insert_phi_at_block_phis_mono]
QED

Triviality insert_phis_block_phis_mono:
  ∀ms cfg dom ef fuel wl l.
    l ∈ FDOM ms.ms_block_phis ⇒
    l ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_phis
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >>
  fs[Once mem_ssa_insert_phis_def] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `_ = (_,_)` (assume_tac o GSYM) >>
  first_x_assum match_mp_tac >>
  metis_tac[process_frontiers_block_phis_mono]
QED

(* insert_phi_at: new block_phis entries are at the specified label *)
Triviality insert_phi_at_block_phis_new:
  ∀ms cfg dom fuel lbl ms' inserted l.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    l ∈ FDOM ms'.ms_block_phis ∧
    l ∉ FDOM ms.ms_block_phis ⇒
    l = lbl
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  fs[FDOM_FUPDATE]
QED

(* process_frontiers: new block_phis entries are in fronts *)
Triviality process_frontiers_block_phis_new:
  ∀fronts ms cfg dom fuel ms' wl l.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    l ∈ FDOM ms'.ms_block_phis ∧
    l ∉ FDOM ms.ms_block_phis ⇒
    MEM l fronts
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `l ∈ FDOM ms1.ms_block_phis`
  >- (
    DISJ1_TAC >>
    metis_tac[insert_phi_at_block_phis_new])
  >> DISJ2_TAC >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`] >> simp[]
QED

(* process_frontiers: worklist contains exactly the newly inserted labels *)
Triviality insert_phi_at_inserted_in_fdom:
  ∀ms cfg dom fuel lbl ms'.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', T) ⇒
    lbl ∈ FDOM ms'.ms_block_phis
Proof
  rpt strip_tac >>
  fs[mem_ssa_insert_phi_at_def] >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >> gvs[FDOM_FUPDATE]
QED

Triviality process_frontiers_wl_subset:
  ∀fronts ms cfg dom fuel ms' wl b.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    MEM b wl ⇒
    b ∈ FDOM ms'.ms_block_phis
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `inserted` >> gvs[MEM]
  >- (
    drule insert_phi_at_inserted_in_fdom >> strip_tac >>
    metis_tac[process_frontiers_block_phis_mono])
  >- metis_tac[]
  >> metis_tac[]
QED

(* Helper: dom_fixpoint_equation contrapositive — if c doesn't dominate lbl,
   there exists a predecessor of lbl that c also doesn't dominate *)
Triviality not_dom_pred_exists:
  ∀fn cfg dom lbl c.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    cfg_reachable_of cfg lbl ∧
    cfg_preds_of cfg lbl <> [] ∧
    fn_entry_label fn <> SOME lbl ∧
    lbl <> c ∧
    ¬dominates dom c lbl ⇒
    ∃q. MEM q (cfg_preds_of cfg lbl) ∧ ¬dominates dom c q
Proof
  rpt strip_tac >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  (* Get entry_block *)
  `fn_has_entry fn` by fs[venomWfTheory.wf_function_def] >>
  `fn.fn_blocks <> []` by fs[venomWfTheory.fn_has_entry_def] >>
  `∃bb. entry_block fn = SOME bb` by
    (simp[venomInstTheory.entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `lbl <> bb.bb_label` by (
    fs[venomInstTheory.entry_block_def, venomInstTheory.fn_entry_label_def] >>
    Cases_on `fn.fn_blocks` >> fs[]) >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  (* Apply dom_fixpoint_equation *)
  mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `lbl`]
    dom_fixpoint_equation) >>
  simp[] >> strip_tac >>
  (* ¬dom c lbl ∧ c ≠ lbl ⇒ c ∉ BIGINTER ⇒ ∃ pred q with ¬dom c q *)
  CCONTR_TAC >> fs[] >>
  (* After negation: ∀q. MEM q preds ⇒ dominates dom c q
     Derive contradiction: MEM c (domlist lbl) contradicts ¬dominates *)
  qpat_x_assum `¬dominates _ c lbl` mp_tac >>
  simp[dominatorDefsTheory.dominates_def] >>
  (* Goal: MEM c (domlist lbl) *)
  (* fixpoint: set(domlist lbl) = {lbl} ∪ BIGINTER ..., so MEM c list ⟺ c ∈ {lbl} ∪ ... *)
  qpat_x_assum `set _ = _` (mp_tac o
    REWRITE_RULE [pred_setTheory.EXTENSION]) >>
  simp[pred_setTheory.IN_BIGINTER, pred_setTheory.IN_IMAGE] >>
  disch_then (fn th => REWRITE_TAC [GSYM th]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `p` mp_tac) >>
  simp[dominatorDefsTheory.dominates_def]
QED

(* Main invariant: insert_phis maintains phi-at-frontier property *)
Triviality insert_phis_phi_at_frontier:
  ∀ms cfg dom ef fuel wl.
    nodes_fresh ms ∧
    (∀l. l ∈ FDOM ms.ms_block_phis ⇒
       ∃src. (fmap_lookup_list ms.ms_block_defs src <> [] ∨
              src ∈ FDOM ms.ms_block_phis) ∧ MEM l (frontier_of dom src)) ∧
    (∀b. MEM b wl ⇒
       fmap_lookup_list ms.ms_block_defs b <> [] ∨
       b ∈ FDOM ms.ms_block_phis) ⇒
    ∀l. l ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_phis ⇒
      ∃src. (fmap_lookup_list ms.ms_block_defs src <> [] ∨
             src ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_block_phis) ∧
            MEM l (frontier_of dom src)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >>
  fs[Once mem_ssa_insert_phis_def] >>
  TRY (res_tac >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  (* Establish IH preconditions for ms' *)
  `nodes_fresh ms'` by metis_tac[process_frontiers_preserves_fresh] >>
  `ms'.ms_block_defs = ms.ms_block_defs` by
    (drule process_frontiers_fields >> simp[]) >>
  (* Rewrite to use ms' block_defs everywhere *)
  qpat_x_assum `ms'.ms_block_defs = ms.ms_block_defs`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >>
              REWRITE_TAC [GSYM th]) >>
  (* Apply IH: discharge preconditions, then specialize *)
  qpat_x_assum `nodes_fresh ms' ∧ _ ⇒ _` mp_tac >>
  impl_tac
  >- (rpt conj_tac
    >- first_x_assum ACCEPT_TAC
    >- (
      (* phi witness condition for ms' *)
      rpt strip_tac >>
      Cases_on `l' ∈ FDOM ms.ms_block_phis`
      >- (
        res_tac >> qexists_tac `src` >> simp[] >>
        metis_tac[process_frontiers_block_phis_mono])
      >> qexists_tac `b` >> conj_tac
      >- metis_tac[process_frontiers_block_phis_mono]
      >> metis_tac[process_frontiers_block_phis_new])
    >> (* worklist condition — LIFO: new_wl ++ wl *)
    rpt strip_tac >> fs[MEM_APPEND]
    >- metis_tac[process_frontiers_wl_subset]
    >> metis_tac[process_frontiers_block_phis_mono])
  >> disch_then (qspec_then `l` mp_tac) >> simp[]
QED

(* mem_ssa_phi_at_frontier: DROPPED — FALSE as stated (Phase 4 removes
   redundant src phi). See memSSACexScript.sml. No consumer needs it. *)

(* ==========================================================================
   Property 6: Reaching-def chain is acyclic
   ========================================================================== *)

(* find_prev_def result comes from an instruction before the target.
   Precondition: target is actually in the instruction list. *)
Triviality find_prev_def_before_target:
  ∀ms insts target d.
    mem_ssa_find_prev_def ms insts target = SOME d ∧
    MEM target (MAP (λi. i.inst_id) insts) ⇒
    ∃pfx sfx.
      insts = pfx ++ sfx ∧
      (∃i. MEM i sfx ∧ i.inst_id = target) ∧
      (∃j. MEM j pfx ∧ FLOOKUP ms.ms_inst_def j.inst_id = SOME d)
Proof
  Induct_on `insts`
  >- simp[mem_ssa_find_prev_def_def]
  >> rpt gen_tac >> simp[mem_ssa_find_prev_def_def] >>
  Cases_on `h.inst_id = target`
  >- simp[]
  >> simp[] >>
  Cases_on `mem_ssa_find_prev_def ms insts target`
  >- (
    simp[] >> strip_tac >>
    `MEM target (MAP (\i. i.inst_id) insts)` by simp[] >>
    qexistsl_tac [`[h]`, `insts`] >>
    fs[MEM_MAP] >> metis_tac[])
  >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`ms`, `target`, `x`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qexistsl_tac [`h::pfx`, `sfx`] >>
  gvs[] >> metis_tac[]
QED

Definition reaching_chain_def:
  reaching_chain ms 0 a b = (a = b) ∧
  reaching_chain ms (SUC n) a b =
    (∃mid. FLOOKUP ms.ms_reaching a = SOME mid ∧
           (mid = b ∨ reaching_chain ms n mid b))
End

(* Elements in pfx have strictly smaller INDEX_OF than elements in sfx *)
Triviality index_lt_in_append:
  ∀x y pfx sfx.
    ALL_DISTINCT (pfx ++ sfx) ∧ MEM x pfx ∧ MEM y sfx ⇒
    ∃i j. INDEX_OF x (pfx ++ sfx) = SOME i ∧
          INDEX_OF y (pfx ++ sfx) = SOME j ∧ i < j
Proof
  rpt strip_tac >>
  drule_all index_of_append_left >> strip_tac >>
  `INDEX_OF x pfx <> NONE` by fs[INDEX_OF_eq_NONE] >>
  Cases_on `INDEX_OF x pfx` >> gvs[] >>
  `INDEX_OF y sfx <> NONE` by fs[INDEX_OF_eq_NONE] >>
  Cases_on `INDEX_OF y sfx` >> gvs[] >>
  mp_tac (Q.SPECL [`y`, `pfx`, `sfx`, `x''`] index_of_append_right) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `x'' + LENGTH pfx` >> simp[] >>
  fs[INDEX_OF_eq_SOME]
QED

(* If x is in pfx and y is in sfx of an ALL_DISTINCT list,
   and we know their INDEX_OF positions, then idx_x < idx_y *)
Triviality index_lt_from_positions:
  !(x:num) y pfx sfx idx_x idx_y.
    ALL_DISTINCT (pfx ++ sfx) /\
    MEM x pfx /\ MEM y sfx /\
    INDEX_OF x (pfx ++ sfx) = SOME idx_x /\
    INDEX_OF y (pfx ++ sfx) = SOME idx_y ==>
    idx_x < idx_y
Proof
  rpt strip_tac >>
  drule_all index_lt_in_append >> strip_tac >>
  metis_tac[optionTheory.SOME_11]
QED

(* find_prev_def result has strictly earlier INDEX_OF than target *)
Triviality find_prev_def_index_lt:
  ∀ms insts target d.
    mem_ssa_find_prev_def ms insts target = SOME d ∧
    MEM target (MAP (λi. i.inst_id) insts) ∧
    ALL_DISTINCT (MAP (λi. i.inst_id) insts) ∧
    mem_ssa_inst_maps_consistent ms ⇒
    ∃idx_d idx_target.
      INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes d)))
               (MAP (λi. i.inst_id) insts) = SOME idx_d ∧
      INDEX_OF target (MAP (λi. i.inst_id) insts) = SOME idx_target ∧
      idx_d < idx_target
Proof
  rpt strip_tac >>
  drule find_prev_def_before_target >> impl_tac >- simp[] >>
  strip_tac >>
  (* j ∈ pfx has FLOOKUP ms_inst_def j.inst_id = SOME d *)
  (* inst_maps_consistent: inst_def maps to a node whose mn_inst_id = iid *)
  `mn_inst_id (THE (FLOOKUP ms.ms_nodes d)) = j.inst_id` by (
    fs[mem_ssa_inst_maps_consistent_def] >> res_tac >>
    Cases_on `FLOOKUP ms.ms_nodes d` >> gvs[mn_inst_id_def]) >>
  (* Now use index_lt_in_append on MAP inst_id lists *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) (pfx ++ sfx))` by metis_tac[] >>
  `MEM j.inst_id (MAP (\i. i.inst_id) pfx)` by (fs[MEM_MAP] >> metis_tac[]) >>
  `MEM target (MAP (\i. i.inst_id) sfx)` by (
    fs[MEM_MAP] >> qexists_tac `i` >> simp[]) >>
  fs[MAP_APPEND] >>
  drule_all index_lt_in_append >> strip_tac >>
  metis_tac[]
QED

(* find_prev_def NONE + ALL_DISTINCT: no instruction before target has
   an inst_def entry. *)
Triviality find_prev_def_none_no_defs:
  !btw tgt aft ms.
    mem_ssa_find_prev_def ms (btw ++ [tgt] ++ aft) tgt.inst_id = NONE /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (btw ++ [tgt] ++ aft)) ==>
    !k. MEM k btw ==> FLOOKUP ms.ms_inst_def k.inst_id = NONE
Proof
  Induct >> simp[mem_ssa_find_prev_def_def] >>
  rpt gen_tac >> rpt DISCH_TAC >> gvs[] >>
  (* case_eq = NONE, ALL_DISTINCT, h.inst_id <> tgt.inst_id, IH *)
  rpt strip_tac >> gvs[]
  >- (
    (* k = h: case split on recursive find_prev_def *)
    pop_assum kall_tac (* drop MEM-related, not needed *) >>
    qpat_x_assum `_ = NONE` mp_tac >>
    Cases_on `mem_ssa_find_prev_def ms (btw ++ [tgt] ++ aft) tgt.inst_id` >>
    simp[])
  (* MEM k btw: use IH on recursive call = NONE *)
  >> qpat_x_assum `_ = NONE` mp_tac >>
  Cases_on `mem_ssa_find_prev_def ms (btw ++ [tgt] ++ aft) tgt.inst_id` >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`tgt`, `aft`, `ms`] mp_tac) >>
  simp[]
QED

(* Contrapositive of find_prev_def_none_no_defs: if any instruction
   before target has inst_def <> NONE, then find_prev_def <> NONE. *)
Triviality find_prev_def_some_when_def_exists:
  !btw tgt aft ms k.
    MEM k btw /\ FLOOKUP ms.ms_inst_def k.inst_id <> NONE /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (btw ++ [tgt] ++ aft)) ==>
    ?d. mem_ssa_find_prev_def ms (btw ++ [tgt] ++ aft) tgt.inst_id = SOME d
Proof
  rpt strip_tac >>
  Cases_on `mem_ssa_find_prev_def ms (btw ++ [tgt] ++ aft) tgt.inst_id`
  >- (drule_all find_prev_def_none_no_defs >> metis_tac[])
  >> metis_tac[]
QED

(* INDEX_OF-level wrapper: if there's an instruction with inst_def entry
   at a position before the target, find_prev_def succeeds. *)
Triviality find_prev_def_some_when_earlier_def:
  !ms insts target iid idx_d idx_t.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    INDEX_OF iid (MAP (\i. i.inst_id) insts) = SOME idx_d /\
    INDEX_OF target (MAP (\i. i.inst_id) insts) = SOME idx_t /\
    idx_d < idx_t /\
    FLOOKUP ms.ms_inst_def iid <> NONE ==>
    ?d. mem_ssa_find_prev_def ms insts target = SOME d
Proof
  rpt strip_tac >>
  (* Derive LENGTH and EL facts NON-DESTRUCTIVELY *)
  `idx_t < LENGTH insts` by (
    qpat_x_assum `INDEX_OF target _ = SOME idx_t` mp_tac >>
    simp[INDEX_OF_eq_SOME, LENGTH_MAP]) >>
  `idx_d < LENGTH insts` by (
    qpat_x_assum `INDEX_OF iid _ = SOME idx_d` mp_tac >>
    simp[INDEX_OF_eq_SOME, LENGTH_MAP]) >>
  `(EL idx_t insts).inst_id = target` by (
    qpat_x_assum `INDEX_OF target _ = SOME idx_t` mp_tac >>
    simp[INDEX_OF_eq_SOME, EL_MAP]) >>
  `(EL idx_d insts).inst_id = iid` by (
    qpat_x_assum `INDEX_OF iid _ = SOME idx_d` mp_tac >>
    simp[INDEX_OF_eq_SOME, EL_MAP]) >>
  (* Decompose insts = TAKE idx_t insts ++ [EL idx_t insts] ++ DROP (SUC idx_t) insts *)
  (* and apply find_prev_def_some_when_def_exists *)
  mp_tac (Q.SPECL [`TAKE idx_t insts`,
                    `EL idx_t insts`,
                    `DROP (SUC idx_t) insts`,
                    `ms`,
                    `EL idx_d insts`]
           find_prev_def_some_when_def_exists) >>
  impl_tac >- (
    conj_tac >- (simp[MEM_EL] >> qexists_tac `idx_d` >>
                  simp[EL_TAKE, LENGTH_TAKE]) >>
    conj_tac >- simp[] >>
    metis_tac[TAKE_DROP_SUC]
  ) >>
  simp[] >> metis_tac[TAKE_DROP_SUC]
QED

(* find_prev_def closest: the result comes from the instruction closest
   to (and before) the target. Between that instruction and target,
   no other instruction has an inst_def entry. *)
Triviality find_prev_def_closest:
  !ms insts target d.
    mem_ssa_find_prev_def ms insts target = SOME d /\
    MEM target (MAP (\i. i.inst_id) insts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ?pfx mid btw tgt aft.
      insts = pfx ++ [mid] ++ btw ++ [tgt] ++ aft /\
      FLOOKUP ms.ms_inst_def mid.inst_id = SOME d /\
      tgt.inst_id = target /\
      (!k. MEM k btw ==> FLOOKUP ms.ms_inst_def k.inst_id = NONE)
Proof
  Induct_on `insts` >> simp[mem_ssa_find_prev_def_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_id = target` >> simp[] >>
  strip_tac >>
  Cases_on `mem_ssa_find_prev_def ms insts target` >> gvs[]
  (* NONE: recursive call found nothing, d = inst_def of h *)
  >- (
    qpat_x_assum `MEM target _` mp_tac >>
    simp[Once MEM_MAP] >> strip_tac >>
    drule_then strip_assume_tac (iffLR MEM_SPLIT_APPEND_first) >>
    gvs[] >>
    qexistsl_tac [`[]`, `h`, `pfx`, `i`, `sfx`] >> simp[] >>
    match_mp_tac find_prev_def_none_no_defs >>
    qexistsl_tac [`i`, `sfx`] >>
    gvs[ALL_DISTINCT])
  (* SOME x: recursive call found d deeper in the list *)
  >> first_x_assum (qspecl_then [`ms`, `target`, `d`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`h::pfx`, `mid`, `btw`, `tgt`, `aft`] >>
  gvs[]
QED

(* Reaching chain step: if mid continues the chain, mid has a reaching entry *)
Triviality reaching_chain_mid_has_reaching:
  ∀ms n mid b.
    reaching_chain ms (SUC n) mid b ⇒
    ∃next. FLOOKUP ms.ms_reaching mid = SOME next
Proof
  simp[Once reaching_chain_def] >> metis_tac[]
QED

(* connect_list preserves NONE reaching for skipped nodes:
   nodes with NONE or MnPhi lookup never get ms_reaching entries *)
Triviality connect_list_skips_reaching:
  ∀aids ms dom fn fuel k.
    (FLOOKUP ms.ms_nodes k = NONE ∨
     ∃blk. FLOOKUP ms.ms_nodes k = SOME (MnPhi blk)) ∧
    FLOOKUP ms.ms_reaching k = NONE ⇒
    FLOOKUP (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching k = NONE
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP ms.ms_nodes h` >> simp[] >>
  Cases_on `x` >> simp[] >>
  first_x_assum match_mp_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, connect_list_fields] >>
  Cases_on `h = k` >> gvs[]
QED

(* connect_all preserves NONE reaching for skipped nodes *)
Triviality connect_all_skips_reaching:
  ∀order ms dom fn fuel k.
    (FLOOKUP ms.ms_nodes k = NONE ∨
     ∃blk. FLOOKUP ms.ms_nodes k = SOME (MnPhi blk)) ∧
    FLOOKUP ms.ms_reaching k = NONE ⇒
    FLOOKUP (mem_ssa_connect_all ms dom fn fuel order).ms_reaching k = NONE
Proof
  Induct >> simp[mem_ssa_connect_all_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  simp[connect_list_fields] >>
  `FLOOKUP (mem_ssa_connect_list ms dom fn fuel
      (fmap_lookup_list ms.ms_block_uses h)).ms_reaching k = NONE` by (
    match_mp_tac connect_list_skips_reaching >>
    simp[connect_list_fields]) >>
  match_mp_tac connect_list_skips_reaching >>
  simp[connect_list_fields]
QED


(* Strengthened freshness: all node ids are ≥ lb, given lb ≤ ms_next_id.
   Propagated through each phase; combined with mem_ssa_init gives lb=1. *)
Triviality process_inst_ids_ge:
  ∀bp addr_sp lbl ms inst lb aid.
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ∧
    aid ∈ FDOM (mem_ssa_process_inst bp addr_sp lbl ms inst).ms_nodes ⇒
    lb ≤ aid
Proof
  rw[mem_ssa_process_inst_def] >>
  rpt (COND_CASES_TAC >> gvs[finite_mapTheory.FDOM_FUPDATE]) >>
  res_tac >> DECIDE_TAC
QED

Triviality process_block_ids_ge:
  ∀insts bp addr_sp lbl ms lb aid.
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ∧
    aid ∈ FDOM (mem_ssa_process_block bp addr_sp lbl ms insts).ms_nodes ⇒
    lb ≤ aid
Proof
  Induct >> simp[mem_ssa_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `lbl`,
    `mem_ssa_process_inst bp addr_sp lbl ms h`, `lb`, `aid`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac
    >- (rpt strip_tac >> match_mp_tac process_inst_ids_ge >> metis_tac[])
    >- (`ms.ms_next_id ≤ (mem_ssa_process_inst bp addr_sp lbl ms h).ms_next_id` by
          metis_tac[process_inst_next_id_mono] >> simp[])
    >> simp[])
  >> simp[]
QED

Triviality process_blocks_ids_ge:
  ∀lbls bp addr_sp fn ms lb aid.
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ∧
    aid ∈ FDOM (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_nodes ⇒
    lb ≤ aid
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block h fn.fn_blocks` >> gvs[] >- metis_tac[] >>
  `(∀a. a ∈ FDOM (mem_ssa_process_block bp addr_sp h ms
      x.bb_instructions).ms_nodes ⇒ lb ≤ a)` by
    (rpt strip_tac >> match_mp_tac process_block_ids_ge >> metis_tac[]) >>
  `lb ≤ (mem_ssa_process_block bp addr_sp h ms
      x.bb_instructions).ms_next_id` by
    (`ms.ms_next_id ≤ (mem_ssa_process_block bp addr_sp h ms
        x.bb_instructions).ms_next_id`
      suffices_by simp[] >>
     simp[process_block_next_id_mono]) >>
  metis_tac[]
QED

Triviality insert_phi_at_ids_ge:
  ∀ms cfg dom fuel lbl ms' inserted lb.
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ∧
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ⇒
    (∀a. a ∈ FDOM ms'.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms'.ms_next_id
Proof
  rw[mem_ssa_insert_phi_at_def, LET_THM] >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >> gvs[]
QED

Triviality process_frontiers_ids_ge:
  ∀fronts ms cfg dom fuel ms' wl lb.
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ∧
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ⇒
    (∀a. a ∈ FDOM ms'.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms'.ms_next_id
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  qexists_tac `ms1` >> simp[] >>
  metis_tac[insert_phi_at_ids_ge]
QED

Triviality insert_phis_ids_ge:
  ∀ms cfg dom ef fuel wl lb.
    (∀a. a ∈ FDOM ms.ms_nodes ⇒ lb ≤ a) ∧ lb ≤ ms.ms_next_id ⇒
    (∀a. a ∈ FDOM (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes ⇒ lb ≤ a)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  rpt strip_tac >>
  fs[Once mem_ssa_insert_phis_def] >>
  TRY (res_tac >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `_ = (_,_)` (assume_tac o GSYM) >>
  mp_tac (Q.SPECL [`frontier_of dom b`, `ms`, `cfg`, `dom`, `ef`,
    `ms'`, `new_wl`, `lb`] process_frontiers_ids_ge) >>
  impl_tac >- simp[] >>
  strip_tac >> metis_tac[]
QED

Triviality process_blocks_next_id_mono:
  ∀lbls bp addr_sp fn ms.
    ms.ms_next_id ≤ (mem_ssa_process_blocks bp addr_sp fn ms lbls).ms_next_id
Proof
  Induct >> simp[mem_ssa_process_blocks_def] >>
  rpt gen_tac >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  `ms.ms_next_id ≤
     (mem_ssa_process_block bp addr_sp h ms x.bb_instructions).ms_next_id`
    by simp[process_block_next_id_mono] >>
  first_x_assum (qspecl_then [`bp`, `addr_sp`, `fn`,
    `mem_ssa_process_block bp addr_sp h ms x.bb_instructions`] mp_tac) >>
  simp[]
QED

(* For mem_ssa_build output: 0 ∉ FDOM ms_nodes *)
Triviality build_zero_not_in_nodes:
  ∀cfg dom bp fn addr_sp.
    0 ∉ FDOM (mem_ssa_build cfg dom bp fn addr_sp).ms_nodes
Proof
  rpt gen_tac >>
  simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
       connect_all_fields, insert_phis_fields, process_blocks_fields] >>
  RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.EXP_2]) >>
  REWRITE_TAC [arithmeticTheory.EXP_2] >>
  strip_tac >>
  (* Compose: process_blocks_ids_ge + process_blocks_next_id_mono
     discharge insert_phis_ids_ge preconditions *)
  mp_tac (MATCH_MP
    (Q.SPECL [`mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
       cfg.cfg_dfs_pre`, `cfg`, `dom`, `LENGTH (fn_labels fn)`,
       `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
       `MAP FST (fmap_to_alist
          (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
             cfg.cfg_dfs_pre).ms_block_defs)`, `1`]
       insert_phis_ids_ge)
    (CONJ (REWRITE_RULE [GSYM mem_ssa_init_def]
             (SIMP_RULE (srw_ss()) [mem_ssa_init_def]
               (Q.SPECL [`cfg.cfg_dfs_pre`, `bp`, `addr_sp`, `fn`,
                          `mem_ssa_init`, `1`] process_blocks_ids_ge)))
          (REWRITE_RULE [GSYM mem_ssa_init_def]
             (SIMP_RULE (srw_ss()) [mem_ssa_init_def]
               (Q.SPECL [`cfg.cfg_dfs_pre`, `bp`, `addr_sp`, `fn`,
                          `mem_ssa_init`] process_blocks_next_id_mono))))) >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

(* For mem_ssa_build output, node 0 has no ms_reaching entry *)
Triviality build_zero_no_reaching:
  ∀cfg dom bp fn addr_sp.
    FLOOKUP (mem_ssa_build cfg dom bp fn addr_sp).ms_reaching 0 = NONE
Proof
  rpt gen_tac >>
  simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
       connect_all_fields] >>
  match_mp_tac connect_all_skips_reaching >>
  conj_tac
  >- (DISJ1_TAC >>
      mp_tac (Q.SPECL [`cfg`, `dom`, `bp`, `fn`, `addr_sp`]
        build_zero_not_in_nodes) >>
      simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
           connect_all_fields, insert_phis_fields, process_blocks_fields,
           FLOOKUP_DEF])
  >- simp[insert_phis_fields, process_blocks_fields, mem_ssa_init_def]
QED

(* For mem_ssa_build output, phi nodes have no ms_reaching entry *)
Triviality build_phi_no_reaching:
  ∀cfg dom bp fn addr_sp ms phi_id blk.
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) ⇒
    FLOOKUP ms.ms_reaching phi_id = NONE
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  match_mp_tac connect_all_skips_reaching >>
  fs[insert_phis_fields, process_blocks_fields, mem_ssa_init_def] >>
  DISJ2_TAC >> metis_tac[]
QED

(* Non-phi nodes in mem_ssa_build have reachable blocks *)
Triviality build_non_phi_reachable:
  ∀cfg dom bp fn addr_sp ms a node.
    wf_function fn ∧ cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    FLOOKUP ms.ms_nodes a = SOME node ∧
    (∀blk. node <> MnPhi blk) ⇒
    cfg_reachable_of cfg (mn_block node)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ms = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.EXP_2]) >>
  REWRITE_TAC [arithmeticTheory.EXP_2] >>
  qmatch_asmsub_abbrev_tac `FLOOKUP ms2.ms_nodes` >>
  (* du_covered: non-phi node → in block_defs or block_uses at some lbl *)
  `?lbl. MEM a (fmap_lookup_list ms2.ms_block_defs lbl) \/
         MEM a (fmap_lookup_list ms2.ms_block_uses lbl)` by
    (UNABBREV_ALL_TAC >> metis_tac[phase12_du_covered]) >>
  (* lbl must be in cfg_dfs_pre *)
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (CCONTR_TAC >> UNABBREV_ALL_TAC >>
     imp_res_tac phase12_defs_uses_local >> gvs[]) >>
  (* block_maps_correct gives mn_block = lbl *)
  `block_maps_correct ms2` by
    (UNABBREV_ALL_TAC >> metis_tac[phase12_block_maps_correct]) >>
  fs[block_maps_correct_def] >>
  res_tac >> gvs[mn_block_def] >>
  `mn_block node IN set (cfg_analyze fn).cfg_dfs_pre` by simp[] >>
  imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
  gvs[EXTENSION]
QED

(* Nodes with a reaching entry are reachable (corollary: has reaching ⇒ non-phi ⇒ reachable) *)
Triviality build_reaching_reachable:
  ∀cfg dom bp fn addr_sp ms a mid.
    wf_function fn ∧ cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    a ∈ FDOM ms.ms_nodes ∧
    FLOOKUP ms.ms_reaching a = SOME mid ⇒
    cfg_reachable_of cfg (mn_block (THE (FLOOKUP ms.ms_nodes a)))
Proof
  rpt gen_tac >> strip_tac >>
  `?node. FLOOKUP ms.ms_nodes a = SOME node` by fs[flookup_thm] >>
  `THE (FLOOKUP ms.ms_nodes a) = node` by simp[] >>
  simp[] >>
  mp_tac (Q.SPECL [`cfg`, `dom`, `bp`, `fn`, `addr_sp`, `ms`,
                    `a`, `node`] build_non_phi_reachable) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      mp_tac (Q.SPECL [`cfg`, `dom`, `bp`, `fn`, `addr_sp`, `ms`,
                        `a`, `blk`] build_phi_no_reaching) >>
      simp[])
  >- simp[]
QED

(* Dominance across a reaching chain: if reaching_chain ms n a b and
   every reaching step satisfies dominance, then dominates(block b, block a) *)
Triviality reaching_chain_dominates:
  ∀n a b bp fn addr_sp.
    wf_function fn ∧
    reaching_chain
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp)
      n a b ∧ n > 0 ∧
    a ∈ FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes ∧
    b ≠ 0 ⇒
    b ∈ FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes ∧
    dominates (dom_analyze (cfg_analyze fn) fn)
      (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)))
      (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)))
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  assume_tac (SIMP_RULE (srw_ss()) [] mem_ssa_reaching_def_dominates) >>
  assume_tac (SIMP_RULE (srw_ss()) [] build_zero_no_reaching) >>
  fs[] >>
  qpat_x_assum `reaching_chain _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE[reaching_chain_def]) >>
  strip_tac >> gvs[]
  (* mid = b: single step → res_tac gives dominance directly *)
  >- (res_tac >> simp[])
  (* reaching_chain n mid b: case split on n *)
  >> Cases_on `n`
  (* n = 0: mid = b, same as above *)
  >- (fs[reaching_chain_def] >> gvs[] >> res_tac >> simp[])
  (* n = SUC n' *)
  >> `FLOOKUP (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_reaching 0 = NONE`
       by (first_x_assum (qspecl_then [`cfg_analyze fn`,
             `dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`, `addr_sp`]
             mp_tac) >> simp[]) >>
  `mid <> 0` by (
    strip_tac >> pop_assum SUBST_ALL_TAC >>
    qpat_x_assum `reaching_chain _ _ 0 _`
      (mp_tac o PURE_REWRITE_RULE[reaching_chain_def]) >>
    simp[]) >>
  (* step dominance: a → mid *)
  qpat_x_assum `!bp' fn' addr_sp' use_id def_id. _`
    (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `mid`] mp_tac) >>
  simp[] >> strip_tac >>
  (* IH: b ∈ FDOM ∧ dom(b, mid) *)
  first_x_assum (qspecl_then [`mid`, `b`, `bp`, `fn`, `addr_sp`] mp_tac) >>
  simp[] >> strip_tac >>
  match_mp_tac dominates_chain >>
  qexists_tac `mn_block (THE (FLOOKUP
    (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
     bp fn addr_sp).ms_nodes mid))` >>
  simp[] >>
  match_mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_reachable) >>
  qexists_tac `mid` >> simp[]
QED

(* Same-block reaching step must come from find_prev_def.
   If reaching_in_block returns d with mn_block d = blk_lbl,
   then d came from find_prev_def (not idom, not phi, not 0). *)
Triviality reaching_same_block_is_find_prev_def:
  ∀ms dom fn fuel inst_id blk_lbl d bb cfg.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ dom = dom_analyze cfg fn ∧
    block_maps_correct ms ∧
    cfg_reachable_of cfg blk_lbl ∧
    lookup_block blk_lbl fn.fn_blocks = SOME bb ∧
    mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl = d ∧
    d ≠ 0 ∧ d ∈ FDOM ms.ms_nodes ∧
    mn_block (THE (FLOOKUP ms.ms_nodes d)) = blk_lbl ∧
    (∀blk. THE (FLOOKUP ms.ms_nodes d) ≠ MnPhi blk) ∧
    (∀iid did.
       MEM iid (MAP (λi. i.inst_id) bb.bb_instructions) ∧
       FLOOKUP ms.ms_inst_def iid = SOME did ⇒
       MEM did (fmap_lookup_list ms.ms_block_defs blk_lbl)) ⇒
    mem_ssa_find_prev_def ms bb.bb_instructions inst_id = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `mem_ssa_reaching_in_block _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [mem_ssa_reaching_in_block_def]) >>
  fs[] >>
  (* Case split on find_prev_def *)
  Cases_on `mem_ssa_find_prev_def ms bb.bb_instructions inst_id` >> fs[]
  (* find_prev_def = SOME x → d = x, conclusion immediate *)
  >- (
    (* NONE: Case split on block_phis *)
    Cases_on `FLOOKUP ms.ms_block_phis blk_lbl` >> fs[]
    >- (* no phi: idom case or 0 *)
     (CCONTR_TAC >> fs[] >>
      Cases_on `idom_of (dom_analyze (cfg_analyze fn) fn) blk_lbl` >>
      fs[] >>
      drule_all idom_dominates >> strip_tac >>
      mp_tac (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fn`,
        `fuel`, `x`, `d`, `cfg_analyze fn`] get_exit_def_dominates) >>
      simp[] >> strip_tac >>
      mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `x`, `blk_lbl`]
        dominates_antisym) >>
      simp[LET_THM] >> strip_tac >>
      (* x = blk_lbl; substitute *)
      pop_assum SUBST_ALL_TAC >>
      (* idom_of ... blk_lbl = SOME blk_lbl → strict_dominates blk_lbl blk_lbl *)
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
        (Q.SPECL [`fn`, `cfg_analyze fn`, `blk_lbl`, `blk_lbl`]
          idom_is_immediate)) >>
      simp[dominatorDefsTheory.strict_dominates_def])
    (* phi case → x ≠ d because d is not MnPhi but x is *)
    >> CCONTR_TAC >> fs[] >>
    `FLOOKUP ms.ms_nodes d = SOME (MnPhi blk_lbl)` by
      (fs[block_maps_correct_def] >> res_tac) >>
    fs[] >>
    metis_tac[])
  (* find_prev_def = SOME x, d = x, immediate *)
  >> simp[]
QED

(* Helper: single reaching step a→mid gives mid ∈ FDOM when mid ≠ 0 *)
Triviality build_reaching_step_in_fdom:
  ∀bp fn addr_sp a mid.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn ∧
    FLOOKUP ms.ms_reaching a = SOME mid ∧ mid <> 0 ∧
    a ∈ FDOM ms.ms_nodes ⇒
    mid ∈ FDOM ms.ms_nodes
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [] mem_ssa_reaching_def_dominates) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `mid`] mp_tac) >>
  simp[]
QED

(* Build-level wrapper: non-phi node → inst_id is in its block's instructions,
   and the block has ALL_DISTINCT inst_ids. *)
Triviality build_node_inst_id_in_block:
  ∀bp fn addr_sp aid node.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn ∧
    FLOOKUP ms.ms_nodes aid = SOME node ∧ (∀blk. node ≠ MnPhi blk) ⇒
    ∃bb. lookup_block (mn_block node) fn.fn_blocks = SOME bb ∧
         MEM (mn_inst_id node) (MAP (λi. i.inst_id) bb.bb_instructions) ∧
         ALL_DISTINCT (MAP (λi. i.inst_id) bb.bb_instructions)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  (* phase12_node_inst_id_in_block gives lookup_block + MEM *)
  drule_all phase12_node_inst_id_in_block >> strip_tac >>
  (* fn_inst_ids_block_distinct gives ALL_DISTINCT *)
  imp_res_tac lookup_block_props >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by (
    match_mp_tac fn_inst_ids_block_distinct >>
    qexists_tac `fn` >>
    fs[venomWfTheory.wf_function_def] >> simp[]) >>
  metis_tac[]
QED

(* Any node with a reaching entry is non-phi *)
Triviality build_reaching_src_non_phi:
  ∀bp fn addr_sp a rd.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    FLOOKUP ms.ms_reaching a = SOME rd ⇒
    ∃anode. FLOOKUP ms.ms_nodes a = SOME anode ∧ (∀blk. anode <> MnPhi blk)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  qpat_x_assum `FLOOKUP (mem_ssa_connect_all _ _ _ _ _).ms_reaching a = SOME rd`
    (mp_tac o MATCH_MP connect_all_reaching_characterize) >>
  simp[insert_phis_fields, process_blocks_fields, mem_ssa_init_def,
       finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY]
QED

(* Build-level: if c strictly dominates blk(use_id) and c has defs,
   then ms_reaching(use_id) lands in a block dominated by c.
   Bridges reaching_in_block_dominated_by_ancestor to the build level. *)
Triviality build_reaching_dominated_by_ancestor:
  !bp fn addr_sp use_id x c.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching use_id = SOME x /\ x <> 0 /\
    use_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes use_id) <> MnPhi blk) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) c
      (mn_block (THE (FLOOKUP ms.ms_nodes use_id))) /\
    fmap_lookup_list ms.ms_block_defs c <> [] ==>
    dominates (dom_analyze (cfg_analyze fn) fn) c
      (mn_block (THE (FLOOKUP ms.ms_nodes x)))
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `FLOOKUP _ use_id = SOME x` mp_tac >>
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  qmatch_goalsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  sg `block_maps_correct ms2`
  >- simp[Abbr `ms2`, phase12_block_maps_correct] >>
  sg `mem_ssa_inst_maps_consistent ms2`
  >- simp[Abbr `ms2`, phase12_inst_maps] >>
  DISCH_TAC >>
  drule connect_all_reaching_characterize >> strip_tac
  >- (fs[Abbr `ms2`, insert_phis_fields, process_blocks_fields,
         mem_ssa_init_def, finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY])
  >> gvs[] >>
  `MEM (mn_block node) (cfg_analyze fn).cfg_dfs_pre` by (
    UNABBREV_ALL_TAC >> drule phase12_du_covered >> simp[] >> strip_tac >>
    `mn_block node = lbl` by (fs[block_maps_correct_def] >> res_tac >> gvs[]) >>
    gvs[] >> CCONTR_TAC >> gvs[] >>
    imp_res_tac phase12_defs_uses_local >> gvs[]) >>
  `cfg_reachable_of (cfg_analyze fn) (mn_block node)` by (
    imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
    fs[pred_setTheory.EXTENSION]) >>
  match_mp_tac (SIMP_RULE (srw_ss()) [] reaching_in_block_dominated_by_ancestor) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `Abbrev (ms2 = _)` (SUBST_ALL_TAC o
    SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]) >>
  match_mp_tac phase12_inst_def_block_defs >>
  simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
  metis_tac[]
QED

(* Build-level: if reaching predecessor y of non-phi use_id is a phi at
   phi_blk, then phi_blk = blk(use_id) or block_defs(phi_blk) = [].
   Bridges reaching_in_block_phi_not_at_defs_block to build level. *)
Triviality build_reaching_phi_location:
  !bp fn addr_sp use_id y phi_blk ms.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp /\
    wf_function fn /\
    FLOOKUP ms.ms_reaching use_id = SOME y /\ y <> 0 /\
    use_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes use_id) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes y = SOME (MnPhi phi_blk) ==>
    phi_blk = mn_block (THE (FLOOKUP ms.ms_nodes use_id)) \/
    fmap_lookup_list ms.ms_block_defs phi_blk = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FLOOKUP _ use_id = SOME y` mp_tac >>
  qpat_x_assum `FLOOKUP _ y = SOME (MnPhi _)` mp_tac >>
  qpat_x_assum `use_id IN _` mp_tac >>
  qpat_x_assum `!blk. _` mp_tac >>
  qpat_x_assum `ms = _` SUBST_ALL_TAC >>
  simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  qmatch_goalsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  sg `block_maps_correct ms2`
  >- simp[Abbr `ms2`, phase12_block_maps_correct] >>
  sg `mem_ssa_inst_maps_consistent ms2`
  >- simp[Abbr `ms2`, phase12_inst_maps] >>
  rpt DISCH_TAC >>
  drule connect_all_reaching_characterize >> strip_tac
  >- (fs[Abbr `ms2`, insert_phis_fields, process_blocks_fields,
         mem_ssa_init_def, finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY])
  >> gvs[] >>
  sg `mn_block node = mn_block (THE (FLOOKUP ms2.ms_nodes use_id))`
  >- (fs[block_maps_correct_def] >> res_tac >> gvs[]) >>
  (* Establish block_defs_are_defs for ms2 *)  
  sg `!lbl' aid. MEM aid (fmap_lookup_list ms2.ms_block_defs lbl') ==>
      ?iid loc. FLOOKUP ms2.ms_nodes aid = SOME (MnDef iid lbl' loc)`
  >- (rpt strip_tac >>
      qpat_x_assum `Abbrev (ms2 = _)` (fn abbr =>
        let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] abbr in
          ASSUME_TAC abbr >>
          qpat_x_assum `MEM _ _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          SUBST1_TAC eq
        end) >>
      metis_tac[phase12_block_defs_are_defs]) >>
  (* Establish inst_def_block_defs for ms2 *)
  sg `!bb iid did.
      lookup_block (mn_block node) fn.fn_blocks = SOME bb /\
      MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
      FLOOKUP ms2.ms_inst_def iid = SOME did ==>
      MEM did (fmap_lookup_list ms2.ms_block_defs (mn_block node))`
  >- (rpt strip_tac >>
      qpat_x_assum `Abbrev (ms2 = _)` (fn abbr =>
        let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] abbr in
          ASSUME_TAC abbr >>
          qpat_x_assum `MEM _ _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          qpat_x_assum `FLOOKUP _ _ = SOME did`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          qpat_x_assum `lookup_block _ _ = _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          SUBST1_TAC eq
        end) >>
      irule phase12_inst_def_block_defs >>
      simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
      metis_tac[]) >>
  (* Apply reaching_in_block_phi_not_at_defs_block *)
  mp_tac (Q.SPECL [`ms2`, `dom_analyze (cfg_analyze fn) fn`, `fn`,
    `LENGTH (fn_labels fn)`, `mn_inst_id node`, `mn_block node`, `phi_blk`]
    reaching_in_block_phi_not_at_defs_block) >>
  (impl_tac >- (
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

(* Build-level: cross-block non-phi reaching result is LAST of block_defs.
   Lifts reaching_in_block_cross_block_nonphi_is_last to build level. *)
Triviality build_reaching_cross_block_is_last:
  !fn bp addr_sp a z znode ms.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    wf_function fn /\
    FLOOKUP ms.ms_reaching a = SOME z /\ z <> 0 /\
    a IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes a) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes z = SOME znode /\
    (!blk. znode <> MnPhi blk) /\
    mn_block znode <> mn_block (THE (FLOOKUP ms.ms_nodes a)) /\
    fmap_lookup_list ms.ms_block_defs (mn_block znode) <> [] ==>
    z = LAST (fmap_lookup_list ms.ms_block_defs (mn_block znode))
Proof
  rpt gen_tac >> strip_tac >>
  (* Push ALL ms-field hypotheses, substitute ms, expand build *)
  ntac 9 (pop_assum mp_tac) >>
  pop_assum SUBST_ALL_TAC >>
  simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  qmatch_goalsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  sg `block_maps_correct ms2`
  >- simp[Abbr `ms2`, phase12_block_maps_correct] >>
  rpt DISCH_TAC >>
  drule connect_all_reaching_characterize >> strip_tac
  >- (fs[Abbr `ms2`, insert_phis_fields, process_blocks_fields,
         mem_ssa_init_def, finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY])
  >> gvs[] >>
  (* Now: z = reaching_in_block ms2 ..., all assumptions in ms2 form *)
  sg `mn_block node = mn_block (THE (FLOOKUP ms2.ms_nodes a))`
  >- (fs[block_maps_correct_def] >> res_tac >> gvs[]) >>
  (* block_defs_are_defs for ms2 *)
  sg `!lbl' aid. MEM aid (fmap_lookup_list ms2.ms_block_defs lbl') ==>
      ?iid loc. FLOOKUP ms2.ms_nodes aid = SOME (MnDef iid lbl' loc)`
  >- (rpt strip_tac >>
      qpat_x_assum `Abbrev (ms2 = _)` (fn abbr =>
        let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] abbr in
          ASSUME_TAC abbr >>
          qpat_x_assum `MEM aid _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          SUBST1_TAC eq
        end) >>
      metis_tac[phase12_block_defs_are_defs]) >>
  (* inst_def_block_defs for ms2 *)
  sg `!bb iid did.
      lookup_block (mn_block node) fn.fn_blocks = SOME bb /\
      MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
      FLOOKUP ms2.ms_inst_def iid = SOME did ==>
      MEM did (fmap_lookup_list ms2.ms_block_defs (mn_block node))`
  >- (rpt strip_tac >>
      qpat_x_assum `Abbrev (ms2 = _)` (fn abbr =>
        let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] abbr in
          ASSUME_TAC abbr >>
          qpat_x_assum `MEM iid _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          qpat_x_assum `FLOOKUP _ iid = SOME did`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          qpat_x_assum `lookup_block _ _ = _`
            (ASSUME_TAC o PURE_REWRITE_RULE [eq]) >>
          SUBST1_TAC eq
        end) >>
      irule phase12_inst_def_block_defs >>
      simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
      metis_tac[]) >>
  (* Apply reaching_in_block_cross_block_nonphi_is_last *)
  mp_tac (Q.SPECL [`ms2`, `dom_analyze (cfg_analyze fn) fn`, `fn`,
    `LENGTH (fn_labels fn)`, `mn_inst_id node`, `mn_block node`]
    reaching_in_block_cross_block_nonphi_is_last) >>
  disch_then (qspecl_then [
    `mem_ssa_reaching_in_block ms2 (dom_analyze (cfg_analyze fn) fn) fn
       (LENGTH (fn_labels fn)) (mn_inst_id node) (mn_block node)`,
    `znode`] mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  simp[]
QED

(* Build-level: a single reaching step a→b in the same block
   implies find_prev_def gives b, and INDEX_OF ordering.
   Encapsulates the phase12 boilerplate for same-block reasoning. *)
Triviality build_same_block_reaching_index:
  ∀bp fn addr_sp a b.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn ∧
    FLOOKUP ms.ms_reaching a = SOME b ∧
    a ∈ FDOM ms.ms_nodes ∧ b <> 0 ∧
    b ∈ FDOM ms.ms_nodes ∧
    (∀blk. THE (FLOOKUP ms.ms_nodes b) <> MnPhi blk) ∧
    mn_block (THE (FLOOKUP ms.ms_nodes a)) =
      mn_block (THE (FLOOKUP ms.ms_nodes b)) ⇒
    ∃idx_a idx_b bb.
      lookup_block (mn_block (THE (FLOOKUP ms.ms_nodes b))) fn.fn_blocks = SOME bb ∧
      INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes a)))
               (MAP (λi. i.inst_id) bb.bb_instructions) = SOME idx_a ∧
      INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes b)))
               (MAP (λi. i.inst_id) bb.bb_instructions) = SOME idx_b ∧
      idx_a > idx_b
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  (* Expand build to ms2 *)
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.EXP_2]) >>
  REWRITE_TAC [arithmeticTheory.EXP_2] >>
  qmatch_asmsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  `block_maps_correct ms2` by
    simp[Abbr `ms2`, phase12_block_maps_correct] >>
  `mem_ssa_inst_maps_consistent ms2` by
    simp[Abbr `ms2`, phase12_inst_maps] >>
  (* Characterize reaching: connect_all output → reaching_in_block on ms2 *)
  qpat_x_assum `FLOOKUP (mem_ssa_connect_all _ _ _ _ _).ms_reaching a = SOME b`
    (mp_tac o MATCH_MP connect_all_reaching_characterize) >>
  (* ms2.ms_reaching = FEMPTY, so first disjunct is impossible *)
  `ms2.ms_reaching = FEMPTY` by
    simp[Abbr `ms2`, insert_phis_fields, process_blocks_fields, mem_ssa_init_def] >>
  `FLOOKUP ms2.ms_reaching a <> SOME b` by
    fs[finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY] >>
  simp[] >> strip_tac >>
  (* node for a: non-phi, reaching_in_block ms2 ... (mn_inst_id node) (mn_block node) = b *)
  rename [`FLOOKUP ms2.ms_nodes a = SOME anode`] >>
  (* node for b *)
  `?bnode. FLOOKUP ms2.ms_nodes b = SOME bnode` by fs[flookup_thm] >>
  `THE (FLOOKUP ms2.ms_nodes b) = bnode` by simp[] >>
  `THE (FLOOKUP ms2.ms_nodes a) = anode` by simp[] >>
  fs[] >>
  (* Both nodes' inst_ids are in their blocks *)
  `?bb_a. lookup_block (mn_block anode) fn.fn_blocks = SOME bb_a /\
          MEM (mn_inst_id anode) (MAP (\i. i.inst_id) bb_a.bb_instructions)` by
    (simp[Abbr `ms2`] >> metis_tac[phase12_node_inst_id_in_block]) >>
  `?bb_b. lookup_block (mn_block bnode) fn.fn_blocks = SOME bb_b /\
          MEM (mn_inst_id bnode) (MAP (\i. i.inst_id) bb_b.bb_instructions)` by
    (simp[Abbr `ms2`] >> metis_tac[phase12_node_inst_id_in_block]) >>
  (* Same block → same bb → unify *)
  `mn_block anode = mn_block bnode` by fs[] >>
  gvs[] >>
  (* ALL_DISTINCT inst_ids *)
  imp_res_tac lookup_block_props >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb_a.bb_instructions)` by (
    match_mp_tac fn_inst_ids_block_distinct >> qexists_tac `fn` >>
    fs[venomWfTheory.wf_function_def]) >>
  (* cfg_reachable_of *)
  `cfg_reachable_of (cfg_analyze fn) (mn_block bnode)` by
    (simp[Abbr `ms2`] >> metis_tac[phase12_non_phi_reachable]) >>
  (* inst_def → block_defs for this block (needed by reaching_same_block) *)
  `!iid did. MEM iid (MAP (\i. i.inst_id) bb_a.bb_instructions) /\
     FLOOKUP ms2.ms_inst_def iid = SOME did ==>
     MEM did (fmap_lookup_list ms2.ms_block_defs (mn_block bnode))` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`bp`, `addr_sp`, `fn`, `(cfg_analyze fn).cfg_dfs_pre`,
      `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
      `LENGTH (fn_labels fn)`,
      `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
      `MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
          (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)`,
      `mn_block bnode`, `bb_a`, `iid`, `did`]
      phase12_inst_def_block_defs) >>
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct, Abbr `ms2`]) >>
  (* reaching_same_block_is_find_prev_def *)
  `mem_ssa_find_prev_def ms2 bb_a.bb_instructions (mn_inst_id anode) =
     SOME (mem_ssa_reaching_in_block ms2 (dom_analyze (cfg_analyze fn) fn)
             fn (LENGTH (fn_labels fn)) (mn_inst_id anode) (mn_block bnode))` by (
    match_mp_tac reaching_same_block_is_find_prev_def >>
    MAP_EVERY qexists_tac [`dom_analyze (cfg_analyze fn) fn`,
      `fn`, `LENGTH (fn_labels fn)`, `mn_block bnode`, `cfg_analyze fn`] >>
    rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
    simp[mn_block_def]) >>
  (* find_prev_def_index_lt: get INDEX_OF ordering *)
  drule find_prev_def_index_lt >> impl_tac
  >- (rpt conj_tac >> first_x_assum ACCEPT_TAC)
  >> strip_tac >>
  `THE (FLOOKUP ms2.ms_nodes (mem_ssa_reaching_in_block ms2
      (dom_analyze (cfg_analyze fn) fn) fn (LENGTH (fn_labels fn))
      (mn_inst_id anode) (mn_block bnode))) = bnode` by simp[] >>
  gvs[arithmeticTheory.GREATER_DEF]
QED

(* Same-block reaching step: if ms_reaching(a)=b (same block), then any other
   MnDef d in the same block with idx_d < idx_a must have idx_d < idx_b.
   This follows from find_prev_def_closest: b is the closest previous def to a,
   so no MnDef can exist between b and a in instruction order. *)
Triviality build_same_block_reaching_closest:
  !bp fn addr_sp a b d d_iid d_blk d_loc.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching a = SOME b /\
    a IN FDOM ms.ms_nodes /\ b <> 0 /\
    b IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes b) <> MnPhi blk) /\
    mn_block (THE (FLOOKUP ms.ms_nodes a)) =
      mn_block (THE (FLOOKUP ms.ms_nodes b)) /\
    FLOOKUP ms.ms_nodes d = SOME (MnDef d_iid d_blk d_loc) /\
    d_blk = mn_block (THE (FLOOKUP ms.ms_nodes a)) /\
    d <> b ==>
    !bb idx_a idx_b idx_d.
      lookup_block d_blk fn.fn_blocks = SOME bb /\
      INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes a)))
               (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_a /\
      INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes b)))
               (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_b /\
      INDEX_OF d_iid (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_d /\
      idx_d < idx_a ==>
      idx_d < idx_b
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Expand build to ms2 *)
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.EXP_2]) >>
  REWRITE_TAC [arithmeticTheory.EXP_2] >>
  qmatch_asmsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  `block_maps_correct ms2` by
    simp[Abbr `ms2`, phase12_block_maps_correct] >>
  `mem_ssa_inst_maps_consistent ms2` by
    simp[Abbr `ms2`, phase12_inst_maps] >>
  (* Characterize reaching: connect_all output -> reaching_in_block on ms2 *)
  qpat_x_assum `FLOOKUP (mem_ssa_connect_all _ _ _ _ _).ms_reaching a = SOME b`
    (mp_tac o MATCH_MP connect_all_reaching_characterize) >>
  `ms2.ms_reaching = FEMPTY` by
    simp[Abbr `ms2`, insert_phis_fields, process_blocks_fields, mem_ssa_init_def] >>
  `FLOOKUP ms2.ms_reaching a <> SOME b` by
    fs[finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY] >>
  simp[] >> strip_tac >>
  rename [`FLOOKUP ms2.ms_nodes a = SOME anode`] >>
  `?bnode. FLOOKUP ms2.ms_nodes b = SOME bnode` by fs[flookup_thm] >>
  `THE (FLOOKUP ms2.ms_nodes b) = bnode` by simp[] >>
  `THE (FLOOKUP ms2.ms_nodes a) = anode` by simp[] >>
  fs[] >>
  (* ALL_DISTINCT inst_ids *)
  imp_res_tac lookup_block_props >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by (
    match_mp_tac fn_inst_ids_block_distinct >> qexists_tac `fn` >>
    fs[venomWfTheory.wf_function_def]) >>
  (* cfg_reachable_of *)
  `cfg_reachable_of (cfg_analyze fn) (mn_block bnode)` by
    (simp[Abbr `ms2`] >> metis_tac[phase12_non_phi_reachable]) >>
  (* inst_def -> block_defs for this block *)
  `!iid did. MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
     FLOOKUP ms2.ms_inst_def iid = SOME did ==>
     MEM did (fmap_lookup_list ms2.ms_block_defs (mn_block bnode))` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`bp`, `addr_sp`, `fn`, `(cfg_analyze fn).cfg_dfs_pre`,
      `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
      `LENGTH (fn_labels fn)`,
      `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
      `MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
          (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)`,
      `mn_block bnode`, `bb`, `iid`, `did`]
      phase12_inst_def_block_defs) >>
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct, Abbr `ms2`]) >>
  (* MEM: use mp_tac on phase12 theorem with explicit specialization *)
  `MEM (mn_inst_id anode) (MAP (\i. i.inst_id) bb.bb_instructions)` by (
    mp_tac (Q.SPECL [`bp`, `addr_sp`, `fn`,
      `(cfg_analyze fn).cfg_dfs_pre`,
      `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
      `LENGTH (fn_labels fn)`,
      `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
      `MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
          (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)`,
      `a`, `anode`] phase12_node_inst_id_in_block) >>
    simp[Abbr `ms2`]) >>
  (* reaching_same_block_is_find_prev_def *)
  `mem_ssa_find_prev_def ms2 bb.bb_instructions (mn_inst_id anode) = SOME b` by (
    match_mp_tac reaching_same_block_is_find_prev_def >>
    MAP_EVERY qexists_tac [`dom_analyze (cfg_analyze fn) fn`,
      `fn`, `LENGTH (fn_labels fn)`, `mn_block bnode`, `cfg_analyze fn`] >>
    rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
    simp[mn_block_def]) >>
  drule_all find_prev_def_closest >> strip_tac >>
  (* Establish FLOOKUP ms2.ms_inst_def d_iid = SOME d via phase12_inst_def_reverse *)
  `FLOOKUP ms2.ms_nodes d = SOME (MnDef d_iid (mn_block anode) d_loc)` by
    gvs[connect_all_fields] >>
  `FLOOKUP ms2.ms_inst_def d_iid = SOME d` by (
    qpat_x_assum `FLOOKUP ms2.ms_nodes d = _` mp_tac >>
    simp[Abbr `ms2`] >> strip_tac >>
    irule phase12_inst_def_reverse >>
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct]) >>
  (* mn_inst_id bnode = mid.inst_id via inst_maps_consistent:
     FLOOKUP ms2.ms_inst_def mid.inst_id = SOME b gives
     FLOOKUP ms2.ms_nodes b = SOME (MnDef mid.inst_id _ _)
     combined with FLOOKUP ms2.ms_nodes b = SOME bnode gives
     bnode = MnDef mid.inst_id _ _ *)
  `?iblk iloc. FLOOKUP ms2.ms_nodes b = SOME (MnDef mid.inst_id iblk iloc)` by (
    qpat_x_assum `mem_ssa_inst_maps_consistent ms2` mp_tac >>
    simp[mem_ssa_inst_maps_consistent_def] >>
    disch_then (fn th => mp_tac (CONJUNCT1 th)) >>
    disch_then (qspecl_then [`mid.inst_id`, `b`] mp_tac) >> simp[]) >>
  `mn_inst_id bnode = mid.inst_id` by (gvs[mn_inst_id_def]) >>
  (* Substitute the decomposition into all INDEX_OF assumptions *)
  qpat_x_assum `bb.bb_instructions = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [MAP_APPEND, MAP]) >>
  (* Substitute tgt.inst_id = mn_inst_id anode everywhere *)
  gvs[] >>
  (* Step 1: MEM d_iid (full list) *)
  `MEM d_iid (MAP (λi. i.inst_id) pfx ++ [mid.inst_id] ++
     MAP (λi. i.inst_id) btw ++ [mn_inst_id anode] ++
     MAP (λi. i.inst_id) aft)` by (
    CCONTR_TAC >> gvs[GSYM INDEX_OF_eq_NONE]) >>
  (* Step 2: ~MEM d_iid (MAP inst_id btw) *)
  `~MEM d_iid (MAP (λi. i.inst_id) btw)` by (
    strip_tac >> fs[MEM_MAP] >>
    res_tac >> gvs[]) >>
  (* Step 3: d_iid <> mn_inst_id anode *)
  `d_iid <> mn_inst_id anode` by (
    strip_tac >> gvs[] >>
    `idx_d = idx_a` by (
      fs[ALL_DISTINCT_APPEND] >>
      metis_tac[ALL_DISTINCT_INDEX_OF_EL, optionTheory.SOME_11]) >>
    fs[]) >>
  (* Step 4: d_iid <> mid.inst_id *)
  `d_iid <> mid.inst_id` by (
    strip_tac >> gvs[]) >>
  (* Now d_iid is in pfx or aft *)
  gvs[MEM_APPEND]
  >- ((* pfx case: d_iid before mid.inst_id *)
    match_mp_tac index_lt_from_positions >>
    qexistsl_tac [`d_iid`, `mid.inst_id`,
      `MAP (\i. i.inst_id) pfx`,
      `[mid.inst_id] ++ MAP (\i. i.inst_id) btw ++
       [mn_inst_id anode] ++ MAP (\i. i.inst_id) aft`] >>
    simp[MEM_APPEND])
  >- ((* aft case: mn_inst_id anode before d_iid => contradiction with idx_d < idx_a *)
    `idx_a < idx_d` by (
      match_mp_tac index_lt_from_positions >>
      qexistsl_tac [`mn_inst_id anode`, `d_iid`,
        `MAP (\i. i.inst_id) pfx ++ [mid.inst_id] ++
         MAP (\i. i.inst_id) btw ++ [mn_inst_id anode]`,
        `MAP (\i. i.inst_id) aft`] >>
      simp[MEM_APPEND]) >>
    fs[])
QED

(* Build-level: if there is a def (with inst_def entry) before x in the same
   block, then ms_reaching(x) stays in the same block. This is because
   find_prev_def succeeds, so reaching_in_block returns the find_prev_def
   result which is always in the same block.
   This is the key helper that lets walk_same_block_visits_def apply its IH. *)
Triviality build_reaching_same_block:
  !bp fn addr_sp x rd def_id def_iid def_blk def_loc bb idx_x idx_d.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching x = SOME rd /\
    x IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes x) <> MnPhi blk) /\
    mn_block (THE (FLOOKUP ms.ms_nodes x)) = def_blk /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    lookup_block def_blk fn.fn_blocks = SOME bb /\
    INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes x)))
             (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_x /\
    INDEX_OF def_iid (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_d /\
    idx_d < idx_x ==>
    mn_block (THE (FLOOKUP ms.ms_nodes rd)) = def_blk /\
    rd <> 0 /\ rd IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes rd) <> MnPhi blk)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  (* Expand build to ms2 *)
  fs[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
     connect_all_fields] >>
  RULE_ASSUM_TAC (REWRITE_RULE [arithmeticTheory.EXP_2]) >>
  REWRITE_TAC [arithmeticTheory.EXP_2] >>
  qmatch_asmsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  `block_maps_correct ms2` by
    simp[Abbr `ms2`, phase12_block_maps_correct] >>
  `mem_ssa_inst_maps_consistent ms2` by
    simp[Abbr `ms2`, phase12_inst_maps] >>
  `mem_ssa_ids_valid ms2` by
    simp[Abbr `ms2`, phase12_ids_valid] >>
  (* Characterize reaching *)
  qpat_x_assum `FLOOKUP (mem_ssa_connect_all _ _ _ _ _).ms_reaching x = SOME rd`
    (mp_tac o MATCH_MP connect_all_reaching_characterize) >>
  `ms2.ms_reaching = FEMPTY` by
    simp[Abbr `ms2`, insert_phis_fields, process_blocks_fields, mem_ssa_init_def] >>
  `FLOOKUP ms2.ms_reaching x <> SOME rd` by
    fs[finite_mapTheory.FLOOKUP_DEF, FDOM_FEMPTY] >>
  simp[] >> strip_tac >>
  rename [`FLOOKUP ms2.ms_nodes x = SOME xnode`] >>
  `THE (FLOOKUP ms2.ms_nodes x) = xnode` by simp[] >>
  fs[] >>
  (* ALL_DISTINCT inst_ids *)
  imp_res_tac lookup_block_props >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by (
    match_mp_tac fn_inst_ids_block_distinct >> qexists_tac `fn` >>
    fs[venomWfTheory.wf_function_def]) >>
  (* cfg_reachable_of *)
  `cfg_reachable_of (cfg_analyze fn) (mn_block xnode)` by
    (simp[Abbr `ms2`] >> metis_tac[phase12_non_phi_reachable]) >>
  (* inst_def -> block_defs for this block *)
  `!iid did. MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
     FLOOKUP ms2.ms_inst_def iid = SOME did ==>
     MEM did (fmap_lookup_list ms2.ms_block_defs (mn_block xnode))` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`bp`, `addr_sp`, `fn`, `(cfg_analyze fn).cfg_dfs_pre`,
      `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
      `LENGTH (fn_labels fn)`,
      `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
      `MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
          (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)`,
      `mn_block xnode`, `bb`, `iid`, `did`]
      phase12_inst_def_block_defs) >>
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct, Abbr `ms2`]) >>
  (* MEM of xnode's inst_id in block *)
  `MEM (mn_inst_id xnode) (MAP (\i. i.inst_id) bb.bb_instructions)` by (
    mp_tac (Q.SPECL [`bp`, `addr_sp`, `fn`,
      `(cfg_analyze fn).cfg_dfs_pre`,
      `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
      `LENGTH (fn_labels fn)`,
      `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
      `MAP FST (fmap_to_alist
        (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
          (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)`,
      `x`, `xnode`] phase12_node_inst_id_in_block) >>
    simp[Abbr `ms2`]) >>
  (* inst_def for def_id: original has def_blk, connect_all preserves ms_nodes *)
  `FLOOKUP ms2.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc)` by
    fs[connect_all_fields] >>
  `FLOOKUP ms2.ms_inst_def def_iid = SOME def_id` by (
    qpat_x_assum `FLOOKUP ms2.ms_nodes def_id = SOME (MnDef _ def_blk _)` mp_tac >>
    simp[Abbr `ms2`] >> strip_tac >>
    irule phase12_inst_def_reverse >>
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct]) >>
  (* Use find_prev_def_some_when_earlier_def *)
  `mn_block xnode = def_blk` by gvs[] >>
  `FLOOKUP ms2.ms_inst_def def_iid <> NONE` by simp[] >>
  `?fpd. mem_ssa_find_prev_def ms2 bb.bb_instructions
    (mn_inst_id xnode) = SOME fpd` by (
    match_mp_tac find_prev_def_some_when_earlier_def >>
    qexistsl_tac [`def_iid`, `idx_d`, `idx_x`] >> simp[]) >>
  (* reaching_in_block returns fpd when find_prev_def succeeds *)
  `mem_ssa_reaching_in_block ms2 (dom_analyze (cfg_analyze fn) fn) fn
     (LENGTH (fn_labels fn)) (mn_inst_id xnode) def_blk = fpd` by
    simp[mem_ssa_reaching_in_block_def] >>
  (* fpd is MnDef: from find_prev_def_from_inst_def + inst_maps *)
  drule find_prev_def_from_inst_def >> strip_tac >>
  `?fpd_blk fpd_loc. FLOOKUP ms2.ms_nodes fpd = SOME (MnDef iid fpd_blk fpd_loc)` by (
    qpat_x_assum `mem_ssa_inst_maps_consistent ms2` mp_tac >>
    simp[mem_ssa_inst_maps_consistent_def] >> strip_tac >>
    res_tac >> metis_tac[]) >>
  `fpd IN FDOM ms2.ms_nodes` by fs[flookup_thm] >>
  (* fpd <> 0: fpd IN FDOM but 0 NOTIN FDOM *)
  `0 NOTIN FDOM ms2.ms_nodes` by (
    simp[Abbr `ms2`] >>
    mp_tac (SIMP_RULE (srw_ss()) [] build_zero_not_in_nodes) >>
    simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
         connect_all_fields]) >>
  `fpd <> 0` by metis_tac[] >>
  (* mn_block: find_prev_def_in_block *)
  `mn_block (THE (FLOOKUP ms2.ms_nodes fpd)) = mn_block xnode` by
    (drule_all find_prev_def_in_block >> simp[]) >>
  (* non-phi: fpd is MnDef *)
  `!blk. THE (FLOOKUP ms2.ms_nodes fpd) <> MnPhi blk` by simp[] >>
  gvs[connect_all_fields]
QED

(* Same-block reaching chains have strictly decreasing INDEX_OF.
   Precondition: b is not phi (for cycles a=b, this follows from a having
   a reaching entry, which phis don't have). *)
Triviality reaching_chain_same_block_dec:
  ∀n bp fn addr_sp a b.
    wf_function fn ∧
    reaching_chain
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp)
      n a b ∧ n > 0 ∧
    a ∈ FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes ∧
    b <> 0 ∧
    (∀blk. THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b) <> MnPhi blk) ∧
    mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)) =
      mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)) ⇒
    ∃idx_a idx_b bb.
      lookup_block (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b))) fn.fn_blocks = SOME bb ∧
      INDEX_OF (mn_inst_id (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)))
               (MAP (λi. i.inst_id) bb.bb_instructions) = SOME idx_a ∧
      INDEX_OF (mn_inst_id (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)))
               (MAP (λi. i.inst_id) bb.bb_instructions) = SOME idx_b ∧
      idx_a > idx_b
Proof
  Induct \\ simp[] \\ rpt gen_tac \\ disch_tac
  \\ assume_tac (SIMP_RULE (srw_ss()) [] build_zero_no_reaching)
  \\ fs[]
  \\ qpat_x_assum `reaching_chain _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [reaching_chain_def])
  \\ strip_tac \\ gvs[]
  (* Case 1: mid = b, single step a → b *)
  >- (
    `b IN FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp).ms_nodes` by (
      mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_step_in_fdom) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `b`] mp_tac) >>
      simp[]) >>
    mp_tac (SIMP_RULE (srw_ss()) [] build_same_block_reaching_index) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `b`] mp_tac) >>
    simp[])
  (* Case 2: reaching_chain n mid b, multi-step *)
  \\ Cases_on `n`
  (* n = 0: chain 0 mid b means mid = b, same as Case 1 *)
  >- (
    fs[reaching_chain_def] >> gvs[] >>
    `b IN FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp).ms_nodes` by (
      mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_step_in_fdom) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `b`] mp_tac) >>
      simp[]) >>
    mp_tac (SIMP_RULE (srw_ss()) [] build_same_block_reaching_index) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `b`] mp_tac) >>
    simp[])
  (* n = SUC n': establish mid properties then use IH *)
  \\ rename [`reaching_chain _ (SUC n') mid b`]
  (* mid ≠ 0: phis have no reaching, but mid has a reaching chain *)
  \\ `mid <> 0` by (
    strip_tac >> pop_assum SUBST_ALL_TAC >>
    qpat_x_assum `reaching_chain _ _ 0 _`
      (mp_tac o PURE_REWRITE_RULE [reaching_chain_def]) >>
    qpat_x_assum `!cfg dom bp fn addr_sp. _`
      (qspecl_then [`cfg_analyze fn`,
        `dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`, `addr_sp`] mp_tac) >>
    simp[])
  (* mid ∈ FDOM ms.ms_nodes *)
  \\ `mid IN FDOM (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp).ms_nodes` by (
    mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_step_in_fdom) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `mid`] mp_tac) >>
    simp[])
  (* mid is non-phi: mid has reaching entry from chain, so non-phi *)
  \\ `?mid_next. FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_reaching mid
       = SOME mid_next` by (
    irule reaching_chain_mid_has_reaching >> metis_tac[])
  \\ `?midnode. FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid
       = SOME midnode /\ (!blk. midnode <> MnPhi blk)` by (
    mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_src_non_phi) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `mid`, `mid_next`] mp_tac) >>
    simp[])
  \\ `!blk. THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)
       <> MnPhi blk` by simp[]
  (* Dominance: chain gives dom(block_b, block_mid) *)
  \\ `dominates (dom_analyze (cfg_analyze fn) fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)))
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)))` by (
    mp_tac (Q.SPECL [`SUC n'`, `mid`, `b`, `bp`, `fn`, `addr_sp`]
      reaching_chain_dominates) >>
    simp[])
  (* Single step gives dom(block_mid, block_a) *)
  \\ `dominates (dom_analyze (cfg_analyze fn) fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)))
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)))` by (
    mp_tac (SIMP_RULE (srw_ss()) [] mem_ssa_reaching_def_dominates) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `mid`] mp_tac) >>
    simp[])
  (* cfg_reachable_of for mid's block (has reaching entry mid_next) *)
  \\ `cfg_reachable_of (cfg_analyze fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)))` by (
    match_mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_reachable) >>
    qexists_tac `mid_next` >> simp[])
  (* cfg_reachable_of for a's block (has reaching entry mid) *)
  \\ `cfg_reachable_of (cfg_analyze fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)))` by (
    match_mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_reachable) >>
    qexists_tac `mid` >> simp[])
  (* cfg_reachable_of for b's block: follows from a's since block_a = block_b *)
  \\ `cfg_reachable_of (cfg_analyze fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)))` by
    metis_tac[]
  (* Derive dom(mid, b) from dom(mid, a) and block_a = block_b *)
  \\ `dominates (dom_analyze (cfg_analyze fn) fn)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)))
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b)))` by
    metis_tac[]
  (* Antisym: dom(b,mid) ∧ dom(mid,b) → block_mid = block_b *)
  \\ `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid)) =
     mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b))` by (
    mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`,
      `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
         (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid))`,
      `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
         (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes b))`]
      dominates_antisym) >>
    simp[LET_THM])
  (* mn_block mid = mn_block a follows from mid=b and a=b *)
  \\ `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes a)) =
     mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes mid))` by fs[]
  (* IH: reaching_chain (SUC n') mid b in same block → idx_mid > idx_b *)
  \\ first_x_assum (qspecl_then [`bp`, `fn`, `addr_sp`, `mid`, `b`] mp_tac)
  \\ simp[]
  \\ disch_tac
  (* Single step a→mid in same block → idx_a > idx_mid *)
  \\ mp_tac (SIMP_RULE (srw_ss()) [] build_same_block_reaching_index)
  \\ disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `a`, `mid`] mp_tac)
  \\ simp[]
  \\ disch_tac
  (* Both results use same bb since block_mid = block_b; combine *)
  \\ gvs[]
QED

(* Reaching-def chain acyclicity: holds when cfg and dom are correctly computed. *)
Theorem mem_ssa_reaching_acyclic:
  ∀fn bp addr_sp ms aid.
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
    wf_function fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    aid ∈ FDOM ms.ms_nodes ∧ aid ≠ 0 ⇒
    ¬∃n. n > 0 ∧ reaching_chain ms n aid aid
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `ms = _` SUBST_ALL_TAC >>
  CCONTR_TAC >> fs[] >>
  `?rd. FLOOKUP (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_reaching aid = SOME rd` by (
    Cases_on `n` >> fs[reaching_chain_def]) >>
  `?aidnode. FLOOKUP (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes aid = SOME aidnode /\
    (!blk. aidnode <> MnPhi blk)` by (
    mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_src_non_phi) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `aid`, `rd`] mp_tac) >>
    simp[]) >>
  `!blk. THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes aid)
    <> MnPhi blk` by simp[] >>
  mp_tac (Q.SPECL [`n`, `bp`, `fn`, `addr_sp`, `aid`, `aid`]
    reaching_chain_same_block_dec) >>
  simp[]
QED

(* ==========================================================================
   Property 7: Clobber walk soundness
   ========================================================================== *)

(* access_id must not be MnPhi — see memSSACexScript.sml for counterexample. *)
(* Clobber soundness: if the walk returns LiveOnEntry (SOME 0), no
   strictly-dominating MnDef completely_contains the access location.
   Uses strict_dominates (not dominates) because same-block defs AFTER
   the access are not on the reaching chain — walk_clobber follows
   ms_reaching backward and find_prev_def only finds defs BEFORE
   the access. See memSSACexScript.sml for the same-block counterexample. *)
(* Visited monotonicity for collect_phi_clobbers, given walker monotonicity *)
Triviality collect_phi_visited_mono:
  ∀ops walker visited clobbers visited'.
    mem_ssa_collect_phi_clobbers walker visited ops = (clobbers, visited') ∧
    (∀v rd r v'. walker v rd = (r, v') ⇒ ∀x. MEM x v ⇒ MEM x v') ⇒
    ∀x. MEM x visited ⇒ MEM x visited'
Proof
  Induct >> rw[mem_ssa_collect_phi_clobbers_def] >>
  Cases_on `h` >> gvs[mem_ssa_collect_phi_clobbers_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `MEM x visited1` by (Cases_on `result` >> gvs[] >> res_tac) >>
  Cases_on `result` >> gvs[] >>
  metis_tac[]
QED

(* Visited monotonicity for walk_clobber *)
Triviality walk_clobber_visited_mono:
  ∀ms fuel visited current qloc result visited'.
    mem_ssa_walk_clobber ms fuel visited current qloc = (result, visited') ⇒
    ∀x. MEM x visited ⇒ MEM x visited'
Proof
  Induct_on `fuel`
  >- (rw[mem_ssa_walk_clobber_def] >> gvs[])
  >> rpt gen_tac
  >> simp[Once mem_ssa_walk_clobber_def, LET_THM]
  >> Cases_on `current = 0` >- simp[]
  >> Cases_on `MEM current visited` >- simp[]
  >> simp[]
  >> Cases_on `FLOOKUP ms.ms_nodes current` >> simp[]
  >- (strip_tac >> gvs[MEM])
  >> Cases_on `x:mem_ssa_node` >> simp[]
  (* MnDef *)
  >- (IF_CASES_TAC >- (strip_tac >> gvs[MEM]) >>
      Cases_on `FLOOKUP ms.ms_reaching current` >> simp[]
      >- (strip_tac >> gvs[MEM]) >>
      strip_tac >>
      first_x_assum (drule_then assume_tac) >> simp[MEM] >> metis_tac[])
  (* MnUse *)
  >- (Cases_on `FLOOKUP ms.ms_reaching current` >> simp[]
      >- (strip_tac >> gvs[MEM]) >>
      strip_tac >>
      first_x_assum (drule_then assume_tac) >> simp[MEM] >> metis_tac[])
  (* MnPhi *)
  >> Cases_on `FLOOKUP ms.ms_phi_ops current` >> simp[]
  >- (strip_tac >> gvs[MEM])
  >> pairarg_tac >> simp[]
  >> qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
       (fn eq =>
         assume_tac eq >>
         mp_tac (MATCH_MP
           (collect_phi_visited_mono |> REWRITE_RULE [GSYM AND_IMP_INTRO]) eq))
  >> (impl_tac >-
       (simp[] >> rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]))
  >> strip_tac
  >> CONV_TAC (DEPTH_CONV BETA_CONV) >> simp[]
  >> Cases_on `clobbers` >> simp[]
  >> TRY (Cases_on `t` >> simp[])
  >> strip_tac >> gvs[]
QED

(* walk_clobber adds current to visited (when fuel > 0, current non-zero,
   not already visited) *)
Triviality walk_clobber_visits_current:
  ∀ms fuel visited current qloc result visited'.
    mem_ssa_walk_clobber ms (SUC fuel) visited current qloc = (result, visited') ∧
    current ≠ 0 ∧ ¬MEM current visited ⇒
    MEM current visited'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `mem_ssa_walk_clobber _ _ _ _ _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [mem_ssa_walk_clobber_def]) >>
  simp[LET_THM] >>
  Cases_on `FLOOKUP ms.ms_nodes current` >> simp[]
  >- (strip_tac >> gvs[MEM])
  >> Cases_on `x:mem_ssa_node` >> simp[]
  (* MnDef *)
  >- (IF_CASES_TAC >- (strip_tac >> gvs[MEM]) >>
      Cases_on `FLOOKUP ms.ms_reaching current` >> simp[]
      >- (strip_tac >> gvs[MEM]) >>
      strip_tac >> drule walk_clobber_visited_mono >> simp[MEM])
  (* MnUse *)
  >- (Cases_on `FLOOKUP ms.ms_reaching current` >> simp[]
      >- (strip_tac >> gvs[MEM]) >>
      strip_tac >> drule walk_clobber_visited_mono >> simp[MEM])
  (* MnPhi *)
  >> Cases_on `FLOOKUP ms.ms_phi_ops current` >> simp[]
  >- (strip_tac >> gvs[MEM])
  >> pairarg_tac >> simp[]
  >> qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
       (fn eq =>
         assume_tac eq >>
         mp_tac (MATCH_MP
           (collect_phi_visited_mono |> REWRITE_RULE [GSYM AND_IMP_INTRO]) eq))
  >> (impl_tac >-
       (simp[] >> rpt gen_tac >> strip_tac >> drule walk_clobber_visited_mono >> simp[]))
  >> strip_tac
  >> CONV_TAC (DEPTH_CONV BETA_CONV) >> simp[]
  >> Cases_on `clobbers` >> simp[]
  >> TRY (Cases_on `t` >> simp[])
  >> strip_tac >> gvs[]
QED

(* Part A helper: collect_phi_clobbers returning [] means the walker
   returned NONE for every operand, so no newly-visited MnDef contains. *)
Triviality collect_phi_none_sound:
  ∀ops walker visited visited' ms qloc.
    mem_ssa_collect_phi_clobbers walker visited ops = ([], visited') ∧
    (∀vis rd v vis'.
       MEM (rd,v) ops ∧ walker vis rd = (NONE, vis') ⇒
       ∀nid iid blk loc.
         MEM nid vis' ∧ ~MEM nid vis ∧
         FLOOKUP ms.ms_nodes nid = SOME (MnDef iid blk loc) ⇒
         ¬completely_contains loc qloc) ⇒
    ∀nid iid blk loc.
      MEM nid visited' ∧ ~MEM nid visited ∧
      FLOOKUP ms.ms_nodes nid = SOME (MnDef iid blk loc) ⇒
      ¬completely_contains loc qloc
Proof
  Induct >> rw[mem_ssa_collect_phi_clobbers_def] >>
  rename1 `h::ops` >> Cases_on `h` >> rename1 `(rd0, v0)` >>
  gvs[mem_ssa_collect_phi_clobbers_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `walker visited rd0 = (result, visited1)` >>
  Cases_on `result` >> gvs[] >>
  Cases_on `MEM nid visited1`
  >- (* MEM nid visited1: nid from walker call. Use walker hyp. *)
     (first_x_assum (qspecl_then [`visited`, `rd0`, `v0`, `visited1`] mp_tac) >>
      simp[MEM] >>
      disch_then (qspecl_then [`nid`, `iid`, `blk`, `loc`] mp_tac) >> simp[])
  >- (* ~MEM nid visited1: nid from rest recursion. Use IH. *)
     (qpat_x_assum `!w v1 v2 m q. mem_ssa_collect_phi_clobbers w v1 ops = _ /\ _ ==> _`
        (qspecl_then [`walker`, `visited1`, `visited'`, `ms`, `qloc`] mp_tac) >>
      impl_tac
      >- (conj_tac >- simp[] >>
          rpt strip_tac >> res_tac)
      >> disch_then (qspecl_then [`nid`, `iid`, `blk`, `loc`] mp_tac) >> simp[])
QED

(* Part A: walk_clobber returning NONE means no newly-visited MnDef
   completely contains the query location. *)
Triviality walk_clobber_none_sound:
  ∀ms fuel visited current qloc visited'.
    mem_ssa_walk_clobber ms fuel visited current qloc = (NONE, visited') ⇒
    ∀nid iid blk loc.
      MEM nid visited' ∧ ~MEM nid visited ∧
      FLOOKUP ms.ms_nodes nid = SOME (MnDef iid blk loc) ⇒
      ¬completely_contains loc qloc
Proof
  Induct_on `fuel`
  >- (rw[mem_ssa_walk_clobber_def] >> gvs[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `mem_ssa_walk_clobber _ _ _ _ _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [mem_ssa_walk_clobber_def]) >>
  Cases_on `current = 0` >- (simp[] >> strip_tac >> gvs[]) >>
  Cases_on `MEM current visited` >- (simp[] >> strip_tac >> gvs[]) >>
  simp[LET_THM] >>
  Cases_on `FLOOKUP ms.ms_nodes current` >> simp[]
  >- (strip_tac >> gvs[MEM])
  >> Cases_on `x` >> simp[]
  >~ [`MnDef _ _ _`]
  >- (Cases_on `completely_contains m qloc` >- simp[] >>
      Cases_on `FLOOKUP ms.ms_reaching current` >> simp[] >> strip_tac >>
      Cases_on `nid = current` >> gvs[mem_ssa_node_11, MEM] >>
      first_x_assum (qspecl_then [`ms`,`current::visited`,`x`,`qloc`,`visited'`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`nid`,`iid`,`blk`,`loc`] mp_tac) >>
      simp[MEM])
  >~ [`MnUse _ _ _`]
  >- (Cases_on `FLOOKUP ms.ms_reaching current` >> simp[] >> strip_tac >>
      Cases_on `nid = current` >> gvs[mem_ssa_node_distinct, MEM] >>
      first_x_assum (qspecl_then [`ms`,`current::visited`,`x`,`qloc`,`visited'`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`nid`,`iid`,`blk`,`loc`] mp_tac) >>
      simp[MEM])
  (* MnPhi *)
  >> Cases_on `FLOOKUP ms.ms_phi_ops current` >> simp[]
  >- (strip_tac >> Cases_on `nid = current` >> gvs[mem_ssa_node_distinct, MEM])
  >> pairarg_tac >> simp[] >>
  Cases_on `clobbers` >> simp[]
  >- (strip_tac >>
      Cases_on `nid = current` >> gvs[mem_ssa_node_distinct, MEM] >>
      qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
        (mp_tac o MATCH_MP
          (collect_phi_none_sound |> REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
      disch_then (qspecl_then [`ms`, `qloc`] mp_tac) >>
      (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[MEM] >>
                     metis_tac[])) >>
      disch_then (qspecl_then [`nid`, `iid`, `blk`, `loc`] mp_tac) >>
      simp[MEM])
  >> Cases_on `t` >> simp[]
QED

(* --- Part B infrastructure --- *)

(* Build-level: phi_ops entries satisfy predecessor + dominance properties.
   For each (rd, pred) in phi_ops[phi_id]:
   - phi_id is an MnPhi node
   - pred is a CFG predecessor of the phi's block
   - rd = 0 or rd's block dominates pred *)
Triviality block_maps_correct_ids_valid:
  !ms. block_maps_correct ms ==> mem_ssa_ids_valid ms
Proof
  rw[block_maps_correct_def, mem_ssa_ids_valid_def] >> rpt strip_tac
  >- (`MEM aid (fmap_lookup_list ms.ms_block_defs lbl)` by
        simp[cfgDefsTheory.fmap_lookup_list_def] >>
      res_tac >> fs[FLOOKUP_DEF])
  >- (`MEM aid (fmap_lookup_list ms.ms_block_uses lbl)` by
        simp[cfgDefsTheory.fmap_lookup_list_def] >>
      res_tac >> fs[FLOOKUP_DEF])
  >> res_tac >> fs[FLOOKUP_DEF]
QED

(* Phi ops structure invariant: each phi_ops entry has correct shape.
   Packaging as a definition avoids simp/gvs explosion in lifting proofs. *)
Definition phi_ops_structure_ok_def:
  phi_ops_structure_ok ms cfg dom <=>
  (!phi_id ops rd pred.
     FLOOKUP ms.ms_phi_ops phi_id = SOME ops /\ MEM (rd, pred) ops ==>
     (?blk. FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) /\
            MEM pred (cfg_preds_of cfg blk)) /\
     (rd <> 0 ==> rd IN FDOM ms.ms_nodes) /\
     (rd <> 0 /\ cfg_reachable_of cfg pred ==>
        dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes rd))) pred) /\
     (!c. rd <> 0 /\ cfg_reachable_of cfg pred /\
          dominates dom c pred /\
          fmap_lookup_list ms.ms_block_defs c <> [] ==>
          dominates dom c
            (mn_block (THE (FLOOKUP ms.ms_nodes rd)))) /\
     (rd <> 0 /\ (!b. THE (FLOOKUP ms.ms_nodes rd) <> MnPhi b) /\
      fmap_lookup_list ms.ms_block_defs
        (mn_block (THE (FLOOKUP ms.ms_nodes rd))) <> [] ==>
      rd = LAST (fmap_lookup_list ms.ms_block_defs
        (mn_block (THE (FLOOKUP ms.ms_nodes rd))))) /\
     (rd <> 0 /\ (?b. THE (FLOOKUP ms.ms_nodes rd) = MnPhi b) ==>
      fmap_lookup_list ms.ms_block_defs
        (mn_block (THE (FLOOKUP ms.ms_nodes rd))) = []) /\
     (!c. cfg_reachable_of cfg pred /\
          dominates dom c pred /\
          fmap_lookup_list ms.ms_block_defs c <> [] ==>
          rd <> 0))
End

Triviality phi_ops_structure_ok_eq:
  !ms1 ms2 cfg dom.
    ms1.ms_phi_ops = ms2.ms_phi_ops /\
    ms1.ms_nodes = ms2.ms_nodes /\
    ms1.ms_block_defs = ms2.ms_block_defs ==>
    (phi_ops_structure_ok ms1 cfg dom <=> phi_ops_structure_ok ms2 cfg dom)
Proof
  simp[phi_ops_structure_ok_def]
QED

Triviality insert_phi_at_7th_clause:
  !ms fn fuel pred c.
    mem_ssa_ids_valid ms /\ 0 NOTIN FDOM ms.ms_nodes /\
    fuel >= LENGTH (fn_labels fn) /\
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    dominates (dom_analyze (cfg_analyze fn) fn) c pred /\
    fmap_lookup_list ms.ms_block_defs c <> [] ==>
    mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred <> 0
Proof
  rpt strip_tac >>
  mp_tac get_exit_def_nonzero >>
  disch_then (qspecl_then [`ms`, `dom_analyze (cfg_analyze fn) fn`,
    `fn`, `fuel`, `pred`, `c`, `cfg_analyze fn`] mp_tac) >>
  simp[]
QED

(* insert_phi_at preserves phi_ops structure:
   For each phi_ops entry, phi_id -> MnPhi blk, pred in preds of blk,
   and rd dominates pred when rd <> 0. *)
Triviality insert_phi_at_phi_ops_structure:
  !ms cfg dom fuel lbl ms' inserted fn.
    wf_function fn /\ cfg = cfg_analyze fn /\
    dom = dom_analyze cfg fn /\
    fuel >= LENGTH (fn_labels fn) /\
    nodes_fresh ms /\ block_maps_correct ms /\
    0 NOTIN FDOM ms.ms_nodes /\ ms.ms_next_id > 0 /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) /\
    phi_ops_structure_ok ms cfg dom ==>
    phi_ops_structure_ok ms' cfg dom
Proof
  rpt gen_tac >>
  simp[phi_ops_structure_ok_def, mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  (* SOME case: ms' = ms, invariant preserved trivially *)
  TRY (rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  (* NONE case: new phi created.
     insert_phi_at does NOT change ms_block_defs. *)
  `mem_ssa_ids_valid ms` by simp[block_maps_correct_ids_valid] >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `phi_id = ms.ms_next_id` >> simp[]
  >- (
    (* NEW entry: phi_id = ms.ms_next_id *)
    strip_tac >> gvs[MEM_MAP] >>
    qpat_x_assum `!phi_id ops rd pred. _` kall_tac >>
    rpt conj_tac
    >- (
      (* rd <> 0 ==> rd IN FDOM ms'.ms_nodes *)
      strip_tac >>
      DISJ2_TAC >>
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
        (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fuel`, `pred`]
          get_exit_def_valid)) >>
      simp[])
    >- (
      (* rd <> 0 /\ reachable ==> dominates blk(rd) pred *)
      strip_tac >>
      `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
         IN FDOM ms.ms_nodes` by (
        mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
          (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fuel`, `pred`]
            get_exit_def_valid)) >> simp[]) >>
      `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
         < ms.ms_next_id` by (
        qpat_x_assum `nodes_fresh ms`
          (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
        res_tac) >>
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM] get_exit_def_dominates) >>
      disch_then (qspecl_then [`ms`, `fn`, `fuel`, `pred`] mp_tac) >>
      simp[] >> strip_tac >> simp[FLOOKUP_UPDATE])
    >- (
    (* 4th clause: dom c blk(rd) when dom c pred and c has defs *)
    rpt strip_tac >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       IN FDOM ms.ms_nodes` by (
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
        (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fuel`, `pred`]
          get_exit_def_valid)) >> simp[]) >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       < ms.ms_next_id` by (
      qpat_x_assum `nodes_fresh ms`
        (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
      res_tac) >>
    mp_tac get_exit_def_dominated_by_ancestor >>
    disch_then (qspecl_then [`ms`, `dom_analyze (cfg_analyze fn) fn`,
      `fn`, `fuel`, `pred`,
      `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred`,
      `c`, `cfg_analyze fn`] mp_tac) >>
    simp[] >> strip_tac >> simp[FLOOKUP_UPDATE])
    (* 5th clause: nonphi rd = LAST(block_defs(blk(rd))) *)
    >- (
    strip_tac >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       IN FDOM ms.ms_nodes` by (
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
        (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fuel`, `pred`]
          get_exit_def_valid)) >> simp[]) >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       < ms.ms_next_id` by (
      qpat_x_assum `nodes_fresh ms`
        (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
      res_tac) >>
    `FLOOKUP (ms.ms_nodes |+ (ms.ms_next_id, MnPhi lbl))
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred) =
     FLOOKUP ms.ms_nodes
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred)` by
      simp[FLOOKUP_UPDATE] >>
    `?rnode. FLOOKUP ms.ms_nodes
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred) =
       SOME rnode` by metis_tac[flookup_thm] >>
    mp_tac get_exit_def_nonphi_is_last >>
    disch_then (qspecl_then [`fuel`, `ms`,
      `dom_analyze (cfg_analyze fn) fn`, `pred`,
      `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred`,
      `rnode`] mp_tac) >>
    simp[] >> gvs[])
    (* 6th clause: phi rd => block_defs(blk(rd)) = [] *)
    >- (
    strip_tac >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       IN FDOM ms.ms_nodes` by (
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
        (Q.SPECL [`ms`, `dom_analyze (cfg_analyze fn) fn`, `fuel`, `pred`]
          get_exit_def_valid)) >> simp[]) >>
    `mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred
       < ms.ms_next_id` by (
      qpat_x_assum `nodes_fresh ms`
        (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
      res_tac) >>
    `FLOOKUP (ms.ms_nodes |+ (ms.ms_next_id, MnPhi lbl))
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred) =
     FLOOKUP ms.ms_nodes
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred)` by
      simp[FLOOKUP_UPDATE] >>
    `FLOOKUP ms.ms_nodes
       (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred) =
       SOME (MnPhi b)` by (
      Cases_on `FLOOKUP ms.ms_nodes
        (mem_ssa_get_exit_def ms (dom_analyze (cfg_analyze fn) fn) fuel pred)`
      >> gvs[flookup_thm]) >>
    mp_tac get_exit_def_phi_has_no_defs >>
    disch_then (qspecl_then [`fuel`, `ms`,
      `dom_analyze (cfg_analyze fn) fn`, `pred`, `b`] mp_tac) >>
    simp[] >> gvs[mn_block_def])
    (* 7th clause: dom(c, pred) /\ block_defs(c) <> [] ==> rd <> 0 *)
    >> (rpt strip_tac >>
        mp_tac (Q.SPECL [`ms`, `fn`, `fuel`, `pred`, `c`]
          insert_phi_at_7th_clause) >>
        simp[]))
  (* OLD entry: phi_id <> ms.ms_next_id *)
  >> strip_tac >> res_tac >>
  qpat_x_assum `!phi_id ops rd pred. _` kall_tac >>
  sg `rd = 0 \/ rd < ms.ms_next_id`
  >- (Cases_on `rd = 0` >> simp[] >>
      sg `rd IN FDOM ms.ms_nodes` >- gvs[] >>
      qpat_x_assum `nodes_fresh ms`
        (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
      res_tac) >>
  simp[FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  metis_tac[]
QED

Triviality fupdate_preserves_old_lookup:
  !fm (k:num) v k' v'. FLOOKUP fm k' = SOME v' /\ k' < k ==>
    FLOOKUP (fm |+ (k, v)) k' = SOME v'
Proof
  rpt strip_tac >> `k' <> k` by DECIDE_TAC >> simp[FLOOKUP_UPDATE]
QED

Triviality insert_phi_at_preserves_block_maps_correct:
  !ms cfg dom fuel lbl ms' inserted.
    nodes_fresh ms /\ block_maps_correct ms /\
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) ==>
    block_maps_correct ms'
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  (* SOME case: ms' = ms, trivial *)
  TRY (rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  (* NONE case: new phi node. Expand block_maps_correct for subgoals *)
  simp[block_maps_correct_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  (* Helper: for each branch, old lookups preserved via freshness *)
  >> TRY (
    (* defs and uses branches: identical *)
    fs[block_maps_correct_def] >> res_tac >>
    qexists_tac `node` >> simp[] >>
    irule fupdate_preserves_old_lookup >> simp[] >>
    qpat_x_assum `!lbl aid. MEM aid (fmap_lookup_list ms.ms_block_defs _) ==> _` kall_tac >>
    qpat_x_assum `!lbl aid. MEM aid (fmap_lookup_list ms.ms_block_uses _) ==> _` kall_tac >>
    qpat_x_assum `!lbl phi_id. _ ==> _` kall_tac >>
    fs[nodes_fresh_def, flookup_thm]
    >> NO_TAC)
  (* phis: Cases_on lbl' = lbl *)
  >> Cases_on `lbl' = lbl` >> gvs[FLOOKUP_UPDATE]
  (* lbl' <> lbl: old phi entry, preserved by fupdate *)
  >> `FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi lbl')` by (
    fs[block_maps_correct_def])
  >> `phi_id < ms.ms_next_id` by (
    qpat_x_assum `block_maps_correct _` kall_tac >>
    qpat_x_assum `nodes_fresh ms`
      (strip_assume_tac o REWRITE_RULE [nodes_fresh_def]) >>
    res_tac >> fs[flookup_thm])
  >> simp[]
QED

Triviality process_frontiers_preserves_block_maps_correct:
  !fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms /\ block_maps_correct ms /\
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ==>
    block_maps_correct ms'
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  metis_tac[insert_phi_at_preserves_fresh,
            insert_phi_at_preserves_block_maps_correct]
QED

Triviality process_frontiers_preserves_block_defs_are_defs:
  !fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) ==>
    (!lbl' aid. MEM aid (fmap_lookup_list ms'.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms'.ms_nodes aid = SOME (MnDef iid lbl' loc))
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`, `rest`] >> simp[] >>
  metis_tac[insert_phi_at_preserves_fresh,
            insert_phi_at_preserves_block_defs_are_defs]
QED

Triviality process_frontiers_preserves_phi_ops_structure:
  !fronts ms cfg dom fuel ms' wl fn.
    wf_function fn /\ cfg = cfg_analyze fn /\
    dom = dom_analyze cfg fn /\
    fuel >= LENGTH (fn_labels fn) /\
    nodes_fresh ms /\ block_maps_correct ms /\
    0 NOTIN FDOM ms.ms_nodes /\ ms.ms_next_id > 0 /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) /\
    phi_ops_structure_ok ms cfg dom ==>
    phi_ops_structure_ok ms' cfg dom
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  last_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `fuel`, `rest`] >> simp[] >>
  rpt conj_tac
  >- metis_tac[insert_phi_at_preserves_fresh]
  >- metis_tac[insert_phi_at_preserves_block_maps_correct]
  >- metis_tac[insert_phi_at_preserves_zero_not_in_nodes]
  >- metis_tac[insert_phi_at_preserves_zero_not_in_nodes]
  >- metis_tac[insert_phi_at_preserves_fresh,
               insert_phi_at_preserves_block_defs_are_defs]
  >> match_mp_tac (GEN_ALL insert_phi_at_phi_ops_structure) >>
  qexistsl_tac [`ms`, `fuel`, `h`, `inserted`, `fn`] >>
  simp[]
QED

Triviality insert_phis_preserves_phi_ops_structure:
  !ms cfg dom ef fuel wl fn.
    wf_function fn /\ cfg = cfg_analyze fn /\
    dom = dom_analyze cfg fn /\
    ef >= LENGTH (fn_labels fn) /\
    mem_ssa_ids_valid ms /\ nodes_fresh ms /\
    block_maps_correct ms /\
    0 NOTIN FDOM ms.ms_nodes /\ ms.ms_next_id > 0 /\
    (!lbl' aid. MEM aid (fmap_lookup_list ms.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms.ms_nodes aid = SOME (MnDef iid lbl' loc)) /\
    phi_ops_structure_ok ms cfg dom ==>
    phi_ops_structure_ok
      (mem_ssa_insert_phis ms cfg dom ef fuel wl) cfg dom
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >> rpt conj_tac >>
  TRY (rpt gen_tac >> strip_tac >> simp[] >> NO_TAC) >>
  (* b::wl step case *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >>
  strip_tac >>
  (* Substitute cfg/dom equations early to unify forms *)
  qpat_x_assum `cfg = _` (SUBST_ALL_TAC) >>
  qpat_x_assum `dom = _` (SUBST_ALL_TAC) >>
  `nodes_fresh ms' /\ block_maps_correct ms'` by
    metis_tac[process_frontiers_preserves_fresh,
              process_frontiers_preserves_block_maps_correct] >>
  `mem_ssa_ids_valid ms'` by
    metis_tac[process_frontiers_preserves_ids_valid] >>
  `0 NOTIN FDOM ms'.ms_nodes /\ ms'.ms_next_id > 0` by
    metis_tac[process_frontiers_preserves_zero_not_in_nodes] >>
  sg `!lbl' aid. MEM aid (fmap_lookup_list ms'.ms_block_defs lbl') ==>
       ?iid loc. FLOOKUP ms'.ms_nodes aid = SOME (MnDef iid lbl' loc)`
  >- (match_mp_tac (GEN_ALL
        (SIMP_RULE (srw_ss()) [LET_THM]
          process_frontiers_preserves_block_defs_are_defs)) >>
      metis_tac[]) >>
  (* Apply IH — specialize fn' := fn to make cfg/dom equations trivial *)
  first_x_assum (qspecl_then [`ms'`, `new_wl`] mp_tac) >>
  simp[] >>
  disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  (* Prove phi_ops_structure for ms' via process_frontiers *)
  mp_tac (GEN_ALL process_frontiers_preserves_phi_ops_structure) >>
  disch_then (qspecl_then [`frontier_of (dom_analyze (cfg_analyze fn) fn) b`,
    `ms`, `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
    `ef`, `ms'`, `new_wl`, `fn`] mp_tac) >>
  simp[]
QED

Triviality process_blocks_phi_ops_structure_ok_init:
  !bp fn addr_sp.
    phi_ops_structure_ok
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
         (cfg_analyze fn).cfg_dfs_pre)
      (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
Proof
  simp[phi_ops_structure_ok_def, process_blocks_fields,
       mem_ssa_init_def, FLOOKUP_DEF]
QED

Triviality insert_phis_phase_phi_ops_structure:
  !bp fn addr_sp.
    wf_function fn ==>
    phi_ops_structure_ok
      (mem_ssa_insert_phis
         (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
            (cfg_analyze fn).cfg_dfs_pre)
         (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         (LENGTH (fn_labels fn))
         (LENGTH (fn_labels fn) * LENGTH (fn_labels fn))
         (MAP FST (fmap_to_alist
            (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
               (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)))
      (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
Proof
  rpt strip_tac >>
  match_mp_tac (GEN_ALL insert_phis_preserves_phi_ops_structure) >>
  qexists_tac `fn` >>
  simp[phase1_block_maps_correct, phase1_fresh, phase1_ids_valid,
       process_blocks_phi_ops_structure_ok_init] >>
  conj_tac
  >- (spose_not_then ASSUME_TAC >> gvs[] >>
      mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`,
        `fn`, `mem_ssa_init`, `1`, `0`] process_blocks_ids_ge) >>
      simp[mem_ssa_init_def, FDOM_FEMPTY]) >>
  conj_tac
  >- (mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`,
        `fn`, `mem_ssa_init`] process_blocks_next_id_mono) >>
      simp[mem_ssa_init_def]) >>
  match_mp_tac process_blocks_block_defs_are_defs >>
  simp[mem_ssa_init_def, nodes_fresh_def, FLOOKUP_DEF,
       fmap_lookup_list_fempty]
QED

Triviality build_phi_ops_structure:
  !bp fn addr_sp.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn ==>
    phi_ops_structure_ok ms (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
Proof
  rpt gen_tac >> simp[LET_THM] >>
  PURE_REWRITE_TAC[mem_ssa_build_def, LET_THM] >> BETA_TAC >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `phi_ops_structure_ok (mem_ssa_remove_redundant_phis (mem_ssa_connect_all ms_ip _ _ _ _) _) _ _` >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] (iffLR phi_ops_structure_ok_eq)) >>
  qexists_tac `ms_ip` >>
  REWRITE_TAC[connect_all_fields, remove_redundant_phis_fields] >>
  simp[Abbr `ms_ip`, insert_phis_phase_phi_ops_structure]
QED

(* --- phi_has_ops: every MnPhi node has phi_ops with MAP SND = cfg_preds --- *)

Definition phi_has_ops_def:
  phi_has_ops ms cfg <=>
  !q blk. FLOOKUP ms.ms_nodes q = SOME (MnPhi blk) ==>
    ?ops. FLOOKUP ms.ms_phi_ops q = SOME ops /\
          MAP SND ops = cfg_preds_of cfg blk
End

Triviality phi_has_ops_eq:
  !ms1 ms2 cfg.
    ms1.ms_nodes = ms2.ms_nodes /\
    ms1.ms_phi_ops = ms2.ms_phi_ops ==>
    (phi_has_ops ms1 cfg <=> phi_has_ops ms2 cfg)
Proof
  simp[phi_has_ops_def]
QED

Triviality insert_phi_at_phi_has_ops:
  !ms cfg dom fuel lbl ms' inserted.
    nodes_fresh ms /\
    mem_ssa_insert_phi_at ms cfg dom fuel lbl = (ms', inserted) /\
    phi_has_ops ms cfg ==>
    phi_has_ops ms' cfg
Proof
  rpt gen_tac >> simp[phi_has_ops_def] >> strip_tac >>
  Cases_on `FLOOKUP ms.ms_block_phis lbl` >>
  gvs[mem_ssa_insert_phi_at_def] >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `q = ms.ms_next_id` >> simp[] >>
  strip_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF]
QED

Triviality process_frontiers_phi_has_ops:
  !fronts ms cfg dom fuel ms' wl.
    nodes_fresh ms /\
    mem_ssa_process_frontiers ms cfg dom fuel fronts = (ms', wl) /\
    phi_has_ops ms cfg ==>
    phi_has_ops ms' cfg
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `dom`, `fuel`, `rest`] >> simp[] >>
  metis_tac[insert_phi_at_preserves_fresh,
            insert_phi_at_phi_has_ops]
QED

Triviality insert_phis_phi_has_ops:
  !ms cfg dom ef fuel wl.
    mem_ssa_ids_valid ms /\ nodes_fresh ms /\
    phi_has_ops ms cfg ==>
    phi_has_ops (mem_ssa_insert_phis ms cfg dom ef fuel wl) cfg
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >> rpt conj_tac >>
  TRY (rpt gen_tac >> strip_tac >> simp[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`ms'`, `new_wl`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[process_frontiers_preserves_fresh,
            process_frontiers_preserves_ids_valid,
            process_frontiers_phi_has_ops]
QED

Triviality process_blocks_phi_has_ops_init:
  !bp fn addr_sp.
    phi_has_ops
      (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
         (cfg_analyze fn).cfg_dfs_pre)
      (cfg_analyze fn)
Proof
  simp[phi_has_ops_def, process_blocks_fields,
       mem_ssa_init_def, FLOOKUP_DEF] >>
  rpt gen_tac >>
  mp_tac (Q.SPECL [`(cfg_analyze fn).cfg_dfs_pre`, `bp`, `addr_sp`,
    `fn`, `mem_ssa_init`, `q`, `blk`] process_blocks_no_new_phi) >>
  simp[mem_ssa_init_def, FLOOKUP_DEF]
QED

Triviality insert_phis_phase_phi_has_ops:
  !bp fn addr_sp.
    phi_has_ops
      (mem_ssa_insert_phis
         (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
            (cfg_analyze fn).cfg_dfs_pre)
         (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         (LENGTH (fn_labels fn))
         (LENGTH (fn_labels fn) * LENGTH (fn_labels fn))
         (MAP FST (fmap_to_alist
            (mem_ssa_process_blocks bp addr_sp fn mem_ssa_init
               (cfg_analyze fn).cfg_dfs_pre).ms_block_defs)))
      (cfg_analyze fn)
Proof
  rpt strip_tac >>
  match_mp_tac (GEN_ALL insert_phis_phi_has_ops) >>
  simp[phase1_fresh, phase1_ids_valid,
       process_blocks_phi_has_ops_init]
QED

Triviality build_phi_has_ops:
  !bp fn addr_sp.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    phi_has_ops ms (cfg_analyze fn)
Proof
  rpt gen_tac >> simp[LET_THM] >>
  PURE_REWRITE_TAC[mem_ssa_build_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `phi_has_ops (mem_ssa_remove_redundant_phis (mem_ssa_connect_all ms_ip _ _ _ _) _) _` >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] (iffLR phi_has_ops_eq)) >>
  qexists_tac `ms_ip` >>
  REWRITE_TAC[connect_all_fields, remove_redundant_phis_fields] >>
  simp[Abbr `ms_ip`, insert_phis_phase_phi_has_ops]
QED

(* --- Frontier reachability helpers --- *)

Triviality walk_to_idom_bounded:
  !fuel idom target runner df n y.
    MEM y (fmap_lookup_list (walk_to_idom idom target runner df fuel) n) ==>
    y = target \/ MEM y (fmap_lookup_list df n)
Proof
  Induct >> simp[dominatorDefsTheory.walk_to_idom_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP idom target` >> simp[] >>
  Cases_on `runner = x` >> simp[] >>
  simp[LET_THM] >> Cases_on `FLOOKUP idom runner` >> simp[]
  >- (strip_tac >> Cases_on `n = runner` >>
      fs[cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_UPDATE,
         cfgHelpersTheory.mem_set_insert])
  >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `n = runner` >>
  fs[cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_UPDATE,
     cfgHelpersTheory.mem_set_insert]
QED

Triviality inner_foldl_bounded:
  !preds idom target df fuel n y.
    MEM y (fmap_lookup_list
      (FOLDL (\df' pred. walk_to_idom idom target pred df' fuel) df preds) n) ==>
    y = target \/ MEM y (fmap_lookup_list df n)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule walk_to_idom_bounded >> simp[]
QED

Triviality compute_df_bounded_aux:
  !order df cfg idom fuel n y.
    MEM y (fmap_lookup_list (FOLDL (\df lbl. let preds = cfg_preds_of cfg lbl in
      if LENGTH preds <= 1 then df
      else FOLDL (\df' pred. walk_to_idom idom lbl pred df' fuel) df preds) df order) n) ==>
    MEM y order \/ MEM y (fmap_lookup_list df n)
Proof
  Induct >> simp[] >> rpt gen_tac >> simp[LET_THM] >>
  strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg h) <= 1`
  >- (first_x_assum (qspecl_then [`df`, `cfg`, `idom`, `fuel`, `n`, `y`] mp_tac) >>
      gvs[] >> metis_tac[MEM])
  >> (first_x_assum (qspecl_then
       [`FOLDL (\df' pred. walk_to_idom idom h pred df' fuel) df
           (cfg_preds_of cfg h)`, `cfg`, `idom`, `fuel`, `n`, `y`] mp_tac) >>
      gvs[] >> strip_tac
      >- metis_tac[MEM]
      >> drule inner_foldl_bounded >> metis_tac[MEM])
QED

Triviality compute_df_bounded:
  !order cfg idom fuel n y.
    MEM y (fmap_lookup_list (compute_df cfg idom order fuel) n) ==>
    MEM y order
Proof
  rpt gen_tac >> simp[dominatorDefsTheory.compute_df_def, LET_THM] >>
  strip_tac >>
  drule (SIMP_RULE (srw_ss()) [LET_THM] compute_df_bounded_aux) >>
  simp[cfgDefsTheory.fmap_lookup_list_def, FLOOKUP_DEF]
QED

Triviality da_frontier_bounded:
  !cfg fn n y.
    MEM y (fmap_lookup_list (dom_analyze cfg fn).da_frontier n) ==>
    MEM y cfg.cfg_dfs_post
Proof
  rpt gen_tac >>
  simp[dominatorDefsTheory.dom_analyze_def, LET_THM] >>
  metis_tac[compute_df_bounded]
QED

(* DFS post-order elements are reachable *)
Triviality dfs_post_reachable:
  !fn lbl. wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_post ==>
    cfg_reachable_of (cfg_analyze fn) lbl
Proof
  rpt gen_tac >> strip_tac >>
  `MEM lbl (fn_labels fn)` by
    metis_tac[dfAnalyzeProofsTheory.cfg_dfs_post_subset_fn_labels] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  simp[cfgDefsTheory.cfg_reachable_of_def,
       cfgHelpersTheory.cfg_analyze_reachable] >>
  Cases_on `entry_block fn`
  >- (fs[cfgHelpersTheory.cfg_analyze_dfs_post])
  >> fs[venomInstTheory.fn_labels_def,
        cfgHelpersTheory.cfg_analyze_dfs_post] >>
  `FLOOKUP (build_reachable (MAP (\bb. bb.bb_label) fn.fn_blocks)
     (FST (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label))) lbl =
   SOME (MEM lbl (FST (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label)))` by
    (irule cfgHelpersTheory.flookup_build_reachable >> simp[]) >>
  simp[] >>
  `set (FST (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label)) =
   set [] UNION set (SND (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label))`
    by metis_tac[cfgHelpersTheory.dfs_post_walk_visited_eq] >>
  gvs[EXTENSION]
QED

(* --- Phi block reachability preservation chain --- *)

Triviality insert_phi_at_preserves_phi_block_reachable:
  !ms cfg dom fuel blk_lbl ms' inserted order.
    mem_ssa_insert_phi_at ms cfg dom fuel blk_lbl = (ms', inserted) /\
    MEM blk_lbl order /\
    (!phi_id blk. FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) ==>
       MEM blk order) ==>
    (!phi_id blk. FLOOKUP ms'.ms_nodes phi_id = SOME (MnPhi blk) ==>
       MEM blk order)
Proof
  rpt gen_tac >> simp[mem_ssa_insert_phi_at_def] >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  Cases_on `phi_id = ms.ms_next_id` >>
  gvs[FLOOKUP_UPDATE] >> res_tac
QED

Triviality process_frontiers_preserves_phi_block_reachable:
  !frontiers ms cfg dom fuel ms' new_wl order.
    mem_ssa_process_frontiers ms cfg dom fuel frontiers = (ms', new_wl) /\
    EVERY (\blk. MEM blk order) frontiers /\
    (!phi_id blk. FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) ==>
       MEM blk order) ==>
    (!phi_id blk. FLOOKUP ms'.ms_nodes phi_id = SOME (MnPhi blk) ==>
       MEM blk order)
Proof
  Induct >> simp[mem_ssa_process_frontiers_def] >>
  rpt gen_tac >> simp[LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> fs[] >>
  last_x_assum match_mp_tac >>
  qexistsl_tac [`ms1`, `cfg`, `dom`, `fuel`, `rest`] >> simp[] >>
  metis_tac[insert_phi_at_preserves_phi_block_reachable]
QED

Triviality insert_phis_preserves_phi_block_reachable:
  !ms cfg dom ef fuel wl fn.
    wf_function fn /\ cfg = cfg_analyze fn /\
    dom = dom_analyze cfg fn ==>
    (!phi_id blk. FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) ==>
       MEM blk cfg.cfg_dfs_post) ==>
    (!phi_id blk.
       FLOOKUP (mem_ssa_insert_phis ms cfg dom ef fuel wl).ms_nodes
         phi_id = SOME (MnPhi blk) ==>
       MEM blk cfg.cfg_dfs_post)
Proof
  recInduct (fetch "memSSADefs" "mem_ssa_insert_phis_ind") >>
  simp[mem_ssa_insert_phis_def] >> rpt conj_tac >>
  TRY (rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pairarg_tac >> simp[] >>
  strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [`ms'`, `new_wl`] mp_tac) >>
  simp[] >>
  disch_then (qspec_then `fn` mp_tac) >> simp[] >>
  disch_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac (GEN_ALL process_frontiers_preserves_phi_block_reachable) >>
  qexistsl_tac [`frontier_of (dom_analyze (cfg_analyze fn) fn) b`,
    `ms`, `cfg_analyze fn`, `dom_analyze (cfg_analyze fn) fn`,
    `ef`, `new_wl`] >> simp[] >>
  simp[dominatorDefsTheory.frontier_of_def, EVERY_MEM] >>
  rpt strip_tac >> TRY (drule da_frontier_bounded >> simp[]) >> res_tac
QED

(* Build-level: phi block is reachable *)
Triviality build_phi_block_reachable:
  !bp fn addr_sp phi_id blk.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) ==>
    cfg_reachable_of (cfg_analyze fn) blk
Proof
  rpt gen_tac >> simp[LET_THM, mem_ssa_build_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_ssa_remove_redundant_phis ms_ca _` >>
  qmatch_asmsub_abbrev_tac `mem_ssa_connect_all ms_ip _ _ _ _` >>
  qmatch_asmsub_abbrev_tac `mem_ssa_insert_phis ms_pb _ _ _ _ _` >>
  `ms_ca.ms_nodes = ms_ip.ms_nodes` by
    simp[connect_all_fields, Abbr `ms_ca`] >>
  `(mem_ssa_remove_redundant_phis ms_ca
      (fmap_to_alist ms_ca.ms_block_phis)).ms_nodes = ms_ca.ms_nodes` by
    simp[remove_redundant_phis_fields] >>
  fs[] >>
  `MEM blk (cfg_analyze fn).cfg_dfs_post` suffices_by
    metis_tac[dfs_post_reachable] >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM]
           insert_phis_preserves_phi_block_reachable) >>
  disch_then (qspecl_then [`ms_pb`,
    `LENGTH (fn_labels fn)`,
    `LENGTH (fn_labels fn) * LENGTH (fn_labels fn)`,
    `MAP FST (fmap_to_alist ms_pb.ms_block_defs)`, `fn`] mp_tac) >>
  simp[Abbr `ms_ip`] >>
  disch_tac >>
  `!phi_id' blk'. FLOOKUP ms_pb.ms_nodes phi_id' = SOME (MnPhi blk') ==>
     MEM blk' (cfg_analyze fn).cfg_dfs_post` by
    (simp[Abbr `ms_pb`] >> rpt strip_tac >>
     drule process_blocks_no_new_phi >>
     simp[mem_ssa_init_def, FLOOKUP_DEF]) >>
  res_tac
QED

(* Any node in mem_ssa_build output has a reachable block *)
Triviality build_node_block_reachable:
  !bp fn addr_sp aid node.
    wf_function fn /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_nodes aid = SOME node ==>
    cfg_reachable_of (cfg_analyze fn) (mn_block node)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?blk. node = MnPhi blk`
  >- (gvs[mn_block_def] >>
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM] build_phi_block_reachable) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `aid`, `blk`] mp_tac) >>
      simp[])
  >- (mp_tac (Q.SPECL [`cfg_analyze fn`,
        `dom_analyze (cfg_analyze fn) fn`,
        `bp`, `fn`, `addr_sp`,
        `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp`,
        `aid`, `node`] build_non_phi_reachable) >>
      simp[] >> gvs[])
QED

(* collect_phi_visits: if the walker visits def_id on at least one branch
   (when def_id not yet in visited), then collect_phi_clobbers puts
   def_id in the final visited. *)
Triviality collect_phi_visits:
  !ops (walker : num list -> num -> num option # num list)
   visited visited' def_id.
    mem_ssa_collect_phi_clobbers walker visited ops = ([], visited') /\
    (!v rd r v'. walker v rd = (r, v') ==> !x. MEM x v ==> MEM x v') /\
    (?rd0 pred0. MEM (rd0, pred0) ops /\
       !vis vis'. ~MEM def_id vis /\ walker vis rd0 = (NONE, vis') ==>
         MEM def_id vis') /\
    ~MEM def_id visited ==>
    MEM def_id visited'
Proof
  Induct >- rw[mem_ssa_collect_phi_clobbers_def] >>
  rpt gen_tac >>
  Cases_on `h` >>
  rename1 `(op_rd, op_pred)` >>
  simp[mem_ssa_collect_phi_clobbers_def, LET_THM] >>
  Cases_on `walker visited op_rd` >>
  rename1 `walker visited op_rd = (wr_res, wr_vis)` >>
  Cases_on `mem_ssa_collect_phi_clobbers walker wr_vis ops` >>
  rename1 `_ = (cr_res, cr_vis)` >>
  simp[] >> disch_tac >>
  (* Extract everything from the conjunction, then kill the original *)
  `?rd0 pred0. MEM (rd0, pred0) ((op_rd,op_pred)::ops) /\
    (!vis vis'. ~MEM def_id vis /\ walker vis rd0 = (NONE, vis') ==>
       MEM def_id vis')` by (fs[] >> metis_tac[]) >>
  `~MEM def_id visited` by fs[] >>
  `!v rd r v'. walker v rd = (r,v') ==> !x. MEM x v ==> MEM x v'`
    by fs[] >>
  `wr_res = NONE /\ cr_res = [] /\ cr_vis = visited'` by (
    `(case wr_res of NONE => (cr_res,cr_vis)
       | SOME c => (c::cr_res,cr_vis)) = ([],visited')` by fs[] >>
    Cases_on `wr_res` >> fs[]) >>
  (* Kill the original big conjunction — we've extracted everything *)
  qpat_x_assum `(case _ of NONE => _ | SOME _ => _) = _ /\ _` kall_tac >>
  (* Case-split on whether rd0 is in head or tail BEFORE gvs *)
  `rd0 = op_rd \/ MEM (rd0, pred0) ops` by fs[MEM] >>
  qpat_x_assum `MEM _ (_::_)` kall_tac
  (* Head case: rd0 = op_rd *)
  >- (
    qpat_x_assum `!w v1 v2 v3. mem_ssa_collect_phi_clobbers _ _ _ = _ /\ _ ==> _` kall_tac >>
    `MEM def_id wr_vis` by (
      qpat_x_assum `!v rd r v'. walker v rd = _ ==> _` kall_tac >>
      res_tac >> gvs[]) >>
    gvs[] >>
    qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
      (mp_tac o MATCH_MP (collect_phi_visited_mono
        |> REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
    disch_then drule >> disch_then (qspec_then `def_id` mp_tac) >> simp[])
  (* Tail case: MEM (rd0, pred0) ops *)
  >> (
    gvs[] >>
    Cases_on `MEM def_id wr_vis`
    >- (
      qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
        (mp_tac o MATCH_MP (collect_phi_visited_mono
          |> REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
      disch_then drule >> disch_then (qspec_then `def_id` mp_tac) >> simp[])
    >> (
      first_x_assum (qspecl_then [`walker`, `wr_vis`, `cr_vis`, `def_id`] mp_tac) >>
      simp[] >> disch_then irule >>
      conj_tac >| [
        first_assum ACCEPT_TAC,
        qexistsl_tac [`rd0`, `pred0`] >> simp[] >>
        first_assum ACCEPT_TAC]))
QED

(* find_prev_def returns a value from ms_inst_def *)
Triviality find_prev_def_in_inst_def:
  !ms insts target x.
    mem_ssa_find_prev_def ms insts target = SOME x ==>
    ?iid. FLOOKUP ms.ms_inst_def iid = SOME x
Proof
  Induct_on `insts` >> rw[mem_ssa_find_prev_def_def] >>
  Cases_on `mem_ssa_find_prev_def ms insts target` >> gvs[] >>
  metis_tac[]
QED

(* If a strictly-dominating MnDef exists, the reaching pointer is nonzero.
   Proof: rd = reaching_in_block(...) via connect_all_reaching_characterize.
   reaching_in_block returns 0 only if no defs/phis on the idom chain.
   But sdom def_blk access_blk means def_blk has defs and is on the chain. *)
Triviality build_sdom_reaching_nonzero:
  !bp fn addr_sp access_id rd def_id def_iid def_blk def_loc.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching access_id = SOME rd /\
    access_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes access_id) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
      (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ==>
    rd <> 0
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  (* Immediately establish reachability *)
  `cfg_reachable_of (cfg_analyze fn) (mn_block (THE (FLOOKUP
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_nodes access_id)))` by (
    mp_tac (SIMP_RULE (srw_ss()) [] build_reaching_reachable) >>
    disch_then (qspecl_then [`dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`,
      `addr_sp`, `access_id`, `0`] mp_tac) >> simp[]) >>
  `?access_node. FLOOKUP (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes access_id =
      SOME access_node` by fs[flookup_thm] >>
  `THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes access_id) =
      access_node` by simp[] >> gvs[] >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `dom = dom_analyze cfg fn` >>
  qabbrev_tac `ms = mem_ssa_build cfg dom bp fn addr_sp` >>
  qabbrev_tac `access_blk = mn_block access_node` >>
  (* entry block exists *)
  `?bb. entry_block fn = SOME bb` by
    (simp[venomInstTheory.entry_block_def] >>
     fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  (* sdom def_blk access_blk => access_blk <> entry *)
  `access_blk <> bb.bb_label` by (
    strip_tac >> gvs[] >>
    gvs[dominatorDefsTheory.strict_dominates_def] >>
    qpat_x_assum `Abbrev (ms = _)` kall_tac >>
    qpat_x_assum `Abbrev (dom = _)`
      (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    qpat_x_assum `Abbrev (cfg = _)`
      (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    `cfg_reachable_of (cfg_analyze fn) def_blk` by
      metis_tac[SIMP_RULE (srw_ss()) [LET_THM] dominates_reachable] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) bb.bb_label def_blk` by (
      irule (SIMP_RULE (srw_ss()) [LET_THM] dom_entry_dominates_all) >>
      simp[]) >>
    metis_tac[SIMP_RULE (srw_ss()) [LET_THM] dominates_antisym]) >>
  (* idom exists for access_blk *)
  `?idom_lbl. idom_of dom access_blk = SOME idom_lbl` by (
    mp_tac idom_exists >>
    disch_then (qspecl_then [`fn`, `cfg`, `bb`, `access_blk`] mp_tac) >>
    simp[Abbr `dom`, LET_THM, Abbr `cfg`]) >>
  (* Unpack build: rd = reaching_in_block ms2 ... *)
  qpat_x_assum `FLOOKUP ms.ms_reaching access_id = SOME 0` mp_tac >>
  qpat_x_assum `FLOOKUP ms.ms_nodes access_id = SOME access_node` mp_tac >>
  simp[Abbr `ms`, mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
       connect_all_fields] >>
  qmatch_goalsub_abbrev_tac `mem_ssa_connect_all ms2` >>
  strip_tac >> strip_tac >>
  drule connect_all_reaching_characterize >> strip_tac
  >- gvs[Abbr `ms2`, insert_phis_fields, process_blocks_fields,
         mem_ssa_init_def]
  >> gvs[] >>
  qpat_x_assum `mem_ssa_reaching_in_block _ _ _ _ _ _ = 0` mp_tac >>
  simp[mem_ssa_reaching_in_block_def] >>
  `?bbb. lookup_block access_blk fn.fn_blocks = SOME bbb` by (
    `MEM access_blk (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
      metis_tac[cfg_analyze_reachable_in_labels, venomInstTheory.fn_labels_def] >>
    drule dfAnalyzeProofsTheory.lookup_block_exists >> strip_tac >> metis_tac[]) >>
  simp[] >>
  Cases_on `mem_ssa_find_prev_def ms2 bbb.bb_instructions (mn_inst_id access_node)` >>
  simp[]
  >- (
    Cases_on `FLOOKUP ms2.ms_block_phis access_blk` >> simp[]
    >- (
      Cases_on `idom_of dom access_blk` >> simp[]
      >- gvs[]
      >> strip_tac >>
      `x = idom_lbl` by gvs[] >> gvs[] >>
      `mem_ssa_ids_valid ms2` by
        simp[Abbr `ms2`, phase12_ids_valid, Abbr `cfg`, Abbr `dom`] >>
      `0 NOTIN FDOM ms2.ms_nodes` by (
        simp[Abbr `ms2`] >>
        mp_tac (SIMP_RULE (srw_ss()) [] build_zero_not_in_nodes) >>
        simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
             connect_all_fields, Abbr `cfg`, Abbr `dom`]) >>
      `dominates dom def_blk idom_lbl` by (
        mp_tac (SIMP_RULE (srw_ss()) [LET_THM] idom_is_immediate) >>
        disch_then (qspecl_then [`fn`, `access_blk`, `idom_lbl`] mp_tac) >>
        impl_tac >- simp[Abbr `cfg`] >>
        simp[Abbr `dom`, Abbr `cfg`] >> strip_tac >>
        Cases_on `def_blk = idom_lbl` >> gvs[]
        >- (irule (SIMP_RULE (srw_ss()) [LET_THM] dom_self) >> simp[] >>
            fs[dominatorDefsTheory.strict_dominates_def] >>
            metis_tac[SIMP_RULE (srw_ss()) [LET_THM] dominates_reachable,
                      cfg_analyze_reachable_in_labels])
        >> first_x_assum (qspec_then `def_blk` mp_tac) >> simp[]) >>
      `cfg_reachable_of cfg idom_lbl` by (
        mp_tac (SIMP_RULE (srw_ss()) [LET_THM] idom_is_immediate) >>
        disch_then (qspecl_then [`fn`, `access_blk`, `idom_lbl`] mp_tac) >>
        impl_tac >- simp[Abbr `cfg`] >>
        simp[Abbr `dom`, Abbr `cfg`] >> strip_tac >>
        gvs[dominatorDefsTheory.strict_dominates_def] >>
        metis_tac[SIMP_RULE (srw_ss()) [LET_THM] dominates_reachable]) >>
      `fmap_lookup_list ms2.ms_block_defs def_blk <> []` by (
        qpat_assum `FLOOKUP (mem_ssa_build _ _ _ _ _).ms_nodes def_id = _`
          (mp_tac o MATCH_MP build_MnDef_block_defs_nonempty) >>
        qpat_x_assum `Abbrev (ms2 = _)`
          (SUBST1_TAC o
           SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]) >>
        PURE_REWRITE_TAC [REWRITE_RULE [GSYM arithmeticTheory.EXP_2]
          build_block_defs_eq] >>
        simp[]) >>
      mp_tac get_exit_def_nonzero >>
      disch_then (qspecl_then [`ms2`, `dom`, `fn`,
        `LENGTH (fn_labels fn)`, `idom_lbl`, `def_blk`, `cfg`] mp_tac) >>
      simp[Abbr `dom`, Abbr `cfg`, LET_THM])
    (* block_phis SOME case: phi_id <> 0 *)
    >> (
      CCONTR_TAC >> gvs[] >>
      `mem_ssa_ids_valid ms2` by
        simp[Abbr `ms2`, phase12_ids_valid, Abbr `cfg`, Abbr `dom`] >>
      `0 NOTIN FDOM ms2.ms_nodes` by (
        simp[Abbr `ms2`] >>
        mp_tac (SIMP_RULE (srw_ss()) [] build_zero_not_in_nodes) >>
        simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
             connect_all_fields, Abbr `cfg`, Abbr `dom`]) >>
      qpat_x_assum `mem_ssa_ids_valid _` mp_tac >>
      simp[mem_ssa_ids_valid_def] >> rpt strip_tac >>
      res_tac >> metis_tac[flookup_thm]))
  (* find_prev_def SOME case: result <> 0 *)
  >> (
    CCONTR_TAC >> gvs[] >>
    drule find_prev_def_in_inst_def >> strip_tac >>
    `mem_ssa_inst_maps_consistent ms2` by
      simp[Abbr `ms2`, phase12_inst_maps, Abbr `cfg`, Abbr `dom`] >>
    `0 NOTIN FDOM ms2.ms_nodes` by (
      simp[Abbr `ms2`] >>
      mp_tac (SIMP_RULE (srw_ss()) [] build_zero_not_in_nodes) >>
      simp[mem_ssa_build_def, LET_THM, remove_redundant_phis_fields,
           connect_all_fields, Abbr `cfg`, Abbr `dom`]) >>
    qpat_x_assum `mem_ssa_inst_maps_consistent _` mp_tac >>
    simp[mem_ssa_inst_maps_consistent_def] >> rpt strip_tac >>
    res_tac >> metis_tac[flookup_thm])
QED

(* Reachable non-entry block has a reachable predecessor *)
Triviality reachable_has_reachable_pred:
  !fn lbl.
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    fn_entry_label fn <> SOME lbl ==>
    ?p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) /\
        cfg_reachable_of (cfg_analyze fn) p
Proof
  rpt strip_tac
  \\ `fn.fn_blocks <> []` by
       fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def]
  \\ `entry_block fn = SOME (HD fn.fn_blocks)` by
       simp[venomInstTheory.entry_block_def, NULL_EQ]
  \\ `cfg_path (cfg_analyze fn) (HD fn.fn_blocks).bb_label lbl` by
       metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability,
                 cfgDefsTheory.cfg_path_def]
  \\ `(HD fn.fn_blocks).bb_label <> lbl` by (
       strip_tac \\ fs[venomInstTheory.fn_entry_label_def])
  \\ qpat_x_assum `cfg_path _ _ lbl`
       (strip_assume_tac o ONCE_REWRITE_RULE [relationTheory.RTC_CASES2]
                         o REWRITE_RULE [cfgDefsTheory.cfg_path_def])
  \\ gvs[]
  \\ qexists_tac `u`
  \\ conj_tac
  >- metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
  \\ metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability,
               cfgDefsTheory.cfg_path_def]
QED

(* Helper: phi operand from a block strictly dominated by def_blk,
   where def_blk has defs and pred is reachable, has dom def_blk blk(rd). *)
Triviality build_phi_ops_dom_by_ancestor:
  !bp fn addr_sp phi_id ops rd pred def_blk def_id def_iid def_loc.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_phi_ops phi_id = SOME ops /\ MEM (rd, pred) ops /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
      (mn_block (THE (FLOOKUP ms.ms_nodes phi_id))) /\
    rd <> 0 /\
    cfg_reachable_of (cfg_analyze fn) pred ==>
    dominates (dom_analyze (cfg_analyze fn) fn) def_blk
      (mn_block (THE (FLOOKUP ms.ms_nodes rd)))
Proof
  rpt gen_tac >> simp[LET_THM] >> strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] build_phi_ops_structure) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`] mp_tac) >>
  simp[] >> simp[phi_ops_structure_ok_def] >>
  disch_then (qspecl_then [`phi_id`, `ops`, `rd`, `pred`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Simplify mn_block (THE (FLOOKUP ... phi_id)) = blk *)
  `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
        phi_id)) = blk` by simp[mn_block_def] >>
  (* Get reachable blk *)
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] build_phi_block_reachable) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `phi_id`, `blk`]
       mp_tac) >>
  simp[] >> strip_tac >>
  (* dom def_blk pred via sdom_dominates_preds *)
  `dominates (dom_analyze (cfg_analyze fn) fn) def_blk pred` by (
    match_mp_tac (SIMP_RULE (srw_ss()) [] sdom_dominates_preds) >>
    qexists_tac `blk` >> fs[]) >>
  (* block_defs def_blk <> [] *)
  `fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
    def_blk <> []` by (
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] build_MnDef_block_defs_nonempty) >>
    disch_then (qspecl_then [`cfg_analyze fn`,
         `dom_analyze (cfg_analyze fn) fn`,
         `bp`, `fn`, `addr_sp`, `def_id`,
         `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
    simp[]) >>
  (* Apply 4th clause *)
  qpat_x_assum `!c. _ ==> _` (qspec_then `def_blk` mp_tac) >> simp[]
QED

(* Extend a reaching chain by one step at the end *)
Triviality reaching_chain_extend:
  !ms n v current x.
    reaching_chain ms n v current /\
    FLOOKUP ms.ms_reaching current = SOME x ==>
    reaching_chain ms (SUC n) v x
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- (fs[reaching_chain_def] >>
      simp[Once reaching_chain_def])
  >> qpat_x_assum `reaching_chain _ (SUC _) _ _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [reaching_chain_def]) >>
  rpt strip_tac >> gvs[]
  (* Case mid = current *)
  >- (simp[Once reaching_chain_def] >>
      disj2_tac >> simp[Once reaching_chain_def])
  (* Case reaching_chain n mid current *)
  >> simp[Once reaching_chain_def] >> disj2_tac >>
  first_x_assum (qspecl_then [`ms`, `mid`, `current`, `x`] mp_tac) >>
  simp[]
QED

(* Reaching chain + one more step back to v creates a cycle, contradicting
   mem_ssa_reaching_acyclic. Caller provides v ∈ FDOM and v ≠ 0. *)
Triviality reaching_chain_no_revisit:
  !ms fn bp addr_sp n v current.
    wf_function fn /\
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
                       bp fn addr_sp /\
    reaching_chain ms n v current /\ n > 0 /\
    FLOOKUP ms.ms_reaching current = SOME v /\
    v IN FDOM ms.ms_nodes /\ v <> 0 ==> F
Proof
  rpt strip_tac >>
  `reaching_chain ms (SUC n) v v` by (
    irule reaching_chain_extend >> qexists_tac `current` >> simp[]) >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] mem_ssa_reaching_acyclic) >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `v`] mp_tac) >>
  simp[] >> gvs[] >> qexists_tac `SUC n` >> simp[]
QED

(* Helper: one step of the reaching chain preserves all invariants needed
   for the walk induction. Covers both MnDef and MnUse cases.
   Uses strict_dominates to avoid the same-block boundary issue. *)
(* Helper: ms_reaching current = SOME x implies x <> current (acyclicity) *)
Triviality build_reaching_not_self:
  !fn bp addr_sp current x.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching current = SOME x /\
    current IN FDOM ms.ms_nodes /\ current <> 0 ==>
    x <> current
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  strip_tac >> strip_tac >> pop_assum SUBST_ALL_TAC >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] mem_ssa_reaching_acyclic) >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `current`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `1` mp_tac) >>
  PURE_REWRITE_TAC[arithmeticTheory.ONE] >> simp[reaching_chain_def]
QED

Triviality fuel_positive_lemma:
  !A (x:num) fuel. FINITE A /\ x IN A /\ fuel >= CARD A ==> fuel >= 1
Proof
  rpt strip_tac >>
  `A <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `CARD A <> 0` by metis_tac[CARD_EQ_0] >>
  decide_tac
QED

Triviality fuel_step_lemma:
  !A (x:num) vs fuel. FINITE A /\ x IN A /\ ~MEM x vs /\
    SUC fuel >= CARD (A DIFF set vs) ==>
    fuel >= CARD (A DIFF set (x::vs))
Proof
  rpt strip_tac >>
  `FINITE (A DIFF set vs)` by simp[] >>
  `A DIFF set (x::vs) PSUBSET A DIFF set vs` by (
    simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
    metis_tac[]) >>
  imp_res_tac CARD_PSUBSET >> DECIDE_TAC
QED

Triviality walk_reaching_step_invariants:
  !fn bp addr_sp current visited x def_id def_iid def_blk def_loc fuel.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    FLOOKUP ms.ms_reaching current = SOME x /\
    current IN FDOM ms.ms_nodes /\ current <> 0 /\ ~MEM current visited /\
    (!blk. THE (FLOOKUP ms.ms_nodes current) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    ~MEM def_id visited /\ def_id <> current /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
      (mn_block (THE (FLOOKUP ms.ms_nodes current))) /\
    SUC fuel >= CARD (FDOM ms.ms_nodes DIFF set visited) /\
    (!v. MEM v visited ==> ?n. n > 0 /\ reaching_chain ms n v current) ==>
    x <> 0 /\ ~MEM x (current::visited) /\ x IN FDOM ms.ms_nodes /\
    (strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP ms.ms_nodes x))) \/
     mn_block (THE (FLOOKUP ms.ms_nodes x)) = def_blk) /\
    fuel >= CARD (FDOM ms.ms_nodes DIFF set (current::visited)) /\
    (!v. MEM v (current::visited) ==>
         ?n. n > 0 /\ reaching_chain ms n v x)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac
  \\ `x <> 0` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      build_sdom_reaching_nonzero)) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `current`, `x`,
      `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
    impl_tac >- simp[] >> simp[])
  \\ `x IN FDOM (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      build_reaching_step_in_fdom)) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `current`, `x`] mp_tac) >>
    impl_tac >- simp[] >> simp[])
  \\ `x <> current` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      build_reaching_not_self)) >>
    disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `current`, `x`] mp_tac) >>
    impl_tac >- simp[] >> simp[])
  \\ `~MEM x visited` by (
    strip_tac >> res_tac >>
    metis_tac[reaching_chain_no_revisit])
  \\ `dominates (dom_analyze (cfg_analyze fn) fn)
        (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
           (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes x)))
        (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
           (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
             current)))` by (
    mp_tac (SIMP_RULE (srw_ss()) [] mem_ssa_reaching_def_dominates) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `current`, `x`] mp_tac) >>
    DISCH_TAC >>
    `wf_function fn /\
     FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp).ms_reaching current = SOME x /\ x <> 0 /\
     current IN FDOM (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes` by simp[] >>
    res_tac >> simp[])
  (* Step A: block_defs nonempty *)
  >> `fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
        def_blk <> []` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      build_MnDef_block_defs_nonempty)) >>
    disch_then (qspecl_then [`cfg_analyze fn`,
      `dom_analyze (cfg_analyze fn) fn`,
      `bp`, `fn`, `addr_sp`, `def_id`, `def_iid`,
      `def_blk`, `def_loc`] mp_tac) >>
    simp[])
  (* Step B: dom def_blk blk(x) *)
  >> `dominates (dom_analyze (cfg_analyze fn) fn) def_blk
        (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
           (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes x)))` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      build_reaching_dominated_by_ancestor)) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `current`, `x`,
      `def_blk`] mp_tac) >>
    impl_tac >- simp[] >> simp[])
  (* Step C: fuel >= CARD(FDOM DIFF set(current::visited)) *)
  >> `fuel >= CARD (FDOM (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
        DIFF set (current::visited))` by (
    irule fuel_step_lemma >> simp[])
  (* Step D: reaching_chain *)
  >> `!v. MEM v (current::visited) ==>
       ?n. n > 0 /\ reaching_chain
         (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
            bp fn addr_sp) n v x` by (
    rpt strip_tac >> Cases_on `v = current`
    >- (qexists_tac `1` >> PURE_REWRITE_TAC [arithmeticTheory.ONE] >>
        simp[reaching_chain_def])
    >> `MEM v visited` by gvs[] >>
       res_tac >>
       drule_all reaching_chain_extend >> strip_tac >>
       qexists_tac `SUC n` >> simp[])
  (* Step E: sdom/eq split *)
  >> Cases_on `mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes x)) = def_blk`
  >- simp[]
  >> simp[dominatorDefsTheory.strict_dominates_def]
QED


(* Shared tactic for MnDef/MnUse within-block step in walk_same_block_visits_def.
   Expects: assumptions simplified by gvs[mn_block_def, mn_inst_id_def] after
   Cases_on cur_node, with FLOOKUP...x = SOME (MnDef/MnUse n s m),
   FLOOKUP...ms_reaching x = SOME rd, and walk equation as goal implication.
   Establishes rd properties, acyclicity, fuel step, reaching_chain, INDEX_OF,
   then case-splits on def_id = rd (monotonicity vs IH). *)
(* walk_same_block_step_tac: shared tactic for MnDef/MnUse within-block step.
   After SUBST_ALL_TAC on ms and Cases_on cur_node >> gvs[mn_block_def, mn_inst_id_def],
   the build term is fully expanded. Variables: n (inst_id), def_blk (block), m (loc).
   Assumes: wf_function fn, FLOOKUP...reaching x = SOME rd, walk equation as goal imp.
   Approach: SUBST_ALL_TAC pattern — all ms references are the expanded build term. *)

(* Helper: non-phi node's inst_id is MEM in given block's instructions.
   Avoids the existential in build_node_inst_id_in_block by taking bb directly. *)
Triviality build_node_mem_in_block:
  !bp fn addr_sp aid node bb.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
                           bp fn addr_sp in
    wf_function fn /\ FLOOKUP ms.ms_nodes aid = SOME node /\
    (!blk. node <> MnPhi blk) /\
    lookup_block (mn_block node) fn.fn_blocks = SOME bb ==>
    MEM (mn_inst_id node) (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_inst_id_in_block)) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `aid`, `node`] mp_tac) >>
  simp[]
QED

(* Helper: pre-specialize reaching_chain lemmas to eliminate ms=build(...) *)
fun rcnr_for_fn () =
  reaching_chain_no_revisit
  |> Q.SPECL [`mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp`,
              `fn`, `bp`, `addr_sp`]
  |> REWRITE_RULE [];

fun rce_for_fn () =
  reaching_chain_extend
  |> Q.SPEC `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp`;

(* walk_same_block_step_tac: shared tactic for both MnDef and MnUse cases.
   IH pattern: match on '!a b c d. _' to avoid matching single-∀ assumptions
   like '!blk. rd_node <> MnPhi blk' or '!v. MEM v visited ==> _'. *)
fun walk_same_block_step_tac () =
  (* Step 1: rd properties (same block, nonzero, in FDOM, non-phi) *)
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_reaching_same_block)) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `x`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `bb`, `idx_x`, `idx_d`] mp_tac) >>
  (impl_tac >- simp[mn_block_def, mn_inst_id_def]) >> strip_tac >>
  (* Step 2: rd <> x *)
  `rd <> x` by (
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_reaching_not_self)) >>
    disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `x`, `rd`] mp_tac) >>
    simp[]) >>
  (* Step 3: ~MEM rd visited — acyclicity via reaching_chain *)
  `~MEM rd visited` by (
    strip_tac >>
    qpat_x_assum `!v. MEM v visited ==> _`
      (qspec_then `rd` mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum `!a b c d. _` kall_tac >>
    metis_tac[rcnr_for_fn ()]) >>
  (* Step 4: fuel step *)
  `fuel >= CARD (FDOM (mem_ssa_build (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
     DIFF set (x::visited))` by (
    irule fuel_step_lemma >> simp[CARD_DIFF_EQN]) >>
  (* Step 5: reaching_chain for x::visited w.r.t. rd *)
  `!v. MEM v (x::visited) ==> ?nn. nn > 0 /\
     reaching_chain (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp) nn v rd` by (
    rpt strip_tac >> Cases_on `v = x`
    >- (qexists_tac `1` >> PURE_REWRITE_TAC [arithmeticTheory.ONE] >>
        simp[reaching_chain_def])
    >> (qpat_x_assum `!a b c d. _` kall_tac >>
       `MEM v visited` by fs[] >>
       qpat_x_assum `!v. MEM v visited ==> _`
         (qspec_then `v` mp_tac) >> simp[] >>
       disch_then (qx_choose_then `kk` strip_assume_tac) >>
       drule_all (rce_for_fn ()) >> strip_tac >>
       qexists_tac `SUC kk` >> simp[])) >>
  (* Step 6: rd node existence *)
  `?rd_node. FLOOKUP (mem_ssa_build (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes rd
     = SOME rd_node /\ (!blk. rd_node <> MnPhi blk)` by
    (qpat_x_assum `!a b c d. _` kall_tac >>
     qexists_tac `THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes rd)` >>
     conj_tac
     >- (Cases_on `FLOOKUP (mem_ssa_build (cfg_analyze fn)
           (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes rd`
         >> gvs[flookup_thm])
     >> simp[]) >>
  (* CRITICAL: substitute THE(FLOOKUP...rd) = rd_node globally *)
  `THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes rd)
     = rd_node` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  (* Step 6b: INDEX_OF for rd_node in bb *)
  `?idx_rd. INDEX_OF (mn_inst_id rd_node)
     (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_rd` by (
    qpat_x_assum `!a b c d. _` kall_tac >>
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_mem_in_block)) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `rd`, `rd_node`, `bb`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    Cases_on `INDEX_OF (mn_inst_id rd_node)
      (MAP (\i. i.inst_id) bb.bb_instructions)`
    >- gvs[INDEX_OF_eq_NONE]
    >> simp[]) >>
  (* Step 7: Case split on def_id = rd *)
  Cases_on `def_id = rd`
  >- (
    qpat_x_assum `!a b c d. _` kall_tac >>
    `fuel >= 1` by (
      irule fuel_positive_lemma >>
      qexistsl_tac [`FDOM (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
        DIFF set (x::visited)`, `rd`] >>
      simp[]) >>
    `?k. fuel = SUC k` by (Cases_on `fuel` >> gvs[]) >>
    gvs[] >>
    drule walk_clobber_visits_current >>
    simp[])
  >> (
    `idx_d < idx_rd` by (
      mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
        build_same_block_reaching_closest)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `x`, `rd`,
        `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      (impl_tac >- simp[mn_block_def, mn_inst_id_def]) >>
      disch_then (qspecl_then [`bb`, `idx_x`, `idx_rd`, `idx_d`] mp_tac) >>
      simp[mn_inst_id_def]) >>
    first_x_assum (qspecl_then [
      `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp`,
      `fn`, `bp`, `addr_sp`,
      `x::visited`, `rd`, `qloc`, `visited'`, `def_id`, `def_iid`,
      `def_blk`, `def_loc`, `bb`, `idx_rd`, `idx_d`] mp_tac) >>
    simp[mn_block_def, mn_inst_id_def, CARD_DIFF_EQN]);

(* Within-block walk: if walk starts at node x in def_blk and
   def_id is an MnDef in def_blk with a lower instruction index,
   the walk visits def_id. The INDEX_OF precondition ensures x is
   "above" def_id in instruction order. *)
Triviality walk_same_block_visits_def:
  !fuel ms fn bp addr_sp visited x qloc visited'
   def_id def_iid def_blk def_loc bb idx_x idx_d.
    wf_function fn /\
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
                       bp fn addr_sp /\
    mem_ssa_walk_clobber ms fuel visited x qloc = (NONE, visited') /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    ~MEM def_id visited /\ def_id <> x /\
    x <> 0 /\ ~MEM x visited /\ x IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes x) <> MnPhi blk) /\
    mn_block (THE (FLOOKUP ms.ms_nodes x)) = def_blk /\
    fuel >= CARD (FDOM ms.ms_nodes DIFF set visited) /\
    (!v. MEM v visited ==> ?n. n > 0 /\ reaching_chain ms n v x) /\
    lookup_block def_blk fn.fn_blocks = SOME bb /\
    INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes x)))
             (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_x /\
    INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes def_id)))
             (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_d /\
    idx_d < idx_x ==>
    MEM def_id visited'
Proof
  Induct_on `fuel`
  (* Base: fuel = 0, x ∈ FDOM DIFF set visited → CARD > 0 contradicts 0 >= *)
  >- (rpt gen_tac >> strip_tac >>
      `x IN (FDOM ms.ms_nodes DIFF set visited)` by simp[] >>
      `FINITE (FDOM ms.ms_nodes DIFF set visited)` by simp[] >>
      `FDOM ms.ms_nodes DIFF set visited <> {}` by
        metis_tac[MEMBER_NOT_EMPTY] >>
      `CARD (FDOM ms.ms_nodes DIFF set visited) <> 0` by
        metis_tac[CARD_EQ_0] >>
      decide_tac)
  \\ rpt gen_tac \\ strip_tac
  (* Substitute ms, unfold walk *)
  \\ qpat_x_assum `ms = _` SUBST_ALL_TAC
  \\ qpat_x_assum `mem_ssa_walk_clobber _ _ _ _ _ = _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [mem_ssa_walk_clobber_def])
  \\ PURE_REWRITE_TAC [LET_THM] \\ BETA_TAC \\ simp[]
  (* Establish cur_node *)
  \\ `?cur_node. FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes x
       = SOME cur_node` by fs[flookup_thm]
  \\ `THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes x)
       = cur_node` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th) \\ simp[]
  (* Establish ms_reaching x = SOME rd *)
  \\ `?rd. FLOOKUP (mem_ssa_build (cfg_analyze fn)
       (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_reaching x
       = SOME rd` by (
      qpat_x_assum `!a b c d. _` kall_tac >>
      `wf_mssa (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp)` by simp[mem_ssa_build_wf] >>
      fs[wf_mem_ssa_def, mem_ssa_reaching_complete_def] >>
      first_x_assum (qspecl_then [`x`, `cur_node`] mp_tac) >> simp[])
  (* Rewrite reaching in goal to eliminate NONE branches *)
  \\ pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th)
  (* Save and remove IH before gvs to avoid expensive rewriting *)
  \\ qpat_x_assum `!a b c d. _` (fn ih =>
       Cases_on `cur_node` >> gvs[mn_block_def, mn_inst_id_def] >>
       assume_tac ih)
  (* MnDef case: handle completely_contains T (contradicts NONE), then step *)
  >- (Cases_on `completely_contains m qloc` >> simp[] >>
      strip_tac >> walk_same_block_step_tac ())
  (* MnUse case: same step tactic *)
  \\ strip_tac \\ walk_same_block_step_tac ()
QED

(* ===================================================================
   Part B: Walk visits every strictly-dominating MnDef.
   
   Architecture: Instead of tracking a reaching_chain invariant through
   fuel induction, we decompose into:
   1. walk_reachable: inductive relation for walk-graph reachability
   2. walk_clobber_succ_closed: walk output is "successor-closed"
   3. walk_reachable_in_closed: successor-closed + reachable => visited
   4. walk_reachable_from_rd: SSA structure gives walk_reachable
   5. walk_clobber_visits_dom_defs: combining everything
   =================================================================== *)

(* Walk-graph reachability: x can reach z by following ms_reaching edges
   at non-phi nodes and ms_phi_ops edges at phi nodes. *)
Inductive walk_reachable:
[~refl:]
  (!ms x. walk_reachable ms x x)
[~reaching:]
  (!ms x y z.
     FLOOKUP ms.ms_reaching x = SOME y /\
     (!blk. THE (FLOOKUP ms.ms_nodes x) <> MnPhi blk) /\
     walk_reachable ms y z ==>
     walk_reachable ms x z)
[~phi_op:]
  (!ms blk ops pred x y z.
     FLOOKUP ms.ms_nodes x = SOME (MnPhi blk) /\
     FLOOKUP ms.ms_phi_ops x = SOME ops /\
     MEM (y, pred) ops /\
     walk_reachable ms y z ==>
     walk_reachable ms x z)
End

(* Transitivity of walk_reachable *)
Triviality walk_reachable_trans:
  !ms a b c. walk_reachable ms a b /\ walk_reachable ms b c ==>
    walk_reachable ms a c
Proof
  Induct_on `walk_reachable` >> rpt strip_tac >> gvs[]
  >- metis_tac[walk_reachable_reaching]
  >> metis_tac[walk_reachable_phi_op]
QED

(* walk_reachable from 0 is trivial: z = 0 *)
(* General: walk_reachable from 0 only reaches 0 *)
Triviality walk_reachable_from_zero_gen:
  !ms z. walk_reachable ms 0 z /\
    0 NOTIN FDOM ms.ms_nodes /\
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes ==>
    z = 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `walk_reachable _ _ _` mp_tac >>
  simp[Once walk_reachable_cases] >>
  strip_tac >> gvs[flookup_thm] >>
  metis_tac[SUBSET_DEF, flookup_thm]
QED

(* connect_list only adds reaching entries for aids already in ms_nodes *)
Triviality connect_list_reaching_subset:
  !aids ms dom fn fuel.
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes ==>
    FDOM (mem_ssa_connect_list ms dom fn fuel aids).ms_reaching SUBSET
    FDOM (mem_ssa_connect_list ms dom fn fuel aids).ms_nodes
Proof
  Induct >> simp[mem_ssa_connect_list_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[] >>
  strip_tac >> first_x_assum irule >>
  simp[SUBSET_DEF, FDOM_FUPDATE] >>
  metis_tac[SUBSET_DEF, flookup_thm]
QED

Triviality connect_all_reaching_subset:
  !lbls ms dom fn fuel.
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes ==>
    FDOM (mem_ssa_connect_all ms dom fn fuel lbls).ms_reaching SUBSET
    FDOM (mem_ssa_connect_all ms dom fn fuel lbls).ms_nodes
Proof
  Induct >> simp[mem_ssa_connect_all_def] >>
  rpt gen_tac >> simp[connect_list_fields] >> strip_tac >>
  first_x_assum irule >>
  irule connect_list_reaching_subset >>
  irule connect_list_reaching_subset >> simp[]
QED

Triviality build_reaching_subset_nodes:
  !cfg dom bp fn addr_sp.
    FDOM (mem_ssa_build cfg dom bp fn addr_sp).ms_reaching SUBSET
    FDOM (mem_ssa_build cfg dom bp fn addr_sp).ms_nodes
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC[mem_ssa_build_def, LET_THM] >> BETA_TAC >>
  simp[remove_redundant_phis_fields] >>
  irule connect_all_reaching_subset >>
  simp[insert_phis_fields, process_blocks_fields,
       mem_ssa_init_def, FDOM_FEMPTY, EMPTY_SUBSET]
QED

(* Specialized to build *)
Triviality walk_reachable_from_zero:
  !fn bp addr_sp z.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    walk_reachable ms 0 z ==> z = 0
Proof
  rpt gen_tac >> simp[LET_THM] >> strip_tac >>
  irule walk_reachable_from_zero_gen >>
  qexists_tac `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
                 bp fn addr_sp` >>
  simp[build_reaching_subset_nodes] >>
  mp_tac build_zero_not_in_nodes >>
  disch_then (qspecl_then [`cfg_analyze fn`,
    `dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`, `addr_sp`] mp_tac) >>
  simp[]
QED

(* Per-node successor property: node y's successors are in visited *)
Definition node_succ_in_def:
  node_succ_in ms y visited <=>
    y <> 0 /\ y IN FDOM ms.ms_nodes ==>
    (case FLOOKUP ms.ms_nodes y of
       SOME (MnDef _ _ _) =>
         (case FLOOKUP ms.ms_reaching y of
            NONE => T | SOME rd => rd = 0 \/ MEM rd visited)
     | SOME (MnUse _ _ _) =>
         (case FLOOKUP ms.ms_reaching y of
            NONE => T | SOME rd => rd = 0 \/ MEM rd visited)
     | SOME (MnPhi _) =>
         (case FLOOKUP ms.ms_phi_ops y of
            NONE => T
          | SOME ops => EVERY (\(rd, pred). rd = 0 \/ MEM rd visited) ops)
     | NONE => T)
End

(* Successor-closed: every visited node's successors are in visited *)
Definition walk_succ_closed_def:
  walk_succ_closed ms visited <=>
    !y. MEM y visited ==> node_succ_in ms y visited
End

(* node_succ_in is monotone in visited *)
Triviality node_succ_in_mono:
  !ms y v1 v2. node_succ_in ms y v1 /\ (!x. MEM x v1 ==> MEM x v2) ==>
    node_succ_in ms y v2
Proof
  rw[node_succ_in_def] >>
  rpt CASE_TAC >> gvs[] >>
  TRY (metis_tac[]) >>
  gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

(* collect_phi: NONE result ([] clobbers) => new nodes have node_succ_in,
   and each operand rd is in output *)
Triviality fuel_diff_mono:
  !A (vs1 : num list) vs2 fuel.
    FINITE A /\ (!x. MEM x vs1 ==> MEM x vs2) /\
    fuel >= CARD (A DIFF set vs1) ==>
    fuel >= CARD (A DIFF set vs2)
Proof
  rpt strip_tac >>
  `A DIFF set vs2 SUBSET A DIFF set vs1` by
    (simp[SUBSET_DEF] >> metis_tac[]) >>
  `FINITE (A DIFF set vs1)` by simp[] >>
  `CARD (A DIFF set vs2) <= CARD (A DIFF set vs1)` by
    metis_tac[CARD_SUBSET] >>
  decide_tac
QED

(* Specialized visited monotonicity for collect_phi with walk_clobber.
   Eliminates HO matching issues with the lambda walker argument. *)
Triviality collect_phi_walk_visited_mono:
  !ops ms fuel qloc visited clobbers visited'.
    mem_ssa_collect_phi_clobbers
      (\v rd. mem_ssa_walk_clobber ms fuel v rd qloc)
      visited ops = (clobbers, visited') ==>
    !x. MEM x visited ==> MEM x visited'
Proof
  rpt strip_tac >>
  qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
    (mp_tac o BETA_RULE o MATCH_MP
      (collect_phi_visited_mono |> REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
  (impl_tac >- metis_tac[walk_clobber_visited_mono]) >>
  metis_tac[]
QED

Triviality collect_phi_new_node_succ:
  !ops ms fuel qloc visited visited''.
    mem_ssa_collect_phi_clobbers
      (\v rd. mem_ssa_walk_clobber ms fuel v rd qloc)
      visited ops = ([], visited'') /\
    (!v current v'.
      mem_ssa_walk_clobber ms fuel v current qloc = (NONE, v') /\
      fuel >= CARD (FDOM ms.ms_nodes DIFF set v) ==>
      !y. MEM y v' /\ ~MEM y v ==> node_succ_in ms y v') /\
    fuel >= CARD (FDOM ms.ms_nodes DIFF set visited) /\
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes /\
    0 NOTIN FDOM ms.ms_nodes ==>
    (!y. MEM y visited'' /\ ~MEM y visited ==> node_succ_in ms y visited'') /\
    (!rd pred. MEM (rd, pred) ops /\ rd <> 0 /\ ~MEM rd visited /\
              rd IN FDOM ms.ms_nodes ==> MEM rd visited'')
Proof
  Induct
  >- rw[mem_ssa_collect_phi_clobbers_def]
  >> rpt gen_tac
  >> Cases_on `h`
  >> PURE_REWRITE_TAC [mem_ssa_collect_phi_clobbers_def, LET_THM]
  >> BETA_TAC
  >> pairarg_tac >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> pairarg_tac >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> strip_tac
  >> reverse (Cases_on `result`)
  >- fs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> fs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> sg `fuel >= CARD (FDOM ms.ms_nodes DIFF set visited1)`
  >- (mp_tac (Q.SPECL [`FDOM ms.ms_nodes`, `visited`, `visited1`, `fuel`]
        fuel_diff_mono) >>
      simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
      metis_tac[walk_clobber_visited_mono])
  >> first_x_assum (qspecl_then [`ms`, `fuel`, `qloc`, `visited1`, `visited''`]
       mp_tac)
  >> (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC))
  >> strip_tac
  (* Part 1: new nodes in visited'' have node_succ_in *)
  >> conj_tac >- (
    rpt strip_tac >> Cases_on `MEM y visited1`
    (* y was added by the walker — use walker IH + mono *)
    >- (
      sg `node_succ_in ms y visited1`
      >- (first_x_assum (qspecl_then [`visited`, `q`, `visited1`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then (qspec_then `y` mp_tac) >>
          (impl_tac >- simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
          simp[]) >>
      sg `!x. MEM x visited1 ==> MEM x visited''`
      >- (drule collect_phi_walk_visited_mono >> metis_tac[]) >>
      metis_tac[node_succ_in_mono])
    (* y was added by collect_phi — use list IH directly *)
    >> qpat_x_assum `!y. MEM y visited'' /\ ~MEM y visited1 ==> _`
         (qspec_then `y` mp_tac) >> simp[])
  (* Part 2: each (rd,pred) in ops has rd in visited'' *)
  >> rpt strip_tac
  (* Case: rd = q (head element) *)
  >- (
    gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
    sg `fuel >= 1`
    >- (irule fuel_positive_lemma >>
        qexists_tac `FDOM ms.ms_nodes DIFF set visited` >>
        qexists_tac `q` >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
    sg `MEM q visited1`
    >- (Cases_on `fuel` >- gvs[] >>
        drule walk_clobber_visits_current >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
    drule collect_phi_walk_visited_mono >> metis_tac[])
  (* Case: MEM (rd,pred) ops *)
  >> Cases_on `MEM rd visited1`
  >- (drule collect_phi_walk_visited_mono >> metis_tac[])
  >> qpat_x_assum `!rd' pred'. MEM (rd',pred') ops /\ _ ==> _`
       (qspecl_then [`rd`, `pred`] mp_tac) >>
  simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
  metis_tac[walk_clobber_visited_mono]
QED

(* Key lemma: new nodes in NONE walk output have node_succ_in.
   Proved by fuel induction. No precondition on visited. *)
Triviality walk_clobber_new_node_succ:
  !fuel ms visited current qloc visited'.
    mem_ssa_walk_clobber ms fuel visited current qloc = (NONE, visited') /\
    fuel >= CARD (FDOM ms.ms_nodes DIFF set visited) /\
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes /\
    0 NOTIN FDOM ms.ms_nodes /\
    mem_ssa_edges_valid ms ==>
    !y. MEM y visited' /\ ~MEM y visited ==>
      node_succ_in ms y visited'
Proof
  Induct
  (* fuel = 0: visited' = visited, trivial *)
  >- (rw[mem_ssa_walk_clobber_def] >> gvs[])
  >> rpt gen_tac
  >> simp[Once mem_ssa_walk_clobber_def, LET_THM,
          Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> Cases_on `current = 0`
  >- simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> Cases_on `MEM current visited`
  >- simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> Cases_on `FLOOKUP ms.ms_nodes current`
  >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  (* NONE node: visited' = current::visited, only new node is current *)
  >- (strip_tac >> rpt strip_tac >> gvs[node_succ_in_def])
  >> Cases_on `x:mem_ssa_node`
  >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  (* ========== MnDef ========== *)
  >- (
    IF_CASES_TAC
    >- simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
    Cases_on `FLOOKUP ms.ms_reaching current`
    >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
    >- (strip_tac >> rpt strip_tac >> gvs[node_succ_in_def])
    >> strip_tac >>
    sg `current IN FDOM ms.ms_nodes` >- gvs[flookup_thm] >>
    sg `fuel >= CARD (FDOM ms.ms_nodes DIFF set (current::visited))`
    >- (irule fuel_step_lemma >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
    first_x_assum (qspecl_then [`ms`, `current::visited`, `x`, `qloc`,
      `visited'`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >> rpt strip_tac >>
    Cases_on `y = current`
    >- (gvs[node_succ_in_def, Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
        Cases_on `x = 0` >- simp[] >>
        Cases_on `MEM x (current::visited)`
        >- (drule walk_clobber_visited_mono >> metis_tac[]) >>
        sg `x IN FDOM ms.ms_nodes`
        >- (fs[mem_ssa_edges_valid_def] >> res_tac >> gvs[]) >>
        sg `fuel >= 1`
        >- (irule fuel_positive_lemma >>
            qexists_tac `FDOM ms.ms_nodes DIFF set (current::visited)` >>
            qexists_tac `x` >>
            simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
            gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
        Cases_on `fuel` >- gvs[] >>
        drule walk_clobber_visits_current >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])
    >> first_x_assum (qspec_then `y` mp_tac) >>
    gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF", MEM])
  (* ========== MnUse ========== *)
  >- (
    Cases_on `FLOOKUP ms.ms_reaching current`
    >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
    >- (strip_tac >> rpt strip_tac >> gvs[node_succ_in_def])
    >> strip_tac >>
    sg `current IN FDOM ms.ms_nodes` >- gvs[flookup_thm] >>
    sg `fuel >= CARD (FDOM ms.ms_nodes DIFF set (current::visited))`
    >- (irule fuel_step_lemma >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
    first_x_assum (qspecl_then [`ms`, `current::visited`, `x`, `qloc`,
      `visited'`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >> rpt strip_tac >>
    Cases_on `y = current`
    >- (gvs[node_succ_in_def, Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
        Cases_on `x = 0` >- simp[] >>
        Cases_on `MEM x (current::visited)`
        >- (drule walk_clobber_visited_mono >> metis_tac[]) >>
        sg `x IN FDOM ms.ms_nodes`
        >- (fs[mem_ssa_edges_valid_def] >> res_tac >> gvs[]) >>
        sg `fuel >= 1`
        >- (irule fuel_positive_lemma >>
            qexists_tac `FDOM ms.ms_nodes DIFF set (current::visited)` >>
            qexists_tac `x` >>
            simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
            gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]) >>
        Cases_on `fuel` >- gvs[] >>
        drule walk_clobber_visits_current >>
        simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])
    >> first_x_assum (qspec_then `y` mp_tac) >>
    gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF", MEM])
  (* ========== MnPhi ========== *)
  >> Cases_on `FLOOKUP ms.ms_phi_ops current`
  >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >- (strip_tac >> rpt strip_tac >> gvs[node_succ_in_def])
  >> pairarg_tac >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> Cases_on `clobbers` >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> TRY (Cases_on `t` >> simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])
  >> strip_tac >> gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"]
  >> sg `current IN FDOM ms.ms_nodes` >- gvs[flookup_thm]
  >> sg `fuel >= CARD (FDOM ms.ms_nodes DIFF set (current::visited))`
  >- (irule fuel_step_lemma >>
      simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])
  (* Apply collect_phi_new_node_succ via MATCH_MP *)
  >> qpat_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
       (fn th => mp_tac (MATCH_MP
         (collect_phi_new_node_succ |> REWRITE_RULE [GSYM AND_IMP_INTRO])
         th)) >>
  (impl_tac >- (
    rpt gen_tac >> strip_tac >> rpt strip_tac >>
    first_x_assum (qspecl_then [`ms`, `v`, `current'`, `qloc`, `v'`] mp_tac) >>
    simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])) >>
  simp[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"] >>
  strip_tac >>
  (* Now have: new_succ_closed for visited'\current::visited,
     and phi_ops_in_visited' *)
  rpt strip_tac >>
  Cases_on `y = current`
  >- (
    (* y = current: need node_succ_in ms current visited' for MnPhi *)
    simp[node_succ_in_def, Excl "CARD_DIFF_EQN", Excl "CARD_DIFF",
         EVERY_MEM, FORALL_PROD] >>
    rpt strip_tac >>
    rename1 `MEM (rd, pred) x` >>
    Cases_on `rd = 0` >- simp[] >>
    disj2_tac >>
    sg `rd = 0 \/ rd IN FDOM ms.ms_nodes`
    >- (fs[mem_ssa_edges_valid_def] >> res_tac) >>
    gvs[] >>
    Cases_on `MEM rd (current::visited)`
    >- (qpat_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
          (fn th => mp_tac (MATCH_MP
            (collect_phi_walk_visited_mono |> REWRITE_RULE [GSYM AND_IMP_INTRO])
            th)) >>
        disch_then (qspec_then `rd` mp_tac) >> simp[])
    >> first_x_assum (qspecl_then [`rd`, `pred`] mp_tac) >>
    gvs[MEM, Excl "CARD_DIFF_EQN", Excl "CARD_DIFF"])
  (* y <> current: use collect_phi new node succ *)
  >> first_x_assum (qspec_then `y` mp_tac) >>
  gvs[Excl "CARD_DIFF_EQN", Excl "CARD_DIFF", MEM]
QED

(* walk_succ_closed for walk starting from [] *)
Triviality walk_clobber_succ_closed:
  !fuel ms current qloc visited'.
    mem_ssa_walk_clobber ms fuel [] current qloc = (NONE, visited') /\
    fuel >= CARD (FDOM ms.ms_nodes) /\
    FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes /\
    0 NOTIN FDOM ms.ms_nodes /\
    mem_ssa_edges_valid ms ==>
    walk_succ_closed ms visited'
Proof
  rpt strip_tac >>
  drule walk_clobber_new_node_succ >> simp[] >>
  strip_tac >> rw[walk_succ_closed_def] >>
  rpt strip_tac >>
  irule node_succ_in_mono >>
  qexists_tac `visited'` >> simp[] >>
  first_x_assum irule >> simp[]
QED

(* walk_reachable + succ_closed + MEM start => MEM target *)
Triviality walk_reachable_in_closed:
  !ms x z. walk_reachable ms x z ==>
    !visited. walk_succ_closed ms visited /\
              MEM x visited /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
              0 NOTIN FDOM ms.ms_nodes /\
              FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes ==>
              MEM z visited
Proof
  ho_match_mp_tac walk_reachable_strongind >> rpt conj_tac
  (* refl *)
  >- simp[]
  (* reaching: FLOOKUP ms.ms_reaching x = SOME x', walk_reachable ms x' z *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `x IN FDOM ms.ms_nodes` by
        metis_tac[SUBSET_DEF, flookup_thm] >>
      `x <> 0` by (strip_tac >> gvs[]) >>
      (* node_succ_in gives: x' = 0 or MEM x' visited *)
      `x' = 0 \/ MEM x' visited` by (
        `node_succ_in ms x visited` by
          metis_tac[walk_succ_closed_def] >>
        pop_assum mp_tac >> simp[node_succ_in_def] >>
        `?nd. FLOOKUP ms.ms_nodes x = SOME nd` by
          metis_tac[flookup_thm] >>
        simp[] >> Cases_on `nd` >> gvs[] >> simp[]) >>
      gvs[]
      >- (drule walk_reachable_from_zero_gen >> simp[])
      >> first_x_assum irule >>
      metis_tac[walk_succ_closed_def])
  (* phi_op *)
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `x IN FDOM ms.ms_nodes` by gvs[flookup_thm] >>
  `x <> 0` by (strip_tac >> gvs[]) >>
  `node_succ_in ms x visited` by
    metis_tac[walk_succ_closed_def] >>
  pop_assum mp_tac >> simp[node_succ_in_def] >>
  Cases_on `FLOOKUP ms.ms_phi_ops x` >> gvs[] >>
  simp[EVERY_MEM, FORALL_PROD] >>
  disch_then (qspecl_then [`x'`, `pred`] mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `x' = 0` >> gvs[]
  >- (drule walk_reachable_from_zero_gen >> simp[])
  >> first_x_assum irule >> metis_tac[walk_succ_closed_def]
QED

(* Sub-lemma 1: reaching_chain implies walk_reachable for build-produced ms.
   Each step in the chain has a non-phi source (by build_reaching_src_non_phi),
   so the walk_reachable reaching rule applies. *)
Triviality walk_reachable_from_reaching_chain:
  !n fn bp addr_sp a b.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn /\
    reaching_chain ms n a b ==>
    walk_reachable ms a b
Proof
  Induct >> rpt gen_tac >> simp[]
  >- (simp[reaching_chain_def] >> metis_tac[walk_reachable_refl])
  >> simp[Once reaching_chain_def] >> strip_tac
  (* Both cases: apply build_reaching_src_non_phi to get non-phi *)
  >> (
    qpat_assum `FLOOKUP _ a = SOME _`
      (fn th => mp_tac (MATCH_MP
        (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
           build_reaching_src_non_phi)) th)) >>
    strip_tac)
  (* Case mid = b: single step a -> b *)
  >- (
    gvs[] >> match_mp_tac walk_reachable_reaching >>
    qexists_tac `b` >> gvs[walk_reachable_refl])
  (* Case reaching_chain n mid b: IH gives walk_reachable mid b *)
  >> match_mp_tac walk_reachable_reaching >>
  qexists_tac `mid` >> gvs[] >>
  first_x_assum (qspecl_then [`fn`, `bp`, `addr_sp`, `mid`, `b`] mp_tac) >>
  simp[]
QED

(* NRC of the reaching relation gives a reaching_chain (reversed) *)
Triviality nrc_reaching_to_chain:
  !n ms a b.
    NRC (\y x. FLOOKUP ms.ms_reaching x = SOME y /\
               x IN FDOM ms.ms_nodes /\ y IN FDOM ms.ms_nodes) n a b ==>
    reaching_chain ms n b a
Proof
  Induct >> rpt gen_tac
  >- simp[arithmeticTheory.NRC, reaching_chain_def]
  >> simp[arithmeticTheory.NRC] >> strip_tac >>
  (* NRC (SUC n) a b: ∃z. R a z ∧ NRC n z b
     R a z means ms_reaching(z) = a.
     IH gives reaching_chain n b z.
     reaching_chain_extend gives chain (SUC n) b a. *)
  irule reaching_chain_extend >>
  rename1 `NRC _ n z b` >>
  qexists_tac `z` >> simp[]
QED

(* Helper: reaching relation restricted to FDOM is well-founded.
   Uses FINITE_WF_noloops + mem_ssa_reaching_acyclic. *)
Triviality build_reaching_wf:
  !fn bp addr_sp.
    let ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp in
    wf_function fn ==>
    WF (REL_RESTRICT
      (\y x. FLOOKUP ms.ms_reaching x = SOME y)
      (FDOM ms.ms_nodes))
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  qabbrev_tac `ms = mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp` >>
  qabbrev_tac `R = \y x. FLOOKUP ms.ms_reaching x = SOME y` >>
  `FINITE (FDOM ms.ms_nodes)` by simp[FDOM_FINITE] >>
  simp[FINITE_WF_noloops] >>
  simp[relationTheory.irreflexive_def] >>
  rpt strip_tac >>
  (* (REL_RESTRICT R (FDOM ms.ms_nodes))^+ x x => contradiction *)
  `?n. NRC (REL_RESTRICT R (FDOM ms.ms_nodes)) (SUC n) x x` by
    (qpat_x_assum `_ x x` mp_tac >>
     PURE_REWRITE_TAC[arithmeticTheory.TC_eq_NRC] >> simp[]) >>
  (* REL_RESTRICT R S ⊆ R restricted to S elements *)
  `NRC (\y x'. FLOOKUP ms.ms_reaching x' = SOME y /\
                x' IN FDOM ms.ms_nodes /\ y IN FDOM ms.ms_nodes)
       (SUC n) x x` by (
    qpat_x_assum `NRC _ _ _ _` mp_tac >>
    qmatch_goalsub_abbrev_tac `NRC R1 _ _ _ ==> NRC R2 _ _ _` >>
    `!n' a b. NRC R1 n' a b ==> NRC R2 n' a b` suffices_by metis_tac[] >>
    Induct >> simp[arithmeticTheory.NRC] >>
    rpt strip_tac >>
    qexists_tac `z` >> gvs[Abbr `R1`, Abbr `R2`,
      pred_setTheory.REL_RESTRICT_DEF, Abbr `R`] >>
    metis_tac[]) >>
  drule nrc_reaching_to_chain >> strip_tac >>
  (* reaching_chain (SUC n) x x contradicts acyclicity *)
  `x IN FDOM ms.ms_nodes` by (
    qpat_x_assum `NRC _ (SUC n) x x` mp_tac >>
    simp[arithmeticTheory.NRC] >> strip_tac >>
    gvs[pred_setTheory.REL_RESTRICT_DEF]) >>
  `x <> 0` by (
    strip_tac >>
    `0 NOTIN FDOM ms.ms_nodes` by (
      simp[Abbr `ms`, build_zero_not_in_nodes]) >>
    metis_tac[]) >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] mem_ssa_reaching_acyclic) >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`] mp_tac) >>
  gvs[Abbr `ms`] >>
  qexists_tac `x` >> simp[] >>
  qexists_tac `SUC n` >> simp[]
QED

(* Helper: within def_blk, if rd is a non-phi after def_id (by INDEX_OF),
   then walk_reachable ms rd def_id. Uses complete induction on idx_rd - idx_d.
   Reformulated: ms is explicit equality (not let-bound) to avoid Abbr mismatches. *)
Triviality walk_reachable_within_block:
  !fn bp addr_sp ms rd def_id def_iid def_blk def_loc bb idx_rd idx_d.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    (!blk. THE (FLOOKUP ms.ms_nodes rd) <> MnPhi blk) /\
    mn_block (THE (FLOOKUP ms.ms_nodes rd)) = def_blk /\
    lookup_block def_blk fn.fn_blocks = SOME bb /\
    INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes rd)))
             (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_rd /\
    INDEX_OF def_iid (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_d /\
    idx_d < idx_rd ==>
    walk_reachable ms rd def_id
Proof
  rpt gen_tac >> strip_tac >>
  (* Generalize rd for induction *)
  `!n rd' idx_rd'.
     n = idx_rd' - idx_d /\
     rd' IN FDOM ms.ms_nodes /\ rd' <> 0 /\ rd' <> def_id /\
     (!blk. THE (FLOOKUP ms.ms_nodes rd') <> MnPhi blk) /\
     mn_block (THE (FLOOKUP ms.ms_nodes rd')) = def_blk /\
     INDEX_OF (mn_inst_id (THE (FLOOKUP ms.ms_nodes rd')))
              (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_rd' /\
     idx_d < idx_rd' ==>
     walk_reachable ms rd' def_id` suffices_by (
    disch_then (qspecl_then [`idx_rd - idx_d`, `rd`, `idx_rd`] mp_tac) >>
    simp[]) >>
  completeInduct_on `n` >>
  rpt gen_tac >> strip_tac >>
  (* 1. reaching_complete => exists next *)
  `mem_ssa_reaching_complete ms` by (
    `wf_mssa ms` by (gvs[] >> simp[mem_ssa_build_wf]) >>
    fs[wf_mem_ssa_def]) >>
  `?rd_node. FLOOKUP ms.ms_nodes rd' = SOME rd_node` by fs[flookup_thm] >>
  `!blk. rd_node <> MnPhi blk` by (Cases_on `rd_node` >> gvs[]) >>
  `?next. FLOOKUP ms.ms_reaching rd' = SOME next` by (
    qpat_x_assum `mem_ssa_reaching_complete ms` mp_tac >>
    PURE_REWRITE_TAC [mem_ssa_reaching_complete_def] >>
    disch_then (qspecl_then [`rd'`, `rd_node`] mp_tac) >>
    simp[]) >>
  (* 2. build_reaching_same_block => next properties *)
  use_build_lemma build_reaching_same_block [`bp`, `fn`, `addr_sp`, `rd'`,
    `next`, `def_id`, `def_iid`, `def_blk`, `def_loc`, `bb`, `idx_rd'`,
    `idx_d`] >>
  (* Re-establish conclusions in ms form *)
  `next IN FDOM ms.ms_nodes` by gvs[] >>
  `!blk. THE (FLOOKUP ms.ms_nodes next) <> MnPhi blk` by gvs[] >>
  `mn_block (THE (FLOOKUP ms.ms_nodes next)) = def_blk` by gvs[] >>
  (* 3. Case split on next = def_id *)
  Cases_on `next = def_id`
  >- ((* BASE: walk_reachable_reaching + refl *)
    irule walk_reachable_reaching >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `def_id` >>
    conj_tac
    >- (qpat_x_assum `next = def_id` (SUBST1_TAC o GSYM) >>
        first_assum ACCEPT_TAC)
    >> simp[walk_reachable_refl])
  >> (* STEP: reaching + IH *)
  irule walk_reachable_reaching >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `next` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* 4. Establish FLOOKUP and non-phi for next *)
  `?next_node. FLOOKUP ms.ms_nodes next = SOME next_node` by fs[flookup_thm] >>
  `THE (FLOOKUP ms.ms_nodes next) = next_node` by simp[] >>
  `!blk. next_node <> MnPhi blk` by (
    qpat_x_assum `!blk. THE (FLOOKUP ms.ms_nodes next) <> MnPhi blk` mp_tac >>
    simp[]) >>
  (* 5. MEM next's inst_id in block *)
  use_build_lemma build_node_mem_in_block
    [`bp`, `fn`, `addr_sp`, `next`, `next_node`, `bb`] >>
  `?idx_next. INDEX_OF (mn_inst_id next_node)
              (MAP (\i. i.inst_id) bb.bb_instructions) = SOME idx_next` by (
    Cases_on `INDEX_OF (mn_inst_id next_node)
                       (MAP (\i. i.inst_id) bb.bb_instructions)` >>
    gvs[INDEX_OF_eq_NONE]) >>
  (* 6. idx_d < idx_next *)
  use_build_lemma2 build_same_block_reaching_closest
    [`bp`, `fn`, `addr_sp`, `rd'`, `next`,
     `def_id`, `def_iid`, `def_blk`, `def_loc`]
    [`bb`, `idx_rd'`, `idx_next`, `idx_d`] >>
  (* 7. idx_next < idx_rd' *)
  use_build_lemma build_same_block_reaching_index
    [`bp`, `fn`, `addr_sp`, `rd'`, `next`] >>
  `idx_next < idx_rd'` by (
    `bb' = bb` by (
      `lookup_block def_blk fn.fn_blocks = SOME bb'` by gvs[] >>
      gvs[]) >>
    gvs[] >>
    simp[arithmeticTheory.GREATER_DEF]) >>
  (* 8. Apply IH *)
  first_x_assum (qspecl_then [`idx_next - idx_d`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`next`, `idx_next`] mp_tac) >>
  simp[]
QED

(* Consolidated reaching predecessor facts: for a non-phi node rd with
   sdom def_blk, its reaching predecessor y satisfies all the key properties. *)
Triviality reaching_predecessor_props:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    wf_function fn /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\
    (!blk. THE (FLOOKUP ms.ms_nodes rd) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] ==>
    ?y yn. FLOOKUP ms.ms_reaching rd = SOME y /\
        FLOOKUP ms.ms_nodes y = SOME yn /\
        y <> 0 /\ y IN FDOM ms.ms_nodes /\
        dominates dom def_blk (mn_block yn) /\
        dominates dom (mn_block yn)
                      (mn_block (THE (FLOOKUP ms.ms_nodes rd)))
Proof
  rpt strip_tac >>
  qpat_x_assum `ms = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dom = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  sg `wf_mssa ms` >- simp[Abbr `ms`, mem_ssa_build_wf] >>
  sg `mem_ssa_reaching_complete ms` >- fs[wf_mem_ssa_def] >>
  sg `?rd_node. FLOOKUP ms.ms_nodes rd = SOME rd_node`
  >- metis_tac[flookup_thm] >>
  sg `?y. FLOOKUP ms.ms_reaching rd = SOME y`
  >- (fs[mem_ssa_reaching_complete_def] >>
      first_x_assum (qspecl_then [`rd`, `rd_node`] mp_tac) >>
      simp[] >> Cases_on `rd_node` >> gvs[]) >>
  sg `y <> 0`
  >- (mp_tac (SIMP_RULE (srw_ss()) [] build_sdom_reaching_nonzero) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `rd`, `y`,
        `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`]) >>
  sg `y IN FDOM ms.ms_nodes`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
         build_reaching_step_in_fdom)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `rd`, `y`] mp_tac) >>
      simp[Abbr `ms`]) >>
  sg `dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes y)))`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
         build_reaching_dominated_by_ancestor)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `rd`, `y`,
        `def_blk`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`]) >>
  sg `?yn. FLOOKUP ms.ms_nodes y = SOME yn`
  >- metis_tac[flookup_thm] >>
  (* dom blk(y) blk(rd) *)
  sg `dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes y)))
                    (mn_block (THE (FLOOKUP ms.ms_nodes rd)))`
  >- (mp_tac mem_ssa_reaching_def_dominates >>
      disch_then (qspecl_then [`cfg_analyze fn`, `dom`, `bp`, `fn`, `addr_sp`,
        `ms`, `rd`, `y`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`]) >>
  (* Resolve THE(FLOOKUP) *)
  sg `THE (FLOOKUP ms.ms_nodes y) = yn` >- simp[] >>
  qexistsl_tac [`y`, `yn`] >> gvs[]
QED

(* Phi case helper for walk_reachable_block_exit: when reaching predecessor y
   is a phi at phi_blk with def_blk <> phi_blk, pick z = y.
   Takes def_blk <> phi_blk as precondition (caller establishes via
   build_reaching_phi_location at a nesting level where simp[Abbr] works). *)
Triviality walk_reachable_block_exit_phi_case:
  !x y phi_blk def_id def_blk ms dom.
    y IN FDOM ms.ms_nodes /\ y <> 0 /\
    FLOOKUP ms.ms_nodes y = SOME (MnPhi phi_blk) /\
    dominates dom def_blk phi_blk /\
    def_blk <> phi_blk /\
    walk_reachable ms x y ==>
    ?z. walk_reachable ms x z /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
        (z = def_id \/
         (strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes z))) /\
          mn_block (THE (FLOOKUP ms.ms_nodes z)) <>
          mn_block (THE (FLOOKUP ms.ms_nodes x))) \/
         (?b. THE (FLOOKUP ms.ms_nodes z) = MnPhi b /\
              strict_dominates dom def_blk b))
Proof
  rpt strip_tac >>
  qexists_tac `y` >> simp[] >>
  disj2_tac >> disj2_tac >>
  fs[dominatorDefsTheory.strict_dominates_def]
QED

(* Inductive step for walk_reachable_block_exit, extracted as standalone
   Triviality to avoid Abbrev/batch issues. Takes ms=, dom= as plain
   equalities and the IH in expanded form. *)
Triviality walk_reachable_block_exit_step:
  !fn bp addr_sp x def_id def_iid def_blk def_loc ms dom.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    wf_function fn /\
    x IN FDOM ms.ms_nodes /\ x <> 0 /\ x <> def_id /\
    (!blk. THE (FLOOKUP ms.ms_nodes x) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes x))) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    (* IH in expanded form — uses dominates (not strict) in 2nd disjunct
       to handle blk(y)=def_blk case *)
    (!y. y IN FDOM ms.ms_nodes /\ FLOOKUP ms.ms_reaching x = SOME y /\
         y <> 0 /\ y <> def_id /\
         (!blk. THE (FLOOKUP ms.ms_nodes y) <> MnPhi blk) /\
         strict_dominates dom def_blk
           (mn_block (THE (FLOOKUP ms.ms_nodes y))) ==>
         ?z. walk_reachable ms y z /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
             dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes z)))
               (mn_block (THE (FLOOKUP ms.ms_nodes y))) /\
             (z = def_id \/
              (dominates dom def_blk
                 (mn_block (THE (FLOOKUP ms.ms_nodes z))) /\
               (!blk. THE (FLOOKUP ms.ms_nodes z) <> MnPhi blk) /\
               mn_block (THE (FLOOKUP ms.ms_nodes z)) <>
               mn_block (THE (FLOOKUP ms.ms_nodes y)) /\
               (mn_block (THE (FLOOKUP ms.ms_nodes z)) = def_blk ==>
                z = LAST (fmap_lookup_list ms.ms_block_defs def_blk))) \/
              (?b. THE (FLOOKUP ms.ms_nodes z) = MnPhi b /\
                   strict_dominates dom def_blk b))) ==>
    ?z. walk_reachable ms x z /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
        dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes z)))
          (mn_block (THE (FLOOKUP ms.ms_nodes x))) /\
        (z = def_id \/
         (dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes z))) /\
          (!blk. THE (FLOOKUP ms.ms_nodes z) <> MnPhi blk) /\
          mn_block (THE (FLOOKUP ms.ms_nodes z)) <>
          mn_block (THE (FLOOKUP ms.ms_nodes x)) /\
          (mn_block (THE (FLOOKUP ms.ms_nodes z)) = def_blk ==>
           z = LAST (fmap_lookup_list ms.ms_block_defs def_blk))) \/
         (?b. THE (FLOOKUP ms.ms_nodes z) = MnPhi b /\
              strict_dominates dom def_blk b))
Proof
  rpt strip_tac >>
  (* Convert ms=/dom= to Abbrev to prevent fs/gvs/simp from expanding *)
  qpat_x_assum `ms = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dom = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  (* Use reaching_predecessor_props to get all y-related facts at once *)
  mp_tac reaching_predecessor_props >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `x`, `def_id`, `def_iid`,
    `def_blk`, `def_loc`, `ms`, `dom`] mp_tac) >>
  (impl_tac >- simp[Abbr `ms`, Abbr `dom`]) >> strip_tac >>
  sg `walk_reachable ms x y`
  >- (match_mp_tac walk_reachable_reaching >>
      qexists_tac `y` >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (sg `?x_node. FLOOKUP ms.ms_nodes x = SOME x_node`
          >- metis_tac[flookup_thm] >>
          Cases_on `x_node` >> fs[])
      >> simp[walk_reachable_refl]) >>
  Cases_on `y = def_id`
  >- (qexists_tac `def_id` >>
      `THE (FLOOKUP ms.ms_nodes def_id) = MnDef def_iid def_blk def_loc`
        by simp[] >> pop_assum SUBST_ALL_TAC >>
      gvs[flookup_thm, mn_block_def,
          dominatorDefsTheory.strict_dominates_def]) >>
  Cases_on `?phi_blk. yn = MnPhi phi_blk`
  >- (
    (* Phi case: z = y, which is a phi with sdom.
       Need def_blk <> phi_blk: by build_reaching_phi_location,
       phi is at blk(x) or block_defs(phi_blk)=[]; both contradict our assumptions. *)
    gvs[] >>
    sg `def_blk <> phi_blk` >- (
      mp_tac build_reaching_phi_location >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `x`, `y`,
        `phi_blk`, `ms`] mp_tac) >>
      (impl_tac >- simp[Abbr `ms`]) >> strip_tac
      >- fs[dominatorDefsTheory.strict_dominates_def]
      >> metis_tac[]) >>
    qexists_tac `y` >>
    `THE (FLOOKUP ms.ms_nodes y) = MnPhi phi_blk` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    sg `strict_dominates dom def_blk phi_blk`
    >- fs[dominatorDefsTheory.strict_dominates_def, mn_block_def] >>
    simp[mn_block_def]
  ) >>
  sg `!b. yn <> MnPhi b` >- metis_tac[] >>
  sg `?x_node. FLOOKUP ms.ms_nodes x = SOME x_node`
  >- metis_tac[flookup_thm] >>
  Cases_on `mn_block yn = mn_block (THE (FLOOKUP ms.ms_nodes x))`
  >- (
    (* Same block case: apply IH to y, use ASSUME_TAC to avoid splitting disjunction *)
    sg `THE (FLOOKUP ms.ms_nodes y) = yn` >- simp[] >>
    sg `!blk. THE (FLOOKUP ms.ms_nodes y) <> MnPhi blk` >- simp[] >>
    sg `strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes y)))`
    >- fs[] >>
    first_x_assum (qspec_then `y` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qx_choose_then `z` ASSUME_TAC) >>
    qexists_tac `z` >>
    sg `walk_reachable ms x z`
    >- (irule walk_reachable_trans >> qexists_tac `y` >> gvs[]) >>
    (* Substitute THE(FLOOKUP y) = yn, then mn_block yn = mn_block(THE(FLOOKUP x))
       to align IH's blk(z)<>blk(y) with goal's blk(z)<>blk(x) *)
    qpat_x_assum `THE _ = yn` (SUBST_ALL_TAC o SYM) >>
    qpat_x_assum `mn_block _ = mn_block _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
    gvs[]
  )
  >> (
    (* Different block case: z = y directly works. *)
    qexists_tac `y` >>
    sg `THE (FLOOKUP ms.ms_nodes y) = yn` >- simp[] >>
    sg `FLOOKUP ms.ms_nodes y = SOME yn`
    >- (Cases_on `FLOOKUP ms.ms_nodes y` >> gvs[flookup_thm]) >>
    gvs[] >>
    (* New LAST conjunct: if mn_block yn = def_blk then y = LAST(...) *)
    strip_tac >>
    mp_tac build_reaching_cross_block_is_last >>
    disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `x`, `y`, `yn`, `ms`]
      mp_tac) >>
    simp[Abbr `ms`] >>
    (impl_tac >- gvs[]) >>
    simp[]
  )
QED

(* Helper: from a non-phi node at block B with sdom def_blk B,
   follow reaching edges until we exit the block. The result z satisfies:
   - walk_reachable ms rd z
   - z <> 0 /\ z IN FDOM
   - z = def_id, OR z is at a different block with sdom, OR z is a phi with sdom *)
Triviality walk_reachable_block_exit:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    wf_function fn /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    (!blk. THE (FLOOKUP ms.ms_nodes rd) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] ==>
    ?z. walk_reachable ms rd z /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
        dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes z)))
          (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
        (z = def_id \/
         (dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes z))) /\
          (!blk. THE (FLOOKUP ms.ms_nodes z) <> MnPhi blk) /\
          mn_block (THE (FLOOKUP ms.ms_nodes z)) <>
          mn_block (THE (FLOOKUP ms.ms_nodes rd)) /\
          (mn_block (THE (FLOOKUP ms.ms_nodes z)) = def_blk ==>
           z = LAST (fmap_lookup_list ms.ms_block_defs def_blk))) \/
         (?b. THE (FLOOKUP ms.ms_nodes z) = MnPhi b /\
              strict_dominates dom def_blk b))
Proof
  rpt strip_tac >>
  (* Get WF of reaching on FDOM — ms= is a plain equality *)
  sg `WF (REL_RESTRICT (\y x. FLOOKUP ms.ms_reaching x = SOME y)
          (FDOM ms.ms_nodes))`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_reaching_wf)) >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`] mp_tac) >>
      simp[]) >>
  (* WF induction gives: ∀x. P(x). Specialize to rd. *)
  pop_assum (mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  disch_then (qspec_then `\rd'.
    rd' IN FDOM ms.ms_nodes /\ rd' <> 0 /\ rd' <> def_id /\
    (!blk. THE (FLOOKUP ms.ms_nodes rd') <> MnPhi blk) /\
    strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd'))) ==>
    ?z. walk_reachable ms rd' z /\ z <> 0 /\ z IN FDOM ms.ms_nodes /\
        dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes z)))
          (mn_block (THE (FLOOKUP ms.ms_nodes rd'))) /\
        (z = def_id \/
         (dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes z))) /\
          (!blk. THE (FLOOKUP ms.ms_nodes z) <> MnPhi blk) /\
          mn_block (THE (FLOOKUP ms.ms_nodes z)) <>
          mn_block (THE (FLOOKUP ms.ms_nodes rd')) /\
          (mn_block (THE (FLOOKUP ms.ms_nodes z)) = def_blk ==>
           z = LAST (fmap_lookup_list ms.ms_block_defs def_blk))) \/
         (?b. THE (FLOOKUP ms.ms_nodes z) = MnPhi b /\
              strict_dominates dom def_blk b))` mp_tac) >>
  BETA_TAC >>
  PURE_REWRITE_TAC [pred_setTheory.REL_RESTRICT_DEF] >>
  BETA_TAC >>
  strip_tac >>
  (* WF result as assumption: (∀x. IH ⇒ P) ⇒ ∀x. P
     Prove the inductive step, get ∀x. P, specialize to rd. *)
  pop_assum mp_tac >>
  impl_tac
  >- (
    rpt strip_tac >>
    mp_tac walk_reachable_block_exit_step >>
    disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `x`, `def_id`,
      `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >>
        first_x_assum (qspec_then `y` mp_tac) >>
        impl_tac >- simp[] >>
        simp[]) >>
    simp[]
  ) >>
  disch_then (qspec_then `rd` mp_tac) >>
  simp[]
QED

(* INDEX_OF in MAP: if ALL_DISTINCT (MAP f l) and INDEX_OF x l = SOME i,
   then INDEX_OF (f x) (MAP f l) = SOME i *)
Triviality INDEX_OF_MAP:
  !f l x i.
    ALL_DISTINCT (MAP f l) /\
    INDEX_OF x l = SOME i ==>
    INDEX_OF (f x) (MAP f l) = SOME i
Proof
  rpt strip_tac >>
  fs[INDEX_OF_eq_SOME] >>
  simp[INDEX_OF_eq_SOME, EL_MAP] >>
  rpt strip_tac >>
  gvs[EL_MAP] >>
  spose_not_then strip_assume_tac >>
  `EL j (MAP f l) = EL i (MAP f l)` by simp[EL_MAP] >>
  `j < LENGTH (MAP f l)` by simp[] >>
  `i < LENGTH (MAP f l)` by simp[] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Block_defs ordering transfers to instruction ordering.
   If a comes before b in block_defs(lbl), then mn_inst_id(a) comes before
   mn_inst_id(b) in MAP inst_id bb.bb_instructions.
   Chains: build_block_defs_all_distinct, build_block_defs_iids_sublist,
           INDEX_OF_MAP, sublist_index_mono. *)
Triviality block_defs_inst_order:
  !fn bp addr_sp lbl bb a b ia ib.
    wf_function fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    MEM a (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl) /\
    MEM b (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl) /\
    INDEX_OF a (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl) = SOME ia /\
    INDEX_OF b (fmap_lookup_list
      (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp).ms_block_defs lbl) = SOME ib /\
    ia < ib ==>
    ?ja jb.
      INDEX_OF (mn_inst_id (THE (FLOOKUP
        (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp).ms_nodes a)))
        (MAP (\i. i.inst_id) bb.bb_instructions) = SOME ja /\
      INDEX_OF (mn_inst_id (THE (FLOOKUP
        (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp).ms_nodes b)))
        (MAP (\i. i.inst_id) bb.bb_instructions) = SOME jb /\
      ja < jb
Proof
  rpt strip_tac >>
  qabbrev_tac `ms = mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp` >>
  qabbrev_tac `bdefs = fmap_lookup_list ms.ms_block_defs lbl` >>
  (* block_defs ALL_DISTINCT *)
  sg `ALL_DISTINCT bdefs` >- simp[Abbr `bdefs`, Abbr `ms`, build_block_defs_all_distinct] >>
  (* Get the sublist *)
  mp_tac (Q.SPECL [`fn`, `bp`, `addr_sp`, `lbl`, `bb`]
    build_block_defs_iids_sublist) >>
  simp[Abbr `ms`, Abbr `bdefs`] >> strip_tac >>
  qabbrev_tac `ms = mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp` >>
  qabbrev_tac `bdefs = fmap_lookup_list ms.ms_block_defs lbl` >>
  (* instruction ids ALL_DISTINCT per block *)
  sg `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`
  >- (irule fn_inst_ids_block_distinct >>
      gvs[venomWfTheory.wf_function_def] >> metis_tac[lookup_block_props]) >>
  (* Abbreviate the inst_id extraction function *)
  qabbrev_tac `idf = \aid. mn_inst_id (THE (FLOOKUP ms.ms_nodes aid))` >>
  (* MAP idf bdefs is ALL_DISTINCT (sublist of ALL_DISTINCT) *)
  sg `ALL_DISTINCT (MAP idf bdefs)`
  >- (imp_res_tac rich_listTheory.sublist_ALL_DISTINCT >>
      gvs[Abbr `idf`]) >>
  (* INDEX_OF_MAP for a and b *)
  sg `INDEX_OF (idf a) (MAP idf bdefs) = SOME ia`
  >- (match_mp_tac INDEX_OF_MAP >> simp[]) >>
  sg `INDEX_OF (idf b) (MAP idf bdefs) = SOME ib`
  >- (match_mp_tac INDEX_OF_MAP >> simp[]) >>
  (* sublist_index_mono *)
  sg `sublist (MAP idf bdefs) (MAP (\i. i.inst_id) bb.bb_instructions)`
  >- gvs[Abbr `idf`] >>
  drule cfgHelpersTheory.sublist_index_mono >>
  disch_then (qspecl_then [`idf a`, `idf b`, `ia`, `ib`] mp_tac) >>
  simp[Abbr `idf`]
QED

(* Helper: if node = LAST(block_defs(def_blk)) and node <> def_id,
   then walk_reachable ms node def_id. Uses build-level lemmas directly
   (no ms variable — avoids Abbrev mismatch issues). *)
Triviality walk_reachable_last_to_def:
  !fn bp addr_sp node def_id def_iid def_blk def_loc.
    wf_function fn /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_nodes def_id =
      SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
      def_blk <> [] /\
    node IN FDOM (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes /\
    node <> 0 /\ node <> def_id /\
    node = LAST (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
      def_blk) ==>
    walk_reachable (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp) node def_id
Proof
  rpt gen_tac >> strip_tac >>
  (* node = LAST(block_defs) is MnDef at def_blk *)
  sg `?niid nloc. FLOOKUP (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes node =
    SOME (MnDef niid def_blk nloc)`
  >- (mp_tac (Q.SPECL [`fn`, `bp`, `addr_sp`, `node`, `def_blk`]
        build_block_defs_are_defs) >>
      simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  (* Get bb for def_blk via def_id *)
  sg `?bb. lookup_block def_blk fn.fn_blocks = SOME bb /\
    MEM def_iid (MAP (\i. i.inst_id) bb.bb_instructions) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_inst_id_in_block)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `def_id`,
        `MnDef def_iid def_blk def_loc`] mp_tac) >>
      simp[mn_block_def, mn_inst_id_def]) >>
  (* def_id in block_defs *)
  sg `MEM def_id (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
    def_blk)`
  >- (match_mp_tac build_MnDef_in_block_defs >> simp[]) >>
  (* ALL_DISTINCT block_defs *)
  sg `ALL_DISTINCT (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
    def_blk)`
  >- simp[build_block_defs_all_distinct] >>
  (* INDEX_OF for def_id and node *)
  sg `?id_d. INDEX_OF def_id (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
    def_blk) = SOME id_d`
  >- (Cases_on `INDEX_OF def_id (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
        def_blk)` >> gvs[INDEX_OF_eq_NONE]) >>
  sg `?id_n. INDEX_OF node (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
    def_blk) = SOME id_n`
  >- (Cases_on `INDEX_OF node (fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
        (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
        def_blk)` >> gvs[INDEX_OF_eq_NONE, rich_listTheory.MEM_LAST_NOT_NIL]) >>
  (* id_d < id_n *)
  sg `id_d < id_n`
  >- metis_tac[cfgHelpersTheory.index_of_last_max,
               rich_listTheory.MEM_LAST_NOT_NIL] >>
  (* MEM def_blk dfs_pre *)
  sg `MEM def_blk (cfg_analyze fn).cfg_dfs_pre`
  >- (mp_tac (Q.SPECL [`bp`, `fn`, `addr_sp`, `def_id`,
        `MnDef def_iid def_blk def_loc`] build_node_block_reachable) >>
      simp[mn_block_def] >> strip_tac >>
      mp_tac (Q.SPEC `fn` cfgAnalysisPropsTheory.cfg_analyze_reachable_sets) >>
      simp[] >> strip_tac >> gvs[pred_setTheory.EXTENSION]) >>
  (* block_defs_inst_order *)
  mp_tac (Q.SPECL [`fn`, `bp`, `addr_sp`, `def_blk`, `bb`,
    `def_id`, `node`, `id_d`, `id_n`] block_defs_inst_order) >>
  simp[rich_listTheory.MEM_LAST_NOT_NIL] >> strip_tac >>
  (* Apply walk_reachable_within_block *)
  match_mp_tac walk_reachable_within_block >>
  qexistsl_tac [`fn`, `bp`, `addr_sp`, `def_iid`, `def_blk`, `def_loc`,
                 `bb`, `jb`, `ja`] >>
  gvs[mn_inst_id_def, mn_block_def]
QED

(* If qb is a successor of p in the CFG, then p is a predecessor of qb. *)
Triviality cfg_succ_implies_pred[local]:
  !fn p qb.
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) p /\
    MEM qb (cfg_succs_of (cfg_analyze fn) p) ==>
    MEM p (cfg_preds_of (cfg_analyze fn) qb)
Proof
  rpt strip_tac >>
  simp[cfgHelpersTheory.cfg_analyze_preds,
       cfgHelpersTheory.mem_build_preds] >>
  sg `MEM p (fn_labels fn)`
  >- metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels] >>
  fs[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  qexists_tac `bb` >> gvs[] >>
  gvs[GSYM cfgDefsTheory.cfg_succs_of_def,
      cfgHelpersTheory.cfg_analyze_succs]
QED

(* dominates ordering transfers to INDEX_OF ordering in DFS pre-order.
   Reusable helper: covers both x = y (index equality) and x <> y (strict). *)
Triviality dominates_index_le:
  !fn ebb x y i j.
    wf_function fn /\ entry_block fn = SOME ebb /\
    dominates (dom_analyze (cfg_analyze fn) fn) x y /\
    cfg_reachable_of (cfg_analyze fn) y /\
    ALL_DISTINCT (cfg_analyze fn).cfg_dfs_pre /\
    INDEX_OF x (cfg_analyze fn).cfg_dfs_pre = SOME i /\
    INDEX_OF y (cfg_analyze fn).cfg_dfs_pre = SOME j
    ==> i <= j
Proof
  rpt strip_tac >>
  Cases_on `x = y`
  >- (gvs[INDEX_OF_eq_SOME, ALL_DISTINCT_EL_IMP]) >>
  sg `MEM x
        (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators y)`
  >- (gvs[dominatorDefsTheory.dominates_def,
          dominatorDefsTheory.strict_dominates_def] >> res_tac) >>
  mp_tac dominatorProofsTheory.dom_pre_order >>
  disch_then (qspecl_then [`fn`, `ebb`, `x`, `y`] mp_tac) >>
  simp[]
QED

(* Helper: Given phi operand properties + IH, prove walk_reachable ms q def_id.
   Extracted from walk_reachable_from_sdom_phi to avoid batch-mode issues
   with qpat_x_assum pattern matching after simp simplifies phi_ops_structure
   conjuncts. All needed facts are explicit hypotheses here. *)
Triviality walk_reachable_phi_operand_to_def:
  !ms dom cfg dfs_pre fn bp addr_sp def_id def_iid def_blk def_loc
   ebb idx q qb qi ops w p ip.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    q IN FDOM ms.ms_nodes /\ q <> 0 /\ q <> def_id /\
    FLOOKUP ms.ms_nodes q = SOME (MnPhi qb) /\
    strict_dominates dom def_blk qb /\
    INDEX_OF qb dfs_pre = SOME qi /\ qi <= idx /\
    cfg_reachable_of cfg qb /\
    cfg_reachable_of cfg p /\
    MEM p (cfg_preds_of cfg qb) /\
    dominates dom def_blk p /\
    INDEX_OF p dfs_pre = SOME ip /\ ip < qi /\
    FLOOKUP ms.ms_phi_ops q = SOME ops /\
    MEM (w, p) ops /\
    (w <> 0 ==> w IN FDOM ms.ms_nodes) /\
    (w <> 0 ==> dominates dom (mn_block (THE (FLOOKUP ms.ms_nodes w))) p) /\
    (!c. w <> 0 /\ dominates dom c p /\ fmap_lookup_list ms.ms_block_defs c <> [] ==>
         dominates dom c (mn_block (THE (FLOOKUP ms.ms_nodes w)))) /\
    (w <> 0 /\ (!b. THE (FLOOKUP ms.ms_nodes w) <> MnPhi b) /\
     fmap_lookup_list ms.ms_block_defs (mn_block (THE (FLOOKUP ms.ms_nodes w))) <> [] ==>
     w = LAST (fmap_lookup_list ms.ms_block_defs (mn_block (THE (FLOOKUP ms.ms_nodes w))))) /\
    (w <> 0 /\ (?b. THE (FLOOKUP ms.ms_nodes w) = MnPhi b) ==>
     fmap_lookup_list ms.ms_block_defs (mn_block (THE (FLOOKUP ms.ms_nodes w))) = []) /\
    (!c. dominates dom c p /\ fmap_lookup_list ms.ms_block_defs c <> [] ==> w <> 0)
    ==>
    walk_reachable ms q def_id
Proof
  rpt strip_tac >>
  qpat_x_assum `ms = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dom = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `cfg = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dfs_pre = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  (* Reduce to walk_reachable ms w def_id via phi_op rule *)
  irule walk_reachable_phi_op >>
  conj_tac >- (qexists_tac `qb` >> simp[]) >>
  MAP_EVERY qexists_tac [`ops`, `p`, `w`] >> simp[] >>
  (* Establish w <> 0 *)
  sg `w <> 0`
  >- (first_x_assum (qspec_then `def_blk` mp_tac) >>
      simp[] >> fs[dominatorDefsTheory.strict_dominates_def]) >>
  sg `w IN FDOM ms.ms_nodes` >- res_tac >>
  sg `dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes w)))`
  >- (first_x_assum (qspec_then `def_blk` mp_tac) >>
      simp[] >> fs[dominatorDefsTheory.strict_dominates_def]) >>
  sg `?wn. FLOOKUP ms.ms_nodes w = SOME wn`
  >- (Cases_on `FLOOKUP ms.ms_nodes w` >> gvs[flookup_thm]) >>
  sg `THE (FLOOKUP ms.ms_nodes w) = wn` >- simp[] >>
  pop_assum SUBST_ALL_TAC >>
  (* Three-way case split on w *)
  Cases_on `w = def_id`
  >- (gvs[] >> once_rewrite_tac[walk_reachable_cases] >> simp[]) >>
  Cases_on `mn_block wn = def_blk`
  >- (sg `!blk. wn <> MnPhi blk`
      >- (spose_not_then ASSUME_TAC >> res_tac >> gvs[]) >>
      sg `w = LAST (fmap_lookup_list ms.ms_block_defs def_blk)`
      >- (res_tac >> gvs[]) >>
      mp_tac walk_reachable_last_to_def >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `w`, `def_id`,
        `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[Abbr `ms`]) >>
  sg `strict_dominates dom def_blk (mn_block wn)`
  >- gvs[dominatorDefsTheory.strict_dominates_def] >>
  sg `cfg_reachable_of cfg (mn_block wn)`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_block_reachable)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `w`, `wn`] mp_tac) >>
      simp[Abbr `ms`, Abbr `cfg`]) >>
  sg `MEM (mn_block wn) dfs_pre`
  >- (mp_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
      disch_then (qspec_then `fn` mp_tac) >>
      simp[Abbr `cfg`] >> strip_tac >> gvs[pred_setTheory.EXTENSION] >>
      first_x_assum (qspec_then `mn_block wn` mp_tac) >> simp[]) >>
  sg `?widx. INDEX_OF (mn_block wn) dfs_pre = SOME widx`
  >- (Cases_on `INDEX_OF (mn_block wn) dfs_pre` >> gvs[INDEX_OF_eq_NONE]) >>
  sg `widx <= ip`
  >- (mp_tac dominates_index_le >>
      disch_then (qspecl_then [`fn`, `ebb`, `mn_block wn`, `p`,
        `widx`, `ip`] mp_tac) >>
      simp[Abbr `cfg`, Abbr `dom`, Abbr `dfs_pre`]) >>
  qpat_x_assum `!m. m < idx ==> _` (qspec_then `widx` mp_tac) >>
  simp[]
QED

(* INDEX_OF x l = SOME i ==> MEM x l.
   INDEX_OF_SOME_MEM is local to cfgHelpers, so we provide our own. *)
Triviality index_of_some_mem:
  !x l i. INDEX_OF x l = SOME i ==> MEM x l
Proof
  CCONTR_TAC >> gvs[GSYM INDEX_OF_eq_NONE]
QED

(* A strictly dominated label cannot be the entry block. *)
Triviality sdom_not_entry:
  !fn ebb d lbl.
    wf_function fn /\ entry_block fn = SOME ebb /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    cfg_reachable_of (cfg_analyze fn) d /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) d lbl
    ==> lbl <> ebb.bb_label
Proof
  rpt strip_tac >> gvs[] >>
  mp_tac dominatorAnalysisPropsTheory.dom_entry_dominates_all >>
  disch_then (qspecl_then [`fn`, `cfg_analyze fn`, `ebb`, `d`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[dominatorProofsTheory.dominates_antisym_proof,
            dominatorDefsTheory.strict_dominates_def]
QED

(* Phi case of walk_reachable_from_sdom: a phi node with sdom reaches def_id.
   Uses walk_reachable_phi_operand_to_def for the operand-level reasoning. *)
Triviality walk_reachable_from_sdom_phi:
  !fn bp addr_sp def_id def_iid def_blk def_loc ms dom cfg dfs_pre
   ebb idx q qb qi.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    q IN FDOM ms.ms_nodes /\ q <> 0 /\ q <> def_id /\
    FLOOKUP ms.ms_nodes q = SOME (MnPhi qb) /\
    strict_dominates dom def_blk qb /\
    INDEX_OF qb dfs_pre = SOME qi /\ qi <= idx ==>
    walk_reachable ms q def_id
Proof
  rpt strip_tac >>
  qpat_x_assum `ms = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dom = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `cfg = _`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `dfs_pre = cfg.cfg_dfs_pre`
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  (* P1: MEM qb dfs_pre *)
  sg `MEM qb dfs_pre` >- (imp_res_tac index_of_some_mem) >>
  (* P2: cfg_reachable_of cfg qb *)
  sg `cfg_reachable_of cfg qb` >- res_tac >>
  (* P3: cfg_reachable_of cfg def_blk *)
  sg `cfg_reachable_of cfg def_blk`
  >- (fs[dominatorDefsTheory.strict_dominates_def, Abbr `dom`, Abbr `cfg`] >>
      metis_tac[dominatorProofsTheory.dominates_reachable]) >>
  (* P4: qb <> entry — uses extracted helper *)
  sg `qb <> ebb.bb_label`
  >- (mp_tac sdom_not_entry >>
      disch_then (qspecl_then [`fn`, `ebb`, `def_blk`, `qb`] mp_tac) >>
      simp[Abbr `dom`, Abbr `cfg`]) >>
  (* P5: DFS tree parent predecessor *)
  sg `dfs_pre = SND (dfs_pre_walk cfg.cfg_succs [] ebb.bb_label)`
  >- (simp[Abbr `dfs_pre`, Abbr `cfg`,
           cfgDefsTheory.cfg_analyze_def, LET_THM] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
  mp_tac (CONJUNCT1 cfgHelpersTheory.dfs_pre_walk_has_pred) >>
  disch_then (qspecl_then [`cfg.cfg_succs`, `[]`, `ebb.bb_label`,
                           `qb`] mp_tac) >>
  qpat_x_assum `dfs_pre = SND _`
    (fn eq => REWRITE_TAC [GSYM eq]) >>
  (impl_tac >- simp[]) >>
  simp[GSYM cfgDefsTheory.cfg_succs_of_def] >>
  strip_tac >>
  (* P6: MEM p dfs_pre *)
  sg `MEM p dfs_pre` >- (imp_res_tac index_of_some_mem) >>
  (* P7: cfg_reachable_of cfg p *)
  sg `cfg_reachable_of cfg p` >- res_tac >>
  (* P8: MEM p (cfg_preds_of cfg qb) *)
  sg `MEM p (cfg_preds_of cfg qb)`
  >- (mp_tac cfg_succ_implies_pred >>
      disch_then (qspecl_then [`fn`, `p`, `qb`] mp_tac) >>
      simp[Abbr `cfg`]) >>
  (* P9: phi_ops exist *)
  sg `?ops. FLOOKUP ms.ms_phi_ops q = SOME ops /\
            MAP SND ops = cfg_preds_of cfg qb`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_phi_has_ops)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`] mp_tac) >>
      simp[phi_has_ops_def, Abbr `ms`, Abbr `cfg`, Abbr `dom`]) >>
  (* P10: find operand (w, p) in ops *)
  sg `MEM p (MAP SND ops)` >- gvs[] >>
  sg `?w. MEM (w, p) ops`
  >- (fs[listTheory.MEM_MAP] >> rename1 `MEM wp ops` >>
      qexists_tac `FST wp` >> Cases_on `wp` >> gvs[]) >>
  (* P11: dominates dom def_blk p — via dom_dominates_pred *)
  sg `dominates dom def_blk p`
  >- (mp_tac dominatorProofsTheory.dom_dominates_pred >>
      disch_then (qspecl_then [`fn`, `cfg`, `ebb`, `def_blk`, `qb`, `p`] mp_tac) >>
      simp[Abbr `dom`, Abbr `cfg`] >>
      fs[dominatorDefsTheory.strict_dominates_def]) >>
  (* Apply walk_reachable_phi_operand_to_def directly *)
  mp_tac walk_reachable_phi_operand_to_def >>
  disch_then (qspecl_then [`ms`, `dom`, `cfg`, `dfs_pre`, `fn`, `bp`, `addr_sp`,
    `def_id`, `def_iid`, `def_blk`, `def_loc`, `ebb`, `idx`, `q`, `qb`, `qi`,
    `ops`, `w`, `p`, `ip`] mp_tac) >>
  (impl_tac >-
    (simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`] >>
     mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_phi_ops_structure)) >>
     disch_then (qspecl_then [`bp`, `fn`, `addr_sp`] mp_tac) >>
     simp[] >>
     simp[phi_ops_structure_ok_def] >>
     disch_then (qspecl_then [`q`, `ops`, `w`, `p`] mp_tac) >>
     simp[] >>
     strip_tac >> simp[])) >>
  simp[]
QED

(* Bidirectional: reachable ↔ MEM in dfs_pre. Avoids expanding cfg_analyze_def. *)
Triviality reachable_mem_dfs_pre:
  !fn x. wf_function fn /\ cfg_reachable_of (cfg_analyze fn) x ==>
         MEM x (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
  gvs[EXTENSION, SPECIFICATION]
QED

Triviality mem_dfs_pre_reachable:
  !fn x. wf_function fn /\ MEM x (cfg_analyze fn).cfg_dfs_pre ==>
         cfg_reachable_of (cfg_analyze fn) x
Proof
  rpt strip_tac >>
  imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
  gvs[EXTENSION, SPECIFICATION]
QED

(* Strict dominance implies strictly smaller INDEX_OF in DFS pre-order.
   Generalizes dominates_index_le to the strict case. *)
Triviality sdom_index_lt:
  !fn ebb x y j.
    wf_function fn /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT (cfg_analyze fn).cfg_dfs_pre /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) x y /\
    cfg_reachable_of (cfg_analyze fn) x /\
    INDEX_OF y (cfg_analyze fn).cfg_dfs_pre = SOME j ==>
    ?i. INDEX_OF x (cfg_analyze fn).cfg_dfs_pre = SOME i /\ i < j
Proof
  rpt strip_tac >>
  gvs[dominatorDefsTheory.strict_dominates_def] >>
  (* MEM x dfs_pre from reachable *)
  imp_res_tac reachable_mem_dfs_pre >>
  sg `?i. INDEX_OF x (cfg_analyze fn).cfg_dfs_pre = SOME i`
  >- (Cases_on `INDEX_OF x (cfg_analyze fn).cfg_dfs_pre` >>
      gvs[INDEX_OF_eq_NONE]) >>
  qexists_tac `i` >> simp[] >>
  (* cfg_reachable y from INDEX_OF *)
  sg `cfg_reachable_of (cfg_analyze fn) y`
  >- (imp_res_tac index_of_some_mem >> imp_res_tac mem_dfs_pre_reachable) >>
  mp_tac dominates_index_le >>
  disch_then (qspecl_then [`fn`, `ebb`, `x`, `y`, `i`, `j`] mp_tac) >>
  simp[] >> strip_tac >>
  CCONTR_TAC >>
  `i = j` by gvs[] >>
  metis_tac[INDEX_OF_eq_SOME, ALL_DISTINCT_EL_IMP]
QED

(* D2 helper for sdom_step: non-phi z from block_exit, different block from rd.
   Handles sub-cases: z=def_id, blk(z)=def_blk (LAST), blk(z)<>def_blk (IH).
   Reachability for z provided as hypothesis to keep nesting flat. *)
Triviality walk_reachable_from_sdom_step_d2:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   z z_node.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\
    INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME idx /\
    walk_reachable ms rd z /\
    z <> 0 /\ z IN FDOM ms.ms_nodes /\
    FLOOKUP ms.ms_nodes z = SOME z_node /\
    cfg_reachable_of cfg (mn_block z_node) /\
    dominates dom (mn_block z_node) (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    dominates dom def_blk (mn_block z_node) /\
    (!blk. z_node <> MnPhi blk) /\
    mn_block z_node <> mn_block (THE (FLOOKUP ms.ms_nodes rd)) /\
    (mn_block z_node = def_blk ==>
     z = LAST (fmap_lookup_list ms.ms_block_defs def_blk)) ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  (* Case 1: z = def_id — immediate *)
  Cases_on `z = def_id` >- gvs[] >>
  (* Case 2: blk(z) = def_blk — z = LAST, use walk_reachable_last_to_def *)
  Cases_on `mn_block z_node = def_blk`
  >- (irule walk_reachable_trans >> qexists_tac `z` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      mp_tac walk_reachable_last_to_def >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `z`, `def_id`,
        `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[Abbr `ms`] >> gvs[]) >>
  (* Case 3: blk(z) <> def_blk — sdom(def_blk, blk(z)), sdom_index_lt, IH *)
  irule walk_reachable_trans >> qexists_tac `z` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  sg `THE (FLOOKUP ms.ms_nodes z) = z_node` >- gvs[] >>
  (* Derive strict_dominates for z_node's block vs rd's block *)
  sg `strict_dominates dom (mn_block z_node) (mn_block (THE (FLOOKUP ms.ms_nodes rd)))`
  >- gvs[dominatorDefsTheory.strict_dominates_def] >>
  sg `strict_dominates dom def_blk (mn_block z_node)`
  >- gvs[dominatorDefsTheory.strict_dominates_def] >>
  (* Get INDEX_OF for z_node's block via sdom_index_lt *)
  mp_tac sdom_index_lt >>
  disch_then (qspecl_then [`fn`, `ebb`, `mn_block z_node`,
    `mn_block (THE (FLOOKUP ms.ms_nodes rd))`, `idx`] mp_tac) >>
  simp[Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`] >>
  strip_tac >>
  (* Apply IH with index i *)
  qpat_x_assum `!m. m < idx ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `z` mp_tac) >> simp[]
QED

(* D3 helper for sdom_step: phi z from block_exit with sdom(def_blk, b).
   Calls walk_reachable_from_sdom_phi. *)
Triviality walk_reachable_from_sdom_step_d3:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   z b.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\
    INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME idx /\
    walk_reachable ms rd z /\
    z <> 0 /\ z IN FDOM ms.ms_nodes /\
    FLOOKUP ms.ms_nodes z = SOME (MnPhi b) /\
    dominates dom b (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    cfg_reachable_of cfg b /\
    cfg_reachable_of cfg (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    strict_dominates dom def_blk b ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  irule walk_reachable_trans >> qexists_tac `z` >> simp[] >>
  (* INDEX_OF b dfs_pre from reachable *)
  sg `?qi. INDEX_OF b dfs_pre = SOME qi`
  >- (imp_res_tac reachable_mem_dfs_pre >>
      Cases_on `INDEX_OF b dfs_pre` >> gvs[Abbr `dfs_pre`, INDEX_OF_eq_NONE]) >>
  (* qi <= idx via dominates_index_le *)
  sg `qi <= idx`
  >- (mp_tac dominates_index_le >>
      disch_then (qspecl_then [`fn`, `ebb`, `b`,
        `mn_block (THE (FLOOKUP ms.ms_nodes rd))`, `qi`, `idx`] mp_tac) >>
      simp[Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`, mn_block_def] >>
      gvs[dominatorDefsTheory.strict_dominates_def]) >>
  mp_tac walk_reachable_from_sdom_phi >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `def_id`, `def_iid`,
    `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `z`, `b`, `qi`] mp_tac) >>
  simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`, mn_block_def] >>
  (impl_tac >- (strip_tac >> gvs[])) >> simp[]
QED

(* Phi helper for sdom_step: rd is a phi node.
   Calls walk_reachable_from_sdom_phi with qi = idx. *)
Triviality walk_reachable_from_sdom_step_phi:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   phi_blk.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    FLOOKUP ms.ms_nodes rd = SOME (MnPhi phi_blk) /\
    strict_dominates dom def_blk phi_blk /\
    INDEX_OF phi_blk dfs_pre = SOME idx ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  mp_tac walk_reachable_from_sdom_phi >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `def_id`, `def_iid`,
    `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `rd`, `phi_blk`, `idx`] mp_tac) >>
  simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`, mn_block_def]
QED

(* Wrapper: block_exit D2 result (non-phi z) → walk_reachable via _step_d2.
   Adds cfg_reachable_of as needed by _step_d2. *)
Triviality walk_reachable_from_sdom_nonphi_d2_wrap:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   z z_node.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\
    INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME idx /\
    walk_reachable ms rd z /\
    z <> 0 /\ z IN FDOM ms.ms_nodes /\
    FLOOKUP ms.ms_nodes z = SOME z_node /\
    dominates dom (mn_block z_node) (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    dominates dom def_blk (mn_block z_node) /\
    (!blk. z_node <> MnPhi blk) /\
    mn_block z_node <> mn_block (THE (FLOOKUP ms.ms_nodes rd)) /\
    (mn_block z_node = def_blk ==>
     z = LAST (fmap_lookup_list ms.ms_block_defs def_blk)) ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  sg `cfg_reachable_of cfg (mn_block z_node)`
  >- (mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_block_reachable)) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `z`, `z_node`] mp_tac) >>
      (impl_tac >- simp[Abbr `ms`]) >>
      simp[Abbr `cfg`]) >>
  mp_tac walk_reachable_from_sdom_step_d2 >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `z`, `z_node`] mp_tac) >>
  simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`]
QED

(* Wrapper: block_exit D3 result (phi z with sdom) → walk_reachable via _step_d3.
   Adds cfg_reachable_of as needed by _step_d3. *)
Triviality walk_reachable_from_sdom_nonphi_d3_wrap:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   z b.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\
    INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME idx /\
    walk_reachable ms rd z /\
    z <> 0 /\ z IN FDOM ms.ms_nodes /\
    FLOOKUP ms.ms_nodes z = SOME (MnPhi b) /\
    dominates dom b (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    strict_dominates dom def_blk b ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  sg `cfg_reachable_of cfg (mn_block (THE (FLOOKUP ms.ms_nodes rd)))`
  >- (imp_res_tac index_of_some_mem >> gvs[]) >>
  sg `cfg_reachable_of cfg b`
  >- (gvs[dominatorDefsTheory.strict_dominates_def] >>
      metis_tac[dominatorProofsTheory.dominates_reachable]) >>
  mp_tac walk_reachable_from_sdom_step_d3 >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `z`, `b`] mp_tac) >>
  simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`]
QED

(* Nonphi step for walk_reachable_from_sdom: non-phi rd_node, calls block_exit
   then dispatches D1/D2/D3 to standalone wrappers. *)
Triviality walk_reachable_from_sdom_step_nonphi:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   rd_node.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    FLOOKUP ms.ms_nodes rd = SOME rd_node /\
    (!blk. rd_node <> MnPhi blk) /\
    strict_dominates dom def_blk (mn_block rd_node) /\
    INDEX_OF (mn_block rd_node) dfs_pre = SOME idx ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  mp_tac walk_reachable_block_exit >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`] mp_tac) >>
  (impl_tac >- (simp[Abbr `ms`, Abbr `dom`] >> gvs[])) >>
  disch_then (qx_choose_then `z` ASSUME_TAC) >>
  Cases_on `z = def_id`
  >- gvs[] >>
  Cases_on `FLOOKUP ms.ms_nodes z`
  >- (gvs[] >> metis_tac[flookup_thm]) >>
  rename1 `FLOOKUP ms.ms_nodes z = SOME z_node` >>
  Cases_on `?b. z_node = MnPhi b`
  >- (gvs[] >>
      mp_tac walk_reachable_from_sdom_nonphi_d3_wrap >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
        `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
        `ebb`, `idx`, `z`, `b`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`] >>
      gvs[dominatorDefsTheory.strict_dominates_def, mn_block_def])
  >> (gvs[] >>
      mp_tac walk_reachable_from_sdom_nonphi_d2_wrap >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
        `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
        `ebb`, `idx`, `z`, `z_node`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`])
QED

(* Inductive step for walk_reachable_from_sdom: all context as explicit hypotheses.
   rd_node added as hypothesis to avoid sg>- nesting in batch mode. *)
Triviality walk_reachable_from_sdom_step:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb idx
   rd_node.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    (!m. m < idx ==>
      !rd. rd IN FDOM ms.ms_nodes ==> rd <> 0 ==> rd <> def_id ==>
        strict_dominates dom def_blk (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
        INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME m ==>
        walk_reachable ms rd def_id) /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    FLOOKUP ms.ms_nodes rd = SOME rd_node /\
    strict_dominates dom def_blk (mn_block rd_node) /\
    INDEX_OF (mn_block rd_node) dfs_pre = SOME idx ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  wrap_build_abbrevs >>
  Cases_on `?phi_blk. rd_node = MnPhi phi_blk`
  >- (gvs[mn_block_def] >>
      mp_tac walk_reachable_from_sdom_step_phi >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
        `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
        `ebb`, `idx`, `phi_blk`] mp_tac) >>
      simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`]) >>
  mp_tac walk_reachable_from_sdom_step_nonphi >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `rd_node`] mp_tac) >>
  simp[Abbr `ms`, Abbr `dom`, Abbr `cfg`, Abbr `dfs_pre`] >>
  metis_tac[]
QED

(* Helper: walk_reachable for any node with sdom, by complete induction
   on DFS pre-order index of rd's block.
   All setup facts are explicit hypotheses for batch-mode reliability.
   Callers derive these via build_sdom_setup. *)
Triviality walk_reachable_from_sdom:
  !fn bp addr_sp rd def_id def_iid def_blk def_loc ms dom cfg dfs_pre ebb
   idx.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
           bp fn addr_sp /\
    dom = dom_analyze (cfg_analyze fn) fn /\
    cfg = cfg_analyze fn /\
    dfs_pre = cfg.cfg_dfs_pre /\
    wf_function fn /\
    entry_block fn = SOME ebb /\
    ALL_DISTINCT dfs_pre /\
    (!lbl. MEM lbl dfs_pre ==> cfg_reachable_of cfg lbl) /\
    rd IN FDOM ms.ms_nodes /\ rd <> 0 /\ rd <> def_id /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates dom def_blk
      (mn_block (THE (FLOOKUP ms.ms_nodes rd))) /\
    INDEX_OF (mn_block (THE (FLOOKUP ms.ms_nodes rd))) dfs_pre = SOME idx /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] ==>
    walk_reachable ms rd def_id
Proof
  rpt gen_tac >> strip_tac >>
  (* Push rd-specific and idx-specific hypotheses back to goal *)
  qpat_x_assum `INDEX_OF _ _ = SOME idx` mp_tac >>
  qpat_x_assum `strict_dominates _ _ _` mp_tac >>
  qpat_x_assum `rd <> def_id` mp_tac >>
  qpat_x_assum `rd <> 0` mp_tac >>
  qpat_x_assum `rd IN FDOM _` mp_tac >>
  qid_spec_tac `rd` >> qid_spec_tac `idx` >>
  completeInduct_on `idx` >>
  rpt strip_tac >>
  `?rd_node. FLOOKUP ms.ms_nodes rd = SOME rd_node`
    by metis_tac[flookup_thm] >>
  `THE (FLOOKUP ms.ms_nodes rd) = rd_node` by gvs[] >>
  mp_tac walk_reachable_from_sdom_step >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`, `ms`, `dom`, `cfg`, `dfs_pre`,
    `ebb`, `idx`, `rd_node`] mp_tac) >>
  (impl_tac >- gvs[]) >> simp[]
QED


(* SSA structural lemma: walk_reachable ms rd def_id when
   access_id is non-phi with sdom(def_blk, blk(access_id)).
   Split into _same_block (blk(rd)=def_blk), _core (case dispatch), wrapper. *)

Triviality wf_function_has_entry_block:
  !fn. wf_function fn ==> ?ebb. entry_block fn = SOME ebb
Proof
  rpt strip_tac >>
  gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
      venomInstTheory.entry_block_def, listTheory.NULL_EQ]
QED

(* Helper: reaching def for non-phi access at sdom block can't be phi *)
Triviality reaching_at_sdom_block_not_phi:
  !fn bp addr_sp access_id rd rd_node blk.
    wf_function fn /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_reaching access_id = SOME rd /\
    access_id IN FDOM (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes /\
    (!blk. THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes access_id) <>
      MnPhi blk) /\
    rd <> 0 /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_nodes rd = SOME rd_node /\
    fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
      (mn_block rd_node) <> [] /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) (mn_block rd_node)
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
          access_id))) ==>
    rd_node <> MnPhi blk
Proof
  rpt strip_tac >> gvs[] >>
  mp_tac build_reaching_phi_location >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `access_id`, `rd`,
    `blk`,
    `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >> gvs[dominatorDefsTheory.strict_dominates_def,
                   memSSADefsTheory.mn_block_def]
QED

(* Same-block case: rd is at def_blk, so rd = LAST(block_defs), walk to def_id.
   Key: rd is non-phi (build_reaching_phi_location + sdom contradicts phi). *)
Triviality walk_reachable_from_rd_same_block:
  !fn bp addr_sp access_id rd rd_node def_id def_iid def_blk def_loc.
    wf_function fn /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_reaching access_id = SOME rd /\
    access_id IN FDOM (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes /\
    (!blk. THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes access_id) <>
      MnPhi blk) /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_nodes def_id =
      SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP (mem_ssa_build (cfg_analyze fn)
          (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes
          access_id))) /\
    def_id <> rd /\ rd <> 0 /\
    rd IN FDOM (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes /\
    fmap_lookup_list (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_block_defs
      def_blk <> [] /\
    FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp).ms_nodes rd = SOME rd_node /\
    mn_block rd_node = def_blk ==>
    walk_reachable (mem_ssa_build (cfg_analyze fn)
      (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp) rd def_id
Proof
  rpt strip_tac >>
  (* Step 1: rd is non-phi *)
  (* Step 1: rd is non-phi *)
  `!blk. rd_node <> MnPhi blk`
    by metis_tac[reaching_at_sdom_block_not_phi] >>
  (* Step 2: rd = LAST(block_defs def_blk) *)
  mp_tac build_reaching_cross_block_is_last >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `access_id`,
    `rd`, `rd_node`,
    `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp`] mp_tac) >>
  simp[] >>
  (impl_tac >- gvs[dominatorDefsTheory.strict_dominates_def]) >>
  strip_tac >>
  (* Step 3: walk from LAST to def_id *)
  mp_tac walk_reachable_last_to_def >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
  simp[]
QED

(* Core dispatch: case split on blk(rd)=def_blk, delegates to helpers *)
Triviality walk_reachable_from_rd_core:
  !fn bp addr_sp access_id rd def_id def_iid def_blk def_loc ms.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp /\
    wf_function fn /\
    FLOOKUP ms.ms_reaching access_id = SOME rd /\
    access_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes access_id) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) /\
    def_id <> rd /\
    rd <> 0 /\
    rd IN FDOM ms.ms_nodes /\
    fmap_lookup_list ms.ms_block_defs def_blk <> [] /\
    dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP ms.ms_nodes rd))) ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >> gvs[] >>
  sg `?rd_node. FLOOKUP (mem_ssa_build (cfg_analyze fn)
     (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp).ms_nodes rd =
     SOME rd_node` >- metis_tac[flookup_thm] >>
  Cases_on `mn_block rd_node = def_blk`
  >- (mp_tac walk_reachable_from_rd_same_block >>
      disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `access_id`, `rd`,
        `rd_node`, `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[]) >>
  (* Derive strict_dominates from dominates + neq *)
  `THE (FLOOKUP (mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
     bp fn addr_sp).ms_nodes rd) = rd_node` by simp[] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk (mn_block rd_node)`
    by gvs[dominatorDefsTheory.strict_dominates_def] >>
  (* Get entry_block *)
  imp_res_tac wf_function_has_entry_block >>
  (* Get reachable and INDEX_OF *)
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] build_node_block_reachable)) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `rd`, `rd_node`] mp_tac) >>
  simp[] >> strip_tac >>
  imp_res_tac reachable_mem_dfs_pre >>
  `?idx. INDEX_OF (mn_block rd_node) (cfg_analyze fn).cfg_dfs_pre = SOME idx`
    by metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_SOME_NONE,
                 optionTheory.option_nchotomy] >>
  (* Apply walk_reachable_from_sdom *)
  mp_tac walk_reachable_from_sdom >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `rd`, `def_id`,
    `def_iid`, `def_blk`, `def_loc`,
    `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
       bp fn addr_sp`,
    `dom_analyze (cfg_analyze fn) fn`,
    `cfg_analyze fn`, `(cfg_analyze fn).cfg_dfs_pre`, `ebb`, `idx`] mp_tac) >>
  simp[] >>
  (impl_tac >- (
    rpt conj_tac
    >- metis_tac[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct]
    >> (rpt strip_tac >> imp_res_tac mem_dfs_pre_reachable >> gvs[]))) >>
  simp[]
QED

(* Wrapper: establishes rd<>0, rd IN FDOM, fmap_lookup_list<>[], dominates *)
Triviality walk_reachable_from_rd:
  !fn bp addr_sp access_id rd def_id def_iid def_blk def_loc ms.
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
               bp fn addr_sp /\
    wf_function fn /\
    FLOOKUP ms.ms_reaching access_id = SOME rd /\
    access_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes access_id) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) /\
    def_id <> rd ==>
    walk_reachable ms rd def_id
Proof
  rpt strip_tac >>
  mp_tac walk_reachable_from_rd_core >>
  disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `access_id`, `rd`,
    `def_id`, `def_iid`, `def_blk`, `def_loc`, `ms`] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  sg `rd <> 0`
  >- (strip_tac >> gvs[] >>
      mp_tac (SIMP_RULE (srw_ss()) [] build_sdom_reaching_nonzero) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `access_id`, `0`,
        `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[]) >>
  sg `mem_ssa_edges_valid ms` >- metis_tac[mem_ssa_build_wf, wf_mem_ssa_def] >>
  sg `rd IN FDOM ms.ms_nodes`
  >- (fs[mem_ssa_edges_valid_def] >> res_tac >> gvs[]) >>
  gvs[] >> rpt conj_tac
  >- metis_tac[build_MnDef_block_defs_nonempty] >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
        build_reaching_dominated_by_ancestor)) >>
  disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `access_id`,
    `rd`, `def_blk`] mp_tac) >>
  gvs[] >>
  (impl_tac >- metis_tac[build_MnDef_block_defs_nonempty]) >>
  simp[]
QED

(* Part B: walk_clobber visits every strictly-dominating MnDef.
   Uses walk_clobber_succ_closed + walk_reachable_in_closed + walk_reachable_from_rd. *)
Triviality walk_clobber_visits_dom_defs:
  !fuel ms fn bp addr_sp access_id rd qloc visited'
   def_id def_iid def_blk def_loc.
    wf_function fn /\
    ms = mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
                       bp fn addr_sp /\
    mem_ssa_walk_clobber ms fuel [] rd qloc = (NONE, visited') /\
    FLOOKUP ms.ms_reaching access_id = SOME rd /\
    access_id IN FDOM ms.ms_nodes /\
    (!blk. THE (FLOOKUP ms.ms_nodes access_id) <> MnPhi blk) /\
    FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) def_blk
       (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) /\
    def_id <> rd /\
    fuel >= CARD (FDOM ms.ms_nodes) ==>
    MEM def_id visited'
Proof
  rpt gen_tac >> strip_tac >>
  (* Build well-formedness conditions *)
  `FDOM ms.ms_reaching SUBSET FDOM ms.ms_nodes` by (
    gvs[] >> simp[build_reaching_subset_nodes]) >>
  `0 NOTIN FDOM ms.ms_nodes` by (
    gvs[] >>
    mp_tac build_zero_not_in_nodes >>
    disch_then (qspecl_then [`cfg_analyze fn`,
      `dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`, `addr_sp`] mp_tac) >>
    simp[]) >>
  `mem_ssa_edges_valid ms` by (
    `wf_mssa ms` by (gvs[] >> simp[mem_ssa_build_wf]) >>
    fs[wf_mem_ssa_def]) >>
  `def_id IN FDOM ms.ms_nodes` by gvs[flookup_thm] >>
  `def_id <> 0` by metis_tac[] >>
  (* walk_reachable ms rd def_id *)
  `walk_reachable ms rd def_id` by (
    mp_tac walk_reachable_from_rd >>
    disch_then (qspecl_then [`fn`, `bp`, `addr_sp`, `access_id`, `rd`,
      `def_id`, `def_iid`, `def_blk`, `def_loc`, `ms`] mp_tac) >>
    gvs[]) >>
  (* walk output is successor-closed *)
  `walk_succ_closed ms visited'` by (
    drule walk_clobber_succ_closed >> simp[]) >>
  (* rd is in visited' — need rd <> 0 *)
  `rd <> 0` by (
    mp_tac (SIMP_RULE (srw_ss()) [] build_sdom_reaching_nonzero) >>
    disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `access_id`, `rd`,
      `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
    gvs[]) >>
  `fuel >= 1` by (
    irule fuel_positive_lemma >>
    qexists_tac `FDOM ms.ms_nodes` >>
    qexists_tac `def_id` >> simp[]) >>
  `MEM rd visited'` by (
    Cases_on `fuel` >- fs[] >>
    drule walk_clobber_visits_current >> simp[]) >>
  (* walk_reachable + succ_closed => MEM def_id visited' *)
  irule walk_reachable_in_closed >> simp[] >>
  qexistsl_tac [`ms`, `rd`] >> simp[]
QED

(* collect_phi_clobbers: all clobber IDs are nonzero if walker gives nonzero *)
Triviality collect_phi_some_nonzero:
  !ops (walker : num list -> num -> num option # num list) visited cs v.
    mem_ssa_collect_phi_clobbers walker visited ops = (cs, v) /\
    (!vis rd x v'. walker vis rd = (SOME x, v') ==> x <> 0) ==>
    !c. MEM c cs ==> c <> 0
Proof
  Induct >>
  simp[mem_ssa_collect_phi_clobbers_def] >>
  rpt gen_tac >>
  Cases_on `h` >> simp[mem_ssa_collect_phi_clobbers_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  Cases_on `result` >> simp[]
  (* NONE: cs = rest *)
  >- (strip_tac >> rpt strip_tac >>
      first_x_assum (qspecl_then [`walker`, `visited1`, `rest`,
        `visited2`] mp_tac) >>
      simp[] >> metis_tac[])
  (* SOME x: cs = x::rest *)
  >> strip_tac >> rpt strip_tac >> gvs[]
  >- metis_tac[]
  >> first_x_assum (qspecl_then [`walker`, `visited1`, `rest`,
       `visited2`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* walk_clobber never returns SOME 0. *)
Triviality walk_clobber_some_nonzero:
  !fuel ms visited current qloc x v.
    mem_ssa_walk_clobber ms fuel visited current qloc = (SOME x, v) ==>
    x <> 0
Proof
  Induct >> rpt gen_tac
  >- simp[mem_ssa_walk_clobber_def]
  >> simp[Once mem_ssa_walk_clobber_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP ms.ms_nodes current` >> simp[] >>
  Cases_on `x'`
  (* MnDef *)
  >- (simp[] >> IF_CASES_TAC >> simp[] >>
      Cases_on `FLOOKUP ms.ms_reaching current` >> simp[] >>
      metis_tac[])
  (* MnUse *)
  >- (simp[] >> Cases_on `FLOOKUP ms.ms_reaching current` >> simp[] >>
      metis_tac[])
  (* MnPhi *)
  >> simp[] >>
  Cases_on `FLOOKUP ms.ms_phi_ops current` >> simp[] >>
  pairarg_tac >> simp[] >>
  Cases_on `clobbers` >> simp[] >>
  Cases_on `t` >> simp[] >>
  (* [h] — single clobber (multi-clobber solved by simp[] above) *)
  strip_tac >> simp[] >>
  qpat_x_assum `mem_ssa_collect_phi_clobbers _ _ _ = _`
    (mp_tac o MATCH_MP
      (collect_phi_some_nonzero |> REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
  impl_tac >- metis_tac[] >>
  simp[]
QED

Theorem mem_ssa_clobber_sound:
  ∀cfg dom bp fn addr_sp ms access_id fuel.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    ms = mem_ssa_build cfg dom bp fn addr_sp ∧
    dom = dom_analyze cfg fn ∧
    fuel ≥ CARD (FDOM ms.ms_nodes) ∧
    mem_ssa_get_clobbered ms fuel access_id = SOME 0 ∧
    access_id ∈ FDOM ms.ms_nodes ∧
    (∀blk. THE (FLOOKUP ms.ms_nodes access_id) ≠ MnPhi blk) ⇒
    ∀def_id def_iid def_blk def_loc.
      FLOOKUP ms.ms_nodes def_id = SOME (MnDef def_iid def_blk def_loc) ∧
      strict_dominates dom def_blk
        (mn_block (THE (FLOOKUP ms.ms_nodes access_id))) ⇒
      ¬completely_contains def_loc
        (mn_loc (THE (FLOOKUP ms.ms_nodes access_id)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ms = _` SUBST_ALL_TAC >>
  qpat_x_assum `dom = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qabbrev_tac `ms = mem_ssa_build (cfg_analyze fn)
    (dom_analyze (cfg_analyze fn) fn) bp fn addr_sp` >>
  rpt gen_tac >> strip_tac >>
  (* Expand get_clobbered *)
  qpat_x_assum `mem_ssa_get_clobbered _ _ _ = _` mp_tac >>
  simp[mem_ssa_get_clobbered_def] >>
  `access_id <> 0` by (
    CCONTR_TAC >> gvs[] >>
    mp_tac build_zero_not_in_nodes >>
    disch_then (qspecl_then [`cfg_analyze fn`,
      `dom_analyze (cfg_analyze fn) fn`, `bp`, `fn`, `addr_sp`] mp_tac) >>
    simp[Abbr `ms`]) >>
  `?access_node. FLOOKUP ms.ms_nodes access_id = SOME access_node` by
    fs[flookup_thm] >>
  simp[] >>
  Cases_on `FLOOKUP ms.ms_reaching access_id`
  >- (
    (* No reaching — non-phi should have reaching by reaching_complete *)
    `mem_ssa_reaching_complete ms` by (
      `wf_mssa ms` by (
        simp[Abbr `ms`] >> irule mem_ssa_build_wf >> simp[]) >>
      fs[wf_mem_ssa_def]) >>
    fs[mem_ssa_reaching_complete_def] >>
    `?blk. access_node <> MnPhi blk` by (Cases_on `access_node` >> gvs[]) >>
    res_tac >> gvs[])
  >> simp[] >>
  rename1 `FLOOKUP ms.ms_reaching access_id = SOME rd` >>
  pairarg_tac >> simp[] >>
  Cases_on `result` >> simp[]
  >- (
    (* result = NONE => SOME 0 *)
    strip_tac >> gvs[] >>
    (* Step 1: rd <> 0 *)
    `rd <> 0` by (
      mp_tac (SIMP_RULE (srw_ss()) [] build_sdom_reaching_nonzero) >>
      disch_then (qspecl_then [`bp`, `fn`, `addr_sp`, `access_id`, `rd`,
        `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
      simp[Abbr `ms`]) >>
    Cases_on `def_id = rd`
    (* Case: def_id = rd — walk starts at def_id, an MnDef.
       If completely_contains, walk returns SOME, contradicting NONE. *)
    >- (gvs[] >>
        qpat_x_assum `mem_ssa_walk_clobber _ _ _ _ _ = _`
          (mp_tac o PURE_ONCE_REWRITE_RULE [mem_ssa_walk_clobber_def]) >>
        simp[LET_THM] >>
        `?fuel'. fuel = SUC fuel'` by (
          Cases_on `fuel` >> gvs[] >>
          `CARD (FDOM ms.ms_nodes) >= 1` suffices_by simp[] >>
          `access_id IN FDOM ms.ms_nodes` by simp[] >>
          `FDOM ms.ms_nodes <> {}` by (strip_tac >> gvs[]) >>
          `FINITE (FDOM ms.ms_nodes)` by simp[] >>
          metis_tac[CARD_EQ_0, DECIDE ``~(x = 0n) ==> x >= 1``]) >>
        gvs[] >> simp[mem_ssa_walk_clobber_def, LET_THM] >>
        Cases_on `completely_contains def_loc (mn_loc access_node)` >>
        simp[])
    (* Case: def_id <> rd — use walk_clobber_visits_dom_defs *)
    >> (
    (* Step 2: walk_clobber_visits_dom_defs gives MEM def_id _0 *)
    mp_tac walk_clobber_visits_dom_defs >>
    disch_then (qspecl_then [`fuel`,
      `mem_ssa_build (cfg_analyze fn) (dom_analyze (cfg_analyze fn) fn)
         bp fn addr_sp`,
      `fn`, `bp`, `addr_sp`, `access_id`, `rd`,
      `mn_loc access_node`, `_0`,
      `def_id`, `def_iid`, `def_blk`, `def_loc`] mp_tac) >>
    simp[Abbr `ms`] >>
    strip_tac >>
    (* Step 3: walk_clobber_none_sound + MEM → ¬completely_contains *)
    qpat_x_assum `mem_ssa_walk_clobber _ _ _ _ _ = (NONE, _0)`
      (mp_tac o MATCH_MP walk_clobber_none_sound) >>
    disch_then (qspecl_then [`def_id`, `def_iid`, `def_blk`, `def_loc`]
      mp_tac) >>
    simp[]))
  (* result = SOME x => x = 0, but walk never returns SOME 0 *)
  >> strip_tac >> gvs[] >>
  metis_tac[walk_clobber_some_nonzero]
QED
