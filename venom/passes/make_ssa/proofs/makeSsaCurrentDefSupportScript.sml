Theory makeSsaCurrentDefSupport
Ancestors
  makeSsaCurrentAnalysis makeSsaCurrentOccurrence makeSsaDefs list alist sorting

Theorem compute_defs_update_support[local]:
  !acc v roots d key lbl.
    ALOOKUP (alist_update_or_append key (CONS lbl) [lbl] acc) v = SOME roots /\
    MEM d roots ==>
    (d = lbl /\ v = key) \/
    ?old. ALOOKUP acc v = SOME old /\ MEM d old
Proof
  Induct >> simp[alist_update_or_append_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[alist_update_or_append_def] >>
  Cases_on `q = key` >> simp[] >>
  Cases_on `q = v` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem compute_defs_fold_support[local]:
  !xs acc v roots d lbl.
    ALOOKUP (FOLDL (\a key.
      alist_update_or_append key (CONS lbl) [lbl] a) acc xs) v = SOME roots /\
    MEM d roots ==>
    (d = lbl /\ MEM v xs) \/
    ?old. ALOOKUP acc v = SOME old /\ MEM d old
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_all compute_defs_update_support >> metis_tac[]
QED

Theorem compute_defs_acc_support[local]:
  !bbs acc v roots d.
    ALOOKUP (compute_defs_acc acc bbs) v = SOME roots /\ MEM d roots ==>
    (?old. ALOOKUP acc v = SOME old /\ MEM d old) \/
    ?bb inst. MEM bb bbs /\ bb.bb_label = d /\
      MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs
Proof
  Induct >> simp[compute_defs_acc_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- (drule_all compute_defs_fold_support >>
      simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem compute_defs_support:
  ALOOKUP (compute_defs bbs) v = SOME roots /\ MEM d roots ==>
  ?bb inst. MEM bb bbs /\ bb.bb_label = d /\
    MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs
Proof
  simp[compute_defs_def] >> strip_tac >>
  drule_all compute_defs_acc_support >> simp[]
QED

Theorem current_compute_defs_single_support:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME entry /\
  ALOOKUP (compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    v = SOME roots /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1 ==>
  !d. MEM d roots ==> d = db.bb_label
Proof
  rpt strip_tac >> drule_all compute_defs_support >> strip_tac >>
  drule_all current_ordered_blocks_perm >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[PERM_MEM_EQ] >>
  metis_tac[current_single_def_occurrence]
QED
