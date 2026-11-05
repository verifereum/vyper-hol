Theory makeSsaRfAnnotations
Ancestors makeSsaRfRenameTrace makeSsaHelper venomInst irSupply list alist pair arithmetic

Definition rf_output_annotations_def:
  (rf_output_annotations l i j [] = []) /\
  (rf_output_annotations l i j (v::vs) =
    (CurrentOriginal l i j,v)::rf_output_annotations l i (SUC j) vs)
End

Definition rf_inst_annotations_def:
  (rf_inst_annotations l i [] = []) /\
  (rf_inst_annotations l i (inst::insts) =
    rf_output_annotations l i 0 inst.inst_outputs ::
    rf_inst_annotations l (SUC i) insts)
End

Definition rf_block_annotations_def:
  rf_block_annotations bbs =
    MAP (\bb. rf_inst_annotations bb.bb_label 0 bb.bb_instructions) bbs
End

Theorem rf_output_annotations_erase:
  !vs l i j. MAP SND (rf_output_annotations l i j vs) = vs
Proof
  Induct >> simp[rf_output_annotations_def]
QED

Theorem rf_output_annotations_member:
  !vs l i j t v. MEM (t,v) (rf_output_annotations l i j vs) ==>
    (?k. t = CurrentOriginal l i k /\ j <= k) /\ MEM v vs
Proof
  Induct >> simp[rf_output_annotations_def] >> rpt strip_tac >> gvs[] >>
  res_tac >> simp[] >> metis_tac[LESS_EQ_TRANS, DECIDE ``j <= SUC j``]
QED

Theorem rf_output_annotations_distinct:
  !vs l i j. ALL_DISTINCT (MAP FST (rf_output_annotations l i j vs))
Proof
  Induct >> simp[rf_output_annotations_def] >> rpt strip_tac >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  drule rf_output_annotations_member >> simp[]
QED

Theorem rf_inst_annotations_erase:
  !insts l i. LIST_REL (\a inst. MAP SND a = inst.inst_outputs)
    (rf_inst_annotations l i insts) insts
Proof
  Induct >> simp[rf_inst_annotations_def, rf_output_annotations_erase]
QED

Theorem rf_inst_annotations_member:
  !insts l i t v. MEM (t,v) (FLAT (rf_inst_annotations l i insts)) ==>
    (?k j. t = CurrentOriginal l k j /\ i <= k) /\
    (?inst. MEM inst insts /\ MEM v inst.inst_outputs)
Proof
  Induct >> simp[rf_inst_annotations_def] >> rpt gen_tac >>
  disch_then DISJ_CASES_TAC
  >- (drule rf_output_annotations_member >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  `i <= k` by decide_tac >> metis_tac[]
QED

Theorem rf_inst_annotations_distinct:
  !insts l i. ALL_DISTINCT (MAP FST (FLAT (rf_inst_annotations l i insts)))
Proof
  Induct >> simp[rf_inst_annotations_def, MAP_APPEND,
    ALL_DISTINCT_APPEND, rf_output_annotations_distinct] >>
  rpt gen_tac >> simp[MEM_MAP] >> rpt strip_tac >>
  PairCases_on `y` >> PairCases_on `y'` >> gvs[] >>
  drule rf_output_annotations_member >> strip_tac >>
  drule rf_inst_annotations_member >> strip_tac >> gvs[]
QED

Theorem rf_block_annotations_erase:
  LIST_REL (\bb anns.
    LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
    bbs (rf_block_annotations bbs)
Proof
  Induct_on `bbs` >> gvs[rf_block_annotations_def, rf_inst_annotations_erase]
QED

Theorem rf_block_annotations_member:
  !bbs t v. MEM (t,v) (FLAT (FLAT (rf_block_annotations bbs))) ==>
    ?bb i j inst. MEM bb bbs /\ t = CurrentOriginal bb.bb_label i j /\
      MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs
Proof
  Induct >> simp[rf_block_annotations_def, FLAT_APPEND] >> rpt strip_tac
  >- (drule rf_inst_annotations_member >> strip_tac >> metis_tac[])
  >> fs[rf_block_annotations_def] >> first_x_assum drule >>
  strip_tac >> metis_tac[]
QED

Theorem rf_block_annotations_distinct:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP FST (FLAT (FLAT (rf_block_annotations bbs))))
Proof
  Induct >> simp[rf_block_annotations_def, FLAT_APPEND, MAP_APPEND,
    ALL_DISTINCT_APPEND, rf_inst_annotations_distinct] >>
  rpt strip_tac >> gvs[rf_block_annotations_def, MEM_MAP] >> rpt strip_tac >>
  PairCases_on `y` >> PairCases_on `y'` >> gvs[] >>
  drule rf_inst_annotations_member >> strip_tac >>
  `MEM (y'0,y'1) (FLAT (FLAT (rf_block_annotations bbs)))` by
    gvs[rf_block_annotations_def] >>
  drule rf_block_annotations_member >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rf_block_annotations_nondefault:
  MEM (t,v) (FLAT (FLAT (rf_block_annotations bbs))) ==>
  !w. t <> CurrentDefault w
Proof
  strip_tac >> drule rf_block_annotations_member >> strip_tac >> simp[]
QED

Theorem rf_block_annotations_owner:
  MEM (t,v) (FLAT (FLAT (rf_block_annotations bbs))) ==>
  MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  strip_tac >> drule rf_block_annotations_member >> strip_tac >>
  simp[MEM_FLAT, MEM_MAP, block_ir_vars_def] >>
  qexists_tac `FLAT (MAP inst_ir_vars bb.bb_instructions)` >> conj_tac
  >- (qexists_tac `bb` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `inst_ir_vars inst` >> conj_tac
  >- (qexists_tac `inst` >> simp[]) >>
  simp[inst_ir_vars_def]
QED

Theorem rf_block_annotations_ok:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!v. MEM v (FLAT (MAP block_ir_vars bbs)) ==> MEM v V) ==>
  current_annotations_ok V [] (FLAT (FLAT (rf_block_annotations bbs)))
Proof
  strip_tac >> simp[current_annotations_ok_def,
    rf_block_annotations_distinct, EVERY_MEM] >>
  rpt gen_tac >> PairCases_on `e` >> simp[] >> strip_tac >>
  metis_tac[rf_block_annotations_nondefault, rf_block_annotations_owner]
QED

Definition current_annotation_map_def:
  current_annotation_map bbs
    (annsss : (current_token # string) list list list) l =
    case ALOOKUP (ZIP (MAP (\bb. bb.bb_label) bbs,annsss)) l of
      NONE => [] | SOME anns => anns
End

Definition current_unvisited_annotations_def:
  current_unvisited_annotations A visited bbs <=>
    !l bb. ~MEM l visited /\ lookup_block l bbs = SOME bb ==>
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) (A l) bb.bb_instructions
End

Definition current_pending_annotations_def:
  current_pending_annotations V A (H : (current_token # string # string) list) visited <=>
    !l. ~MEM l visited ==> current_annotations_ok V H (FLAT (A l))
End

Definition current_annotation_separation_def:
  current_annotation_separation (A : string -> (current_token # string) list list) <=>
    !l k t. MEM t (MAP FST (FLAT (A l))) /\
      MEM t (MAP FST (FLAT (A k))) ==> l = k
End

Theorem current_annotation_map_owners:
  !bbs annsss.
    LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss ==>
    !l bb. lookup_block l bbs = SOME bb ==>
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs)
        (current_annotation_map bbs annsss l) bb.bb_instructions
Proof
  Induct >> Cases_on `annsss` >>
  simp[lookup_block_def, FIND_thm, current_annotation_map_def] >>
  rpt strip_tac >> rename1 `old.bb_label = l` >>
  Cases_on `old.bb_label = l` >> gvs[] >>
  first_x_assum drule >> simp[current_annotation_map_def, lookup_block_def]
QED

Theorem current_annotation_map_initial:
  LIST_REL (\bb anns.
    LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
    bbs annsss ==>
  current_unvisited_annotations (current_annotation_map bbs annsss) [] bbs
Proof
  simp[current_unvisited_annotations_def] >>
  metis_tac[current_annotation_map_owners]
QED

Theorem current_annotation_map_keys_bound:
  !bbs annsss l t.
    LENGTH bbs = LENGTH annsss /\
    MEM t (MAP FST (FLAT (current_annotation_map bbs annsss l))) ==>
    MEM t (MAP FST (FLAT (FLAT annsss)))
Proof
  Induct >> Cases_on `annsss` >>
  simp[current_annotation_map_def, MAP_APPEND] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'.bb_label = l` >> gvs[] >>
  disj2_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `l` >> simp[current_annotation_map_def]
QED

Theorem current_annotation_map_separation:
  !bbs annsss.
    LENGTH bbs = LENGTH annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) ==>
    current_annotation_separation (current_annotation_map bbs annsss)
Proof
  Induct >> Cases_on `annsss` >>
  simp[current_annotation_map_def, current_annotation_separation_def, MAP_APPEND,
    ALL_DISTINCT_APPEND] >> rpt gen_tac >> strip_tac >>
  `current_annotation_separation (current_annotation_map bbs t)` by
    (first_x_assum irule >> simp[]) >>
  qspecl_then [`bbs`, `t`] mp_tac current_annotation_map_keys_bound >>
  simp[current_annotation_map_def] >> strip_tac >>
  rpt gen_tac >>
  Cases_on `h'.bb_label = l` >> Cases_on `h'.bb_label = k` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  fs[current_annotation_map_def, current_annotation_separation_def] >> metis_tac[]
QED

Theorem current_annotation_map_ok:
  !bbs annsss V H.
    LENGTH bbs = LENGTH annsss /\
    current_annotations_ok V H (FLAT (FLAT annsss)) ==>
    !l. current_annotations_ok V H (FLAT (current_annotation_map bbs annsss l))
Proof
  Induct >> Cases_on `annsss` >> simp[current_annotation_map_def,
    current_annotations_ok_def, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `h'.bb_label = l` >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `V`, `H`] mp_tac) >>
  simp[current_annotation_map_def, current_annotations_ok_def] >>
  disch_then (qspec_then `l` ACCEPT_TAC)
QED

Theorem current_annotation_map_pending:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V H (FLAT (FLAT annsss)) ==>
  current_pending_annotations V (current_annotation_map bbs annsss) H visited
Proof
  simp[current_pending_annotations_def] >> metis_tac[current_annotation_map_ok]
QED

Theorem rf_block_annotation_map_initial:
  current_unvisited_annotations
    (current_annotation_map bbs (rf_block_annotations bbs)) [] bbs
Proof
  irule current_annotation_map_initial >> simp[rf_block_annotations_erase]
QED

Theorem rf_block_annotation_map_separation:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  current_annotation_separation
    (current_annotation_map bbs (rf_block_annotations bbs))
Proof
  strip_tac >> irule current_annotation_map_separation >>
  simp[rf_block_annotations_def] >>
  metis_tac[rf_block_annotations_distinct, rf_block_annotations_def]
QED

Theorem rf_block_annotation_map_pending:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!v. MEM v (FLAT (MAP block_ir_vars bbs)) ==> MEM v V) ==>
  current_pending_annotations V
    (current_annotation_map bbs (rf_block_annotations bbs)) [] visited
Proof
  strip_tac >> irule current_annotation_map_pending >>
  simp[rf_block_annotations_def] >>
  metis_tac[rf_block_annotations_ok, rf_block_annotations_def]
QED
