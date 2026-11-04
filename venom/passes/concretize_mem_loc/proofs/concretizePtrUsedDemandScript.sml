Theory concretizePtrUsedDemand
Ancestors
  concretizePtrOrdering concretizePtrReadCoverage concretizeMemLocDefs
  finite_map list indexedLists

Definition ptr_used_seed_def:
  ptr_used_seed a bp mems inst <=>
    (?op. MEM op inst.inst_operands /\ MEM a (find_base_allocas bp op)) \/
    (inst.inst_opcode = INVOKE /\
      ?lbl rest. inst.inst_operands = Label lbl :: rest /\ MEM a (mems lbl))
End

Theorem ptr_merge_fold_membership[local]:
  !xss xs. MEM a (FOLDL (smerge alloc_to) xs xss) <=>
    MEM a xs \/ EXISTS (MEM a) xss
Proof
  Induct_on `xss` >> simp[ptr_smerge_union] >> metis_tac[]
QED

Theorem ptr_used_inst_membership:
  MEM a (FST (ml_used_inst bp mems label idx inst cur us)) <=>
    MEM a cur \/ ptr_used_seed a bp mems inst
Proof
  simp[ml_used_inst_def, ptr_smerge_union, ptr_merge_fold_membership,
       listTheory.EXISTS_MEM, listTheory.MEM_MAP, ptr_used_seed_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[ptr_smerge_union] >>
  Cases_on `inst.inst_operands` >> simp[ptr_smerge_union] >>
  Cases_on `h` >>
  simp[ptr_merge_fold_membership, ptr_smerge_union,
       listTheory.EXISTS_MEM, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem ptr_used_insts_membership:
  !cur us. MEM a (FST (ml_used_insts bp mems label cur us insts)) <=>
    MEM a cur \/ EXISTS (\p. ptr_used_seed a bp mems (SND p)) insts
Proof
  Induct_on `insts` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >>
  pairarg_tac >> simp[] >>
  metis_tac[ptr_used_inst_membership, pairTheory.FST]
QED

Theorem ptr_used_insts_other_address[local]:
  !cur us. ~MEM addr (MAP (\p. (label,FST p)) insts) ==>
    ml_lookup (SND (ml_used_insts bp mems label cur us insts)) addr =
    ml_lookup us addr
Proof
  Induct_on `insts` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def, ml_used_inst_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ptr_used_inst_record[local]:
  ml_lookup (SND (ml_used_inst bp mems label idx inst cur us)) (label,idx) =
  FST (ml_used_inst bp mems label idx inst cur us)
Proof
  simp[ml_used_inst_def, ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ptr_used_insts_input_records:
  !cur us idx inst. ALL_DISTINCT (MAP FST insts) /\
    MEM (idx,inst) insts /\ MEM a cur ==>
    MEM a (ml_lookup (SND (ml_used_insts bp mems label cur us insts)) (label,idx))
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >> strip_tac >>
  pairarg_tac >> gvs[]
  >- (`ml_lookup (SND (ml_used_insts bp mems label cur' us' insts)) (label,h0) =
        ml_lookup us' (label,h0)` by
        (irule ptr_used_insts_other_address >>
         gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
      metis_tac[ptr_used_inst_record, ptr_used_inst_membership,
                pairTheory.FST, pairTheory.SND]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[ptr_used_inst_membership, pairTheory.FST]
QED

Theorem ptr_used_insts_head_records[local]:
  ALL_DISTINCT (MAP FST ((idx,inst)::xs)) /\
  MEM (j,i) ((idx,inst)::xs) /\
  (MEM a cur \/ ptr_used_seed a bp mems inst) ==>
  MEM a (ml_lookup
    (SND (ml_used_insts bp mems label cur us ((idx,inst)::xs))) (label,j))
Proof
  disch_tac >> simp[ml_used_insts_def] >> pairarg_tac >>
  `MEM a cur'` by metis_tac[ptr_used_inst_membership, pairTheory.FST] >>
  `ALL_DISTINCT (MAP FST ((idx,inst)::xs)) /\ MEM (j,i) ((idx,inst)::xs)`
    by metis_tac[] >>
  qpat_x_assum `_ /\ _ /\ _` kall_tac >> gvs[]
  >- (`ml_lookup (SND (ml_used_insts bp mems label cur' us' xs)) (label,idx) =
        ml_lookup us' (label,idx)` by
        (irule ptr_used_insts_other_address >>
         gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
      metis_tac[ptr_used_inst_record, pairTheory.FST, pairTheory.SND]) >>
  irule ptr_used_insts_input_records >> simp[] >> metis_tac[]
QED

Theorem ptr_used_insts_append[local]:
  !cur us. ml_used_insts bp mems label cur us (xs ++ ys) =
    ml_used_insts bp mems label
      (FST (ml_used_insts bp mems label cur us xs))
      (SND (ml_used_insts bp mems label cur us xs)) ys
Proof
  Induct_on `xs` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >> pairarg_tac >> simp[]
QED

Theorem ptr_used_seed_suffix_records:
  ALL_DISTINCT (MAP FST ((idx,inst)::rest)) /\
  MEM (j,i) ((idx,inst)::rest) /\ ptr_used_seed a bp mems inst ==>
  MEM a (ml_lookup
    (SND (ml_used_insts bp mems label cur us (pre ++ (idx,inst)::rest))) (label,j))
Proof
  strip_tac >> simp[ptr_used_insts_append] >>
  irule ptr_used_insts_head_records >> gvs[] >> metis_tac[]
QED

Definition ptr_used_path_def:
  (ptr_used_path cfg b [] c <=> b = c) /\
  (ptr_used_path cfg b (h::t) c <=>
    MEM b (cfg_preds_of cfg h) /\ ptr_used_path cfg h t c)
End

Theorem ptr_used_block_seed_suffix:
  MAPi (\n inst. (n,inst)) bb.bb_instructions = pre ++ (idx,inst)::rest /\
  ALL_DISTINCT (MAP FST ((idx,inst)::rest)) /\
  MEM (j,i) ((idx,inst)::rest) /\ ptr_used_seed a bp mems inst ==>
  MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,j))
Proof
  strip_tac >> simp[ml_used_block_def] >> pairarg_tac >> simp[] >>
  metis_tac[ptr_used_seed_suffix_records, pairTheory.SND]
QED

Theorem ptr_used_block_unchanged_endpoint:
  ~FST (ml_used_block bp mems pallocas cfg us bb blocks) ==>
  ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,PRE (LENGTH bb.bb_instructions)) =
  ml_lookup us (bb.bb_label,PRE (LENGTH bb.bb_instructions))
Proof
  simp[ml_used_block_def] >> pairarg_tac >> simp[]
QED

Theorem ptr_used_insts_other_label[local]:
  label <> FST addr ==>
  ml_lookup (SND (ml_used_insts bp mems label cur us insts)) addr = ml_lookup us addr
Proof
  strip_tac >> irule ptr_used_insts_other_address >>
  simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem ptr_used_block_other_label:
  bb.bb_label <> FST addr ==>
  ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks)) addr =
  ml_lookup us addr
Proof
  strip_tac >> simp[ml_used_block_def] >> pairarg_tac >> simp[] >>
  metis_tac[ptr_used_insts_other_label, pairTheory.SND]
QED

Theorem ptr_indexed_distinct[local]:
  ALL_DISTINCT (MAP FST (MAPi (\i inst. (i,inst)) insts))
Proof
  `MAP FST (MAPi (\i inst. (i,inst)) insts) = GENLIST I (LENGTH insts)` by
    (irule listTheory.LIST_EQ >> simp[indexedListsTheory.EL_MAPi]) >>
  simp[listTheory.ALL_DISTINCT_GENLIST]
QED

Theorem ptr_used_block_pred_records:
  MEM pred (cfg_preds_of cfg bb.bb_label) /\
  FIND (\b. b.bb_label = pred) blocks = SOME pbb /\
  MEM a (ml_lookup us (pbb.bb_label,PRE (LENGTH pbb.bb_instructions))) /\
  MEM (j,i) (MAPi (\n inst. (n,inst)) bb.bb_instructions) ==>
  MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,j))
Proof
  strip_tac >> simp[ml_used_block_def] >> pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `ml_used_insts bp mems bb.bb_label initial us _` >>
  `MEM a initial` by
    (simp[Abbr `initial`, ptr_smerge_union, ptr_merge_fold_membership,
          listTheory.EXISTS_MEM, listTheory.MEM_MAP] >>
     disj2_tac >>
     qexists_tac `ml_lookup us (pbb.bb_label,PRE (LENGTH pbb.bb_instructions))` >>
     simp[] >> qexists_tac `pred` >> simp[]) >>
  metis_tac[ptr_used_insts_input_records, ptr_indexed_distinct, pairTheory.SND]
QED
