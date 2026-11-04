Theory concretizePtrOrdering
Ancestors
  concretizeMemLocDefs enumeral

Theorem ptr_incr_sbuild_ordered[local]:
  !xs. OL_sublists cmp (incr_sbuild cmp xs)
Proof
  Induct >> simp[incr_sbuild, OL_sublists] >>
  gen_tac >> irule incr_smerge_OL >> simp[OL]
QED

Theorem ptr_smerge_out_ordered[local]:
  !xss xs. OL_sublists cmp xss /\ OL cmp xs ==>
  OL cmp (smerge_out cmp xs xss)
Proof
  Induct >> simp[smerge_out, OL_sublists] >>
  Cases_on `h` >> simp[smerge_out, OL_sublists] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[smerge_OL]
QED

Theorem ptr_incr_ssort_ordered:
  OL cmp (incr_ssort cmp xs)
Proof
  simp[incr_ssort] >> irule ptr_smerge_out_ordered >>
  simp[ptr_incr_sbuild_ordered, OL]
QED

Theorem ptr_base_allocas_ordered:
  OL alloc_to (find_base_allocas bpr op)
Proof
  Cases_on `op` >> simp[find_base_allocas_def, ptr_incr_ssort_ordered, OL]
QED

Theorem ptr_base_allocas_opt_ordered:
  OL alloc_to (find_base_allocas_opt bpr op)
Proof
  Cases_on `op` >> simp[find_base_allocas_opt_def, ptr_base_allocas_ordered, OL]
QED

Definition ptr_ml_ordered_def:
  ptr_ml_ordered st <=> !addr. OL alloc_to (ml_lookup st addr)
End

Theorem ptr_ml_ordered_empty[simp]:
  ptr_ml_ordered FEMPTY
Proof
  simp[ptr_ml_ordered_def, ml_lookup_def, OL]
QED

Theorem ptr_ml_ordered_update:
  ptr_ml_ordered st /\ OL alloc_to xs ==>
  ptr_ml_ordered (st |+ (addr,xs))
Proof
  simp[ptr_ml_ordered_def, ml_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem ptr_ordered_merge_fold:
  !xs. OL cmp xs /\ EVERY (OL cmp) xss ==>
  OL cmp (FOLDL (smerge cmp) xs xss)
Proof
  Induct_on `xss` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[smerge_OL]
QED

Theorem ptr_kill_write_ordered[local]:
  OL alloc_to live ==>
  OL alloc_to (ml_kill_write sizes reads wsz live a)
Proof
  strip_tac >> simp[ml_kill_write_def] >>
  Cases_on `sizes a` >> simp[] >>
  rpt IF_CASES_TAC >> simp[]
  >- (drule OL_DIFF_IMP >> disch_then (qspec_then `[a]` mp_tac) >> simp[OL]) >>
  irule smerge_OL >> simp[OL]
QED

Theorem ptr_operand_allocas_fold_ordered[local]:
  OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) ops))
Proof
  irule ptr_ordered_merge_fold >>
  simp[OL, listTheory.EVERY_MAP, listTheory.EVERY_MEM, ptr_base_allocas_ordered]
QED


Theorem ptr_used_inst_ordered:
  (!name. OL alloc_to (mems name)) /\
  OL alloc_to live /\ ptr_ml_ordered us ==>
  OL alloc_to (FST (ml_used_inst bpr mems lbl idx inst live us)) /\
  ptr_ml_ordered (SND (ml_used_inst bpr mems lbl idx inst live us))
Proof
  strip_tac >>
  `OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) inst.inst_operands))` by
    metis_tac[ptr_operand_allocas_fold_ordered] >>
  rewrite_tac[ml_used_inst_def] >>
  qabbrev_tac `bases = FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) inst.inst_operands)` >>
  qabbrev_tac `new_used = smerge alloc_to live bases` >>
  `OL alloc_to bases` by metis_tac[] >>
  `OL alloc_to new_used` by (simp[Abbr `new_used`] >> irule smerge_OL >> simp[]) >>
  qabbrev_tac `new_used2 = if inst.inst_opcode = INVOKE then
    (case inst.inst_operands of Label name :: _ => smerge alloc_to new_used (mems name)
     | _ => new_used) else new_used` >>
  `OL alloc_to new_used2` by
    (simp[Abbr `new_used2`] >> Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `h` >> simp[] >> irule smerge_OL >> simp[]) >>
  simp[] >> irule ptr_ml_ordered_update >> simp[]
QED

Theorem ptr_liveat_inst_ordered:
  (!name. OL alloc_to (mems name)) /\
  OL alloc_to live /\ ptr_ml_ordered la ==>
  OL alloc_to (FST (ml_liveat_inst bpr mems sizes lbl idx inst live la)) /\
  ptr_ml_ordered (SND (ml_liveat_inst bpr mems sizes lbl idx inst live la))
Proof
  strip_tac >>
  `OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) inst.inst_operands))` by
    metis_tac[ptr_operand_allocas_fold_ordered] >>
  rewrite_tac[ml_liveat_inst_def] >>
  qabbrev_tac `bases = FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) inst.inst_operands)` >>
  qabbrev_tac `reads = find_base_allocas_opt bpr (inst_read_op inst)` >>
  qabbrev_tac `writes = find_base_allocas_opt bpr (inst_write_op inst)` >>
  qabbrev_tac `live1 = smerge alloc_to live reads` >>
  `OL alloc_to bases` by metis_tac[] >>
  `OL alloc_to reads` by metis_tac[ptr_base_allocas_opt_ordered] >>
  `OL alloc_to live1` by (simp[Abbr `live1`] >> irule smerge_OL >> simp[]) >>
  qabbrev_tac `live2 = if inst.inst_opcode = INVOKE then
    (case inst.inst_operands of Label name :: _ =>
      smerge alloc_to live1 (smerge alloc_to (mems name) bases)
     | _ => live1) else live1` >>
  `OL alloc_to live2` by
    (simp[Abbr `live2`] >> Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
     Cases_on `inst.inst_operands` >> simp[] >> Cases_on `h` >> simp[] >>
     irule smerge_OL >> simp[] >> irule smerge_OL >> simp[]) >>
  simp[] >> reverse conj_tac
  >- (irule ptr_ml_ordered_update >> simp[]) >>
  Cases_on `inst_write_size inst` >> Cases_on `writes` >> simp[] >>
  Cases_on `t` >> simp[ptr_kill_write_ordered]
QED

Theorem ptr_liveat_insts_ordered:
  !live la. (!name. OL alloc_to (mems name)) /\
  OL alloc_to live /\ ptr_ml_ordered la ==>
  OL alloc_to (FST (ml_liveat_insts_rev bpr mems sizes lbl live la insts)) /\
  ptr_ml_ordered (SND (ml_liveat_insts_rev bpr mems sizes lbl live la insts))
Proof
  Induct_on `insts`
  >- simp[ml_liveat_insts_rev_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  first_x_assum (qspecl_then [`live`,`la`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes lbl live la insts` >>
  gvs[] >> simp[ml_liveat_insts_rev_def] >>
  irule ptr_liveat_inst_ordered >> simp[]
QED

Theorem ptr_used_insts_ordered:
  !live us. (!name. OL alloc_to (mems name)) /\
  OL alloc_to live /\ ptr_ml_ordered us ==>
  OL alloc_to (FST (ml_used_insts bpr mems lbl live us insts)) /\
  ptr_ml_ordered (SND (ml_used_insts bpr mems lbl live us insts))
Proof
  Induct_on `insts`
  >- simp[ml_used_insts_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `OL alloc_to (FST (ml_used_inst bpr mems lbl h0 h1 live us)) /\
   ptr_ml_ordered (SND (ml_used_inst bpr mems lbl h0 h1 live us))` by
    (irule ptr_used_inst_ordered >> simp[]) >>
  Cases_on `ml_used_inst bpr mems lbl h0 h1 live us` >>
  gvs[] >> simp[ml_used_insts_def] >> first_x_assum irule >> simp[]
QED

Theorem ptr_ml_ordered_lookup:
  ptr_ml_ordered st ==> OL alloc_to (ml_lookup st addr)
Proof
  simp[ptr_ml_ordered_def]
QED

Theorem ptr_liveat_block_ordered:
  (!name. OL alloc_to (mems name)) /\ ptr_ml_ordered la ==>
  ptr_ml_ordered (SND (ml_liveat_block bpr mems sizes cfg la bb))
Proof
  strip_tac >>
  `OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la (lbl,0)) (cfg_succs_of cfg bb.bb_label)))` by
    (irule ptr_ordered_merge_fold >>
     simp[OL, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
     metis_tac[ptr_ml_ordered_lookup]) >>
  simp[ml_liveat_block_def, pairTheory.pair_case_def] >>
  pairarg_tac >> simp[] >>
  drule ptr_liveat_insts_ordered >>
  metis_tac[pairTheory.FST, pairTheory.SND]
QED

Theorem ptr_used_block_ordered:
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ptr_ml_ordered us ==>
  ptr_ml_ordered (SND (ml_used_block bpr mems pallocas cfg us bb blocks))
Proof
  strip_tac >>
  `!addr. OL alloc_to (ml_lookup us addr)` by
    metis_tac[ptr_ml_ordered_lookup] >>
  `!lbl. OL alloc_to (case FIND (\b. b.bb_label = lbl) blocks of
     NONE => ml_lookup us (lbl,0)
   | SOME pred => ml_lookup us (pred.bb_label, PRE (LENGTH pred.bb_instructions)))` by
    (gen_tac >> CASE_TAC >> simp[]) >>
  `OL alloc_to (FOLDL (smerge alloc_to) [] (MAP (\lbl.
     case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us (lbl,0)
     | SOME pred => ml_lookup us (pred.bb_label, PRE (LENGTH pred.bb_instructions)))
     (cfg_preds_of cfg bb.bb_label)))` by
    (irule ptr_ordered_merge_fold >> simp[OL, listTheory.EVERY_MAP, listTheory.EVERY_MEM]) >>
  simp[ml_used_block_def, pairTheory.pair_case_def] >>
  pairarg_tac >> simp[] >>
  drule ptr_used_insts_ordered >>
  metis_tac[pairTheory.FST, pairTheory.SND, smerge_OL]
QED
