Theory concretizePtrOrdering
Ancestors
  concretizeMemLocDefs enumeral concretizePtrStoreCoverage

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

Theorem ptr_liveat_pass_ordered:
  !la. (!name. OL alloc_to (mems name)) /\ ptr_ml_ordered la ==>
  ptr_ml_ordered (SND (ml_one_pass_liveat bpr mems sizes cfg blocks labels la))
Proof
  Induct_on `labels` >- simp[ml_one_pass_liveat_def] >>
  rpt gen_tac >> strip_tac >> simp[ml_one_pass_liveat_def] >>
  CASE_TAC >> simp[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `ptr_ml_ordered la'` by
    (drule ptr_liveat_block_ordered >> metis_tac[pairTheory.SND]) >>
  first_x_assum (qspec_then `la'` mp_tac) >> simp[]
QED

Theorem ptr_used_pass_ordered:
  !us. (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ptr_ml_ordered us ==>
  ptr_ml_ordered (SND (ml_one_pass_used bpr mems pallocas cfg blocks labels us))
Proof
  Induct_on `labels` >- simp[ml_one_pass_used_def] >>
  rpt gen_tac >> strip_tac >> simp[ml_one_pass_used_def] >>
  CASE_TAC >> simp[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `ptr_ml_ordered us'` by
    (drule ptr_used_block_ordered >> metis_tac[pairTheory.SND]) >>
  first_x_assum (qspec_then `us'` mp_tac) >> simp[]
QED

Theorem ptr_one_pass_ordered:
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ptr_ml_ordered la /\ ptr_ml_ordered us /\
  ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,la',us') ==>
  ptr_ml_ordered la' /\ ptr_ml_ordered us'
Proof
  strip_tac >>
  qpat_x_assum `ml_one_pass _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[ml_one_pass_def] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[ptr_liveat_pass_ordered, ptr_used_pass_ordered, pairTheory.SND]
QED

Theorem ptr_iterate_fuel_ordered:
  !la us la' us'.
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ptr_ml_ordered la /\ ptr_ml_ordered us /\
  ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn la us = (la',us') ==>
  ptr_ml_ordered la' /\ ptr_ml_ordered us'
Proof
  Induct_on `fuel` >- simp[ml_iterate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> gvs[] >>
  `ptr_ml_ordered liveat' /\ ptr_ml_ordered used'` by
    (drule_all ptr_one_pass_ordered >> simp[]) >>
  Cases_on `changed` >> simp[] >> metis_tac[]
QED

Theorem ptr_iterate_ordered:
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ml_iterate bpr mems sizes pallocas cfg fn = SOME (changed,la,us) ==>
  ptr_ml_ordered la /\ ptr_ml_ordered us
Proof
  strip_tac >>
  ` (\(c,l,u). ptr_ml_ordered l /\ ptr_ml_ordered u) (changed,la,us)` suffices_by simp[] >>
  irule WhileTheory.OWHILE_INV_IND >>
  qexistsl [`\(c,l,u). c`,
    `\(c,l,u). ml_one_pass bpr mems sizes pallocas cfg fn l u`,
    `(T,FEMPTY,FEMPTY)`] >>
  simp[GSYM ml_iterate_def] >>
  rpt gen_tac >> PairCases_on `x` >> simp[] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  drule_all ptr_one_pass_ordered >> simp[]
QED

Theorem ptr_sorted_iterate_fuel_ordered:
  ml_iterate_fuel fuel bpr (\n. incr_ssort alloc_to (mems n)) sizes [] cfg fn
    FEMPTY FEMPTY = (la,us) ==>
  ptr_ml_ordered la /\ ptr_ml_ordered us
Proof
  strip_tac >> irule ptr_iterate_fuel_ordered >>
  goal_assum (drule_at Any) >> simp[ptr_incr_ssort_ordered, OL]
QED

Theorem ptr_sorted_iterate_ordered:
  ml_iterate bpr (\n. incr_ssort alloc_to (mems n)) sizes [] cfg fn =
    SOME (changed,la,us) ==>
  ptr_ml_ordered la /\ ptr_ml_ordered us
Proof
  strip_tac >> irule ptr_iterate_ordered >>
  goal_assum (drule_at Any) >> simp[ptr_incr_ssort_ordered, OL]
QED

Theorem ptr_ordered_iter_used_ordered:
  !la us ola keys us' ola' keys'.
  OL alloc_to pallocas /\ ptr_ml_ordered la /\ ptr_ml_ordered us /\
  ml_ordered_iter fuel bpr mems sizes pallocas cfg fn la us ola keys =
    (us',ola',keys') ==> ptr_ml_ordered us'
Proof
  Induct_on `fuel` >- simp[ml_ordered_iter_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ml_ordered_iter _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[ml_ordered_iter_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> gvs[] >>
  `ptr_ml_ordered la' /\ ptr_ml_ordered us''` by
    (irule ptr_one_pass_ordered >> goal_assum (drule_at Any) >>
     simp[ptr_incr_ssort_ordered]) >>
  pairarg_tac >> gvs[] >> Cases_on `changed` >> simp[] >> metis_tac[]
QED

Theorem ptr_ordered_iter_initial_used_ordered:
  ml_ordered_iter fuel bpr mems sizes [] cfg fn FEMPTY FEMPTY FEMPTY [] =
    (us,ola,keys) ==> ptr_ml_ordered us
Proof
  strip_tac >> irule ptr_ordered_iter_used_ordered >>
  goal_assum (drule_at Any) >> simp[OL]
QED

Definition ptr_livesets_ordered_def:
  ptr_livesets_ordered (ls : (allocation, inst_addr list) fmap) <=>
    !a xs. FLOOKUP ls a = SOME xs ==> OL inst_addr_to xs
End

Theorem ptr_livesets_ordered_empty[simp]:
  ptr_livesets_ordered FEMPTY
Proof
  simp[ptr_livesets_ordered_def]
QED

Theorem ptr_livesets_default_ordered:
  ptr_livesets_ordered ls ==>
  OL inst_addr_to (case FLOOKUP ls a of NONE => [] | SOME xs => xs)
Proof
  strip_tac >> CASE_TAC >> simp[OL] >>
  metis_tac[ptr_livesets_ordered_def]
QED

Theorem ptr_store_insert_ordered:
  ptr_livesets_ordered ls ==> ptr_livesets_ordered (ptr_store_insert addr ls a)
Proof
  strip_tac >>
  drule (ptr_livesets_default_ordered) >> disch_then (qspec_then `a` assume_tac) >>
  simp[ptr_store_insert_def, ptr_livesets_ordered_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >> irule smerge_OL >> simp[OL]) >>
  metis_tac[ptr_livesets_ordered_def]
QED

Theorem ptr_store_fold_ordered:
  !ls. ptr_livesets_ordered ls ==>
  ptr_livesets_ordered (FOLDL (ptr_store_insert addr) ls keys)
Proof
  Induct_on `keys` >> simp[] >> metis_tac[ptr_store_insert_ordered]
QED

Theorem ptr_livesets_insts_ordered:
  !ls. ptr_livesets_ordered ls ==>
  ptr_livesets_ordered (ml_livesets_insts label la us ls insts)
Proof
  Induct_on `insts` >- simp[ml_livesets_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_livesets_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> first_x_assum irule >>
  irule ptr_store_fold_ordered >> simp[]
QED

Theorem ptr_mark_stores_insts_ordered:
  !ls. ptr_livesets_ordered ls ==>
  ptr_livesets_ordered (ml_mark_stores_insts bpr label ls insts)
Proof
  Induct_on `insts` >- simp[ml_mark_stores_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_mark_stores_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> first_x_assum irule >>
  irule ptr_store_fold_ordered >> simp[]
QED

Theorem ptr_livesets_blocks_ordered[local]:
  !ls. ptr_livesets_ordered ls ==>
  ptr_livesets_ordered
    (FOLDL (\m bb. ml_livesets_insts bb.bb_label la us m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks)
Proof
  Induct_on `blocks` >> simp[] >>
  metis_tac[ptr_livesets_insts_ordered]
QED

Theorem ptr_compute_livesets_ordered:
  ptr_livesets_ordered (ml_compute_livesets la us fn)
Proof
  simp[ml_compute_livesets_def, ptr_livesets_blocks_ordered]
QED

Theorem ptr_store_blocks_ordered[local]:
  !ls. ptr_livesets_ordered ls ==>
  ptr_livesets_ordered
    (FOLDL (\m bb. ml_mark_stores_insts bpr bb.bb_label m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks)
Proof
  Induct_on `blocks` >> simp[] >>
  metis_tac[ptr_mark_stores_insts_ordered]
QED

Theorem ptr_mark_stores_live_ordered:
  ptr_livesets_ordered ls ==>
  ptr_livesets_ordered (ml_mark_stores_live bpr fn ls)
Proof
  simp[ml_mark_stores_live_def, ptr_store_blocks_ordered]
QED

Theorem ptr_mem_liveness_ordered:
  ptr_livesets_ordered
    (mem_liveness_analyze bpr mems sizes pallocas cfg fn)
Proof
  rewrite_tac[mem_liveness_analyze_def] >>
  Cases_on `ml_iterate bpr mems sizes pallocas cfg fn` >> simp[] >>
  PairCases_on `x` >>
  simp[ptr_mark_stores_live_ordered, ptr_compute_livesets_ordered]
QED

Theorem ptr_mem_liveness_fuel_ordered:
  ptr_livesets_ordered
    (mem_liveness_analyze_fuel fuel bpr mems sizes pallocas cfg fn)
Proof
  rewrite_tac[mem_liveness_analyze_fuel_def] >>
  Cases_on `ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn FEMPTY FEMPTY` >>
  simp[ptr_mark_stores_live_ordered, ptr_compute_livesets_ordered]
QED

Theorem ptr_context_mem_livesets_ordered:
  ptr_livesets_ordered (context_mem_livesets fuel ctx fn bpr cfg)
Proof
  simp[context_mem_livesets_def, ptr_mem_liveness_fuel_ordered]
QED

Theorem ptr_livesets_sinter_membership:
  ptr_livesets_ordered ls /\
  FLOOKUP ls a = SOME xs /\ FLOOKUP ls b = SOME ys ==>
  (MEM addr (sinter inst_addr_to xs ys) <=> MEM addr xs /\ MEM addr ys)
Proof
  rpt strip_tac >>
  `OL inst_addr_to xs /\ OL inst_addr_to ys` by
    metis_tac[ptr_livesets_ordered_def] >>
  qpat_x_assum `OL inst_addr_to xs` (mp_tac o MATCH_MP OL_INTER_IMP) >>
  disch_then (qspec_then `ys` mp_tac) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem ptr_context_liveset_default_ordered:
  OL inst_addr_to
    (case FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a of
       NONE => [] | SOME xs => xs)
Proof
  irule ptr_livesets_default_ordered >>
  simp[ptr_context_mem_livesets_ordered]
QED

Theorem ptr_context_livesets_sinter_membership:
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a = SOME xs /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) b = SOME ys ==>
  (MEM addr (sinter inst_addr_to xs ys) <=> MEM addr xs /\ MEM addr ys)
Proof
  strip_tac >> irule ptr_livesets_sinter_membership >>
  metis_tac[ptr_context_mem_livesets_ordered]
QED
