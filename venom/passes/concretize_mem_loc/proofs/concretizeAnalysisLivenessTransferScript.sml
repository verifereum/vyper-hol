Theory concretizeAnalysisLivenessTransfer
Ancestors concretizeMemLocDefs concretizePtrReadCoverage concretizePtrOrdering
  enumeral finite_map list pred_set

Definition ml_operand_gen_def:
  ml_operand_gen a bpr inst <=>
    ?op. MEM op inst.inst_operands /\ MEM a (find_base_allocas bpr op)
End

Definition ml_callee_gen_def:
  ml_callee_gen a mems inst <=>
    inst.inst_opcode = INVOKE /\
    ?nm ops. inst.inst_operands = Label nm :: ops /\ MEM a (mems nm)
End

Definition ml_read_gen_def:
  ml_read_gen a bpr mems inst <=>
    MEM a (find_base_allocas_opt bpr (inst_read_op inst)) \/
    ml_callee_gen a mems inst \/
    (inst.inst_opcode = INVOKE /\
     (?nm ops. inst.inst_operands = Label nm :: ops) /\ ml_operand_gen a bpr inst)
End

Definition ml_used_gen_def:
  ml_used_gen a bpr mems inst <=>
    ml_operand_gen a bpr inst \/ ml_callee_gen a mems inst
End

Theorem ml_merge_fold_mem:
  !xss xs. MEM a (FOLDL (smerge cmp) xs xss) <=>
    MEM a xs \/ ?ys. MEM ys xss /\ MEM a ys
Proof
  Induct >> simp[ptr_smerge_union] >> metis_tac[]
QED

Theorem ml_liveat_record_exact:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') ==>
  (MEM a (ml_lookup la' (lbl,idx)) <=> MEM a live \/ ml_read_gen a bpr mems inst)
Proof
  simp[ml_liveat_inst_def] >> strip_tac >>
  gvs[ml_lookup_def, FLOOKUP_UPDATE, ptr_smerge_union, ml_merge_fold_mem,
      ml_read_gen_def, ml_callee_gen_def, ml_operand_gen_def, MEM_MAP] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >>
  Cases_on `inst.inst_operands` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >>
  Cases_on `h` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >> metis_tac[]
QED

Theorem ml_used_exact:
  ml_used_inst bpr mems lbl idx inst used us = (after,us') ==>
  (MEM a after <=> MEM a used \/ ml_used_gen a bpr mems inst) /\
  (MEM a (ml_lookup us' (lbl,idx)) <=> MEM a after)
Proof
  simp[ml_used_inst_def] >> strip_tac >>
  gvs[ml_lookup_def, FLOOKUP_UPDATE, ml_used_gen_def,
      ml_callee_gen_def, ml_operand_gen_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >>
  Cases_on `inst.inst_operands` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >>
  Cases_on `h` >> simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >> metis_tac[]
QED

Theorem ml_sdiff_singleton_mem:
  OL cmp xs ==> (MEM a (sdiff cmp xs [b]) <=> MEM a xs /\ a <> b)
Proof
  strip_tac >> drule OL_DIFF_IMP >>
  disch_then (qspec_then `[b]` mp_tac) >> simp[OL]
QED

Theorem ml_kill_write_mem:
  OL alloc_to live /\ (!r. MEM r reads ==> MEM r live) ==>
  (MEM a (ml_kill_write sizes reads wsz live b) <=>
   MEM a live /\ ~(a = b /\ sizes a = SOME wsz /\ ~MEM a reads))
Proof
  strip_tac >> simp[ml_kill_write_def] >>
  Cases_on `sizes b` >> simp[] >>
  rpt IF_CASES_TAC >> simp[ml_sdiff_singleton_mem, ptr_smerge_union] >> metis_tac[]
QED

Theorem ml_liveat_before_from_record:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') /\
  OL alloc_to (ml_lookup la' (lbl,idx)) ==>
  (MEM a before <=> MEM a (ml_lookup la' (lbl,idx)) /\
    ~ptr_ml_can_kill a bpr sizes inst)
Proof
  strip_tac >>
  `!r. MEM r (find_base_allocas_opt bpr (inst_read_op inst)) ==>
    MEM r (ml_lookup la' (lbl,idx))` by metis_tac[ml_liveat_record_exact, ml_read_gen_def] >>
  qpat_x_assum `ml_liveat_inst _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[ml_liveat_inst_def] >> strip_tac >>
  gvs[ml_lookup_def, FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac `OL alloc_to recorded` >>
  Cases_on `inst_write_size inst` >>
  Cases_on `find_base_allocas_opt bpr (inst_write_op inst)` >>
  simp[ptr_ml_can_kill_def] >>
  Cases_on `t` >> simp[ptr_ml_can_kill_def, ml_kill_write_mem] >> metis_tac[]
QED

Theorem ml_liveat_before_exact:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live ==>
  (MEM a before <=> (MEM a live \/ ml_read_gen a bpr mems inst) /\
    ~ptr_ml_can_kill a bpr sizes inst)
Proof
  strip_tac >>
  `OL alloc_to (ml_lookup la' (lbl,idx))` by
    (gvs[ml_liveat_inst_def, ml_lookup_def, FLOOKUP_UPDATE] >>
     `OL alloc_to (FOLDL (smerge alloc_to) []
       (MAP (find_base_allocas bpr) inst.inst_operands))` by
       (irule ptr_ordered_merge_fold >> simp[OL, EVERY_MAP, EVERY_MEM, ptr_base_allocas_ordered]) >>
     Cases_on `inst.inst_opcode = INVOKE` >>
     simp[ptr_base_allocas_opt_ordered, smerge_OL] >>
     Cases_on `inst.inst_operands` >> simp[ptr_base_allocas_opt_ordered, smerge_OL] >>
     Cases_on `h` >> gvs[] >>
     metis_tac[ptr_base_allocas_opt_ordered, smerge_OL]) >>
  drule_all ml_liveat_before_from_record >>
  disch_then (qspec_then `a` mp_tac) >>
  drule ml_liveat_record_exact >> disch_then (qspec_then `a` mp_tac) >> simp[]
QED

Theorem ml_liveat_other_address:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') /\
  addr <> (lbl,idx) ==> ml_lookup la' addr = ml_lookup la addr
Proof
  simp[ml_liveat_inst_def] >> rpt strip_tac >>
  gvs[ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ml_used_other_address:
  ml_used_inst bpr mems lbl idx inst used us = (after,us') /\
  addr <> (lbl,idx) ==> ml_lookup us' addr = ml_lookup us addr
Proof
  simp[ml_used_inst_def] >> rpt strip_tac >>
  gvs[ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ml_liveat_inst_bit_mono:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') /\
  ml_liveat_inst bpr mems sizes lbl idx inst live2 la2 = (before2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live /\ OL alloc_to live2 /\
  (MEM a live ==> MEM a live2) ==>
  (MEM a before ==> MEM a before2) /\
  (MEM a (ml_lookup la' (lbl,idx)) ==> MEM a (ml_lookup la2' (lbl,idx)))
Proof
  rpt strip_tac
  >- (drule_all ml_liveat_before_exact >> disch_then (qspec_then `a` assume_tac) >>
      rev_drule_all ml_liveat_before_exact >> disch_then (qspec_then `a` assume_tac) >>
      metis_tac[]) >>
  drule ml_liveat_record_exact >> disch_then (qspec_then `a` assume_tac) >>
  rev_drule ml_liveat_record_exact >> disch_then (qspec_then `a` assume_tac) >> metis_tac[]
QED

Theorem ml_liveat_inst_bit_cong:
  ml_liveat_inst bpr mems sizes lbl idx inst live la = (before,la') /\
  ml_liveat_inst bpr mems sizes lbl idx inst live2 la2 = (before2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live /\ OL alloc_to live2 /\
  (MEM a live <=> MEM a live2) ==>
  (MEM a before <=> MEM a before2) /\
  (MEM a (ml_lookup la' (lbl,idx)) <=> MEM a (ml_lookup la2' (lbl,idx)))
Proof
  strip_tac >>
  `MEM a live ==> MEM a live2` by simp[] >>
  `MEM a live2 ==> MEM a live` by simp[] >>
  drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_liveat_inst_bit_mono >>
  disch_then drule_all >> strip_tac >>
  rev_drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_liveat_inst_bit_mono >>
  disch_then drule_all >> metis_tac[]
QED

Theorem ml_used_inst_bit_mono:
  ml_used_inst bpr mems lbl idx inst used us = (after,us') /\
  ml_used_inst bpr mems lbl idx inst used2 us2 = (after2,us2') /\
  (MEM a used ==> MEM a used2) ==>
  (MEM a after ==> MEM a after2) /\
  (MEM a (ml_lookup us' (lbl,idx)) ==> MEM a (ml_lookup us2' (lbl,idx)))
Proof
  strip_tac >>
  drule ml_used_exact >> disch_then (qspec_then `a` assume_tac) >>
  rev_drule ml_used_exact >> disch_then (qspec_then `a` assume_tac) >> metis_tac[]
QED

Theorem ml_used_inst_bit_cong:
  ml_used_inst bpr mems lbl idx inst used us = (after,us') /\
  ml_used_inst bpr mems lbl idx inst used2 us2 = (after2,us2') /\
  (MEM a used <=> MEM a used2) ==>
  (MEM a after <=> MEM a after2) /\
  (MEM a (ml_lookup us' (lbl,idx)) <=> MEM a (ml_lookup us2' (lbl,idx)))
Proof
  strip_tac >>
  `MEM a used ==> MEM a used2` by simp[] >>
  `MEM a used2 ==> MEM a used` by simp[] >>
  drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_used_inst_bit_mono >>
  disch_then drule_all >> strip_tac >>
  rev_drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_used_inst_bit_mono >>
  disch_then drule_all >> metis_tac[]
QED

Theorem ml_liveat_insts_other_address:
  !live la before la'.
  ml_liveat_insts_rev bpr mems sizes lbl live la insts = (before,la') /\
  (!idx inst. MEM (idx,inst) insts ==> addr <> (lbl,idx)) ==>
  ml_lookup la' addr = ml_lookup la addr
Proof
  Induct_on `insts` >> simp[ml_liveat_insts_rev_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[ml_liveat_insts_rev_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `addr <> (lbl,h0)` by metis_tac[] >>
  drule_all ml_liveat_other_address >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem ml_used_insts_other_address:
  !used us after us'.
  ml_used_insts bpr mems lbl used us insts = (after,us') /\
  (!idx inst. MEM (idx,inst) insts ==> addr <> (lbl,idx)) ==>
  ml_lookup us' addr = ml_lookup us addr
Proof
  Induct_on `insts` >> simp[ml_used_insts_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[ml_used_insts_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >>
  metis_tac[ml_used_other_address]
QED

Theorem ml_liveat_insts_bit_mono:
  !live la live2 la2 before la' before2 la2'.
  ml_liveat_insts_rev bpr mems sizes lbl live la insts = (before,la') /\
  ml_liveat_insts_rev bpr mems sizes lbl live2 la2 insts = (before2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live /\ OL alloc_to live2 /\
  ptr_ml_ordered la /\ ptr_ml_ordered la2 /\ (MEM a live ==> MEM a live2) ==>
  (MEM a before ==> MEM a before2) /\
  (!addr. ((?idx inst. MEM (idx,inst) insts /\ addr = (lbl,idx)) \/
     (MEM a (ml_lookup la addr) ==> MEM a (ml_lookup la2 addr))) ==>
     (MEM a (ml_lookup la' addr) ==> MEM a (ml_lookup la2' addr)))
Proof
  Induct_on `insts`
  >- (pure_rewrite_tac [ml_liveat_insts_rev_def, pairTheory.PAIR_EQ] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> pure_rewrite_tac [ml_liveat_insts_rev_def] >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes lbl live la insts` >>
  rename1 `ml_liveat_insts_rev bpr mems sizes lbl live la insts = (tail_live,tail_la)` >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes lbl live2 la2 insts` >>
  rename1 `ml_liveat_insts_rev bpr mems sizes lbl live2 la2 insts = (tail_live2,tail_la2)` >>
  simp[NoAsms] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `OL alloc_to tail_live /\ OL alloc_to tail_live2` by
    metis_tac[ptr_liveat_insts_ordered, pairTheory.FST] >>
  drule_all ml_liveat_inst_bit_mono >> strip_tac >> conj_tac >- simp[] >>
  gen_tac >> Cases_on `addr = (lbl,h0)` >- gvs[] >>
  disch_tac >>
  `ml_lookup la' addr = ml_lookup tail_la addr /\
   ml_lookup la2' addr = ml_lookup tail_la2 addr` by
    metis_tac[ml_liveat_other_address] >>
  qpat_x_assum `!addr. _` (qspec_then `addr` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ml_liveat_insts_bit_cong:
  ml_liveat_insts_rev bpr mems sizes lbl live la insts = (before,la') /\
  ml_liveat_insts_rev bpr mems sizes lbl live2 la2 insts = (before2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live /\ OL alloc_to live2 /\
  ptr_ml_ordered la /\ ptr_ml_ordered la2 /\ (MEM a live <=> MEM a live2) ==>
  (MEM a before <=> MEM a before2) /\
  (!addr. ((?idx inst. MEM (idx,inst) insts /\ addr = (lbl,idx)) \/
     (MEM a (ml_lookup la addr) <=> MEM a (ml_lookup la2 addr))) ==>
     (MEM a (ml_lookup la' addr) <=> MEM a (ml_lookup la2' addr)))
Proof
  strip_tac >>
  `MEM a live ==> MEM a live2` by simp[] >>
  `MEM a live2 ==> MEM a live` by simp[] >>
  drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_liveat_insts_bit_mono >>
  disch_then drule_all >> strip_tac >>
  rev_drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_liveat_insts_bit_mono >>
  disch_then drule_all >> strip_tac >> conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `addr` mp_tac) >>
  first_x_assum (qspec_then `addr` mp_tac) >> metis_tac[]
QED

Theorem ml_used_insts_bit_mono:
  !used us used2 us2 after us' after2 us2'.
  ml_used_insts bpr mems lbl used us insts = (after,us') /\
  ml_used_insts bpr mems lbl used2 us2 insts = (after2,us2') /\
  (MEM a used ==> MEM a used2) ==>
  (MEM a after ==> MEM a after2) /\
  (!addr. ((?idx inst. MEM (idx,inst) insts /\ addr = (lbl,idx)) \/
     (MEM a (ml_lookup us addr) ==> MEM a (ml_lookup us2 addr))) ==>
     (MEM a (ml_lookup us' addr) ==> MEM a (ml_lookup us2' addr)))
Proof
  Induct_on `insts`
  >- (pure_rewrite_tac [ml_used_insts_def, pairTheory.PAIR_EQ] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> pure_rewrite_tac [ml_used_insts_def] >>
  Cases_on `ml_used_inst bpr mems lbl h0 h1 used us` >>
  rename1 `ml_used_inst bpr mems lbl h0 h1 used us = (head_used,head_us)` >>
  Cases_on `ml_used_inst bpr mems lbl h0 h1 used2 us2` >>
  rename1 `ml_used_inst bpr mems lbl h0 h1 used2 us2 = (head_used2,head_us2)` >>
  simp[NoAsms] >> strip_tac >>
  drule_all ml_used_inst_bit_mono >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> conj_tac >- simp[] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!addr. _` (qspec_then `addr` mp_tac) >>
  Cases_on `addr = (lbl,h0)` >- gvs[] >>
  `ml_lookup head_us addr = ml_lookup us addr /\
   ml_lookup head_us2 addr = ml_lookup us2 addr` by
    metis_tac[ml_used_other_address] >>
  simp[] >> metis_tac[]
QED

Theorem ml_used_insts_bit_cong:
  ml_used_insts bpr mems lbl used us insts = (after,us') /\
  ml_used_insts bpr mems lbl used2 us2 insts = (after2,us2') /\
  (MEM a used <=> MEM a used2) ==>
  (MEM a after <=> MEM a after2) /\
  (!addr. ((?idx inst. MEM (idx,inst) insts /\ addr = (lbl,idx)) \/
     (MEM a (ml_lookup us addr) <=> MEM a (ml_lookup us2 addr))) ==>
     (MEM a (ml_lookup us' addr) <=> MEM a (ml_lookup us2' addr)))
Proof
  strip_tac >>
  `MEM a used ==> MEM a used2` by simp[] >>
  `MEM a used2 ==> MEM a used` by simp[] >>
  drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_used_insts_bit_mono >>
  disch_then drule_all >> strip_tac >>
  rev_drule_at (Pat `MEM _ _ ==> MEM _ _`) ml_used_insts_bit_mono >>
  disch_then drule_all >> strip_tac >> conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `addr` mp_tac) >>
  first_x_assum (qspec_then `addr` mp_tac) >> metis_tac[]
QED

Theorem ml_liveat_block_join_mem:
  MEM a (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la (lbl,0)) (cfg_succs_of cfg label))) <=>
  ?lbl. MEM lbl (cfg_succs_of cfg label) /\ MEM a (ml_lookup la (lbl,0))
Proof simp[ml_merge_fold_mem, MEM_MAP] >> metis_tac[]
QED

Theorem ml_used_block_join_mem:
  MEM a (smerge alloc_to live_pallocas
    (FOLDL (smerge alloc_to) [] (MAP (\lbl.
      case FIND (\b. b.bb_label = lbl) blocks of
        NONE => ml_lookup us (lbl,0)
      | SOME bb => ml_lookup us (bb.bb_label,PRE (LENGTH bb.bb_instructions)))
      (cfg_preds_of cfg label)))) <=>
  MEM a live_pallocas \/
  ?lbl. MEM lbl (cfg_preds_of cfg label) /\
    MEM a (case FIND (\b. b.bb_label = lbl) blocks of
      NONE => ml_lookup us (lbl,0)
    | SOME bb => ml_lookup us (bb.bb_label,PRE (LENGTH bb.bb_instructions)))
Proof simp[ptr_smerge_union, ml_merge_fold_mem, MEM_MAP] >> metis_tac[]
QED

Theorem ml_liveat_block_bit_mono:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  ml_liveat_block bpr mems sizes cfg la2 bb = (changed2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\ ptr_ml_ordered la2 /\
  ((?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ MEM a (ml_lookup la (lbl,0))) ==>
   (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ MEM a (ml_lookup la2 (lbl,0)))) /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup la' (bb.bb_label,i)) ==> MEM a (ml_lookup la2' (bb.bb_label,i)))
Proof
  simp[ml_liveat_block_def] >> ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la (lbl,0)) (cfg_succs_of cfg bb.bb_label))) /\
   OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la2 (lbl,0)) (cfg_succs_of cfg bb.bb_label)))` by
    (conj_tac >> irule ptr_ordered_merge_fold >>
     fs[OL, EVERY_MAP, EVERY_MEM, ptr_ml_ordered_def]) >>
  `MEM a (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la (lbl,0)) (cfg_succs_of cfg bb.bb_label))) ==>
   MEM a (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la2 (lbl,0)) (cfg_succs_of cfg bb.bb_label)))` by
    simp[ml_liveat_block_join_mem] >>
  drule_all ml_liveat_insts_bit_mono >> strip_tac >>
  qpat_x_assum `!addr. _` (qspec_then `(bb.bb_label,i)` mp_tac) >>
  impl_tac >- (disj1_tac >>
    qexistsl [`i`, `EL i bb.bb_instructions`] >> simp[indexedListsTheory.MEM_MAPi]) >> simp[]
QED

Theorem ml_liveat_block_bit_factor:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  ml_liveat_block bpr mems sizes cfg la2 bb = (changed2,la2') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\ ptr_ml_ordered la2 /\
  ((?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ MEM a (ml_lookup la (lbl,0))) <=>
   (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ MEM a (ml_lookup la2 (lbl,0)))) /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup la' (bb.bb_label,i)) <=> MEM a (ml_lookup la2' (bb.bb_label,i)))
Proof
  strip_tac >> eq_tac >> strip_tac >>
  irule ml_liveat_block_bit_mono >> metis_tac[]
QED

Theorem ml_used_block_bit_mono:
  ml_used_block bpr mems live_pallocas cfg us bb blocks = (changed,us') /\
  ml_used_block bpr mems live_pallocas cfg us2 bb blocks = (changed2,us2') /\
  (!lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) ==>
    (MEM a (case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us (lbl,0)
     | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions))) ==>
     MEM a (case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us2 (lbl,0)
     | SOME b => ml_lookup us2 (b.bb_label,PRE (LENGTH b.bb_instructions))))) /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup us' (bb.bb_label,i)) ==> MEM a (ml_lookup us2' (bb.bb_label,i)))
Proof
  simp[ml_used_block_def] >> ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `MEM a (smerge alloc_to live_pallocas
     (FOLDL (smerge alloc_to) [] (MAP (\lbl.
       case FIND (\b. b.bb_label = lbl) blocks of
         NONE => ml_lookup us (lbl,0)
       | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions)))
       (cfg_preds_of cfg bb.bb_label)))) ==>
   MEM a (smerge alloc_to live_pallocas
     (FOLDL (smerge alloc_to) [] (MAP (\lbl.
       case FIND (\b. b.bb_label = lbl) blocks of
         NONE => ml_lookup us2 (lbl,0)
       | SOME b => ml_lookup us2 (b.bb_label,PRE (LENGTH b.bb_instructions)))
       (cfg_preds_of cfg bb.bb_label))))` by
     (simp[ml_used_block_join_mem] >> metis_tac[]) >>
  drule_all ml_used_insts_bit_mono >> strip_tac >>
  qpat_x_assum `!addr. _` (qspec_then `(bb.bb_label,i)` mp_tac) >>
  impl_tac >- (disj1_tac >>
    qexistsl [`i`, `EL i bb.bb_instructions`] >> simp[indexedListsTheory.MEM_MAPi]) >> simp[]
QED

Theorem ml_used_block_bit_factor:
  ml_used_block bpr mems live_pallocas cfg us bb blocks = (changed,us') /\
  ml_used_block bpr mems live_pallocas cfg us2 bb blocks = (changed2,us2') /\
  (!lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) ==>
    (MEM a (case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us (lbl,0)
     | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions))) <=>
     MEM a (case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us2 (lbl,0)
     | SOME b => ml_lookup us2 (b.bb_label,PRE (LENGTH b.bb_instructions))))) /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup us' (bb.bb_label,i)) <=> MEM a (ml_lookup us2' (bb.bb_label,i)))
Proof
  strip_tac >> eq_tac >> strip_tac >>
  irule ml_used_block_bit_mono >> metis_tac[]
QED

(* Boolean projections of the indexed folds.  The record is made before
   applying a backward kill; it is not the returned accumulator. *)
Definition ml_liveat_before_bit_def:
  (ml_liveat_before_bit a bpr mems sizes [] bit = bit) /\
  (ml_liveat_before_bit a bpr mems sizes ((idx,inst)::rest) bit =
    ((ml_liveat_before_bit a bpr mems sizes rest bit \/ ml_read_gen a bpr mems inst) /\
      ~ptr_ml_can_kill a bpr sizes inst))
End

Definition ml_liveat_record_bit_def:
  (ml_liveat_record_bit a bpr mems sizes lbl addr [] bit old = old) /\
  (ml_liveat_record_bit a bpr mems sizes lbl addr ((idx,inst)::rest) bit old =
    if addr = (lbl,idx) then
      ml_liveat_before_bit a bpr mems sizes rest bit \/ ml_read_gen a bpr mems inst
    else ml_liveat_record_bit a bpr mems sizes lbl addr rest bit old)
End

Theorem ml_liveat_insts_bits_exact:
  !live la before la'.
  ml_liveat_insts_rev bpr mems sizes lbl live la insts = (before,la') /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to live /\ ptr_ml_ordered la ==>
  (MEM a before <=> ml_liveat_before_bit a bpr mems sizes insts (MEM a live)) /\
  (!addr. MEM a (ml_lookup la' addr) <=>
    ml_liveat_record_bit a bpr mems sizes lbl addr insts
      (MEM a live) (MEM a (ml_lookup la addr)))
Proof
  Induct_on `insts`
  >- (simp[ml_liveat_insts_rev_def, ml_liveat_before_bit_def, ml_liveat_record_bit_def]) >>
  rpt gen_tac >> PairCases_on `h` >> pure_rewrite_tac[ml_liveat_insts_rev_def] >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes lbl live la insts` >>
  rename1 `ml_liveat_insts_rev bpr mems sizes lbl live la insts = (tail_live,tail_la)` >>
  simp[NoAsms] >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  `OL alloc_to tail_live` by metis_tac[ptr_liveat_insts_ordered, pairTheory.FST] >>
  drule_all ml_liveat_before_exact >> disch_then (qspec_then `a` assume_tac) >>
  drule ml_liveat_record_exact >> disch_then (qspec_then `a` assume_tac) >>
  conj_tac >- simp[ml_liveat_before_bit_def] >>
  gen_tac >> Cases_on `addr = (lbl,h0)`
  >- gvs[ml_liveat_record_bit_def] >>
  drule_all ml_liveat_other_address >> simp[ml_liveat_record_bit_def]
QED

Definition ml_used_after_bit_def:
  (ml_used_after_bit a bpr mems [] bit = bit) /\
  (ml_used_after_bit a bpr mems ((idx,inst)::rest) bit =
    ml_used_after_bit a bpr mems rest (bit \/ ml_used_gen a bpr mems inst))
End

Definition ml_used_record_bit_def:
  (ml_used_record_bit a bpr mems lbl addr [] bit old = old) /\
  (ml_used_record_bit a bpr mems lbl addr ((idx,inst)::rest) bit old =
    ml_used_record_bit a bpr mems lbl addr rest (bit \/ ml_used_gen a bpr mems inst)
      (if addr = (lbl,idx) then bit \/ ml_used_gen a bpr mems inst else old))
End

Theorem ml_used_insts_bits_exact:
  !used us after us'.
  ml_used_insts bpr mems lbl used us insts = (after,us') ==>
  (MEM a after <=> ml_used_after_bit a bpr mems insts (MEM a used)) /\
  (!addr. MEM a (ml_lookup us' addr) <=>
    ml_used_record_bit a bpr mems lbl addr insts
      (MEM a used) (MEM a (ml_lookup us addr)))
Proof
  Induct_on `insts`
  >- simp[ml_used_insts_def, ml_used_after_bit_def, ml_used_record_bit_def] >>
  rpt gen_tac >> PairCases_on `h` >> pure_rewrite_tac[ml_used_insts_def] >>
  Cases_on `ml_used_inst bpr mems lbl h0 h1 used us` >>
  rename1 `ml_used_inst bpr mems lbl h0 h1 used us = (head_used,head_us)` >>
  simp[NoAsms] >> strip_tac >>
  drule ml_used_exact >> disch_then (qspec_then `a` assume_tac) >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- simp[ml_used_after_bit_def] >>
  gen_tac >> simp[ml_used_record_bit_def] >>
  Cases_on `addr = (lbl,h0)` >- gvs[] >>
  drule_all ml_used_other_address >> simp[]
QED
