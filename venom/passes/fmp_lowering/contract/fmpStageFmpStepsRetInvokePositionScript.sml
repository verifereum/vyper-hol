Theory fmpStageFmpStepsRetInvokePosition
Ancestors
  fmpStageControl fmpStageRel fmpLowerDefs fmpLowerProps
  fmpLowerIndexedProps fmpStepLayout list rich_list finite_map arithmetic venomInst

Theorem fmp_return_block_restore_count:
  !n. LENGTH (FILTER (\r. FST r = (lbl,k))
    (FLAT (GENLIST (\j.
      case FLOOKUP plan (bl,j) of
        NONE => [] | SOME b => [((bl,j),b)]) n))) =
    if lbl = bl /\ k < n /\ (bl,k) IN FDOM plan then 1 else 0
Proof
  Induct >> simp[GENLIST, FLAT_SNOC, FILTER_APPEND] >>
  Cases_on `FLOOKUP plan (bl,n)` >> simp[] >>
  Cases_on `lbl = bl` >> simp[] >>
  Cases_on `k = n` >> gvs[FLOOKUP_DEF] >>
  Cases_on `k < n` >> simp[]
QED

Theorem fmp_return_plan_restore_count:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  LENGTH (FILTER (\r. FST r = (lbl,k)) (fmp_plan_to_alist fn plan)) <= 1
Proof
  simp[fmp_plan_to_alist_def] >>
  Q.SPEC_TAC (`fn.fn_blocks`,`bbs`) >> Induct >>
  simp[FILTER_APPEND, fmp_return_block_restore_count] >>
  rpt strip_tac >>
  Cases_on `lbl = h.bb_label /\ k < LENGTH h.bb_instructions /\
            (h.bb_label,k) IN FDOM plan` >> simp[] >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `FILTER P xs` >>
  `FILTER P xs = []` suffices_by simp[] >>
  simp[FILTER_EQ_NIL, Abbr `xs`, Abbr `P`, EVERY_MEM, MEM_FLAT, MEM_MAP,
       MEM_GENLIST, PULL_EXISTS] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP plan (bb.bb_label,k')` >> gvs[] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_return_emit_length:
  !bases s code s'. fmp_emit_restores runner s bases = (code,s') ==>
    LENGTH code = LENGTH bases
Proof
  Induct >> simp[fmp_emit_restores_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem fmp_return_inst_length:
  fmp_lower_inst infos ctx runner s inst = SOME (code,s') ==>
  LENGTH code = if inst.inst_opcode = DALLOCA then 4 else 1
Proof
  Cases_on `inst.inst_opcode = DALLOCA` >>
  simp[fmp_lower_inst_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem fmp_return_invoke_head:
  inst.inst_opcode = INVOKE /\
  fmp_lower_inst infos ctx runner s inst = SOME (code,s') ==>
  ?j. code = [j] /\ j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_return_select_length:
  fmp_select_point_restores p restores = (bases,later) ==>
  LENGTH bases = LENGTH (FILTER (\r. FST r = p) restores) /\
  (!q. q <> p ==>
    LENGTH (FILTER (\r. FST r = q) later) =
    LENGTH (FILTER (\r. FST r = q) restores))
Proof
  simp[fmp_select_point_restores_filter] >> strip_tac >> gvs[] >>
  rpt strip_tac >> AP_TERM_TAC >> simp[FILTER_FILTER] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem fmp_return_indexed_position_cert:
  !insts k s restores code leftover s' i.
  fmp_lower_indexed infos ctx runner lbl k s restores insts =
    SOME (code,leftover,s') /\ i < LENGTH insts /\
  (EL i insts).inst_opcode = INVOKE /\
  (!j. j < LENGTH insts ==>
    LENGTH (FILTER (\r. FST r = (lbl,k+j)) restores) =
      if (lbl,k+j) IN FDOM (plan:fmp_reclaim_plan) then 1 else 0) ==>
  ?pre j post.
    code = pre ++ [j] ++ post /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i insts).inst_id /\
    LENGTH pre =
      SUM (GENLIST (\n. (if (lbl,k+n) IN FDOM plan then 1 else 0) +
        (if (EL n insts).inst_opcode = DALLOCA then 4 else 1)) i) +
      (if (lbl,k+i) IN FDOM plan then 1 else 0) /\
    (?sp sp'. fmp_lower_inst infos ctx runner sp (EL i insts) = SOME ([j],sp'))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule fmp_return_select_length >> strip_tac >>
  drule fmp_return_emit_length >> strip_tac >>
  drule fmp_return_inst_length >> strip_tac >>
  Cases_on `i`
  >- (gvs[] >> drule_all fmp_return_invoke_head >> strip_tac >>
      qexistsl_tac [`prefix`,`j`,`tail`] >> simp[] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!k s restores code leftover s' i. _` drule >>
  disch_then (qspec_then `n` mp_tac) >>
  impl_tac >- (rpt strip_tac >> gvs[] >>
    first_x_assum (qspec_then `SUC j` mp_tac) >> simp[ADD_CLAUSES]) >>
  strip_tac >> qexistsl_tac [`prefix ++ head ++ pre`,`j`,`post`] >>
  simp[Once GENLIST_CONS, ADD_CLAUSES, combinTheory.o_DEF] >>
  reverse conj_tac >- metis_tac[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> decide_tac
QED

Theorem fmp_return_indexed_position:
  !insts k s restores code leftover s' i.
  fmp_lower_indexed infos ctx runner lbl k s restores insts =
    SOME (code,leftover,s') /\ i < LENGTH insts /\
  (EL i insts).inst_opcode = INVOKE /\
  (!j. j < LENGTH insts ==>
    LENGTH (FILTER (\r. FST r = (lbl,k+j)) restores) =
      if (lbl,k+j) IN FDOM (plan:fmp_reclaim_plan) then 1 else 0) ==>
  ?pre j post.
    code = pre ++ [j] ++ post /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i insts).inst_id /\
    LENGTH pre =
      SUM (GENLIST (\n. (if (lbl,k+n) IN FDOM plan then 1 else 0) +
        (if (EL n insts).inst_opcode = DALLOCA then 4 else 1)) i) +
      (if (lbl,k+i) IN FDOM plan then 1 else 0)
Proof
  rpt strip_tac >> drule_all fmp_return_indexed_position_cert >>
  strip_tac >> qexistsl_tac [`pre`,`j`,`post`] >> simp[]
QED

Theorem fmp_return_plan_restore_exact:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fmp_reclaim_input fn plan ==>
  LENGTH (FILTER (\r. FST r = (lbl,k)) (fmp_plan_to_alist fn plan)) =
    if (lbl,k) IN FDOM plan then 1 else 0
Proof
  strip_tac >> drule fmp_return_plan_restore_count >> strip_tac >>
  `FILTER (\r. FST r = (lbl,k)) (fmp_plan_to_alist fn plan) = [] <=>
   ~((lbl,k) IN FDOM plan)` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
     drule MEM_fmp_plan_to_alist_FLOOKUP >>
     simp[FLOOKUP_DEF] >> metis_tac[]) >>
  Cases_on `(lbl,k) IN FDOM plan` >> gvs[] >>
  first_x_assum (qspecl_then [`plan`,`lbl`,`k`] assume_tac) >>
  qmatch_goalsub_abbrev_tac `LENGTH xs` >>
  `LENGTH xs <> 0` by metis_tac[LENGTH_NIL] >> decide_tac
QED

Theorem fmp_return_indexed_at_cert:
  fmp_lower_indexed infos ctx runner lbl 0 s restores insts =
    SOME (code,leftover,s') /\ i < LENGTH insts /\
  (EL i insts).inst_opcode = INVOKE /\
  (!j. j < LENGTH insts ==>
    LENGTH (FILTER (\r. FST r = (lbl,j)) restores) =
      if (lbl,j) IN FDOM plan then 1 else 0) ==>
  ?j sp sp'.
    fmp_lower_inst infos ctx runner sp (EL i insts) = SOME ([j],sp') /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i insts).inst_id /\
    fmp_stage_tidx plan NONE lbl insts i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH code /\
    EL (fmp_stage_tidx plan NONE lbl insts i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) code = j
Proof
  strip_tac >> drule fmp_return_indexed_position_cert >>
  disch_then (qspecl_then [`plan`,`i`] mp_tac) >> simp[] >> strip_tac >>
  gvs[fmp_stage_tidx_def] >>
  qexistsl_tac [`sp`,`sp'`] >>
  qpat_assum `LENGTH pre = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[EL_APPEND_EQN, EL_CONS] >> decide_tac
QED

Theorem fmp_return_indexed_at:
  fmp_lower_indexed infos ctx runner lbl 0 s restores insts =
    SOME (code,leftover,s') /\ i < LENGTH insts /\
  (EL i insts).inst_opcode = INVOKE /\
  (!j. j < LENGTH insts ==>
    LENGTH (FILTER (\r. FST r = (lbl,j)) restores) =
      if (lbl,j) IN FDOM plan then 1 else 0) ==>
  ?j. j.inst_opcode = INVOKE /\ j.inst_id = (EL i insts).inst_id /\
    fmp_stage_tidx plan NONE lbl insts i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH code /\
    EL (fmp_stage_tidx plan NONE lbl insts i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) code = j
Proof
  strip_tac >> drule_all fmp_return_indexed_at_cert >>
  strip_tac >> qexists `j` >> simp[]
QED

Theorem fmp_return_indexed_other_count:
  !insts k s restores code leftover s'.
  fmp_lower_indexed infos ctx runner lbl k s restores insts =
    SOME (code,leftover,s') ==>
  !other j. other <> lbl ==>
    LENGTH (FILTER (\r. FST r = (other,j)) leftover) =
    LENGTH (FILTER (\r. FST r = (other,j)) restores)
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspecl_then [`other`,`j`] mp_tac) >>
  simp[] >> strip_tac >> drule fmp_return_select_length >>
  simp[]
QED

Theorem fmp_return_blocks_at:
  !bbs s restores out leftover s' lbl bb.
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  lookup_block lbl bbs = SOME bb /\
  (!bl k. MEM bl (MAP (\b. b.bb_label) bbs) ==>
    LENGTH (FILTER (\r. FST r = (bl,k)) restores) =
      if (bl,k) IN FDOM (plan:fmp_reclaim_plan) then 1 else 0) ==>
  ?bb' sp rs later sp'.
    lookup_block lbl out = SOME bb' /\ bb'.bb_label = bb.bb_label /\
    fmp_lower_indexed infos ctx runner lbl 0 sp rs bb.bb_instructions =
      SOME (bb'.bb_instructions,later,sp') /\
    (!k. LENGTH (FILTER (\r. FST r = (lbl,k)) rs) =
      if (lbl,k) IN FDOM plan then 1 else 0)
Proof
  Induct >- simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[fmp_lower_blocks_def, AllCaseEqs(), lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[]
  >- (qexistsl_tac [`bb with bb_instructions := insts`,`s`,`restores`,
                    `later`,`s2`] >> simp[FIND_thm] >> metis_tac[]) >>
  qpat_x_assum `!s restores out leftover s' lbl bb. _` drule >>
  disch_then (qspecl_then [`lbl`,`bb`] mp_tac) >>
  impl_tac >- (simp[lookup_block_def] >> rpt strip_tac >>
    drule fmp_return_indexed_other_count >>
    disch_then (qspecl_then [`bl`,`k`] mp_tac) >>
    `bl <> h.bb_label` by metis_tac[] >> simp[] >> strip_tac >>
    first_x_assum (qspecl_then [`bl`,`k`] mp_tac) >> simp[] >>
    Cases_on `(bl,k) IN FDOM plan` >> simp[]) >>
  strip_tac >> qexistsl_tac [`bb'`,`sp`,`rs`,`later'`,`sp'`] >>
  fs[lookup_block_def, FIND_thm] >> gen_tac >>
  Cases_on `(lbl,k) IN FDOM plan` >> gvs[] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem fmp_return_tail_index[local]:
  LENGTH b = LENGTH a + d /\ LENGTH a <= q /\
  q < LENGTH (a ++ tail) /\ EL q (a ++ tail) = j ==>
  q + d < LENGTH (b ++ tail) /\ EL (q+d) (b ++ tail) = j
Proof
  simp[EL_APPEND_EQN] >> rpt strip_tac >>
  `~(q < LENGTH a) /\ ~(q+d < LENGTH b) /\
   q+d-LENGTH b = q-LENGTH a` by decide_tac >> gvs[]
QED

Theorem fmp_return_invoke_after_prefix[local]:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix /\
  q < LENGTH (prefix ++ tail) /\
  (EL q (prefix ++ tail)).inst_opcode = INVOKE ==>
  LENGTH prefix <= q
Proof
  rpt strip_tac >> Cases_on `q < LENGTH prefix` >> simp[] >>
  fs[EL_APPEND1, EVERY_EL] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED

Theorem fmp_return_install_at:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
    (users ++ OPTION_TO_LIST oldpc) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s)
    (entry::rest) = SOME (out,s') /\
  lookup_block lbl (entry::rest) = SOME bb /\
  q < LENGTH bb.bb_instructions /\ EL q bb.bb_instructions = j /\
  j.inst_opcode = INVOKE ==>
  ?bb'. lookup_block lbl out = SOME bb' /\
    q + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0)
      < LENGTH bb'.bb_instructions /\
    EL (q + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  Cases_on `lbl = entry.bb_label` >>
  gvs[lookup_block_def, FIND_thm]
  >- (`LENGTH (users ++ OPTION_TO_LIST oldpc) <= q` by
        (irule fmp_return_invoke_after_prefix >>
         reverse conj_tac >- simp[] >> qexists `tail` >>
         simp[APPEND_ASSOC]) >>
      Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
      `LENGTH (OPTION_TO_LIST newpc) = LENGTH (OPTION_TO_LIST oldpc)` by
        (Cases_on `oldpc` >> Cases_on `newpc` >>
         gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      simp[EL_APPEND_EQN] >>
      `~(q < LENGTH users) /\
       ~(q-LENGTH users < LENGTH (OPTION_TO_LIST oldpc)) /\
       ~(q+LENGTH (OPTION_TO_LIST root) < LENGTH users) /\
       ~(q+LENGTH (OPTION_TO_LIST root)-LENGTH users < LENGTH (OPTION_TO_LIST newpc)) /\
       ~(q+LENGTH (OPTION_TO_LIST root)-LENGTH users < LENGTH (OPTION_TO_LIST root))` by decide_tac >>
      simp[] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  qexists `bb` >> simp[lookup_block_def]
QED

Theorem fmp_return_install_checked_at:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  lookup_block lbl blocks = SOME bb /\ q < LENGTH bb.bb_instructions /\
  EL q bb.bb_instructions = j /\ j.inst_opcode = INVOKE ==>
  ?entry rest bb'. blocks = entry::rest /\
    lookup_block lbl out = SOME bb' /\
    q + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0)
      < LENGTH bb'.bb_instructions /\
    EL (q + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >> gvs[] >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
      (users ++ OPTION_TO_LIST oldpc)` by
    (drule split_fmp_entry_parameter_prefix >>
     Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  metis_tac[fmp_return_install_at]
QED

Theorem fmp_return_blocks_invoke_at_cert:
  fmp_lower_blocks infos ctx runner s (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult out leftover s') /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  fmp_reclaim_input fn plan /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j sp sp'. lookup_block lbl out = SOME bb' /\
    fmp_lower_inst infos ctx runner sp (EL i bb.bb_instructions) = SOME ([j],sp') /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx plan NONE lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx plan NONE lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) bb'.bb_instructions = j
Proof
  strip_tac >> drule fmp_return_blocks_at >>
  disch_then (qspecl_then [`plan`,`lbl`,`bb`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
    irule fmp_return_plan_restore_exact >> simp[]) >>
  strip_tac >> drule fmp_return_indexed_at_cert >>
  disch_then (qspecl_then [`plan`,`i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem fmp_return_blocks_invoke_at:
  fmp_lower_blocks infos ctx runner s (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult out leftover s') /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  fmp_reclaim_input fn plan /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl out = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx plan NONE lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx plan NONE lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_return_blocks_invoke_at_cert >>
  strip_tac >> qexistsl_tac [`bb'`,`j`] >> simp[]
QED

Theorem fmp_return_root_offset:
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fn.fn_blocks = entry::rest /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  fmp_stage_tidx plan (fmp_stage_root infos ctx fn) lbl bb.bb_instructions i =
  fmp_stage_tidx plan NONE lbl bb.bb_instructions i +
    (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0)
Proof
  strip_tac >> drule split_fmp_entry_reconstruct >> strip_tac >> gvs[] >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  Cases_on `lbl = entry.bb_label` >>
  gvs[lookup_block_def, FIND_thm]
  >- (`LENGTH (users ++ option_CASE oldpc [] (\i. [i])) <= i` by
        (irule fmp_return_invoke_after_prefix >>
         reverse conj_tac >- simp[] >> qexists `suffix` >> simp[APPEND_ASSOC]) >>
      gvs[fmp_make_root_layout_def, fmp_stage_root_def,
          fmp_stage_tidx_def, AllCaseEqs(), callLayoutDefsTheory.OPTION_TO_LIST_def] >>
      Cases_on `newpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[fmp_make_root_layout_def, fmp_stage_root_def,
      fmp_stage_tidx_def, AllCaseEqs(), callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

Theorem fmp_return_full_blocks_at_cert:
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fn.fn_blocks = entry::rest /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_reclaim_input fn plan /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j sp sp'. lookup_block lbl out = SOME bb' /\
    fmp_lower_inst infos ctx runner sp (EL i bb.bb_instructions) = SOME ([j],sp') /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx plan (fmp_stage_root infos ctx fn) lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx plan (fmp_stage_root infos ctx fn) lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) bb'.bb_instructions = j
Proof
  strip_tac >>
  drule_all fmp_return_blocks_invoke_at_cert >> strip_tac >>
  drule_all fmp_return_install_checked_at >> strip_tac >>
  drule_all fmp_lower_blocks_preserves_labels >> strip_tac >>
  drule_all fmp_return_root_offset >> strip_tac >>
  gvs[] >> qexistsl_tac [`sp`,`sp'`] >> simp[]
QED

Theorem fmp_return_full_blocks_at:
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fn.fn_blocks = entry::rest /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_reclaim_input fn plan /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl out = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx plan (fmp_stage_root infos ctx fn) lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0) < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx plan (fmp_stage_root infos ctx fn) lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM plan then 1 else 0)) bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_return_full_blocks_at_cert >>
  strip_tac >> qexistsl_tac [`bb'`,`j`] >> simp[]
QED

Theorem fmp_return_lowered_full_at_cert:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
    (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j sp sp'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_lower_inst infos ctx runner sp (EL i bb.bb_instructions) = SOME ([j],sp') /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = j
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (Cases_on `split_fmp_entry fn` >> gvs[fmp_lower_input_def] >>
     Cases_on `x` >> metis_tac[]) >>
  `?entry rest. fn.fn_blocks = entry::rest` by
    (Cases_on `fn.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `fn'.fn_blocks = blocks'` by
    gvs[fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()] >>
  gvs[fmp_stage_plan_def] >>
  drule fmp_return_full_blocks_at_cert >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem fmp_return_lowered_full_at:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
    (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> (drule fmp_return_lowered_full_at_cert >>
    disch_then (qspecl_then [`lbl`,`i`,`bb`] mp_tac) >>
    (impl_tac >- (simp[] >> metis_tac[])) >>
    strip_tac >> qexistsl_tac [`bb'`,`j`] >> simp[])
QED

Theorem fmp_return_tidx_empty:
  (!j. j < i ==> (EL j insts).inst_opcode <> DALLOCA) ==>
  fmp_stage_tidx FEMPTY NONE lbl insts i = i
Proof
  strip_tac >> simp[fmp_stage_tidx_def] >>
  `GENLIST (\j. if (EL j insts).inst_opcode = DALLOCA then 4 else 1) i =
   GENLIST (K 1) i` by (irule GENLIST_CONG >> simp[]) >>
  simp[] >> Induct_on `i` >> simp[GENLIST, SUM_SNOC]
QED

Theorem fmp_return_unlowered_no_raw:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  no_raw_fmp_ops fn
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmp_lower_input_def, lookup_function_def] >> metis_tac[FIND_MEM]) >>
  drule_all fmpAnalysisPropsTheory.analyze_fmp_context_unsealed_direct_fields >>
  strip_tac >> irule fmp_direct_info_no_bits_no_raw >> metis_tac[]
QED

Theorem fmp_return_lowered_at:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (irule fmp_return_lowered_full_at >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  drule_all fmp_return_unlowered_no_raw >> strip_tac >>
  `fmp_stage_tidx FEMPTY NONE lbl bb.bb_instructions i = i` by
    (irule fmp_return_tidx_empty >> rpt strip_tac >>
     `MEM (EL j bb.bb_instructions) (fn_insts fn)` by
       (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
        qexists `bb` >> simp[EL_MEM] >>
        gvs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
     gvs[no_raw_fmp_ops_def] >>
     first_x_assum drule >> simp[is_raw_fmp_opcode_def]) >>
  gvs[] >> qexists `bb` >> simp[]
QED

Theorem fmp_return_saved_invoke_position:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE ==>
  ?j. active_inst fn' j t /\ MEM j (fn_insts fn') /\
      j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[contextCodegenRelTheory.active_inst_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  gvs[fmp_frame_rel_def] >>
  drule_all fmp_return_lowered_at >> strip_tac >>
  qexists `j` >> simp[] >>
  `MEM bb' fn'.fn_blocks /\ bb'.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> conj_tac
     >- (irule FIND_MEM >> goal_assum (drule_at Any)) >>
     qpat_assum `FIND _ fn'.fn_blocks = SOME bb'`
       (mp_then Any mp_tac FIND_P) >> simp[]) >>
  conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >>
      qexists `bb'` >>
      qpat_x_assum `_ + _ < LENGTH bb'.bb_instructions` mp_tac >>
      once_rewrite_tac[ADD_COMM] >> strip_tac >>
      qpat_x_assum `EL (_ + _) bb'.bb_instructions = j` mp_tac >>
      once_rewrite_tac[ADD_COMM] >> strip_tac >> simp[]) >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  qexists `bb'` >> simp[] >> metis_tac[EL_MEM]
QED
