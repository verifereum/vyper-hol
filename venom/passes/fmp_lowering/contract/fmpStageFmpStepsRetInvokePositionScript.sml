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
  Induct >- simp[] >> rpt gen_tac >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule fmp_return_select_length >> strip_tac >>
  drule fmp_return_emit_length >> strip_tac >>
  drule fmp_return_inst_length >> strip_tac >>
  Cases_on `i`
  >- (gvs[] >> drule_all fmp_return_invoke_head >> strip_tac >>
      qexistsl_tac [`prefix`,`j`,`tail`] >> simp[] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `!k s restores code leftover s' i. _` drule >>
  disch_then (qspec_then `n` mp_tac) >>
  impl_tac >- (rpt strip_tac >> gvs[] >>
    first_x_assum (qspec_then `SUC j` mp_tac) >> simp[ADD_CLAUSES]) >>
  strip_tac >> qexistsl_tac [`prefix ++ head ++ pre`,`j`,`post`] >>
  simp[Once GENLIST_CONS, ADD_CLAUSES, combinTheory.o_DEF] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> decide_tac
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
  strip_tac >> drule fmp_return_indexed_position >>
  disch_then (qspecl_then [`plan`,`i`] mp_tac) >> simp[] >> strip_tac >>
  gvs[fmp_stage_tidx_def] >>
  simp[EL_APPEND_EQN, EL_CONS] >> decide_tac
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
