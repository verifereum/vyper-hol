(* Predicate-parametric assembly of the inserted-index classification. *)
Theory fmpStageCoverMemAssemble
Ancestors
  fmpStageCoverMemWalk fmpStageControl fmpStageControlLayout
  fmpStageControlWalk fmpStageRel fmpStepLayout fmpLowerDefs
  fmpLowerProps fmpReclaimDefs fmpWfDefs venomInst venomWf
  list rich_list finite_map

Theorem fmp_cover_walk_interval:
  fmp_lower_indexed infos ctx runner lbl 0 s rs xs = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> FLOOKUP plan (lbl,j) = SOME b) /\
  P ASSIGN /\ P ADD /\ P NOT /\ P AND /\ P BUMP /\ P RETPC_PARAM /\
  idx < LENGTH xs /\
  fmp_stage_tidx plan NONE lbl xs idx <= i /\
  i < fmp_stage_tidx plan NONE lbl xs (SUC idx) /\
  (i = fmp_stage_tidx plan NONE lbl xs idx +
       (if (lbl,idx) IN FDOM plan then 1 else 0) ==>
   MEM (EL idx xs).inst_opcode [DALLOCA; RETPC_PARAM]) ==>
  i < LENGTH out /\ P (EL i out).inst_opcode
Proof
  rpt strip_tac >>
  drule fmp_control_walk_suffix >>
  disch_then (qspecl_then [`plan`, `idx`] mp_tac) >> simp[] >>
  strip_tac >>
  `DROP idx xs = EL idx xs :: DROP (SUC idx) xs` by simp[DROP_CONS_EL] >>
  qpat_x_assum `DROP idx xs = _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `SOME (tail,left,s')` >>
  `fmp_stage_tidx plan NONE lbl xs (SUC idx) =
   fmp_stage_tidx plan NONE lbl xs idx +
   (if (lbl,idx) IN FDOM plan then 1 else 0) +
   (if (EL idx xs).inst_opcode = DALLOCA then 4 else 1)` by
    simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  `i - fmp_stage_tidx plan NONE lbl xs idx < LENGTH tail /\
   P (EL (i - fmp_stage_tidx plan NONE lbl xs idx) tail).inst_opcode` by
    (drule fmp_cover_walk_chunk >>
     disch_then (qspecl_then [`i - fmp_stage_tidx plan NONE lbl xs idx`, `plan`, `P`] mp_tac) >>
     simp[] >> (impl_tac >- (conj_tac >- (Cases_on `(EL idx xs).inst_opcode = DALLOCA` >>
       Cases_on `(lbl,idx) IN FDOM plan` >> gvs[]) >> strip_tac >>
       `i = fmp_stage_tidx plan NONE lbl xs idx +
         (if (lbl,idx) IN FDOM plan then 1 else 0)` by
         (Cases_on `(lbl,idx) IN FDOM plan` >> gvs[]) >> fs[])) >> simp[]) >>
  gvs[fmp_stage_tidx_def, Abbr `tail`] >>
  qmatch_asmsub_abbrev_tac `P (EL (i - pos) (DROP pos out)).inst_opcode` >>
  `i - pos + pos = i` by fs[] >>
  `EL (i-pos) (DROP pos out) = EL i out` by
    (qspecl_then [`i-pos`, `pos`, `out`] mp_tac listTheory.EL_DROP >> simp[]) >>
  fs[]
QED

Theorem fmp_cover_root_splice[local]:
  EVERY (\x. x.inst_opcode <> DALLOCA) (users ++ old) /\
  (!j. j < LENGTH users + LENGTH old ==> FLOOKUP plan (lbl,j) = NONE) /\
  LENGTH middle = LENGTH old + 1 /\ EVERY (\x. P x.inst_opcode) middle /\
  (!k h. k < LENGTH (users ++ old ++ suffix) /\
    fmp_stage_tidx plan NONE lbl (users ++ old ++ suffix) k <= h /\
    h < fmp_stage_tidx plan NONE lbl (users ++ old ++ suffix) (SUC k) /\
    (h = fmp_stage_tidx plan NONE lbl (users ++ old ++ suffix) k +
      (if (lbl,k) IN FDOM plan then 1 else 0) ==>
      MEM (EL k (users ++ old ++ suffix)).inst_opcode [DALLOCA; RETPC_PARAM]) ==>
    h < LENGTH (users ++ old ++ tail) /\
    P (EL h (users ++ old ++ tail)).inst_opcode) /\
  idx < LENGTH (users ++ old ++ suffix) /\
  (if idx = 0 then 0 else fmp_stage_tidx plan
    (SOME (lbl,LENGTH users + LENGTH old)) lbl (users ++ old ++ suffix) idx) <= i /\
  i < fmp_stage_tidx plan (SOME (lbl,LENGTH users + LENGTH old)) lbl
    (users ++ old ++ suffix) (SUC idx) /\
  (i = fmp_stage_tidx plan (SOME (lbl,LENGTH users + LENGTH old)) lbl
    (users ++ old ++ suffix) idx + (if (lbl,idx) IN FDOM plan then 1 else 0) ==>
    MEM (EL idx (users ++ old ++ suffix)).inst_opcode [DALLOCA; RETPC_PARAM]) ==>
  i < LENGTH (users ++ middle ++ tail) /\
  P (EL i (users ++ middle ++ tail)).inst_opcode
Proof
  strip_tac >>
  qabbrev_tac `rp = LENGTH users + LENGTH old` >>
  qabbrev_tac `q = \n. fmp_stage_tidx plan NONE lbl (users ++ old ++ suffix) n` >>
  `!n. fmp_stage_tidx plan (SOME (lbl,rp)) lbl (users ++ old ++ suffix) n =
    q n + (if rp <= n then 1 else 0)` by simp[Abbr `q`, fmp_stage_tidx_def] >>
  `!n. n <= q n` by
    (Induct >- simp[Abbr `q`, fmp_stage_tidx_def] >>
     `q (SUC n) = q n + (if (lbl,n) IN FDOM plan then 1 else 0) +
       (if (EL n (users ++ old ++ suffix)).inst_opcode = DALLOCA then 4 else 1)` by
       simp[NoAsms, Abbr `q`, fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
     Cases_on `(lbl,n) IN FDOM plan` >>
     Cases_on `(EL n (users ++ old ++ suffix)).inst_opcode = DALLOCA` >> fs[]) >>
  `!n. n <= rp ==> q n = n` by
    (Induct >- simp[Abbr `q`, fmp_stage_tidx_def] >> strip_tac >>
     `n < LENGTH (users ++ old)` by fs[Abbr `rp`] >>
     `(EL n (users ++ old ++ suffix)).inst_opcode <> DALLOCA` by
       (qpat_x_assum `EVERY _ (users ++ old)` mp_tac >>
        pure_rewrite_tac[EVERY_EL] >> disch_then (qspec_then `n` mp_tac) >>
        simp[GSYM APPEND_ASSOC, EL_APPEND1]) >>
     `FLOOKUP plan (lbl,n) = NONE` by fs[Abbr `rp`] >>
     `q n = n` by fs[] >>
     `~((lbl,n) IN FDOM plan)` by fs[FLOOKUP_DEF] >>
     `q (SUC n) = q n + (if (lbl,n) IN FDOM plan then 1 else 0) +
       (if (EL n (users ++ old ++ suffix)).inst_opcode = DALLOCA then 4 else 1)` by
       simp[NoAsms, Abbr `q`, fmp_stage_tidx_def, GENLIST, SUM_SNOC] >> fs[]) >>
  `idx <= q idx` by fs[] >>
  `idx <= i` by (Cases_on `idx = 0` >> fs[]) >>
  Cases_on `i < LENGTH users`
  >- (`idx < rp /\ SUC idx <= rp` by fs[Abbr `rp`] >>
      `q idx = idx /\ q (SUC idx) = SUC idx` by fs[] >>
      `i = idx` by (Cases_on `rp <= SUC idx` >> fs[Abbr `rp`]) >>
      `i < LENGTH (users ++ old ++ tail) /\
       P (EL i (users ++ old ++ tail)).inst_opcode` by
        (qpat_x_assum `!k h. _` (qspecl_then [`idx`, `i`] mp_tac) >>
         (impl_tac >- (fs[Abbr `q`] >> metis_tac[])) >> simp[]) >>
      gvs[EL_APPEND1]) >>
  Cases_on `i < LENGTH users + LENGTH middle`
  >- (`i - LENGTH users < LENGTH middle` by fs[] >>
      `P (EL (i - LENGTH users) middle).inst_opcode` by
        (qpat_x_assum `EVERY _ middle` mp_tac >>
         pure_rewrite_tac[EVERY_EL] >> simp[]) >>
      simp[EL_APPEND, EL_APPEND1]) >>
  `rp + 1 <= i` by fs[Abbr `rp`] >>
  `rp <= idx` by
    (spose_not_then assume_tac >>
     `SUC idx <= rp` by fs[] >>
     `q (SUC idx) = SUC idx` by fs[] >>
     Cases_on `rp <= SUC idx` >> fs[]) >>
  `q idx <= i - 1 /\ i - 1 < q (SUC idx)` by
    (Cases_on `idx = 0` >> fs[]) >>
  `i - 1 < LENGTH (users ++ old ++ tail) /\
   P (EL (i - 1) (users ++ old ++ tail)).inst_opcode` by
    (qpat_x_assum `!k h. _` (qspecl_then [`idx`, `i-1`] mp_tac) >>
     (impl_tac >-
       (conj_tac >- fs[] >>
        conj_tac >- fs[Abbr `q`] >>
        conj_tac >- fs[Abbr `q`] >> strip_tac >>
        `i = q idx + 1 + (if (lbl,idx) IN FDOM plan then 1 else 0)` by
          (Cases_on `(lbl,idx) IN FDOM plan` >> fs[Abbr `q`]) >>
        fs[Abbr `q`])) >> simp[]) >>
  `i - 1 - rp = i - (LENGTH users + LENGTH middle)` by fs[Abbr `rp`] >>
  `~(i - 1 < LENGTH users + LENGTH old)` by fs[Abbr `rp`] >>
  `~(i < LENGTH users + LENGTH middle)` by fs[] >>
  fs[EL_APPEND, Abbr `rp`] >> gvs[]
QED

Theorem fmp_cover_inserted_from_root:
  (!func users oldpc suffix cx inf run supply n root newpc supply' entry rest tail out supply''.
    split_fmp_entry func = SOME (FmpEntryLayout users oldpc suffix) /\
    fmp_make_root_layout cx func inf run supply = SOME (FmpRootLayout n root newpc supply') /\
    entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
    fmp_install_root cx func (FmpRootLayout n root newpc supply') (entry::rest) = SOME (out,supply'') /\
    P INITIAL_FMP /\ P FMP_PARAM /\ P RETPC_PARAM /\
    EVERY (\x. P x.inst_opcode) (OPTION_TO_LIST oldpc) ==>
    ?middle. out = (entry with bb_instructions := users ++ middle ++ tail)::rest /\
      LENGTH middle = LENGTH (OPTION_TO_LIST oldpc) + LENGTH (OPTION_TO_LIST root) /\
      EVERY (\x. P x.inst_opcode) middle) /\
  EVERY P [ASSIGN; ADD; NOT; AND; BUMP; INITIAL_FMP; FMP_PARAM; RETPC_PARAM] /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (if idx = 0 then 0
   else fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx) <= i /\
  i < fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) lbl bb.bb_instructions (SUC idx) /\
  (i = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
       (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) ==>
   MEM (EL idx bb.bb_instructions).inst_opcode [DALLOCA; RETPC_PARAM]) ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    i < LENGTH bb'.bb_instructions /\ P (EL i bb'.bb_instructions).inst_opcode
Proof
  rpt gen_tac >> strip_tac >> fs[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (fs[] >> (drule fmp_control_rewrite >> simp[] >> strip_tac >>
      drule split_fmp_entry_reconstruct >> strip_tac >>
      drule_all fmp_control_root_layout >> strip_tac >>
      drule_all fmp_control_checked_walk >> strip_tac >>
      drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
      drule fmp_lower_blocks_preserves_labels >> simp[] >> strip_tac >>
      drule fmp_cover_walk_interval >>
      disch_then (qspec_then `fmp_stage_plan infos ctx fn` mp_tac) >>
      simp[] >> disch_then (mk_asm "raw") >>
      qpat_x_assum `blocks = _` SUBST_ALL_TAC >>
      reverse (Cases_on `lbl = entry.bb_label`)
      >- (`lookup_block lbl fn'.fn_blocks = SOME (bb with bb_instructions := code)` by
            (drule fmp_control_install_other >> simp[] >> metis_tac[]) >>
          `!n. fmp_stage_tidx (fmp_stage_plan infos ctx fn)
             (fmp_stage_root infos ctx fn) lbl bb.bb_instructions n =
             fmp_stage_tidx (fmp_stage_plan infos ctx fn) NONE lbl bb.bb_instructions n` by
            (Cases_on `root = NONE` >> gvs[fmp_stage_tidx_def]) >>
          `fmp_stage_tidx (fmp_stage_plan infos ctx fn) NONE lbl bb.bb_instructions idx <= i` by
            (Cases_on `idx = 0` >> gvs[fmp_stage_tidx_def]) >>
          asm "raw" (qspecl_then [`idx`, `i`, `P`] mp_tac) >>
          simp[] >> (impl_tac >- fs[]) >> strip_tac >>
          simp[]) >>
      `bb = entry` by
        (qpat_x_assum `lookup_block lbl fn.fn_blocks = SOME bb` mp_tac >>
         simp[lookup_block_def, FIND_thm]) >>
      `code = entry'.bb_instructions` by
        (qpat_x_assum `lookup_block bb.bb_label (entry'::rest') = _` mp_tac >>
         simp[lookup_block_def, FIND_thm, basic_block_accfupds] >>
         strip_tac >>
         qpat_x_assum `entry' = _` SUBST_ALL_TAC >>
         fs[basic_block_accfupds]) >>
      Cases_on `root = NONE`
      >- (`newpc = oldpc` by metis_tac[] >>
          `fn'.fn_blocks = entry'::rest'` by
            (irule fmp_control_install_no_root >>
             qexistsl_tac [`ctx`, `fn`, `oldpc`, `s2`, `s2`, `tail`, `users`] >>
             Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
          `fmp_stage_root infos ctx fn = NONE` by fs[] >>
          `fmp_stage_tidx (fmp_stage_plan infos ctx fn) NONE lbl bb.bb_instructions idx <= i` by
            (Cases_on `idx = 0` >> gvs[fmp_stage_tidx_def]) >>
          asm "raw" (qspecl_then [`idx`, `i`, `P`] mp_tac) >>
          simp[] >> (impl_tac >- fs[]) >> strip_tac >>
          qexists_tac `entry'` >>
          simp[lookup_block_def, FIND_thm]) >>
      `entry'.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
        (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      `fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s1)
        (entry'::rest') = SOME (fn'.fn_blocks,s1)` by
        (drule_all fmp_install_root_exact_prefix >>
         strip_tac >> fs[]) >>
      `EVERY (\x. P x.inst_opcode) (OPTION_TO_LIST oldpc)` by
        (Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
         drule split_fmp_entry_retpc_opcode >> simp[]) >>
      qpat_x_assum `!func users oldpc suffix cx inf run supply n root newpc supply' entry rest tail out supply''. _`
        (drule_at (Pos hd)) >>
      disch_then drule >> simp[] >> disch_then drule >>
      simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `!j. j < LENGTH users + LENGTH (OPTION_TO_LIST oldpc) ==>
        FLOOKUP (fmp_stage_plan infos ctx fn) (lbl,j) = NONE` by
        (metis_tac[fmp_control_prefix_plan_absent]) >>
      `EVERY (\x. MEM x.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
         (users ++ OPTION_TO_LIST oldpc)` by
        (drule split_fmp_entry_parameter_prefix >>
         Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      `bb.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ suffix` by
        (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      `EVERY (\x. x.inst_opcode <> DALLOCA) (users ++ OPTION_TO_LIST oldpc)` by
        (qpat_x_assum `EVERY (\x. MEM x.inst_opcode _) _` mp_tac >>
         pure_rewrite_tac[EVERY_MEM] >> strip_tac >> gen_tac >>
         disch_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
      `LENGTH (OPTION_TO_LIST root) = 1` by
        (Cases_on `root` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      `i < LENGTH (users ++ middle ++ tail) /\
       P (EL i (users ++ middle ++ tail)).inst_opcode` suffices_by
        (strip_tac >> qexists_tac `entry' with bb_instructions := users ++ middle ++ tail` >>
         gvs[lookup_block_def, FIND_thm, basic_block_accfupds]) >>
      irule fmp_cover_root_splice >> conj_tac >- (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`idx`, `lbl`, `OPTION_TO_LIST oldpc`,
        `fmp_stage_plan infos ctx fn`, `suffix`] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          asm "raw" (qspecl_then [`k`, `h`, `P`] mp_tac) >>
          fs[] >> metis_tac[]) >>
      fs[])) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  `no_raw_fmp_ops fn` by
    (fs[fmp_stage_lowered_def] >>
     gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
     irule fmp_no_need_input_no_raw >> metis_tac[]) >>
  `!j. j < LENGTH bb.bb_instructions ==> (EL j bb.bb_instructions).inst_opcode <> DALLOCA` by
    (rpt strip_tac >>
     gvs[no_raw_fmp_ops_def, fn_insts_def, fn_insts_blocks_def,
         MEM_FLAT, MEM_MAP, is_raw_fmp_opcode_def] >>
     `MEM (EL j bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
       (irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
        qexists_tac `bb` >> simp[EL_MEM]) >>
     first_x_assum drule >> simp[is_raw_fmp_opcode_def]) >>
  `!n. n <= LENGTH bb.bb_instructions ==>
    fmp_stage_tidx FEMPTY NONE lbl bb.bb_instructions n = n` by
    (Induct >- simp[fmp_stage_tidx_def] >> rpt strip_tac >>
     `n <= LENGTH bb.bb_instructions /\ n < LENGTH bb.bb_instructions` by fs[] >>
     `fmp_stage_tidx FEMPTY NONE lbl bb.bb_instructions n = n` by metis_tac[] >>
     `((EL n bb.bb_instructions).inst_opcode <> DALLOCA)` by metis_tac[] >>
     gvs[fmp_stage_tidx_def, GENLIST, SUM_SNOC]) >>
  `fmp_stage_tidx FEMPTY NONE lbl bb.bb_instructions idx = idx /\
   fmp_stage_tidx FEMPTY NONE lbl bb.bb_instructions (SUC idx) = SUC idx` by fs[] >>
  `i = idx` by (Cases_on `idx = 0` >> gvs[]) >>
  qexists_tac `bb` >> fs[] >> metis_tac[]
QED
