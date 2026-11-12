(* INVOKE subsequences of the FMP lowering. *)
Theory fmpStageFmpStepsCallOrdinal
Ancestors
  fmpStageFmpStepsCallRoot fmpStageControl fmpLowerIndexedProps fmpLowerProps fmpWfProps
  fmpLowerDefs venomInst fmpStepLayout fmpStageRel finite_map
  list rich_list option callLayoutDefs passSharedProps arithmetic

Theorem fmp_emit_restores_no_invoke:
  !bases s code s'.
  fmp_emit_restores runner s bases = (code,s') ==>
  FILTER (\i. i.inst_opcode = INVOKE) code = []
Proof
  Induct >> simp[fmp_emit_restores_def] >> rpt gen_tac >>
  Cases_on `fresh_inst_id s` >>
  Cases_on `fmp_emit_restores runner r bases` >>
  simp[fmp_emit_restores_def, mk_inst_def] >> rpt strip_tac >>
  first_x_assum drule >> gvs[]
QED

Theorem fmp_lower_inst_invoke_count:
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') ==>
  LENGTH (FILTER (\i. i.inst_opcode = INVOKE) code) =
    if inst.inst_opcode = INVOKE then 1 else 0
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, is_raw_fmp_opcode_def] >>
  rpt (CASE_TAC >> gvs[mk_inst_def])
QED

Theorem fmp_lower_indexed_invoke_count:
  !insts k sp restores code leftover sp'.
  fmp_lower_indexed infos ctx runner lbl k sp restores insts =
    SOME (code,leftover,sp') ==>
  LENGTH (FILTER (\i. i.inst_opcode = INVOKE) code) =
  LENGTH (FILTER (\i. i.inst_opcode = INVOKE) insts)
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> simp[fmp_lower_indexed_cons] >> strip_tac >>
  drule fmp_emit_restores_no_invoke >> strip_tac >>
  drule fmp_lower_inst_invoke_count >> strip_tac >>
  first_x_assum drule >>
  simp[FILTER_APPEND] >> Cases_on `h.inst_opcode = INVOKE` >> simp[]
QED

Theorem fmp_lower_inst_invoke_filter:
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') /\
  inst.inst_opcode = INVOKE ==>
  ?callee info args.
    fmp_resolve_invoke infos ctx inst = SOME (callee,info,args) /\
    FILTER (\i. i.inst_opcode = INVOKE) code =
    [inst with <| inst_operands := Label callee.fn_name ::
          (args ++ if info.fi_needs_fmp then [Var runner] else []);
       inst_outputs := inst.inst_outputs ++
          if info.fi_publishes_fmp then [runner] else [] |>]
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem fmp_lower_indexed_invoke_at:
  !insts n k sp restores code leftover sp'.
  fmp_lower_indexed infos ctx runner lbl k sp restores insts =
    SOME (code,leftover,sp') /\ n < LENGTH insts /\
  (EL n insts).inst_opcode = INVOKE ==>
  ?sp0 head sp1.
    fmp_lower_inst infos ctx runner sp0 (EL n insts) = SOME (head,sp1) /\
    FILTER (\i. i.inst_opcode = INVOKE) head =
      [EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE n insts)))
          (FILTER (\i. i.inst_opcode = INVOKE) code)]
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[fmp_lower_indexed_cons] >> strip_tac >>
  drule fmp_emit_restores_no_invoke >> strip_tac >>
  Cases_on `n` >> gvs[]
  >- (drule_all fmp_lower_inst_invoke_filter >> strip_tac >>
      qexistsl [`s0`, `head`, `s1`] >> simp[FILTER_APPEND]) >>
  first_x_assum drule >> simp[] >> disch_then drule >> strip_tac >>
  drule fmp_lower_inst_invoke_count >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >>
  simp[FILTER_APPEND, TAKE_def] >>
  Cases_on `h.inst_opcode = INVOKE` >> gvs[] >>
  simp[EL_APPEND2]
QED

Theorem fmp_lower_blocks_invoke_indexed:
  !bbs sp restores out leftover sp'.
  fmp_lower_blocks infos ctx runner sp restores bbs =
    SOME (FmpBlocksResult out leftover sp') ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    ?sp0 rs ls sp1.
      fmp_lower_indexed infos ctx runner bb.bb_label 0 sp0 rs
        bb.bb_instructions = SOME (bb'.bb_instructions,ls,sp1)) bbs out
Proof
  Induct >> simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> conj_tac >- metis_tac[] >> first_x_assum irule >> metis_tac[]
QED

Theorem fmp_make_root_layout_no_invoke[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root newpc s') ==>
  FILTER (\i. i.inst_opcode = INVOKE) (OPTION_TO_LIST root) = [] /\
  FILTER (\i. i.inst_opcode = INVOKE) (OPTION_TO_LIST newpc) = [] /\
  FILTER (\i. i.inst_opcode = INVOKE) (OPTION_TO_LIST oldpc) = []
Proof
  strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def] >>
     metis_tac[split_fmp_entry_retpc_opcode]) >>
  gvs[fmp_make_root_layout_def, AllCaseEqs(), OPTION_TO_LIST_def,
      mk_inst_def, set_param_index_def] >>
  gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_install_root_invoke_filter:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 =
    SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions =
    FILTER (\i. i.inst_opcode = INVOKE) bb.bb_instructions) blocks out
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_no_invoke >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  simp[LIST_REL_EL_EQN, FILTER_APPEND] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[FILTER_APPEND]
QED

Theorem fmp_stage_lowered_invoke_blocks:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    ?code sp0 rs ls sp1.
      fmp_lower_indexed infos ctx runner bb.bb_label 0 sp0 rs
        bb.bb_instructions = SOME (code,ls,sp1) /\
      FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions =
      FILTER (\i. i.inst_opcode = INVOKE) code) fn.fn_blocks fn'.fn_blocks
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[] >> drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn =
      SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_root_invoke_filter >> strip_tac >>
  drule fmp_lower_blocks_invoke_indexed >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> qx_gen_tac `j` >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem call_ordinal_lookup_rel[local]:
  !bbs bbs'. LIST_REL R bbs bbs' /\
  (!b b'. R b b' ==> b'.bb_label = b.bb_label) /\
  lookup_block lbl bbs = SOME bb ==>
  ?bb'. lookup_block lbl bbs' = SOME bb' /\ R bb bb'
Proof
  Induct >> Cases_on `bbs'` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  `h.bb_label = h'.bb_label` by metis_tac[] >>
  Cases_on `h.bb_label = lbl` >> gvs[] >> metis_tac[lookup_block_def]
QED

Theorem fmp_stage_lowered_invoke_block:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ?bb' code sp0 rs ls sp1.
    lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_lower_indexed infos ctx runner bb.bb_label 0 sp0 rs
      bb.bb_instructions = SOME (code,ls,sp1) /\
    FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions =
    FILTER (\i. i.inst_opcode = INVOKE) code
Proof
  strip_tac >> drule fmp_stage_lowered_invoke_blocks >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule call_ordinal_lookup_rel >> simp[] >>
  disch_then drule >> strip_tac >> metis_tac[]
QED

Theorem fmp_stage_lowered_invoke_count:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) =
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE) bb.bb_instructions)
Proof
  strip_tac >>
  Cases_on `?info. FLOOKUP infos fn.fn_name = SOME info /\
                  (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (drule_all fmp_stage_lowered_invoke_block >> strip_tac >>
      drule fmp_lower_indexed_invoke_count >> strip_tac >> metis_tac[]) >>
  drule fmp_stage_unlowered >> simp[] >> strip_tac >> gvs[]
QED

Theorem call_ordinal_suffix_rank[local]:
  LENGTH (FILTER P ys) = LENGTH (FILTER P xs) /\
  LENGTH (FILTER P (DROP k ys)) = LENGTH (FILTER P (DROP n xs)) ==>
  LENGTH (FILTER P (TAKE k ys)) = LENGTH (FILTER P (TAKE n xs))
Proof
  strip_tac >>
  `FILTER P ys = FILTER P (TAKE k ys) ++ FILTER P (DROP k ys)` by
    metis_tac[TAKE_DROP, FILTER_APPEND] >>
  `FILTER P xs = FILTER P (TAKE n xs) ++ FILTER P (DROP n xs)` by
    metis_tac[TAKE_DROP, FILTER_APPEND] >>
  qpat_x_assum `LENGTH (FILTER P ys) = _` mp_tac >>
  asm_rewrite_tac[LENGTH_APPEND] >> decide_tac
QED

Theorem fmp_stage_tidx_invoke_rank:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  MEM bb fn.fn_blocks /\ idx <= LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb'. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
      (TAKE (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx)
        bb'.bb_instructions)) =
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions))
Proof
  strip_tac >> drule fmp_stage_tidx_code >>
  disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all fmp_stage_lowered_invoke_count >> strip_tac >> gvs[] >>
  irule call_ordinal_suffix_rank >>
  simp[] >> drule fmp_lower_indexed_invoke_count >> simp[]
QED

Theorem fmp_lower_indexed_restore_head:
  fmp_lower_indexed infos ctx runner lbl k sp restores (inst::insts) =
    SOME (code,leftover,sp') /\ MEM ((lbl,k),bvar) restores ==>
  ?h tail. code = h::tail /\ h.inst_opcode = ASSIGN
Proof
  simp[fmp_lower_indexed_cons] >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac >>
  `MEM bvar bases` by metis_tac[] >>
  Cases_on `bases` >> gvs[] >>
  gvs[fmp_emit_restores_def, AllCaseEqs(), mk_inst_def]
QED

Theorem fmp_stage_tidx_restore_head:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb' k. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    k = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx /\
    k < LENGTH bb'.bb_instructions /\
    (EL k bb'.bb_instructions).inst_opcode = ASSIGN
Proof
  strip_tac >> drule fmp_stage_tidx_code >>
  disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
  (impl_tac >- metis_tac[LESS_IMP_LESS_OR_EQ]) >> strip_tac >>
  `?bvar. MEM ((bb.bb_label,idx),bvar) restores` by
    (gvs[FLOOKUP_DEF] >> metis_tac[LESS_EQ_REFL]) >>
  `DROP idx bb.bb_instructions =
      EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all fmp_lower_indexed_restore_head >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  qmatch_goalsub_abbrev_tac `EL k bb'.bb_instructions` >>
  gvs[] >>
  `k < LENGTH bb'.bb_instructions` by
    (spose_not_then assume_tac >>
     `DROP k bb'.bb_instructions = []` by simp[DROP_EQ_NIL] >> gvs[]) >>
  `EL k bb'.bb_instructions = h` by metis_tac[DROP_CONS_EL, CONS_11] >>
  simp[]
QED

Theorem fmp_stage_restored_invoke_ordinal:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) /\
  lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
  j = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx +
      (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) /\
  j < LENGTH bb'.bb_instructions /\ (EL j bb'.bb_instructions).inst_opcode = INVOKE ==>
  EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
     (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) =
  EL j bb'.bb_instructions
Proof
  strip_tac >>
  drule fmp_stage_tidx_invoke_rank >>
  disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
  (impl_tac >- metis_tac[LESS_IMP_LESS_OR_EQ]) >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `TAKE k bb'.bb_instructions` >>
  `LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
      (TAKE (k + if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn)
                 then 1 else 0) bb'.bb_instructions)) =
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions))` by
    (Cases_on `(bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn)` >> simp[] >>
     drule fmp_stage_tidx_restore_head >>
     disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
     `LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE (SUC k) bb'.bb_instructions)) =
      LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE k bb'.bb_instructions))` by
       (irule filter_take_nop >> simp[]) >>
     gvs[ADD1]) >>
  drule filter_take_el >> disch_then (qspec_then `\i. i.inst_opcode = INVOKE` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem call_plan_keys[local]:
  !ps. MAP FST (FLAT (MAP (\p. case FLOOKUP plan p of
    NONE => [] | SOME v => [(p,v)]) ps)) = FILTER (\p. p IN FDOM plan) ps
Proof
  Induct >- simp[] >> gen_tac >>
  Cases_on `h IN FDOM plan` >> gvs[FLOOKUP_DEF]
QED

Theorem call_block_points_distinct[local]:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (FLAT (MAP (\bb.
      GENLIST (\k. (bb.bb_label,k)) (LENGTH bb.bb_instructions)) bbs))
Proof
  Induct >> simp[ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP, MEM_GENLIST] >> metis_tac[]
QED

Theorem fmp_plan_to_alist_distinct:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  ALL_DISTINCT (MAP FST (fmp_plan_to_alist fn plan))
Proof
  strip_tac >>
  `fmp_plan_to_alist fn plan = FLAT (MAP (\p. case FLOOKUP plan p of
    NONE => [] | SOME v => [(p,v)])
    (FLAT (MAP (\bb. GENLIST (\k. (bb.bb_label,k))
       (LENGTH bb.bb_instructions)) fn.fn_blocks)))` by
    simp[fmp_plan_to_alist_def, MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF, MAP_GENLIST] >>
  simp[call_plan_keys] >> irule FILTER_ALL_DISTINCT >>
  irule call_block_points_distinct >> simp[]
QED

Theorem fmp_emit_restores_length:
  !bases s code s'. fmp_emit_restores runner s bases = (code,s') ==>
    LENGTH code = LENGTH bases
Proof
  Induct >> simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem fmp_lower_inst_length:
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') ==>
  LENGTH code = if inst.inst_opcode = DALLOCA then 4 else 1
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem call_select_distinct[local]:
  !restores p bases later.
  ALL_DISTINCT (MAP FST restores) /\
  fmp_select_point_restores p restores = (bases,later) ==>
  ALL_DISTINCT (MAP FST later) /\
  LENGTH bases = if MEM p (MAP FST restores) then 1 else 0
Proof
  Induct >- simp[fmp_select_point_restores_def] >>
  Cases_on `h` >> rpt gen_tac >>
  Cases_on `fmp_select_point_restores p restores` >>
  simp[fmp_select_point_restores_def] >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac >>
  Cases_on `q = p` >>
  Cases_on `MEM p (MAP FST restores)` >> gvs[MEM_MAP] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[pairTheory.PAIR]
QED

Theorem call_offset_suc[local]:
  SUM (GENLIST (\j. (if (EL j (h::insts)).inst_opcode = DALLOCA then 4 else 1) +
    (if (lbl,j+k) IN FDOM plan then 1 else 0)) (SUC n)) =
  (if h.inst_opcode = DALLOCA then 4 else 1) +
  (if (lbl,k) IN FDOM plan then 1 else 0) +
  SUM (GENLIST (\j. (if (EL j insts).inst_opcode = DALLOCA then 4 else 1) +
    (if (lbl,j+SUC k) IN FDOM plan then 1 else 0)) n)
Proof
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  pure_rewrite_tac[combinTheory.o_DEF] >> BETA_TAC >>
  pure_rewrite_tac[ADD_CLAUSES, EL, HD, TL, SUM, ADD_ASSOC] >>
  REFL_TAC
QED

Theorem fmp_lower_indexed_invoke_location:
  !insts n k sp restores code leftover sp'.
  fmp_lower_indexed infos ctx runner lbl k sp restores insts =
    SOME (code,leftover,sp') /\ n < LENGTH insts /\
  (EL n insts).inst_opcode = INVOKE /\ ALL_DISTINCT (MAP FST restores) /\
  (!j. k <= j /\ j < k + LENGTH insts ==>
    (MEM (lbl,j) (MAP FST restores) <=> (lbl,j) IN FDOM (plan : fmp_reclaim_plan))) ==>
  ?sp0 head sp1 j.
    j = SUM (GENLIST (\i. (if (lbl,k+i) IN FDOM plan then 1 else 0) +
          (if (EL i insts).inst_opcode = DALLOCA then 4 else 1)) n) +
        (if (lbl,k+n) IN FDOM plan then 1 else 0) /\
    j < LENGTH code /\
    fmp_lower_inst infos ctx runner sp0 (EL n insts) = SOME (head,sp1) /\
    head = [EL j code]
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[fmp_lower_indexed_cons] >> strip_tac >>
  drule_all call_select_distinct >> strip_tac >>
  drule fmp_emit_restores_length >> strip_tac >>
  drule fmp_lower_inst_length >> strip_tac >>
  Cases_on `n` >> gvs[]
  >- (gvs[LENGTH_EQ_1] >> qexistsl [`s0`,`s1`] >>
      qpat_x_assum `LENGTH prefix = _` (mp_tac o GSYM) >>
      simp[EL_APPEND_EQN]) >>
  `!j. SUC k <= j /\ j < SUC k + LENGTH insts ==>
     (MEM (lbl,j) (MAP FST later) <=> (lbl,j) IN FDOM (plan : fmp_reclaim_plan))` by
    (drule fmp_select_point_restores_once >> strip_tac >>
     simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >>
     gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[LESS_EQ, LESS_EQ_TRANS]) >>
  first_x_assum drule >> disch_then (qspec_then `n'` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl [`sp0`,`sp1`] >> rewrite_tac[call_offset_suc] >>
  `k + SUC n' = SUC k + n'` by decide_tac >>
  asm_rewrite_tac[] >>
  qpat_abbrev_tac `(isum:num) = SUM _` >>
  qabbrev_tac `(extra:num) = if (lbl,SUC k + n') IN FDOM plan then 1 else 0` >>
  qpat_x_assum `LENGTH prefix = _` (assume_tac o GSYM) >>
  qpat_x_assum `LENGTH head = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >>
  simp[EL_APPEND_EQN]
QED

Theorem call_indexed_distinct[local]:
  !insts k sp restores code leftover sp'.
  fmp_lower_indexed infos ctx runner lbl k sp restores insts =
    SOME (code,leftover,sp') /\ ALL_DISTINCT (MAP FST restores) ==>
  ALL_DISTINCT (MAP FST leftover)
Proof
  Induct >- simp[fmp_lower_indexed_def] >> rpt gen_tac >>
  simp[fmp_lower_indexed_cons] >> strip_tac >>
  drule_all call_select_distinct >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem fmp_lower_blocks_indexed_plan:
  !bbs sp restores out leftover sp'.
  fmp_lower_blocks infos ctx runner sp restores bbs =
    SOME (FmpBlocksResult out leftover sp') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  ALL_DISTINCT (MAP FST restores) /\
  (!bb j. MEM bb bbs /\ j < LENGTH bb.bb_instructions ==>
    (MEM (bb.bb_label,j) (MAP FST restores) <=> (bb.bb_label,j) IN FDOM (plan : fmp_reclaim_plan))) ==>
  LIST_REL (\bb bb'. bb'.bb_label = bb.bb_label /\
    ?sp0 rs ls sp1.
      fmp_lower_indexed infos ctx runner bb.bb_label 0 sp0 rs
        bb.bb_instructions = SOME (bb'.bb_instructions,ls,sp1) /\
      ALL_DISTINCT (MAP FST rs) /\
      (!j. j < LENGTH bb.bb_instructions ==>
        (MEM (bb.bb_label,j) (MAP FST rs) <=> (bb.bb_label,j) IN FDOM (plan : fmp_reclaim_plan)))) bbs out
Proof
  Induct >- simp[fmp_lower_blocks_def] >> rpt gen_tac >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  conj_tac >- (qexistsl [`sp`,`restores`,`later`,`s2`] >> simp[]) >>
  first_x_assum irule >>
  qexistsl [`leftover`,`later`,`s2`,`sp'`] >> simp[] >>
  reverse conj_tac >- (irule call_indexed_distinct >> metis_tac[]) >>
  drule fmp_lower_indexed_leftover >> strip_tac >>
  rpt strip_tac >>
  `bb.bb_label <> h.bb_label` by (gvs[MEM_MAP] >> metis_tac[]) >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  first_x_assum (qspecl_then [`bb`,`j`] mp_tac) >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD]
QED

Theorem call_blocks_invoke_location[local]:
  fmp_lower_blocks infos ctx runner sp (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover sp') /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  ?cb sp0 head sp1 k.
    lookup_block bb.bb_label blocks = SOME cb /\
    k = SUM (GENLIST (\i. (if (bb.bb_label,i) IN FDOM plan then 1 else 0) +
          (if (EL i bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx) +
        (if (bb.bb_label,idx) IN FDOM plan then 1 else 0) /\
    k < LENGTH cb.bb_instructions /\
    fmp_lower_inst infos ctx runner sp0 (EL idx bb.bb_instructions) = SOME (head,sp1) /\
    head = [EL k cb.bb_instructions]
Proof
  strip_tac >> drule fmp_lower_blocks_indexed_plan >>
  disch_then (qspec_then `plan` mp_tac) >>
  (impl_tac >- (simp[fmp_plan_to_alist_distinct] >>
    rpt strip_tac >> simp[MEM_MAP, pairTheory.EXISTS_PROD, MEM_fmp_plan_to_alist,
      FLOOKUP_DEF, EXISTS_MEM] >> metis_tac[])) >> strip_tac >>
  drule call_ordinal_lookup_rel >> simp[] >> disch_then drule >> strip_tac >>
  drule fmp_lower_indexed_invoke_location >>
  disch_then (qspecl_then [`plan`,`idx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  qexistsl [`sp0'`,`sp1'`] >> simp[]
QED

Theorem call_root_offset[local]:
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner sp = SOME (FmpRootLayout n root pc sp') /\
  fn.fn_blocks = entry::rest /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ lbl = rl ==> rp <= idx) ==>
  (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0) =
    (case fmp_stage_root infos ctx fn of
       SOME (rl,rp) => if lbl = rl /\ rp <= idx then 1 else 0 | NONE => 0)
Proof
  strip_tac >> Cases_on `info.fi_needs_fmp` >>
  gvs[fmp_make_root_layout_def, fmp_stage_root_def, AllCaseEqs(),
      OPTION_TO_LIST_def] >>
  Cases_on `lbl = entry.bb_label` >> gvs[] >> metis_tac[]
QED

Theorem fmp_stage_restored_invoke_location:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ bb.bb_label = rl ==> rp <= idx) ==>
  ?bb' sp0 head sp1 j.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    j = fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
          bb.bb_label bb.bb_instructions idx +
        (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) /\
    j < LENGTH bb'.bb_instructions /\
    fmp_lower_inst infos ctx runner sp0 (EL idx bb.bb_instructions) = SOME (head,sp1) /\
    head = [EL j bb'.bb_instructions]
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[] >> drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule call_blocks_invoke_location >> disch_then (qspecl_then [`idx`,`bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  ` (EL k cb.bb_instructions).inst_opcode = INVOKE` by
    (gvs[fmp_lower_inst_def, AllCaseEqs()] >>
     qpat_x_assum `_ with <| inst_operands := _; inst_outputs := _ |> = _` (mp_tac o Q.AP_TERM `\i. i.inst_opcode`) >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (entry::rest))` by
    (drule fmp_lower_blocks_preserves_labels >> gvs[]) >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  drule_at (Pat `fmp_install_root _ _ _ _ = _`) fmp_install_root_invoke_location >>
  disch_then (qspecl_then [`tail`,`rest`,`oldpc`] mp_tac) >>
  simp[OPTION_TO_LIST_def] >>
  disch_then (qspecl_then [`bb.bb_label`,`k`,`cb`] mp_tac) >>
  (impl_tac >- (Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def])) >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule fmp_lower_blocks_preserves_labels >> strip_tac >>
  `entry'.bb_label = entry.bb_label` by gvs[] >>
  `(if bb.bb_label = entry'.bb_label then LENGTH (OPTION_TO_LIST o') else 0) =
    (case fmp_stage_root infos ctx fn of NONE => 0 |
     SOME (rl,rp) => if bb.bb_label = rl /\ rp <= idx then 1 else 0)` by
    (irule call_root_offset >> simp[] >> metis_tac[]) >>
  gvs[fmp_stage_plan_def, fmp_stage_tidx_def] >> metis_tac[ADD_ASSOC]
QED

Theorem fmp_stage_restored_invoke_at:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ bb.bb_label = rl ==> rp <= idx) ==>
  ?bb' sp0 head sp1 j.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    j = fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
          bb.bb_label bb.bb_instructions idx +
        (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) /\
    j < LENGTH bb'.bb_instructions /\
    fmp_lower_inst infos ctx runner sp0 (EL idx bb.bb_instructions) = SOME (head,sp1) /\
    head = [EL j bb'.bb_instructions] /\
    (EL j bb'.bb_instructions).inst_opcode = INVOKE /\
    EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
       (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = EL j bb'.bb_instructions
Proof
  strip_tac >> drule fmp_stage_restored_invoke_location >>
  disch_then (qspecl_then [`idx`,`bb`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `(EL j bb'.bb_instructions).inst_opcode = INVOKE` by
    (gvs[fmp_lower_inst_def, AllCaseEqs()] >>
     qpat_x_assum `_ with <| inst_operands := _; inst_outputs := _ |> = _`
       (mp_tac o Q.AP_TERM `\i. i.inst_opcode`) >> simp[]) >>
  `EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
     (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = EL j bb'.bb_instructions` by
    (irule fmp_stage_restored_invoke_ordinal >> simp[] >>
     qexistsl [`ctx`,`fn`,`fn'`,`infos`,`runner`] >> simp[] >> metis_tac[]) >>
  qexistsl [`bb'`,`sp0`,`head`,`sp1`,`j`] >> simp[]
QED
