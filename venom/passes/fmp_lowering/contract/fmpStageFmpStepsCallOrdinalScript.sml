(*
 * INVOKE subsequences of FmpLowering's blocks: a source INVOKE's lowering
 * is the target block's INVOKE of the same rank, whichever witness of the
 * lowering reads it.
 *
 * TOP-LEVEL:
 *   fmp_stage_lowered_invoke_block    - a block's INVOKEs are its walk's
 *   fmp_lower_indexed_invoke_at       - a walk's INVOKE of a given rank
 *   fmp_stage_restored_invoke_ordinal - the control map keeps INVOKE ranks
 *   fmp_stage_restored_invoke_at      - a source INVOKE's target, by rank
 *)
Theory fmpStageFmpStepsCallOrdinal
Ancestors
  fmpStageFmpStepsInvokePosition fmpStageControl fmpLowerIndexedProps fmpLowerProps fmpWfProps
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

Theorem fmp_stage_restored_invoke_at:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb'.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions idx +
    (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
       (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) =
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
          bb.bb_label bb.bb_instructions idx +
        (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions
Proof
  strip_tac >>
  `~MEM (EL idx bb.bb_instructions).inst_opcode
     [PARAM; RETPC_PARAM; FMP_PARAM]` by gvs[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
     bb.bb_label = rl ==> rp <= idx` by
    metis_tac[fmp_stage_past_root] >>
  drule_all fmp_stage_invoke_at >> strip_tac >>
  `(EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        bb.bb_label bb.bb_instructions idx +
       (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
     bb'.bb_instructions).inst_opcode = INVOKE` by
    (imp_res_tac fmp_lower_invoke_inst >> gvs[]) >>
  qexists_tac `bb'` >> (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
  irule fmp_stage_restored_invoke_ordinal >> simp[] >> metis_tac[]
QED
