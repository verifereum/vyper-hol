(*
 * The control side of FmpLowering's stage simulation: where a source
 * instruction sits in the lowered block, how the control map moves over
 * one instruction.
 *
 * TOP-LEVEL:
 *   fmp_stage_tidx_code    - the lowered code from a source index on
 *   fmp_stage_unlowered    - an unrewritten function keeps its blocks
 *   fmp_stage_tidx_suc     - the control map over one kept instruction
 *   fmp_stage_plan_point   - a planned restore sits at a reclaim point
 *   fmp_stage_kept_inst    - a kept instruction's place in the target
 *   fmp_stage_root_crossing - the source step reaching the root
 *)
Theory fmpStageControl
Ancestors
  fmpStageRel o1PassContract fmpLowerDefs fmpReclaimDefs fmpWfDefs venomInst
  finite_map list rich_list fmpStepLayout fmpLowerProps
  fmpStageControlWalk fmpStageControlLayout

Theorem fmp_control_sum_lower[local]:
  !n f. (!j. j < n ==> 1 <= f j) ==> n <= SUM (GENLIST f n)
Proof
  Induct >> simp[GENLIST, SUM_SNOC] >> rpt strip_tac >>
  `n <= SUM (GENLIST f n)` by (first_x_assum irule >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* Why: the step proofs read the target's code at the control map's index
   off the lowering's own walk; a point's restores come first, then its
   expansion. *)
Theorem fmp_stage_tidx_code:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx <= LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb' restores sp code leftover sp'.
    lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    (!j b. MEM ((bb.bb_label,j),b) restores <=>
           idx <= j /\
           FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,j) = SOME b) /\
    fmp_lower_indexed infos ctx runner bb.bb_label idx sp restores
      (DROP idx bb.bb_instructions) = SOME (code,leftover,sp') /\
    DROP (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
            (fmp_stage_root infos ctx fn) bb.bb_label
            bb.bb_instructions idx)
         bb'.bb_instructions = code /\
    MEM runner sp.irs_used_vars /\
    list_subset (fn_ir_vars fn) sp.irs_used_vars /\
    ALL_DISTINCT (MAP FST restores)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `?info. _` (qx_choose_then `info` (CONJUNCTS_THEN assume_tac)) >>
  drule fmp_control_rewrite >> simp[] >> strip_tac >>
  drule_all fmp_control_checked_walk >> strip_tac >>
  drule fmp_control_walk_suffix >> simp[] >>
  disch_then (qspecl_then [`fmp_stage_plan infos ctx fn`, `idx`] mp_tac) >>
  simp[] >> strip_tac >>
  `MEM runner sn.irs_used_vars /\ list_subset (fn_ir_vars fn) sn.irs_used_vars` by
    (simp[venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule_all fmp_control_root_layout >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  drule fmp_lower_blocks_preserves_labels >> simp[] >> strip_tac >>
  qpat_x_assum `blocks = _` SUBST_ALL_TAC >>
  reverse (Cases_on `bb.bb_label = entry.bb_label`)
  >- (`lookup_block bb.bb_label fn'.fn_blocks = SOME (bb with bb_instructions := code)` by
        (drule fmp_control_install_other >> simp[] >> metis_tac[]) >>
      qexistsl [`bb with bb_instructions := code`, `rsn`, `sn`, `left0`, `s1'`] >>
      Cases_on `info.fi_needs_fmp` >>
      simp[fmp_stage_tidx_def, arithmeticTheory.ADD_COMM]) >>
  `lookup_block bb.bb_label (entry'::rest') = SOME entry'` by
    gvs[lookup_block_def, FIND_thm] >>
  `code = entry'.bb_instructions` by gvs[basic_block_accfupds] >>
  Cases_on `root = NONE`
  >- (`newpc = oldpc` by metis_tac[] >>
      qpat_x_assum `fmp_install_root _ _ _ _ = _` mp_tac >>
      simp[] >> strip_tac >>
      drule_at Any fmp_control_install_no_root >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
      strip_tac >>
      `fn'.fn_blocks = entry'::rest'` by
        (first_x_assum (qspec_then `tail` mp_tac) >>
         Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
      `~info.fi_needs_fmp` by metis_tac[] >>
      qexistsl [`entry'`, `rsn`, `sn`, `left0`, `s1'`] >>
      simp[fmp_stage_tidx_def, arithmeticTheory.ADD_COMM, lookup_block_def, FIND_thm] >>
      metis_tac[]) >>
  `info.fi_needs_fmp` by metis_tac[] >>
  `LENGTH users + LENGTH (OPTION_TO_LIST oldpc) <= idx` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `DROP m code` >>
  `idx <= m` by
    (simp[Abbr `m`] >> irule fmp_control_sum_lower >>
     rpt strip_tac >> Cases_on `(EL j bb.bb_instructions).inst_opcode = DALLOCA` >>
     Cases_on `(entry.bb_label,j) IN FDOM (fmp_stage_plan infos ctx fn)` >> simp[]) >>
  drule_at (Pat `fmp_install_root _ _ _ _ = _`) fmp_control_install_suffix >>
  disch_then (qspecl_then [`tail`, `oldpc`, `m`] mp_tac) >>
  simp[] >>
  (impl_tac >- (Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def])) >>
  strip_tac >>
  qexistsl [`entry''`, `rsn`, `sn`, `left0`, `s1'`] >>
  simp[fmp_stage_tidx_def, lookup_block_def, FIND_thm] >>
  Cases_on `root` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

(* Why: the other branches of the lowering keep the blocks (a sealed
   function, or one that neither takes nor publishes the FMP, whose plan
   must be empty); there the control map is the identity. *)
Theorem fmp_stage_unlowered:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
           (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  fn'.fn_blocks = fn.fn_blocks /\
  fmp_stage_plan infos ctx fn = FEMPTY /\ fmp_stage_root infos ctx fn = NONE
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs(), fmp_stage_plan_def,
      fmp_stage_root_def, analyze_fmp_reclaims_def, fmp_checked_seal_def,
      fmp_seal_def] >>
  gvs[]
QED

(* Why: past a point with no restore and a one-instruction expansion, the
   next point is one further on, unless the root comes in between. *)
Theorem fmp_stage_tidx_suc:
  ~((lbl,idx) IN FDOM plan) /\ (EL idx insts).inst_opcode <> DALLOCA /\
  (!rl rp. root = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC idx) ==>
  fmp_stage_tidx plan root lbl insts (SUC idx) =
    SUC (fmp_stage_tidx plan root lbl insts idx)
Proof
  strip_tac >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  Cases_on `root` >> simp[] >> rename1 `SOME x` >> PairCases_on `x` >>
  simp[] >> rw[] >> fs[]
QED

(* Why: a restore is planned only where fmp_reclaim_step pops, and it pops
   only at a reclaim point. *)
Theorem fmp_stage_plan_point:
  (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  idx < LENGTH bb.bb_instructions /\
  fmp_is_reclaim_point infos (EL idx bb.bb_instructions)
Proof
  simp[fmp_stage_plan_def] >> CASE_TAC >> simp[] >> strip_tac >>
  rename1 `analyze_fmp_reclaims infos ctx fn = SOME plan` >>
  `fmp_reclaim_entry_ok infos ctx fn (lbl,idx) (plan ' (lbl,idx))` by
    gvs[analyze_fmp_reclaims_def, AllCaseEqs(), fmp_reclaim_plan_ok_def,
        FLOOKUP_DEF] >>
  pop_assum mp_tac >> simp[fmp_reclaim_entry_ok_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >> strip_tac >>
  spose_not_then assume_tac >>
  gvs[fmp_reclaim_step_def, fmp_pop_at_def, fmp_pop_target_def]
QED

Theorem fmp_control_width_one:
  (!j. j < n ==> ~((lbl,j) IN FDOM plan) /\
    (EL j xs).inst_opcode <> DALLOCA) ==>
  SUM (GENLIST (\j. (if (lbl,j) IN FDOM plan then 1 else 0) +
    (if (EL j xs).inst_opcode = DALLOCA then 4 else 1)) n) = n
Proof
  Induct_on `n` >> simp[GENLIST, SUM_SNOC] >>
  rpt strip_tac >>
  `SUM (GENLIST (\j. (if (lbl,j) IN FDOM plan then 1 else 0) +
    (if (EL j xs).inst_opcode = DALLOCA then 4 else 1)) n) = n` by
    (first_x_assum irule >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  gvs[]
QED

Theorem fmp_control_unlowered_no_raw:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  no_raw_fmp_ops fn
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  irule fmp_no_need_input_no_raw >> metis_tac[]
QED

Theorem fmp_control_kept_prefix:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info /\
  (info.fi_needs_fmp \/ info.fi_publishes_fmp) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_stage_root infos ctx fn = SOME (lbl,rp) /\ idx < rp /\
  (EL idx bb.bb_instructions).inst_opcode <> RETPC_PARAM ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    idx < LENGTH bb'.bb_instructions /\
    EL idx bb'.bb_instructions = EL idx bb.bb_instructions /\
    (!j. j <= idx ==> ~((lbl,j) IN FDOM (fmp_stage_plan infos ctx fn)) /\
      (EL j bb.bb_instructions).inst_opcode <> DALLOCA)
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all fmp_control_rewrite >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule_all fmp_control_root_layout >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  drule fmp_lower_blocks_preserves_labels >> simp[] >> strip_tac >>
  `root <> NONE` by gvs[] >>
  `lbl = entry.bb_label /\ rp = LENGTH users + LENGTH (OPTION_TO_LIST oldpc)` by
    gvs[] >>
  `bb = entry` by gvs[lookup_block_def, FIND_thm] >>
  `idx < LENGTH users` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     drule split_fmp_entry_retpc_opcode >> strip_tac >>
     Cases_on `idx < LENGTH users` >> gvs[EL_APPEND_EQN] >>
     `idx = LENGTH users` by decide_tac >> gvs[]) >>
  `!j. j < LENGTH users + LENGTH (OPTION_TO_LIST oldpc) ==>
    FLOOKUP plan (entry.bb_label,j) = NONE` by
    metis_tac[fmp_control_prefix_plan_absent] >>
  drule split_fmp_entry_users >> strip_tac >>
  qpat_x_assum `blocks = _` SUBST_ALL_TAC >>
  `entry'.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmp_control_install_users >> strip_tac >>
  qexists_tac `entry''` >>
  simp[lookup_block_def, FIND_thm, EL_APPEND1] >>
  rpt strip_tac >>
  `j < LENGTH users` by decide_tac >>
  `FLOOKUP plan (entry.bb_label,j) = NONE` by simp[] >>
  gvs[flookup_thm, EL_APPEND1] >>
  fs[EVERY_EL] >> first_x_assum drule >> simp[is_param_opcode_def] >> gvs[]
QED

Theorem fmp_control_kept_suffix[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx < LENGTH bb.bb_instructions /\
  ~MEM (EL idx bb.bb_instructions).inst_opcode
    [DALLOCA; DRET; GETFMP; SETFMP; RETFMP; INVOKE] /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb'. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions idx +
      (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      bb.bb_label bb.bb_instructions idx +
      (if (bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = EL idx bb.bb_instructions
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `idx <= LENGTH bb.bb_instructions` by decide_tac >>
  drule_all fmp_stage_tidx_code >> strip_tac >>
  `DROP idx bb.bb_instructions =
    EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  qpat_x_assum `DROP idx bb.bb_instructions = _` SUBST_ALL_TAC >>
  drule_all fmp_control_walk_kept_head >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  qpat_x_assum `DROP _ bb'.bb_instructions = code` (SUBST_ALL_TAC o GSYM) >>
  qmatch_asmsub_abbrev_tac `offset < LENGTH (DROP pos bb'.bb_instructions)` >>
  `offset + pos < LENGTH bb'.bb_instructions` by fs[LENGTH_DROP] >>
  fs[EL_DROP] >> simp[arithmeticTheory.ADD_COMM]
QED

(* Why: an instruction the lowering keeps as itself (every opcode but
   DALLOCA, INVOKE and RETPC_PARAM, which it rewrites, and the raw FMP
   ones, which row 3 has none of) sits in the target block at the control
   map's index, past its point's restore if it has one.  Before the root
   the target's prefix is the source's user parameters. *)
Theorem fmp_stage_kept_inst:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ inst = EL idx bb.bb_instructions /\
  ~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM] /\
  pre_fmp_opcode inst.inst_opcode ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
        (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
       bb'.bb_instructions = inst
Proof
  rpt strip_tac >> gvs[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (Cases_on `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
        bb.bb_label = rl ==> rp <= idx`
      >- (drule fmp_control_kept_suffix >>
          simp[pre_fmp_opcode_def] >>
          disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
          gvs[pre_fmp_opcode_def]) >>
      gvs[NOT_FORALL_THM] >>
      `idx < rp` by decide_tac >>
      drule fmp_control_kept_prefix >>
      disch_then (qspec_then `rp` mp_tac) >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `idx` mp_tac) >>
      simp[] >> disch_then (qx_choose_then `target` strip_assume_tac) >>
      qexists_tac `target` >>
      `SUM (GENLIST (\j. (if (bb.bb_label,j) IN FDOM (fmp_stage_plan infos ctx fn)
          then 1 else 0) +
        (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx)
        = idx` by
        (irule fmp_control_width_one >> rpt strip_tac >>
         `j <= idx` by decide_tac >>
         qpat_x_assum `!j. j <= idx ==> _` drule >> simp[]) >>
      `~((bb.bb_label,idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
        (qpat_x_assum `!j. j <= idx ==> _` (qspec_then `idx` mp_tac) >> simp[]) >>
      simp[fmp_stage_tidx_def]) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  drule_all fmp_control_unlowered_no_raw >> strip_tac >>
  `!j. j < idx ==> (EL j bb.bb_instructions).inst_opcode <> DALLOCA` by
    (rpt strip_tac >>
     gvs[no_raw_fmp_ops_def, fn_insts_def, fn_insts_blocks_def,
         MEM_FLAT, MEM_MAP, is_raw_fmp_opcode_def] >>
     `j < LENGTH bb.bb_instructions` by decide_tac >>
     `MEM (EL j bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
       (irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
        qexists_tac `bb` >> simp[EL_MEM]) >>
     first_x_assum drule >> simp[is_raw_fmp_opcode_def]) >>
  qexists_tac `bb` >> simp[fmp_stage_tidx_def] >>
  `SUM (GENLIST (\j. (if (lbl,j) IN FDOM (FEMPTY:fmp_reclaim_plan) then 1 else 0) +
    (if (EL j bb.bb_instructions).inst_opcode = DALLOCA then 4 else 1)) idx) = idx` by
    (irule fmp_control_width_one >> simp[]) >>
  gvs[]
QED

(* Why: the root counts from rp on, so the source step that reaches rp
   runs it too.  Outside the context entry that step is RETPC_PARAM (the
   lowering puts the root right before it); in a context entry with no
   parameters there is no such step. *)
Theorem fmp_stage_root_crossing:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  SUC idx = rp /\ idx < LENGTH bb.bb_instructions /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  (EL idx bb.bb_instructions).inst_opcode = RETPC_PARAM
Proof
  simp[fmp_stage_root_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[]
  >- (drule split_fmp_entry_reconstruct >> strip_tac >>
      drule split_fmp_entry_users >> strip_tac >>
      Cases_on `retpc` >>
      gvs[entry_fn_no_params_def, fn_insts_def, fn_insts_blocks_def,
          EVERY_APPEND, callLayoutDefsTheory.OPTION_TO_LIST_def] >>
      Cases_on `users` >> gvs[is_param_opcode_def] >>
      imp_res_tac split_fmp_entry_retpc_opcode >>
      gvs[is_param_opcode_def]) >>
  gvs[lookup_block_def, FIND_def, INDEX_FIND_def] >>
  `retpc <> NONE` by
    (gvs[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
         fmp_make_root_layout_def, AllCaseEqs()] >>
     Cases_on `retpc` >> gvs[]) >>
  Cases_on `retpc` >> gvs[] >>
  drule split_fmp_entry_retpc_opcode >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, EL_APPEND_EQN]
QED
