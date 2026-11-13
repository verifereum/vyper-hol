(* Accepted destinations retain all their original call uses. *)
Theory readonlyInvokeCopyFwdExecutionCallSites
Ancestors
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdHistoryUses readonlyInvokeCopyFwdHistoryCopyUniqueness
  readonlyInvokeCopyFwdHistoryOperandOrigins readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdReadonlyPositions
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdDefs
  internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  venomInst venomWf o1PassContract mem2varProofs passSharedDefs
  list rich_list pred_set finite_map

Theorem ricf_call_block_nop_preserved[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !i. i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = NOP ==>
    i < LENGTH last.bb_instructions /\
    (EL i last.bb_instructions).inst_opcode = NOP
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >> simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  (impl_tac >-
    (drule ricf_event_prefix_and_copy >> strip_tac >>
     simp[ricf_event_opcode])) >> simp[]
QED

Theorem ricf_call_function_position[local]:
  ricf_function_edit original round /\
  b < LENGTH original.fn_blocks /\
  i < LENGTH (EL b original.fn_blocks).bb_instructions ==>
  b < LENGTH round.fn_blocks /\
  i < LENGTH (EL b round.fn_blocks).bb_instructions /\
  ricf_inst_edit (EL i (EL b original.fn_blocks).bb_instructions)
    (EL i (EL b round.fn_blocks).bb_instructions)
Proof
  simp[ricf_function_edit_def, ricf_block_edit_def, LIST_REL_EL_EQN] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ricf_call_sites_fold_complete[local]:
  !uses acc sites.
    FOLDL (\acc (v,inst,pos).
      case acc of NONE => NONE | SOME xs =>
        if icf_is_assign_output_use inst pos then SOME xs
        else if inst.inst_opcode = MCOPY /\ pos = 0 then
          if inst.inst_id = copy_id then SOME xs else NONE
        else if inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos
          then SOME ((inst,pos)::xs) else NONE) acc uses = SOME sites ==>
    (?xs. acc = SOME xs /\
      !ri p. MEM (ri,p) xs ==> MEM (ri,p) sites) /\
    (!v ri p. MEM (v,ri,p) uses /\ ri.inst_opcode = INVOKE ==>
      MEM (ri,p) sites)
Proof
  Induct >> pure_rewrite_tac[FOLDL]
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f next uses = SOME sites` >>
  qpat_x_assum `!acc sites. _` (qspecl_then [`next`,`sites`] mp_tac) >>
  simp[Abbr `f`] >> strip_tac >>
  Cases_on `acc` >>
  gvs[Abbr `next`, AllCaseEqs(), icf_is_assign_output_use_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM]
QED

Theorem ricf_call_event_site_complete:
  ricf_event_ok e current /\
  (ricf_event_copy e current).inst_operands = [Var dst;src;sz] /\
  MEM (v,ri,p)
    (icf_alias_use_positions e.rfe_ctx.icf_dfg
      (icf_collect_aliases e.rfe_ctx.icf_dfg
        (icf_assign_root e.rfe_ctx.icf_dfg {} dst))) /\
  ri.inst_opcode = INVOKE ==>
  MEM (ri,p) e.rfe_sites
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def, ricf_event_copy_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule (INST_TYPE [alpha |-> ``:string``] ricf_call_sites_fold_complete) >>
  simp[] >> metis_tac[]
QED

Theorem ricf_call_block_event_erased[local]:
  ricf_block_trace bb (prefix ++ e::suffix) last /\
  ricf_block_trace bb prefix current ==>
  e.rfe_index < LENGTH last.bb_instructions /\
  (EL e.rfe_index last.bb_instructions).inst_opcode = NOP
Proof
  strip_tac >>
  `ricf_block_trace current (e::suffix) last` by
    metis_tac[ricf_block_trace_split, ricf_block_trace_deterministic] >>
  qpat_x_assum `ricf_block_trace current (e::suffix) last` mp_tac >>
  simp[Once ricf_block_trace_cases] >> strip_tac >>
  irule ricf_call_block_nop_preserved >>
  goal_assum (drule_at Any) >>
  drule ricf_event_copy_shape >> strip_tac >>
  drule ricf_event_prefix_and_copy >> strip_tac >>
  simp[mk_nop_inst_def]
QED

Theorem ricf_call_logged_member_suffix[local]:
  !base fn log last. ricf_logged_function_trace base fn log last ==>
  ricf_function_trace base fn last /\
  (!round logs mid. MEM (round,logs,mid) log ==>
    ricf_function_trace base mid last)
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >> simp[ricf_function_trace_nil] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[ricf_function_trace_cons, ricf_logged_round_erases]
QED

Theorem ricf_call_located_event_erased_at_end:
  !ctx0 original log last round b es prefix e current.
  ricf_logged_function_trace ctx0 original log last /\
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  b < LENGTH last.fn_blocks /\
  e.rfe_index < LENGTH (EL b last.fn_blocks).bb_instructions /\
  (EL e.rfe_index (EL b last.fn_blocks).bb_instructions).inst_opcode = NOP
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ricf_located_event _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ricf_located_event_def]) >>
  `ricf_function_trace ctx0 original round /\
   ricf_logged_round ctx0 round logs mid` by
    metis_tac[ricf_logged_function_trace_member] >>
  `ricf_function_trace ctx0 mid last` by
    metis_tac[ricf_call_logged_member_suffix] >>
  `ricf_function_edit original round` by
    metis_tac[ricf_function_trace_edit] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts round))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_function_trace ctx0 round mid` by
    metis_tac[ricf_logged_round_erases, ricf_function_trace_cons,
      ricf_function_trace_nil] >>
  `ricf_function_edit round mid` by
    metis_tac[ricf_function_trace_edit] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts mid))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_function_edit mid last` by
    metis_tac[ricf_function_trace_edit] >>
  `ricf_block_trace (EL b round.fn_blocks) es (EL b mid.fn_blocks)` by
    metis_tac[ricf_logged_round_block] >>
  `e.rfe_index < LENGTH (EL b mid.fn_blocks).bb_instructions /\
   (EL e.rfe_index (EL b mid.fn_blocks).bb_instructions).inst_opcode = NOP` by
    (irule ricf_call_block_event_erased >> metis_tac[]) >>
  `b < LENGTH mid.fn_blocks /\ b < LENGTH last.fn_blocks /\
   ricf_block_edit (EL b mid.fn_blocks) (EL b last.fn_blocks)` by
    (fs[ricf_function_edit_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule_all ricf_block_edit_EL >> strip_tac >> simp[] >>
  fs[ricf_inst_edit_def] >> metis_tac[]
QED

(* A selected copy is still the original MCOPY in its recorded round. *)
Theorem ricf_call_located_copy_round[local]:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  b < LENGTH original.fn_blocks /\
  e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
  e.rfe_index < LENGTH (EL b round.fn_blocks).bb_instructions /\
  ricf_event_copy e (EL b round.fn_blocks) =
    ricf_event_copy e (EL b original.fn_blocks) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   ricf_inst_edit (ricf_event_copy e (EL b original.fn_blocks))
     (ricf_event_copy e current)` by
    (gvs[ricf_block_edit_def, LIST_REL_EL_EQN, ricf_event_copy_def] >>
     metis_tac[]) >>
  `ricf_function_edit original round` by
    metis_tac[ricf_function_trace_edit] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts round))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_block_edit (EL b round.fn_blocks) current` by
    (irule ricf_block_trace_edit >>
     qexistsl_tac [`EL b round.fn_blocks`,
       `ctx0 with icf_dfg := dfg_build_function round`,`prefix`] >>
     simp[EL_MEM] >> qexists_tac `round` >> simp[] >> metis_tac[EL_MEM]) >>
  `ricf_inst_edit (ricf_event_copy e (EL b round.fn_blocks))
    (ricf_event_copy e current)` by
    (gvs[ricf_block_edit_def, LIST_REL_EL_EQN, ricf_event_copy_def] >>
     metis_tac[]) >>
  drule_all ricf_call_function_position >> strip_tac >>
  gvs[ricf_event_copy_def, ricf_inst_edit_def] >> metis_tac[]
QED

Theorem ricf_call_earlier_destination_distinct[local]:
  ricf_logged_function_trace ctx0 original pre round /\
  ricf_located_event ctx0 original log round b es prefix e current /\
  ricf_located_event ctx0 original pre earlier cb fs before f prior /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  (ricf_event_copy f (EL cb original.fn_blocks)).inst_operands = [Var fdst;fsrc;fsz] ==>
  icf_assign_root (dfg_build_function original) {} dst <>
    icf_assign_root (dfg_build_function original) {} fdst
Proof
  strip_tac >> strip_tac >>
  qpat_assum `ricf_located_event ctx0 original log round b es prefix e current`
    (mp_then Any mp_tac ricf_call_located_copy_round) >>
  simp[] >> strip_tac >>
  `ircf_alias original
    (icf_assign_root (dfg_build_function original) {} fdst) dst` by
    metis_tac[ircf_assign_root_alias] >>
  `b < LENGTH original.fn_blocks /\
   e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY` by
    metis_tac[ricf_call_located_copy_round] >>
  `(ricf_event_copy e (EL b original.fn_blocks)).inst_id =
   (ricf_event_copy f (EL cb original.fn_blocks)).inst_id` by
    (qspecl_then [`ctx0`,`original`,`pre`,`earlier`,`cb`,`fs`,`before`,`f`,`prior`,
       `fdst`,`fsrc`,`fsz`,`b`,`e.rfe_index`,
       `ricf_event_copy e (EL b original.fn_blocks)`,`dst`]
       mp_tac ricf_located_event_destination_unique >>
     simp[GSYM ricf_event_copy_def]) >>
  `cb < LENGTH round.fn_blocks /\
   f.rfe_index < LENGTH (EL cb round.fn_blocks).bb_instructions /\
   (ricf_event_copy f (EL cb round.fn_blocks)).inst_opcode = NOP` by
    (drule_all ricf_call_located_event_erased_at_end >>
     simp[ricf_event_copy_def]) >>
  `cb < LENGTH original.fn_blocks /\
   f.rfe_index < LENGTH (EL cb original.fn_blocks).bb_instructions` by
    metis_tac[ricf_call_located_copy_round] >>
  `ricf_function_edit original round` by
    metis_tac[ricf_logged_function_trace_erases, ricf_function_trace_edit] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts round))` by
    metis_tac[ricf_function_edit_ids] >>
  `ricf_inst_edit (ricf_event_copy f (EL cb original.fn_blocks))
    (ricf_event_copy f (EL cb round.fn_blocks))` by
    (fs[ricf_event_copy_def] >> metis_tac[ricf_call_function_position]) >>
  `b < LENGTH round.fn_blocks /\
   e.rfe_index < LENGTH (EL b round.fn_blocks).bb_instructions` by
    metis_tac[ricf_call_function_position] >>
  `MEM (ricf_event_copy e (EL b round.fn_blocks)) (fn_insts round) /\
   MEM (ricf_event_copy f (EL cb round.fn_blocks)) (fn_insts round)` by
    (pure_rewrite_tac[fn_insts_def, fn_insts_blocks_MEM, ricf_event_copy_def] >>
     metis_tac[EL_MEM]) >>
  `ricf_event_copy e (EL b round.fn_blocks) =
   ricf_event_copy f (EL cb round.fn_blocks)` by
    (irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
     conj_tac >- fs[ricf_inst_edit_def] >>
     qexists_tac `fn_insts round` >> simp[]) >>
  gvs[]
QED

Theorem ricf_call_position_member[local]:
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions ==>
  MEM (EL i (EL b fn.fn_blocks).bb_instructions) (fn_insts fn)
Proof
  simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]
QED

Theorem ricf_call_site_id_original_alias[local]:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_full_alloca_copies original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  MEM old (fn_insts original) /\
  EL p old.inst_operands = Var v /\
  MEM (old.inst_id,p) (MAP (\(ri,p). (ri.inst_id,p)) e.rfe_sites) ==>
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v
Proof
  strip_tac >>
  `?ri. MEM (ri,p) e.rfe_sites /\ ri.inst_id = old.inst_id` by
    (fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  drule_all ricf_call_recorded_site_original_operand >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  `ricf_function_edit original round` by
    metis_tac[ricf_function_trace_edit] >>
  `ricf_inst_edit (EL i (EL cb original.fn_blocks).bb_instructions) ri` by
    metis_tac[ricf_call_function_position] >>
  `MEM (EL i (EL cb original.fn_blocks).bb_instructions) (fn_insts original)` by
    metis_tac[ricf_call_position_member] >>
  `EL i (EL cb original.fn_blocks).bb_instructions = old` by
    (irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
     conj_tac >- fs[ricf_inst_edit_def] >>
     qexists_tac `fn_insts original` >> simp[]) >>
  gvs[]
QED

(* Earlier rewrites cannot consume an original alias of a copy which is
   still accepted in this round: uniqueness would make them the same copy. *)
Theorem ricf_call_original_alias_round_operand:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_full_alloca_copies original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  p < LENGTH (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands /\
  EL p (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v ==>
  EL p (EL i (EL cb round.fn_blocks).bb_instructions).inst_operands = Var v
Proof
  strip_tac >>
  `?pre. ricf_logged_function_trace ctx0 original pre round` by
    (fs[ricf_located_event_def] >>
     drule_all ricf_logged_function_trace_prefix >> metis_tac[]) >>
  qpat_assum `ricf_logged_function_trace ctx0 original pre round`
    (mp_then Any (qspecl_then [`cb`,`i`,`p`] mp_tac)
      ricf_logged_function_operand_origin) >>
  simp[] >> strip_tac >> simp[] >>
  rename1 `ricf_located_event ctx0 original pre earlier cb fs before f prior` >>
  `?fdst fsrc fsz.
    (ricf_event_copy f (EL cb original.fn_blocks)).inst_operands =
      [Var fdst;fsrc;fsz]` by
    metis_tac[ricf_located_event_source_descriptor] >>
  `ircf_alias original
    (icf_assign_root (dfg_build_function original) {} fdst) v` by
    (irule ricf_call_site_id_original_alias >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[ricf_call_position_member]) >>
  `?amount. ircf_alloca_of original
    (icf_assign_root (dfg_build_function original) {} dst) amount` by
    metis_tac[ricf_located_event_destination_alloca_of] >>
  `?amount'. ircf_alloca_of original
    (icf_assign_root (dfg_build_function original) {} fdst) amount'` by
    metis_tac[ricf_located_event_destination_alloca_of] >>
  `icf_assign_root (dfg_build_function original) {} dst =
    icf_assign_root (dfg_build_function original) {} fdst` by
    (irule ircf_alloca_aliases_separate >> metis_tac[]) >>
  metis_tac[ricf_call_earlier_destination_distinct]
QED

Theorem ricf_call_readonly_position[local]:
  ricf_readonly_function_edit rma original round /\
  b < LENGTH original.fn_blocks /\
  i < LENGTH (EL b original.fn_blocks).bb_instructions /\
  (EL i (EL b original.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
  b < LENGTH round.fn_blocks /\
  i < LENGTH (EL b round.fn_blocks).bb_instructions /\
  (EL i (EL b round.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  LENGTH (EL i (EL b round.fn_blocks).bb_instructions).inst_operands =
    LENGTH (EL i (EL b original.fn_blocks).bb_instructions).inst_operands
Proof
  simp[ricf_readonly_function_edit_def, ricf_readonly_block_edit_def,
    LIST_REL_EL_EQN] >> strip_tac >>
  qpat_x_assum `!n. _` (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!n. _` (qspec_then `i` mp_tac) >>
  simp[ricf_readonly_inst_edit_def, ricf_inst_edit_def]
QED

Theorem ricf_call_original_alias_selected_site:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_full_alloca_copies original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  p < LENGTH (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands /\
  EL p (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v ==>
  MEM (EL i (EL cb round.fn_blocks).bb_instructions,p) e.rfe_sites
Proof
  strip_tac >>
  drule_all ricf_call_original_alias_round_operand >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  `ricf_function_edit original round /\
   ricf_readonly_function_edit ctx0.icf_rma original round` by
    metis_tac[ricf_function_trace_edit, ricf_function_trace_readonly_edit] >>
  drule_all ricf_call_readonly_position >> strip_tac >> gvs[] >>
  `ircf_alias round (icf_assign_root (dfg_build_function round) {} dst) v` by
    (fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]) >>
  `MEM (v,EL i (EL cb round.fn_blocks).bb_instructions,p)
    (icf_alias_use_positions (dfg_build_function round)
      (icf_collect_aliases (dfg_build_function round)
        (icf_assign_root (dfg_build_function round) {} dst)))` by
    (pure_rewrite_tac[ircf_alias_use_positions_mem] >>
     metis_tac[ricf_call_position_member]) >>
  irule ricf_call_event_site_complete >>
  simp[] >> qexistsl_tac [`current`,`dst`,`src`,`sz`,`v`] >> simp[]
QED
