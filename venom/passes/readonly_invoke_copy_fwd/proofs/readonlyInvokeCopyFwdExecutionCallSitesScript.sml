(* Accepted destinations retain all their original call uses. *)
Theory readonlyInvokeCopyFwdExecutionCallSites
Ancestors
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdHistoryUses readonlyInvokeCopyFwdHistoryCopyUniqueness
  readonlyInvokeCopyFwdHistoryOperandOrigins readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdDefs
  internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  venomInst venomWf passSharedDefs list rich_list pred_set finite_map

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
