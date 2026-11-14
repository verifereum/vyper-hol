(* A source position can be selected only once in a chronological log. *)
Theory readonlyInvokeCopyFwdHistoryEventUniqueness
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs passSharedDefs venomInst list rich_list

Theorem ricf_block_trace_member_copy[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !e. MEM e es ==>
    e.rfe_index < LENGTH bb.bb_instructions /\
    (EL e.rfe_index bb.bb_instructions).inst_opcode = MCOPY
Proof
  ho_match_mp_tac ricf_block_trace_ind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `f` >>
  pure_rewrite_tac[MEM] >> strip_tac
  >- (drule ricf_event_copy_shape >>
      simp[ricf_event_copy_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  drule ricf_event_prefix_and_copy >> strip_tac >>
  fs[] >> drule ricf_event_opcode >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >>
  rw[] >> gvs[]
QED

Theorem ricf_block_trace_event_unique[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !e f. MEM e es /\ MEM f es /\ e.rfe_index = f.rfe_index ==> e = f
Proof
  ho_match_mp_tac ricf_block_trace_strongind >> simp[] >> rpt strip_tac >>
  `!f. MEM f es ==> f.rfe_index <> e.rfe_index` by
    (rpt strip_tac >> drule_all ricf_block_trace_member_copy >>
     drule ricf_event_prefix_and_copy >>
     simp[mk_nop_inst_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ricf_logged_function_block_trace:
  !base fn log last. ricf_logged_function_trace base fn log last ==>
  !b. b < LENGTH fn.fn_blocks ==>
    ricf_block_trace (EL b fn.fn_blocks)
      (FLAT (MAP (\(round,logs,mid). EL b logs) log))
      (EL b last.fn_blocks)
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >>
  simp[ricf_block_trace_nil] >> rpt strip_tac >>
  rename1 `ricf_logged_round base0 round logs mid` >>
  `LENGTH mid.fn_blocks = LENGTH round.fn_blocks` by
    fs[ricf_logged_round_def, LIST_REL_EL_EQN] >>
  drule_all ricf_logged_round_block >> strip_tac >>
  irule ricf_block_trace_append >> goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[]
QED

Theorem ricf_located_event_position_unique:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ricf_located_event ctx0 original log round' b es' prefix' f current' /\
  b < LENGTH original.fn_blocks /\ e.rfe_index = f.rfe_index ==>
  e = f
Proof
  simp[ricf_located_event_def] >> rpt strip_tac >>
  `MEM e (FLAT (MAP (\(round,logs,mid). EL b logs) log)) /\
   MEM f (FLAT (MAP (\(round,logs,mid). EL b logs) log))` by
    (simp[MEM_FLAT, MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[MEM_APPEND, MEM]) >>
  drule_all ricf_logged_function_block_trace >>
  metis_tac[ricf_block_trace_event_unique]
QED
