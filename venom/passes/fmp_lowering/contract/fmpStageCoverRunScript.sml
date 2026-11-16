(* Residual straight-line runs and revert-forward tails for FMP coverage. *)
Theory fmpStageCoverRun
Ancestors
  fmpStageCoverInv fmpStageRel fmpStageCoverMem fmpStageCoverBack lowerDloadPtrRawReachable
  runInstsProps instIdxIndep analysisSimDefs venomInstProps venomExecSemantics
  venomExecProps venomState venomInst ptrDiscipline contextCodegenRel list rich_list words

Theorem fmp_cov_run_step:
  ALL_DISTINCT (fn_labels fn') /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\ 0 < n /\
  (!k. fmp_target_run k C' name t n u) /\
  (!i. t.vs_inst_idx < i /\ i < t.vs_inst_idx + n ==>
    ~is_terminator (EL i bb'.bb_instructions).inst_opcode /\
    (EL i bb'.bb_instructions).inst_opcode <> INVOKE) ==>
  (!k. fmp_target_run k C' name
    (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n - 1) u)
Proof
  rpt strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >> fs[] >>
  qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `k` mp_tac) >>
  simp[fmp_target_run_def] >> strip_tac >> fs[] >>
  `ti = EL t.vs_inst_idx bb'.bb_instructions` by
    gvs[get_instruction_def] >>
  `DROP t.vs_inst_idx bb'.bb_instructions =
    ti :: DROP (SUC t.vs_inst_idx) bb'.bb_instructions` by
    (gvs[get_instruction_def] >>
     irule DROP_CONS_EL >> decide_tac) >>
  Cases_on `n` >> gvs[TAKE_def, run_insts_def, step_inst_non_invoke] >>
  rename1 `TAKE m (DROP (SUC t.vs_inst_idx) bb.bb_instructions)` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
     (TAKE m (DROP (SUC t.vs_inst_idx) bb.bb_instructions))` by
    (rw[EVERY_EL, EL_TAKE, EL_DROP] >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  drule run_insts_idx_indep >>
  disch_then (qspecl_then [`k`, `C'`, `t2`, `SUC t.vs_inst_idx`] mp_tac) >>
  simp[exec_result_map_def] >> strip_tac >>
  `SUC m + SUC t.vs_inst_idx - 1 = SUC m + t.vs_inst_idx` by decide_tac >> simp[]
QED

Theorem fmp_cov_tail_next:
  ALL_DISTINCT (fn_labels fn') /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  revert_forward_pair bb' p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j /\
  active_inst fn' ti t /\ ~is_terminator ti.inst_opcode /\
  step_inst fuel C' ti t = OK t2 ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >> fs[] >>
  `t.vs_inst_idx < j` by
    (Cases_on `t.vs_inst_idx = j` >> fs[revert_forward_pair_def] >>
     gvs[is_terminator_def]) >>
  simp[fmp_cov_def] >> disj2_tac >>
  qexistsl [`p`, `j`] >> simp[]
QED

Theorem fmp_cov_prefix_next:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
    is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t1 ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' /\
  t.vs_current_bb = t1.vs_current_bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx < t1.vs_inst_idx /\
  (!k. fmp_target_run k C' fn.fn_name t
    (t1.vs_inst_idx - t.vs_inst_idx) t1) /\
  (!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
    i < LENGTH bb'.bb_instructions /\
    fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) /\
  active_inst fn' ti t /\ ~is_terminator ti.inst_opcode /\
  ti.inst_opcode <> INVOKE /\ step_inst fuel C' ti t = OK t2 ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `!i. t.vs_inst_idx < i /\ i < t.vs_inst_idx +
         (t1.vs_inst_idx - t.vs_inst_idx) ==>
     ~is_terminator (EL i bb'.bb_instructions).inst_opcode /\
     (EL i bb'.bb_instructions).inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     qpat_x_assum `!i. _ <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >>
     gvs[fmp_inserted_op_def, is_terminator_def]) >>
  `!k. fmp_target_run k C' fn.fn_name
     (t2 with vs_inst_idx := SUC t.vs_inst_idx)
     ((t1.vs_inst_idx - t.vs_inst_idx) - 1) t1` by
    (irule fmp_cov_run_step >> simp[] >>
     qexistsl [`bb'`, `fuel`, `ti`] >>
     `lookup_block t1.vs_current_bb fn'.fn_blocks = SOME bb'` by metis_tac[] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all step_preserves_control_flow >> strip_tac >>
  simp[fmp_cov_def] >> disj1_tac >>
  qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`, `t1`,
            `ts`, `restored`, `bb'`] >> simp[] >>
  conj_tac >- fs[] >>
  conj_tac >- metis_tac[] >>
  `t1.vs_inst_idx - SUC t.vs_inst_idx =
     t1.vs_inst_idx - t.vs_inst_idx - 1` by decide_tac >>
  fs[arithmeticTheory.ADD1]
QED
