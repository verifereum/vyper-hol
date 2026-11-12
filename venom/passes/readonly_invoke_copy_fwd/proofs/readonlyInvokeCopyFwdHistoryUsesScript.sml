Theory readonlyInvokeCopyFwdHistoryUses
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdHistoryClosure readonlyInvokeCopyFwdHistoryCallPositions
  readonlyInvokeCopyFwdReadonlyPositions readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdPlan internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  invokeCopyFwdMemoryUses venomInst list pred_set

(* The exception records the actual trace step, not just a NOP opcode. *)
Definition ricf_block_erasure_def:
  ricf_block_erasure bb trace i old <=>
    ?pre e post cur.
      trace = pre ++ e::post /\ ricf_block_trace bb pre cur /\
      ricf_event_ok e cur /\ e.rfe_index = i /\
      i < LENGTH cur.bb_instructions /\
      (EL i cur.bb_instructions).inst_id = old.inst_id /\
      (EL i cur.bb_instructions).inst_opcode = MCOPY
End

Theorem ricf_block_trace_erasure:
  !bb trace last. ricf_block_trace bb trace last ==>
  !i old.
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_id = old.inst_id /\
    (EL i bb.bb_instructions).inst_opcode = MCOPY /\ 
    (EL i last.bb_instructions).inst_opcode <> MCOPY ==>
    ricf_block_erasure bb trace i old
Proof
  ho_match_mp_tac ricf_block_trace_ind >> rpt strip_tac >>
  rename1 `ricf_event_ok e bb` >>
  Cases_on `i = e.rfe_index`
  >- (simp[ricf_block_erasure_def] >>
      qexistsl_tac [`[]`,`e`,`trace`,`bb`] >>
      gvs[ricf_block_trace_nil]) >>
  `(EL i (ricf_event_apply e bb).bb_instructions).inst_id = old.inst_id /\
    (EL i (ricf_event_apply e bb).bb_instructions).inst_opcode = MCOPY` by
    (conj_tac
     >- (mp_tac (Q.INST [`e` |-> `e`,`bb` |-> `bb`] ricf_event_ids) >>
         simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
     simp[ricf_event_opcode]) >>
  `i < LENGTH (ricf_event_apply e bb).bb_instructions` by
    metis_tac[ricf_event_prefix_and_copy] >>
  first_x_assum (qspecl_then [`i`,`old`] mp_tac) >> simp[] >>
  simp[ricf_block_erasure_def] >> strip_tac >>
  qexistsl_tac [`e::pre`,`e'`,`post`,`cur`] >>
  simp[] >> metis_tac[ricf_block_trace_cons]
QED

Definition ricf_logged_erasure_def:
  ricf_logged_erasure log b i old <=>
    ?round logs mid. MEM (round,logs,mid) log /\
      b < LENGTH round.fn_blocks /\ b < LENGTH logs /\
      ricf_block_erasure (EL b round.fn_blocks) (EL b logs) i old
End

Theorem ricf_logged_function_trace_erasure:
  !ctx0 fn log last. ricf_logged_function_trace ctx0 fn log last ==>
  !b i old.
    b < LENGTH fn.fn_blocks /\
    i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_id = old.inst_id /\
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = MCOPY /\
    (EL i (EL b last.fn_blocks).bb_instructions).inst_opcode <> MCOPY ==>
    ricf_logged_erasure log b i old
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >> rpt strip_tac >>
  rename1 `ricf_logged_round ctx00 round logs mid` >>
  drule_all ricf_logged_round_block >> strip_tac >>
  Cases_on `(EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = MCOPY`
  >- (`b < LENGTH mid.fn_blocks` by
        gvs[ricf_logged_round_def, LIST_REL_EL_EQN] >>
      `i < LENGTH (EL b mid.fn_blocks).bb_instructions /\
       (EL i (EL b mid.fn_blocks).bb_instructions).inst_id = old.inst_id` by
        (drule ricf_block_trace_ids >>
         simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
      first_x_assum (qspecl_then [`b`,`i`,`old`] mp_tac) >> simp[] >>
      simp[ricf_logged_erasure_def] >> metis_tac[]) >>
  `ricf_block_erasure (EL b round.fn_blocks) (EL b logs) i old` by
    metis_tac[ricf_block_trace_erasure] >>
  simp[ricf_logged_erasure_def] >> metis_tac[]
QED

Theorem ricf_logged_function_trace_prefix:
  !ctx0 fn log last. ricf_logged_function_trace ctx0 fn log last ==>
  !round logs mid. MEM (round,logs,mid) log ==>
    ?pre post. log = pre ++ (round,logs,mid)::post /\
      ricf_logged_function_trace ctx0 fn pre round
Proof
  ho_match_mp_tac ricf_logged_function_trace_ind >> simp[] >>
  rpt strip_tac >> gvs[]
  >- (qexistsl_tac [`[]`,`log`] >> simp[ricf_logged_function_trace_nil]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`(fn,logs,fn')::pre`,`post`] >>
  simp[] >> metis_tac[ricf_logged_function_trace_cons]
QED

Definition ricf_prior_erasure_def:
  ricf_prior_erasure ctx0 original log round b i old <=>
    ?pre post. log = pre ++ post /\
      ricf_logged_function_trace ctx0 original pre round /\
      ricf_logged_erasure pre b i old
End

Theorem ricf_located_event_erased_original_copy:
  ricf_located_event ctx0 original log round b es prefix e current /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  old.inst_opcode = MCOPY /\
  (EL i (EL cb round.fn_blocks).bb_instructions).inst_opcode <> MCOPY ==>
  ricf_prior_erasure ctx0 original log round cb i old
Proof
  simp[ricf_located_event_def] >> rpt strip_tac >>
  drule_all ricf_logged_function_trace_prefix >> strip_tac >>
  `ricf_logged_erasure pre cb i old` by
    (irule ricf_logged_function_trace_erasure >>
     qexistsl_tac [`ctx0`,`original`,`round`] >> gvs[]) >>
  simp[ricf_prior_erasure_def] >> metis_tac[APPEND_ASSOC]
QED

(* Position classification is on the original instruction.  The call's
   record may change, but readonly numbering cannot. *)
Theorem ricf_located_event_original_alias_use:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  p < LENGTH old.inst_operands /\ EL p old.inst_operands = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v ==>
  icf_is_assign_output_use old p \/
  (old.inst_opcode = MCOPY /\ p = 0 /\
    old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id) \/
  (old.inst_opcode = INVOKE /\ icf_is_readonly_op ctx0.icf_rma old p) \/
  (old.inst_opcode = MCOPY /\
    ricf_prior_erasure ctx0 original log round cb i old)
Proof
  strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_function_trace_readonly_edit >>
  simp[ricf_readonly_function_edit_def, LIST_REL_EL_EQN] >> strip_tac >>
  `ricf_readonly_block_edit ctx0.icf_rma (EL cb original.fn_blocks)
     (EL cb round.fn_blocks)` by metis_tac[] >>
  `cb < LENGTH round.fn_blocks /\
   i < LENGTH (EL cb round.fn_blocks).bb_instructions /\
   ricf_readonly_inst_edit ctx0.icf_rma old
     (EL i (EL cb round.fn_blocks).bb_instructions)` by
    (fs[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `ricf_readonly_inst_edit _ old ri` >>
  Cases_on `old.inst_opcode = MCOPY /\ ri.inst_opcode <> MCOPY`
  >- metis_tac[ricf_located_event_erased_original_copy] >>
  Cases_on `old.inst_opcode = INVOKE /\ icf_is_readonly_op ctx0.icf_rma old p`
  >- gvs[] >>
  `p < LENGTH ri.inst_operands /\ EL p ri.inst_operands = Var v` by
    (gvs[ricf_readonly_inst_edit_def, ricf_inst_edit_def] >> metis_tac[]) >>
  `MEM ri (fn_insts round)` by
    (simp[Abbr `ri`, fn_insts_def] >>
     irule fmp_fn_insts_blocks_intro >>
     qexists_tac `EL cb round.fn_blocks` >> simp[EL_MEM]) >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  `ircf_alias round (icf_assign_root (dfg_build_function round) {} dst) v` by
    (fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]) >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  `(ricf_event_copy e current).inst_operands = [Var dst;src;sz]` by metis_tac[] >>
  drule_all ricf_event_alias_use_accepted >>
  gvs[ricf_readonly_inst_edit_def, ricf_inst_edit_def,
      icf_is_assign_output_use_def, icf_is_readonly_op_def] >> metis_tac[]
QED

Theorem ricf_located_event_original_occurrence_use:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  p < LENGTH old.inst_operands /\
  op_prov H (EL p old.inst_operands) = SOME (a,ai.inst_id) ==>
  icf_is_assign_output_use old p \/
  (old.inst_opcode = MCOPY /\ p = 0 /\
    old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id) \/
  (old.inst_opcode = INVOKE /\ icf_is_readonly_op ctx0.icf_rma old p) \/
  (old.inst_opcode = MCOPY /\
    ricf_prior_erasure ctx0 original log round cb i old)
Proof
  strip_tac >>
  drule_all ricf_located_event_destination_occurrence_operand >> strip_tac >>
  irule ricf_located_event_original_alias_use >> metis_tac[]
QED


(* Reads cannot be the retained copy's destination operand; writes can.
   Both statements keep the exact original position and prior log witness. *)
Theorem ricf_located_event_original_address_use:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions ==>
  (!ops. mem_read_ops old = SOME ops ==>
    op_prov H ops.iao_ofst <> SOME (a,ai.inst_id) \/
    (old.inst_opcode = MCOPY /\
      ricf_prior_erasure ctx0 original log round cb i old)) /\
  (!ops. mem_write_ops old = SOME ops ==>
    op_prov H ops.iao_ofst <> SOME (a,ai.inst_id) \/
    (old.inst_opcode = MCOPY /\
      (old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id \/
       ricf_prior_erasure ctx0 original log round cb i old)))
Proof
  strip_tac >> conj_tac >> gen_tac >> strip_tac
  >- (drule icf_read_address_position >> strip_tac >>
      Cases_on `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` >> simp[] >>
      `op_prov H (EL p old.inst_operands) = SOME (a,ai.inst_id)` by simp[] >>
      drule_all ricf_located_event_original_occurrence_use >> metis_tac[]) >>
  drule icf_write_address_position >> strip_tac >>
  Cases_on `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` >> simp[] >>
  `op_prov H (EL p old.inst_operands) = SOME (a,ai.inst_id)` by simp[] >>
  drule_all ricf_located_event_original_occurrence_use >> metis_tac[]
QED
