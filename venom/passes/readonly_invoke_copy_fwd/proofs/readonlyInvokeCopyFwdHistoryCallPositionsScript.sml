Theory readonlyInvokeCopyFwdHistoryCallPositions
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdReadonlyPositions
  readonlyInvokeCopyFwdProtectionSelected readonlyInvokeCopyFwdProtectionProducers
  readonlyInvokeCopyFwdPlan
  internalReturnCopyFwdPlan invokeCopyFwdCommonDefs venomExecSemantics
  indexedLists list pred_set

Theorem ricf_located_event_call_position:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  MEM (ri,p) e.rfe_sites ==>
  ?cb i nm args argsR.
    cb < LENGTH original.fn_blocks /\ cb < LENGTH round.fn_blocks /\
    i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
    i < LENGTH (EL cb round.fn_blocks).bb_instructions /\
    ri = EL i (EL cb round.fn_blocks).bb_instructions /\
    (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    decode_invoke (EL i (EL cb original.fn_blocks).bb_instructions) = SOME (nm,args) /\
    decode_invoke ri = SOME (nm,argsR) /\ LENGTH argsR = LENGTH args /\
    (!k. k < LENGTH args ==> EL k argsR = EL k args \/
       rma_is_readonly ctx0.icf_rma nm k)
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  drule_all ricf_event_sites_function >> strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  `?nm argsR. decode_invoke ri = SOME (nm,argsR)` by
    (gvs[icf_is_readonly_op_def, icf_get_callee_name_def, AllCaseEqs()] >>
     Cases_on `ri.inst_operands` >> gvs[] >>
     Cases_on `h` >> gvs[decode_invoke_def]) >>
  drule_all ricf_function_trace_readonly_edit >>
  simp[ricf_readonly_function_edit_def, LIST_REL_EL_EQN] >> strip_tac >>
  fs[venomInstTheory.fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  `?cb. cb < LENGTH round.fn_blocks /\ EL cb round.fn_blocks = bb` by
    metis_tac[MEM_EL] >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = ri` by
    metis_tac[MEM_EL] >>
  first_x_assum (qspec_then `cb` mp_tac) >>
  simp[ricf_readonly_block_edit_def, LIST_REL_EL_EQN] >> strip_tac >>
  `ricf_readonly_inst_edit ctx0.icf_rma
     (EL i (EL cb original.fn_blocks).bb_instructions) ri` by metis_tac[] >>
  drule_all ricf_readonly_inst_edit_decode_back >> strip_tac >>
  qexistsl_tac [`cb`,`i`,`args`] >> simp[]
QED

(* The source call and selected round call share a position, not a record. *)
Theorem ricf_located_event_original_destination_readonly:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i (EL cb original.fn_blocks).bb_instructions) = SOME (nm,args) /\
  MEM (EL i (EL cb round.fn_blocks).bb_instructions,p) e.rfe_sites /\
  k < LENGTH args /\ EL k args = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v ==>
  rma_is_readonly ctx0.icf_rma nm k
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_function_trace_readonly_positions >> strip_tac >>
  Cases_on `rma_is_readonly ctx0.icf_rma nm k` >> simp[] >>
  `EL k args' = Var v` by metis_tac[] >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  `ircf_alias round (icf_assign_root (dfg_build_function round) {} dst) v` by
    (fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]) >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  `MEM (EL i (EL cb round.fn_blocks).bb_instructions) (fn_insts round)` by
    (simp[venomInstTheory.fn_insts_def] >>
     irule venomInstTheory.fmp_fn_insts_blocks_intro >>
     qexists_tac `EL cb round.fn_blocks` >> simp[EL_MEM]) >>
  `(EL i (EL cb round.fn_blocks).bb_instructions).inst_operands = Label nm::args'` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `(ricf_event_copy e current).inst_operands = [Var dst;src;sz]` by metis_tac[] >>
  `icf_is_readonly_op e.rfe_ctx.icf_rma
     (EL i (EL cb round.fn_blocks).bb_instructions) (SUC k)` by
    (`SUC k < LENGTH (EL i (EL cb round.fn_blocks).bb_instructions).inst_operands /\
      EL (SUC k) (EL i (EL cb round.fn_blocks).bb_instructions).inst_operands = Var v`
       by simp[] >>
     drule_all ricf_event_alias_use_accepted >>
     simp[icf_is_assign_output_use_def]) >>
  gvs[icf_is_readonly_op_def, icf_get_callee_name_def]
QED

Theorem ricf_located_event_original_source_readonly:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function original) sv = SOME ai /\ ai.inst_opcode = ALLOCA /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i (EL cb original.fn_blocks).bb_instructions) = SOME (nm,args) /\
  MEM (EL i (EL cb round.fn_blocks).bb_instructions,p) e.rfe_sites /\
  k < LENGTH args /\ EL k args = Var sv ==>
  rma_is_readonly ctx0.icf_rma nm k
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_function_trace_readonly_positions >> strip_tac >>
  Cases_on `rma_is_readonly ctx0.icf_rma nm k` >> simp[] >>
  `EL k args' = Var sv` by metis_tac[] >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_function_trace_alloca_defs >> strip_tac >>
  `dfg_get_def (dfg_build_function round) sv = SOME ai` by metis_tac[] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  `(ricf_event_copy e current).inst_operands = [Var dst;Var sv;sz]` by metis_tac[] >>
  drule_all ricf_event_source_alloca_name >> strip_tac >>
  `rma_is_readonly e.rfe_ctx.icf_rma nm k` by
    (irule ricf_selected_call_source_readonly >> metis_tac[]) >>
  gvs[]
QED
