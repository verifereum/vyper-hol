(* Prior erased copies retain a located validation and their original source. *)
Theory readonlyInvokeCopyFwdHistoryReadExceptions
Ancestors
  readonlyInvokeCopyFwdHistoryExceptions readonlyInvokeCopyFwdHistoryUses
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdDefs
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdHistoryClosure
  invokeCopyFwdCommonDefs occurrenceOrigin invokeCopyFwdMemoryUses memLocDefs list
  readonlyInvokeCopyFwdProtectionSelected internalReturnCopyFwdPlan
  o1ContractMakeSsaPtrOk dfgAnalysisProps pointerConfinedDefs finite_map pred_set
  ptrDiscipline venomInst

Theorem ricf_logged_erasure_located_event:
  ricf_logged_function_trace ctx0 original log last /\
  ricf_logged_erasure log b i old ==>
  ?round es prefix e current.
    ricf_located_event ctx0 original log round b es prefix e current /\
    e.rfe_index = i
Proof
  simp[ricf_logged_erasure_def, ricf_block_erasure_def] >>
  rpt strip_tac >>
  simp[ricf_located_event_def] >> metis_tac[]
QED

Theorem ricf_prior_erasure_located_event:
  ricf_prior_erasure ctx0 original log round b i old ==>
  ?pre earlier es prefix e current.
    ricf_located_event ctx0 original pre earlier b es prefix e current /\
    e.rfe_index = i
Proof
  simp[ricf_prior_erasure_def] >> rpt strip_tac >>
  drule_all ricf_logged_erasure_located_event >> metis_tac[]
QED

Theorem ricf_located_event_original_destination_alloca:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] ==>
  ?di. dfg_get_def (dfg_build_function original)
    (icf_assign_root (dfg_build_function original) {} dst) = SOME di /\
    icf_is_alloca di
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >> gvs[] >>
  `?di. dfg_get_def (dfg_build_function round)
    (icf_assign_root (dfg_build_function round) {} dst) = SOME di /\
    icf_is_alloca di` by
    (qpat_x_assum `ricf_event_ok _ _` mp_tac >>
     simp[ricf_event_ok_def, ricf_try_forward_def] >>
     gvs[AllCaseEqs(), ricf_event_copy_def, icf_is_alloca_def] >> metis_tac[]) >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  drule ricf_function_trace_alloca_defs >> simp[] >>
  disch_then (qspec_then `di` mp_tac) >>
  simp[GSYM icf_is_alloca_def] >> metis_tac[]
QED

Theorem ricf_located_event_original_read_exclusion:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  mem_read_ops old = SOME ops ==>
  op_prov H ops.iao_ofst <> SOME (a,ai.inst_id)
Proof
  strip_tac >> strip_tac >>
  drule_all ricf_located_event_original_address_use >> strip_tac >>
  `old.inst_opcode = MCOPY /\
   ricf_prior_erasure ctx0 original log round cb i old` by metis_tac[] >>
  drule_all ricf_prior_erasure_located_event >> strip_tac >>
  rename1 `ricf_located_event ctx0 original pre earlier cb es' prefix' e' current'` >>
  `?d ss zz. (ricf_event_copy e' (EL cb original.fn_blocks)).inst_operands =
       [Var d;ss;zz]` by metis_tac[ricf_located_event_source_descriptor] >>
  `?di. dfg_get_def (dfg_build_function original)
      (icf_assign_root (dfg_build_function original) {} d) = SOME di /\
      icf_is_alloca di` by
    (irule ricf_located_event_original_destination_alloca >> metis_tac[]) >>
  `i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
   ricf_event_copy e' (EL cb original.fn_blocks) = old` by
    gvs[ricf_event_copy_def] >>
  `MEM (EL cb original.fn_blocks) original.fn_blocks` by simp[EL_MEM] >>
  `?sv si. ss = Var sv /\
    dfg_get_def (dfg_build_function original) sv = SOME si /\ icf_is_alloca si /\
    (!ii. MEM ii (fn_insts original) /\ MEM (Var sv) ii.inst_operands ==>
      ~is_pointer_preserving_op ii.inst_opcode /\
      (ii.inst_opcode = MCOPY ==> EL 0 ii.inst_operands <> Var sv))` by
    (fs[ricf_src_alloca_def] >> metis_tac[]) >>
  gvs[mem_read_ops_def] >>
  `sv IN pointer_derived_vars original
      {icf_assign_root (dfg_build_function original) {} dst}` by
    (gvs[op_prov_def] >>
     drule_all occurrence_syntax_origin_planned_root >> simp[]) >>
  `MEM sv si.inst_outputs /\ MEM si (fn_insts original)` by
    metis_tac[dfg_build_function_correct] >>
  `sv = icf_assign_root (dfg_build_function original) {} dst` by
    (`FINITE {icf_assign_root (dfg_build_function original) {} dst}` by simp[] >>
     drule_all mssa_derived_definition >>
     gvs[icf_is_alloca_def, is_pointer_preserving_op_def]) >>
  `!fn x v. ircf_alias fn x v ==>
     (!ii. MEM ii (fn_insts fn) /\ MEM (Var x) ii.inst_operands ==>
        ~is_pointer_preserving_op ii.inst_opcode) ==> v = x` by
    (ho_match_mp_tac ircf_alias_ind >> rpt strip_tac >> gvs[] >>
     metis_tac[is_pointer_preserving_op_def]) >>
  `dst = sv` by metis_tac[ircf_assign_root_alias] >>
  `b < LENGTH original.fn_blocks /\
   ricf_block_edit (EL b original.fn_blocks) current` by
    (irule ricf_located_event_source_block >> metis_tac[]) >>
  `ricf_event_ok e current` by metis_tac[ricf_located_event_validation] >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY` by
    (`ricf_event_copy e current = ricf_event_copy e (EL b original.fn_blocks)` by
       metis_tac[ricf_located_event_source_descriptor] >>
     drule ricf_block_edit_EL >> strip_tac >>
     metis_tac[ricf_event_copy_shape]) >>
  `MEM (ricf_event_copy e (EL b original.fn_blocks)) (fn_insts original)` by
    (simp[ricf_event_copy_def, fn_insts_def] >>
     irule fmp_fn_insts_blocks_intro >>
     qexists_tac `EL b original.fn_blocks` >> simp[EL_MEM]) >>
  metis_tac[HD, MEM]
QED
