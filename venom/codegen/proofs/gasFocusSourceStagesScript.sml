Theory gasFocusSourceStages
Ancestors
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic

(* Scratch statement for elaboration and independent review.
   The fixed filling is gs ++ tail. The named source witnesses D, f and
   extra instantiate the bounded H1 source family at that filling. The
   conclusion uses the actual C7 root, with the unchanged assembly FMP. *)
Theorem focus_source_stages_cut:
  let filling = gs ++ tail in
  let n = MIN (LENGTH (markf filling)) (LENGTH filling);
      R = root_entry with vs_gas_readings := gs ++ tail;
      V = vs0 with <|vs_gas_readings := filling; vs_fmp := fmp; vs_initial_fmp := fmp|>
  in
  let A = V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> in
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  dead_wf D /\
  o1_safe_upto D lo n unit.cu_context
    V /\
  MAP project (gas_events_blocks f unit.cu_context entryfn A) = markf filling ++ extra /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rpolicy o1_fn_passes
    (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
  mem_inv (\ctx fn inst u. gas_cut n R u ==> lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
    (stage 7) R /\
  ?fn7 f7.
    (stage 7).ctx_entry = SOME nm /\
    lookup_function nm (stage 7).ctx_functions = SOME fn7 /\ fn_entry_label fn7 = SOME lbl /\
    n <= LENGTH (gas_events_blocks f7 (stage 7) fn7 R) /\
    TAKE n (gas_events_blocks f7 (stage 7) fn7 R) =
      TAKE n (gas_events_blocks f unit.cu_context entryfn A)
Proof
  cheat
QED
