Theory gasFocusSourceStages
Ancestors
  gasFocusLowerDloadCut gasFocusLoweringBridge
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
  o1_safe_upto D lo (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) unit.cu_context
    (vs0 with <|vs_gas_readings := (gs ++ tail); vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  MAP project (gas_events_blocks f unit.cu_context entryfn ((vs0 with <|vs_gas_readings := (gs ++ tail);
    vs_fmp := fmp; vs_initial_fmp := fmp|>) with <|vs_prev_bb := NONE; vs_current_bb := lbl;
    vs_inst_idx := 0|>)) = markf (gs ++ tail) ++ extra /\
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
  mem_inv (\ctx fn inst u. gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (root_entry
    with vs_gas_readings := gs ++ tail) u ==> lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
    (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
  ?fn7 f7.
    (stage 7).ctx_entry = SOME nm /\
    lookup_function nm (stage 7).ctx_functions = SOME fn7 /\ fn_entry_label fn7 = SOME lbl /\
    (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) <= LENGTH (gas_events_blocks f7 (stage 7)
      fn7 (root_entry with vs_gas_readings := gs ++ tail)) /\
    TAKE (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (gas_events_blocks f7 (stage 7) fn7
      (root_entry with vs_gas_readings := gs ++ tail)) =
      TAKE (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (gas_events_blocks f unit.cu_context
        entryfn ((vs0 with <|vs_gas_readings := (gs ++ tail); vs_fmp := fmp; vs_initial_fmp := fmp|>) with
        <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  sg `ptr_discipline_upto lo
        (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail))) (stage 2)
        (vs0 with <|vs_gas_readings := gs ++ tail; vs_fmp := fmp; vs_initial_fmp := fmp|>)`
  >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH lower_dload_stage_focus_safety))) >> cheat) >>
  sg `mem_inv (\ctx fn inst u.
          gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail)))
            (vs0 with <|vs_gas_readings := gs ++ tail; vs_fmp := fmp; vs_initial_fmp := fmp|>) u ==>
          dload_headroom_ok ctx fn inst u)
        (stage 2) (vs0 with <|vs_gas_readings := gs ++ tail; vs_fmp := fmp; vs_initial_fmp := fmp|>)`
  >- (PURE_REWRITE_TAC [mem_inv_raw_reachable] >> BETA_TAC >> conj_tac
      >- cheat >>
      rpt strip_tac >>
      irule (DISCH_ALL (CONJUNCT2 (CONJUNCT2 (UNDISCH (SPEC_ALL
        (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (UNDISCH lower_dload_stage_focus_safety))))))))) >>
      cheat) >>
  sg `mem_inv (\ctx fn inst u.
          gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail)))
            (vs0 with vs_gas_readings := gs ++ tail) u ==>
          lowered_mem_fact eom ctx fn inst u)
        (stage 4) (vs0 with vs_gas_readings := gs ++ tail)`
  >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH
          (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM]
            (Q.INST [`C2` |-> `stage 2`, `C3` |-> `stage 3`, `C4` |-> `stage 4`]
              focus_lowering_cut_bridge)))))) >> cheat) >>
  cheat
QED
