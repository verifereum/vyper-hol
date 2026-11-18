Theory gasFocusStaticPrefixDriver
Ancestors
  gasFocusPrefixDriver gasFocusPacketPipelineStages gasFocusStaticExitLift
  o1StaticPipelineCorrect o1SafeUpto o1PassContract
  o1RequestContract o1PassLift gasEvents codegenEntryRel codegenEntrySim
  codegenAsmProgOk
  asmFrameRel asmSem asmOptimizer callTrace vfmExecution venomExecProps
  unitMemInv staticAbortDefs codegenSymRel contextRawReachable memSafeRun
  vyperCompiler lowerDloadDefs list rich_list pred_set words arithmetic

Theorem focus_producer_finalizer_static:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) /\
  unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
     label_flow_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  (!gs. ?D f extra.
    dead_wf D /\
    (fin = asm_opt_finalizer ==>
       !fn inst s.
         raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
           unit.cu_context fn inst s /\
         gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
           (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
         inst_dload_in_section inst s) /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                    vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      !D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
        (fin = asm_opt_finalizer ==>
           mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                     s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
             unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
        (fin = asm_opt_finalizer ==>
           code_end_offset_ok
             (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
               ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
        ((o1_lowered_inv out.po_unit.cu_context vs0 /\
          (fin = asm_opt_finalizer ==>
             code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
         ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
            mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                      lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
              out.po_unit.cu_context vs0) /\
          !fuel. terminates (run_context fuel unit.cu_context
                    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
                 ?u. run_context fuel unit.cu_context
                       (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
                     Abort ExHalt_abort u))
Proof
  NO_TAC
QED
