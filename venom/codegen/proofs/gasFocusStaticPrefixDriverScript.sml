Theory gasFocusStaticPrefixDriver
Ancestors
  gasFocusPrefixDriver staticAbortDefs o1PipelineCorrect o1SafeUpto
  o1PassContract o1RequestContract o1PassLift gasEvents codegenEntryRel
  codegenAsmProgOk asmFrameRel asmSem asmOptimizer callTrace vfmExecution
  venomExecProps unitMemInv list rich_list pred_set words arithmetic

(* Goal quotation only: the shared focus construction and static O1
   exports must be available before the theorem can be proved. *)
val focus_producer_finalizer_static_goal : term = ``
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
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  (!gs. ?D f extra.
    dead_wf D /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with vs_gas_readings := gs) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_prev_bb := NONE;
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
           (vs0 with vs_gas_readings := raw ++ [0w]))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        (o1_lowered_inv out.po_unit.cu_context vs0 \/
         ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
            mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                      lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
              out.po_unit.cu_context vs0) /\
          !fuel. terminates (run_context fuel unit.cu_context
                    (vs0 with vs_gas_readings := raw ++ [0w])) ==>
                 ?u. run_context fuel unit.cu_context
                       (vs0 with vs_gas_readings := raw ++ [0w]) =
                     Abort ExHalt_abort u))
``;
