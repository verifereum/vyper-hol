Theory asmFinalizerPrefix
Ancestors
  asmOptimizer
  codegenEntrySim
  codegenSymRel
  asmDataEnv
  asmSplice
  asmFrameRel
  asmFrameRun
  asmFrameLocalStep
  asmFinalizerPrefixCompose asmFinalizerPrefixSplice
  asmFinalizerPrefixControl asmFinalizerPrefixAssembly codegenAsmStaticWf

(* Quantitative symbolic transport supplies independent bound and GAS
   witnesses; the frame assembly converts each finalized symbolic prefix
   to a concrete prefix of the nonstarved run. *)
Theorem focus_finalizer_prefix_bridge:
!fin rpolicy unit cpl prog prog' vs0 es0 result final.
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_ready unit.cu_context /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?max_cost. !n ast.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n (entry_asm_state vs0 es0) = AsmOK ast /\
      (?ss. sym_steps prog (asm_data_env prog vs0.vs_code) n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
      n <= max_cost /\
      (ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" ==>
        ast.as_gas_readings <> [])
Proof
  rpt gen_tac >> strip_tac >>
  `asm_static_wf prog` by metis_tac[codegen_asm_static_wf] >>
  mp_tac (BETA_RULE accepted_finalizers_prefix_transport_conditional) >>
  (impl_tac >-
    (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
      (map BETA_RULE
        [merge_iszero_prefix_transport, prune_jumps_prefix_transport,
         inefficient_jumps_prefix_transport, peephole_prefix_transport,
         merge_jumpdests_prefix_transport, prune_unreachable_prefix_transport,
         prune_unused_prefix_transport]))) >>
  disch_then drule_all >> disch_then assume_tac >>
  drule_all (BETA_RULE focus_finalizer_prefix_bridge_conditional) >> simp[]
QED
