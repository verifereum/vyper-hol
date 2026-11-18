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

(* Every accepted finalizer carries a successful symbolic prefix of the
   original program to one of the finalized program; at an observed opcode
   the finalized prefix stops at the same opcode in the same state, up to
   the program counter, label stack entries and label bytes. *)
Theorem accepted_finalizers_prefix_transport:
  !fin rp p q.
    fin IN accepted_finalizers /\ fin rp p = SOME q /\ asm_static_wf p ==>
    ?K. 0 < K /\ !env s n a.
      s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
      (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                   "CREATE2"} /\
         a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
       ?m b. sym_steps q env m (sym_init s) = SymOK b /\
         b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp op /\
         (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
         MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
         FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)
Proof
  mp_tac (BETA_RULE accepted_finalizers_prefix_transport_conditional) >>
  impl_tac >-
    (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
      (map BETA_RULE
        [merge_iszero_prefix_transport, prune_jumps_prefix_transport,
         inefficient_jumps_prefix_transport, peephole_prefix_transport,
         merge_jumpdests_prefix_transport, prune_unreachable_prefix_transport,
         prune_unused_prefix_transport])) >>
  disch_then MATCH_ACCEPT_TAC
QED
