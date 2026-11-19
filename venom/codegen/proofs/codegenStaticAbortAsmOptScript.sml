(* Concrete optimized entry progress after a source abort. The pending
   static-abort window permits arbitrary memory and spill contents. ASSERT
   can choose either its revert sink or its continuation; ASSERT_UNREACHABLE
   can choose its INVALID arm or continuation. Neither case needs a symbolic
   terminal run inside that window. *)
Theory codegenStaticAbortAsmOpt
Ancestors
  staticAbortMixedSeed staticAbortMixedObserve
  staticAbortOptPruneUnreachable staticAbortOptMergeIszero
  staticAbortOptMergeJumpdests staticAbortOptPruneJumps
  staticAbortOptConditionalJumps staticAbortOptUnusedLabels staticAbortOptStack
  asmOptNonemptyCompose
  codegenEntrySim codegenSymRel contextStaticAbortRel asmOptimizer asmSem symbolResolve

val _ = Parse.hide "cp";

(* Compare the workers' lexical presentations without unfolding semantics. *)
val outer_lets = REPEATC (REWR_CONV LET_THM THENC BETA_CONV);
val certificate_nf =
  REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV]) THENC
  PURE_REWRITE_CONV [pred_setTheory.DIFF_EMPTY, GSYM CONJ_ASSOC];

Theorem codegen_entry_asm_sim_abort_asm_opt:
  !fuel rpolicy unit cp prog prog' Inv vs s a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    label_flow_ok unit.cu_context /\
    code_end_offset_ok
      (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      unit.cu_context /\ sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    s.as_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cp prog vs s /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
    ?n ast.
      (asm_steps (SND (compute_label_offsets prog'))
         (build_offset_to_pc prog') prog' n
         (s with as_code := assemble prog' ++ vs.vs_data_section) =
           AsmRevert ast \/
       asm_steps (SND (compute_label_offsets prog'))
         (build_offset_to_pc prog') prog' n
         (s with as_code := assemble prog' ++ vs.vs_data_section) =
           AsmFault ast) /\
      ast.as_requests <<= vs'.vs_requests
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`prog`, `s`, `vs.vs_data_section`, `vs'.vs_requests`, `prog'`]
    (mp_tac o CONV_RULE (outer_lets THENC
       SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [])) mixed_certificate_exception >>
  (impl_tac >- (
    CONV_TAC (UNBETA_CONV ``prog':asm_inst list``) >>
    qmatch_abbrev_tac `M_R prog'` >>
    `!p q ch. M_R p /\ optimize_round p = SOME (q,ch) ==> M_R q` by
      (match_mp_tac (Q.INST [`P` |-> `M_R:asm_inst list -> bool`]
         optimize_round_preserves_predicate) >>
       qpat_x_assum `Abbrev (M_R = _)` (rewrite_tac o single o
         REWRITE_RULE [markerTheory.Abbrev_def]) >>
       CONV_TAC (certificate_nf THENC SIMP_CONV bool_ss []) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) prune_unreachable_abort_certificate) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) merge_iszero_abort_certificate) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) merge_jumpdests_abort_certificate) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) prune_inefficient_jumps_abort_certificate) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) optimize_inefficient_jumps_abort_certificate) >>
       conj_tac >- MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) prune_unused_jumpdests_abort_certificate) >>
       MATCH_ACCEPT_TAC (CONV_RULE
         (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
          certificate_nf THENC SIMP_CONV bool_ss []) stack_peephole_abort_certificate)) >>
    drule asm_opt_finalizer_preserves_predicate >>
    disch_then (qspecl_then [`rpolicy`, `prog`, `prog'`] mp_tac) >>
    (impl_tac >- (
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `Abbrev (M_R = _)` (rewrite_tac o single o
        REWRITE_RULE [markerTheory.Abbrev_def]) >>
      CONV_TAC (certificate_nf THENC SIMP_CONV bool_ss []) >>
      qspecl_then [`fuel`, `rpolicy`, `unit`, `cp`, `prog`, `Inv`, `vs`, `s`, `a`, `vs'`]
        (mp_tac o CONV_RULE (RAND_CONV
          (SIMP_CONV (bool_ss ++ boolSimps.UNWIND_ss) [] THENC
           certificate_nf THENC SIMP_CONV bool_ss []))) codegen_entry_abort_mixed_seed >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
