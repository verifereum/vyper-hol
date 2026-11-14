(* Statement-only: closed terms, no theorem declarations or admissions. *)
Theory guardedCodegenStatements
Ancestors
  guardedFrameSubset unbackedCallReachable unitMemInv
  contextStaticAbortRel codegenCorrectness codegenEntrySim asmFrameRel
  frameRel asmSem symbolResolve staticAbortDefs stackPlanGen dfgDefs
  vfmExecution vfmAccountFrame frameOutcome callTrace
  list relation arithmetic

val _ = Parse.hide "cp";

(* Shared with O1; the memory fact may include the canonical static cut. *)
val guarded_mem_inv_body =
  ``\M ctx vs.
      (?name fn lbl.
        ctx.ctx_entry = SOME name /\
        lookup_function name ctx.ctx_functions = SOME fn /\
        fn_entry_label fn = SOME lbl) /\
      !fn inst s. guarded_raw_reachable vs ctx fn inst s ==>
        M ctx fn inst s``;

(* INVOKE reads/writes no local byte range. Callee effects are covered by
   explicit guarded call/return steps, not unrestricted atomic execution. *)
val guarded_codegen_memory_body =
  ``\ctx cp vs.
      ^guarded_mem_inv_body
        (\ctx fn inst s.
          ~in_revert_forward fn s /\ ~in_static_abort_prefix fn s ==>
          source_memory_reads_disjoint cp inst s /\
          context_source_memory_writes_disjoint cp inst s) ctx vs``;

(* A terminal pre-oracle abort is permitted. This predicate has no producer
   here; actual EVM/control alignment must establish it before composition. *)
val guarded_boundary_stops_body =
  ``\ctx vs. !fn inst s fuel post.
      guarded_raw_reachable vs ctx fn inst s /\
      MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
      s.vs_outcomes = [] ==>
      step_inst fuel ctx inst s <> OK post``;

(* The actual EVM path, not equality of terminal run observations. *)
val actual_evm_prefix_body =
  ``\es k es1.
      FUNPOW (step o SND) k (INL (), es) = (INL (), es1) /\
      (!j. j < k ==>
        ISL (FST (FUNPOW (step o SND) j (INL (), es))) /\
        LENGTH es.contexts <=
          LENGTH (SND (FUNPOW (step o SND) j (INL (), es))).contexts)``;

val guarded_lowered_codegen_memory =
  ``!ctx cp vs eom fmp.
      ^guarded_mem_inv_body
        (\ctx fn inst s.
          in_static_abort_prefix fn s \/ lowered_mem_ok eom fmp ctx fn inst s)
        ctx vs /\
      (!r. MEM r cp.cp_regions ==>
        eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) ==>
      ^guarded_codegen_memory_body ctx cp vs``;

(* An actual-prefix witness for the canonical S1 escape, before any
   refutation. It does not claim the boundary advances or cannot be rejected.
   Existing strict-prefix proofs belong to their canonical supplier. *)
val guarded_codegen_unbacked_prefix =
  ``!rpolicy unit cp prog vs es r target.
      generate_context_plan unit.cu_context = SOME cp /\
      codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
      codegen_context_obligations (\_ _ _ _. F) unit.cu_context cp /\
      ^guarded_codegen_memory_body unit.cu_context cp vs /\
      initial_ctx_rel cp prog unit.cu_context vs es /\
      run_call es = SOME (r, target) /\
      ~frame_resource_starved es r target /\
      unbacked_call_reachable unit.cu_context vs ==>
      ?total.
        FUNPOW (step o SND) total (INL (), es) = (r, target) /\
        (?fn inst s n ast k es1 ps ra rest mem0 bb rest_ops ps_after.
          guarded_raw_reachable vs unit.cu_context fn inst s /\
          MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
          s.vs_outcomes = [] /\
          k < total /\
          asm_steps (SND (compute_label_offsets prog))
            (build_offset_to_pc prog) prog n (entry_asm_state vs es) =
              AsmOK ast /\
          ^actual_evm_prefix_body es k es1 /\
          run_call es1 = SOME (r, target) /\
          lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          generate_block_insts_plan (liveness_analyze fn)
            (dfg_build_function fn) (cfg_analyze fn) fn bb.bb_label
            (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
            (LENGTH bb.bb_instructions)
            (s.vs_inst_idx - LENGTH (get_params bb.bb_instructions))
            (DROP (s.vs_inst_idx - LENGTH (get_params bb.bb_instructions))
              (non_param_insts bb)) ps = SOME (rest_ops, ps_after) /\
          asm_block_at prog ast.as_pc
            (execute_plan cp.cp_initial_fmp rest_ops) /\
          fn_frame_inv unit.cu_context cp (SND (compute_label_offsets prog))
            fn ra rest mem0 ps s ast /\
          asm_frame_rel prog vs.vs_data_section es ast es1 /\
          ast.as_outcomes = s.vs_outcomes /\
          ast.as_gas_readings = s.vs_gas_readings)``;

(* A pending static-write path may fault or take an empty REVERT after
   spill corruption. Source first-abort provenance remains an O1 obligation. *)
val guarded_static_abort_escape_body =
  ``\ctx vs. ?fn inst s.
      guarded_raw_reachable vs ctx fn inst s /\
      in_static_abort_prefix fn s``;

val guarded_terminal_rel_body =
  ``\ctx vs es r target res.
      venom_frame_rel es r target res \/
      (^guarded_static_abort_escape_body ctx vs /\
       ?exc logs. frame_outcome es r target (SOME exc) [] logs)``;

(* Internal conditional composition only. guarded_boundary_stops_from_evm
   and rejected-operation terminal compatibility remain separate producers;
   this premise must not be added to vyper_call_correct/e2eCorrectness. *)
val guarded_codegen_correct_if_stops =
  ``!fuel rpolicy unit cp prog vs es.
      generate_context_plan unit.cu_context = SOME cp /\
      codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
      codegen_context_obligations (\_ _ _ _. F) unit.cu_context cp /\
      ^guarded_codegen_memory_body unit.cu_context cp vs /\
      ^guarded_boundary_stops_body unit.cu_context vs /\
      initial_ctx_rel cp prog unit.cu_context vs es ==>
      ?r target. run_call es = SOME (r, target) /\
        (frame_resource_starved es r target \/
         ^guarded_terminal_rel_body unit.cu_context vs es r target
           (run_context fuel unit.cu_context vs))``;

val statement_bodies =
  [("guarded_mem_inv", guarded_mem_inv_body),
   ("guarded_codegen_memory", guarded_codegen_memory_body),
   ("guarded_boundary_stops", guarded_boundary_stops_body),
   ("actual_evm_prefix", actual_evm_prefix_body),
   ("guarded_static_abort_escape", guarded_static_abort_escape_body),
   ("guarded_terminal_rel", guarded_terminal_rel_body)];
val statement_goals =
  [("guarded_lowered_codegen_memory", guarded_lowered_codegen_memory),
   ("guarded_codegen_unbacked_prefix", guarded_codegen_unbacked_prefix),
   ("guarded_codegen_correct_if_stops", guarded_codegen_correct_if_stops)];
val _ = List.app (fn (name, tm) =>
  if null (free_vars tm) then () else raise Fail (name ^ ": free variables"))
  (statement_bodies @ statement_goals);
val _ = List.app (fn (name, tm) =>
  if type_of tm = bool then () else raise Fail (name ^ ": not a proposition"))
  statement_goals;
