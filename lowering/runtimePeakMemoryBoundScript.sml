Theory runtimePeakMemoryBound
Ancestors
  runtimePeakMemoryPackage runtimePeakMemoryProof runtimePeakMemoryCode
  runtimeDynamicPeakMemory dallocaCalldata exprLoweringProps builtinSystem
  venomExecSemantics vfmExecution vfmBuffer vfmTypes vfmCalldataBound
  runtimePeakMemorySourceGate vyperLoweringCorrect vyperCompiler e2eDefs
  contextCodegenRel contextRawReachable venomLayout venomState venomInst words list

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

Theorem lower_vyper_runtime_unit_dynamic_peak_memory_bound:
  !tops rpolicy (unit:compilation_unit) (cp_fmp:num) am tx
   (fmp:bytes32) vs vs0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    (!vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy ==>
       ~supported_stmts_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty
                  (CreateTarget (CreateFromBlueprint raw) salted rof order)
                  es d)
         body /\
       EVERY (\d0. ~supported_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty
                  (CreateTarget (CreateFromBlueprint raw) salted rof order)
                  es d)
         d0) dflts) /\
    initial_venom_state_rel tops am tx vs /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 unit.cu_context fn i s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (i.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
       !sz_op sz.
         i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `blueprint_create_root =
    (\e. ?ty raw salted rof order es d.
       e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d)` by
    simp[FUN_EQ_THM, blueprint_create_root_def] >>
  `runtime_blueprint_free tops` by (fs[runtime_blueprint_free_def] >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`source_tops` |-> `tops`, `policy` |-> `rpolicy`]
    lower_vyper_runtime_unit_dalloca_windows) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `!fn. MEM fn unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
    (drule lower_vyper_runtime_unit_context_entry >>
     simp[lowering_context_ok_def, EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`source_tops` |-> `tops`]
    lower_vyper_runtime_unit_dynamic_peak_memory_from_windows) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[active_inst_dalloca_windows]) >>
  simp[]
QED

(* At a reached msg.data allocation, use H5 for the cumulative bound.
   The prefix sequence is CALLDATASIZE, which leaves both pointers unchanged. *)
val h5_premises =
  fst (dest_imp (snd (strip_forall
    (concl lower_vyper_runtime_unit_dynamic_peak_memory_bound))));

Theorem lower_vyper_runtime_unit_raw_call_msg_data_peak_memory:
  ^h5_premises /\
  compile_msg_data_to_memory sa = ((data_ptr,data_len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
  fmp_room unit.cu_context fn s /\ ctx_has_dalloca unit.cu_context /\
  run_inst_seq (TAKE 1 (emitted_insts sa sb)) s = OK pre /\
  raw_reachable vs0 unit.cu_context fn (EL 1 (emitted_insts sa sb))
    (pre with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand data_ptr t = SOME s.vs_fmp /\
    eval_operand data_len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    w2n s.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
      dimword (:256) /\
    fmp_room unit.cu_context fn t /\
    fmp_frontier_rel cp_fmp (w2n fmp)
      (cp_fmp + (w2n s.vs_fmp - w2n fmp) +
       venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) t.vs_fmp /\
    (!es c rb rest gas offset.
      es.contexts = (c, rb) :: rest /\
      s.vs_call_ctx.cc_calldata = buffer_to_list c.msgParams.data ==>
      (s.vs_call_ctx.cc_calldata = [] ==>
        copy_to_memory gas offset 0 0 (SOME get_call_data) es =
          consume_gas gas es) /\
      (s.vs_call_ctx.cc_calldata <> [] /\ wf_state es /\ calldata_bounded es /\
       2 ** 64 <= offset + LENGTH s.vs_call_ctx.cc_calldata ==>
        c.msgParams.gasLimit - c.gasUsed <
        memory_expansion_cost (buffer_length c.memory)
          (word_size (offset + LENGTH s.vs_call_ctx.cc_calldata) * 32)))
Proof
  strip_tac >>
  drule calldata_memory_insts >> strip_tac >>
  `pre.vs_initial_fmp = s.vs_initial_fmp /\ pre.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read0_def, bind_outputs_def, update_var_def] >>
     strip_tac >> gvs[]) >>
  fs[mk_inst_def] >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `cp_fmp`, `am`, `tx`, `fmp`,
    `vs`, `vs0`] mp_tac lower_vyper_runtime_unit_dynamic_peak_memory_bound >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`fn`, `EL 1 (emitted_insts sa sb)`,
    `pre with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[mk_inst_def] >> strip_tac >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,
    `lo` |-> `cp_fmp + (w2n s.vs_fmp - w2n (fmp:bytes32))`]
    raw_call_msg_data_site_peak_memory) >>
  impl_tac >- simp[] >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!es c rb rest gas offset. _ ==> _ /\ _`
    (qspecl_then [`es`, `c`, `rb`, `rest`, `0`, `offset`] mp_tac) >>
  simp[]
QED
