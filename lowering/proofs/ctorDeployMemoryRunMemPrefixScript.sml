(* With successful constructor argument binding, absence of a constructor
 * start forces rejection by the initial nonpayable value check. Its three
 * memory-free instructions give memory safety at every fuel, before any
 * immutables setup, argument decoding, or constructor body execution.
 * TOP-LEVEL: deploy_ctor_prefix_fail_run_mem_safe.
 *)
Theory ctorDeployMemoryRunMemPrefix
Ancestors
  ctorDeployLoweringDefs gasSummary memSafeRun venomInst
  ctorDeployMemoryRunMemPrefixLayout ctorDeployMemoryRunMemPrefixPayable
  fragExecMem fragExec compileEnv e2eEntry venomExecSemantics vyperCompiler
  emitHelper rich_list

Theorem deploy_ctor_prefix_fail_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb cf fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_prefix_rejecting_code >> strip_tac >>
  drule_all ctor_prefix_task_entry_label >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `mem_safe_blocks _ _ _ s0` >>
  `fresh_vars_wrt (initial_compile_state "__deploy") s0` by
    (simp[Abbr `s0`] >> irule ctor_prefix_entry_fresh >> metis_tac[]) >>
  `~s0.vs_halted` by
    (drule ctor_prefix_entry_not_halted >> simp[Abbr `s0`]) >>
  `s0.vs_call_ctx.cc_callvalue <> 0w` by
    (drule_all ctorDeployMemoryRunMemPrefixSourceTheory.ctor_prefix_source_obstruction >>
     strip_tac >> drule_all ctor_prefix_entry_value >> simp[Abbr `s0`]) >>
  `frag_exec_mem dunit.cu_context (initial_compile_state "__deploy") st_pay
    (\t. t = s0) (\t. F) (\r. ?t. r = Abort Revert_abort t)` by
    (irule ctor_prefix_payable_mem >> metis_tac[]) >>
  `!fuel. mem_safe_run fuel dunit.cu_context fn s0` by
    (drule frag_exec_mem_complete >>
     disch_then (qspecl_then [`fn`,`s0`] mp_tac) >>
     simp[Abbr `s0`, initial_compile_state_def]) >>
  `?bb. lookup_block "__deploy" fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
     qpat_x_assum `_ = emit_op CALLVALUE _ _` mp_tac >>
     simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, initial_compile_state_def, fn_has_code_def] >>
     rpt strip_tac >> gvs[IS_PREFIX_APPEND] >>
     Cases_on `bb.bb_instructions` >>
     gvs[phi_prefix_length_def, mk_inst_def]) >>
  gen_tac >> Cases_on `fuel` >- simp[Once mem_safe_blocks_def] >>
  `eval_phis s0 bb.bb_instructions = OK s0` by simp[eval_phis_no_phi] >>
  `lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb` by simp[Abbr `s0`] >>
  drule_all mem_safe_blocks_run >>
  simp[Abbr `s0`]
QED
