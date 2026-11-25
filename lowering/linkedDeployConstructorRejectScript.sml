(* Safety of the constructor entry when its non-payable check reverts. *)
Theory linkedDeployConstructorReject
Ancestors
  ctorDeployRejectValue ctorDeployMemoryRunPtrPrefix entryDispatchMem
  fragGasPathMem fragExecMem fragExec venomInst venomState venomExecProofs venomExecSemantics
  ptrDiscipline finite_map list

Theorem linked_deploy_constructor_reject_prefix:
  venomInst$lookup_block "__deploy" fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst 0 CALLVALUE [] ["%0"];
     mk_inst 1 ISZERO [Var "%0"] ["%1"];
     mk_inst 2 ASSERT [Var "%1"] []] ++ tail /\
  vs.vs_call_ctx.cc_callvalue <> 0w /\ ~vs.vs_halted /\
  vs.vs_allocas = FEMPTY /\ (ctx_has_dalloca ctx ==> allocas_below_fmp vs) ==>
  ?post.
    gas_path_mem ctx fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
      0 (Abort Revert_abort post) /\
    (!fuel. mem_safe_blocks fuel ctx fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) /\
    (!fuel. ptr_safe_blocks D cap fuel ctx fn [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  qabbrev_tac `entry = vs with
    <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `entry`] >>
  `entry.vs_inst_idx = 0 /\ ~entry.vs_halted /\
   entry.vs_call_ctx.cc_callvalue <> 0w /\ entry.vs_allocas = FEMPTY /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp entry)` by
    fs[Abbr `entry`, allocas_below_fmp_def] >>
  `?post. gas_path_mem ctx fn entry 0 (Abort Revert_abort post)` by
    (irule nonpayable_check_zero_path >> simp[] >>
     qexistsl_tac [`0`,`1`,`2`,`"%0"`,`"%1"`] >> simp[]) >>
  qexists_tac `post` >> asm_rewrite_tac[] >> conj_tac
  >- (drule gas_path_mem_exec >> simp[] >> strip_tac >>
      `!fuel. mem_safe_run fuel ctx fn entry` by
        (irule mem_safe_run_all_fuel >> goal_assum (drule_at Any) >> simp[]) >>
      irule mem_safe_blocks_no_phi >> conj_tac
      >- (`entry with vs_inst_idx := 0 = entry` by simp[Abbr `entry`] >> simp[]) >>
      qexists_tac `bb` >>
      `phi_prefix_length bb.bb_instructions = 0` by
        simp[phi_prefix_length_def, mk_inst_def] >>
      simp[eval_phis_no_phi, phi_prefix_length_def, mk_inst_def]) >>
  irule nonpayable_check_ptr_safe >> simp[] >>
  qexistsl_tac [`0`,`1`,`2`,`"%0"`,`"%1"`] >> simp[]
QED
