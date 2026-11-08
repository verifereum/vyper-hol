Theory nonreentrantEntry
Ancestors
  list rich_list words finite_map
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  moduleLoweringProps fragExec fragExecMem instMemFrontier
  venomState venomInst venomExecSemantics

Theorem transient_lock_structure[local]:
  compile_nonreentrant_lock nkey T is_view st = ((), st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. MEM i.inst_opcode [TLOAD; EQ; ISZERO; ASSERT; TSTORE])
    (emitted_insts st st')
Proof
  strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_view` >> gvs[comp_return_def] >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC, mk_inst_def]
QED

Theorem lock_opcode[local]:
  (mk_inst id opc ops outs).inst_opcode = opc
Proof
  simp[mk_inst_def]
QED

Theorem transient_lock_steps[local]:
  step_inst_base (mk_inst id EQ ops outs) s =
    exec_pure2 (\x y. bool_to_word (x = y)) (mk_inst id EQ ops outs) s /\
  step_inst_base (mk_inst id ISZERO ops outs) s =
    exec_pure1 (\x. bool_to_word (x = 0w)) (mk_inst id ISZERO ops outs) s /\
  step_inst_base (mk_inst id TLOAD ops outs) s =
    exec_read1 tload (mk_inst id TLOAD ops outs) s /\
  step_inst_base (mk_inst id TSTORE ops outs) s =
    (if s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands ops s) then
       Abort ExHalt_abort (halt_state (set_returndata [] s))
     else exec_write2 tstore (mk_inst id TSTORE ops outs) s) /\
  step_inst_base (mk_inst id ASSERT [a] []) s =
    (case eval_operand a s of
       SOME c => if c = 0w then
         Abort Revert_abort (revert_state (set_returndata [] s)) else OK s
     | NONE => Error "undefined operand")
Proof
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[lock_opcode]) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[lock_opcode]) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[lock_opcode] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[lock_opcode] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[mk_inst_def]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[lock_opcode] >>
  simp[mk_inst_def]
QED

Theorem transient_lock_run[local]:
  compile_nonreentrant_lock nkey T is_view st = ((), st') /\
  fresh_vars_wrt st s0 /\ (~is_view ==> ~s0.vs_call_ctx.cc_static) ==>
  (?t. run_inst_seq (emitted_insts st st') s0 = OK t /\
       tload (n2w nkey) s0 <> 1w /\
       vars_pc_only (if is_view then s0 else tstore (n2w nkey) 1w s0) t /\
       fresh_vars_wrt st' t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0)) \/
  (?t. run_inst_seq (emitted_insts st st') s0 = Abort Revert_abort t /\
       tload (n2w nkey) s0 = 1w /\ t.vs_returndata = [] /\
       t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas /\
       t.vs_alloca_next = s0.vs_alloca_next)
Proof
  strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_view` >> gvs[comp_return_def] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  simp[run_inst_seq_def, transient_lock_steps, step_EQ, step_ISZERO] >>
  simp[exec_read1_def, exec_write2_def, exec_pure1_def, exec_pure2_def, mk_inst_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       tload_def, contract_transient_def] >>
  Cases_on `tload (n2w nkey) s0 = 1w` >>
  gvs[tload_def, contract_transient_def, bool_to_word_def,
      revert_state_def, set_returndata_def, tstore_def, vars_pc_only_def] >>
  conj_tac
  >- (gvs[fresh_vars_wrt_def] >> rpt strip_tac >> gvs[]) >>
  rw[FLOOKUP_UPDATE] >> gvs[not_fresh_at_def] >>
  gvs[fresh_vars_wrt_def] >> rpt strip_tac >> gvs[]
QED

Theorem lock_opcodes_mem_ok[local]:
  !is s. EVERY (\i. MEM i.inst_opcode [TLOAD; EQ; ISZERO; ASSERT; TSTORE]) is ==>
    run_inst_seq_mem_ok is s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt gen_tac >> disch_tac >>
  conj_tac
  >- (irule below_frontier_no_ranges >> gvs[]) >>
  conj_tac >- (irule memSafeRunTheory.inst_dload_in_section_other >> gvs[]) >>
  Cases_on `step_inst_base h s` >> simp[]
QED

Theorem transient_lock_mem_ok[local]:
  compile_nonreentrant_lock nkey T is_view st = ((), st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> irule lock_opcodes_mem_ok >>
  drule transient_lock_structure >> simp[]
QED

(* Transient locks leave the memory and allocation frame intact. A view
   checks the same lock but never acquires it, so only a non-view lock
   needs a non-static frame for its TSTORE. *)
Theorem compile_nonreentrant_lock_frag_mem:
  !ctx nkey is_view st st' s0.
    compile_nonreentrant_lock nkey T is_view st = ((), st') /\
    fresh_vars_wrt st s0 /\ (~is_view ==> ~s0.vs_call_ctx.cc_static) ==>
    frag_exec_mem ctx st st' (\s. s = s0)
      (\t. tload (n2w nkey) s0 <> 1w /\
           vars_pc_only (if is_view then s0
                         else tstore (n2w nkey) 1w s0) t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==>
                lookup_var x t = lookup_var x s0))
      (\r. tload (n2w nkey) s0 = 1w /\
           ?t. r = Abort Revert_abort t /\ t.vs_returndata = [] /\
               t.vs_memory = s0.vs_memory /\
               t.vs_allocas = s0.vs_allocas /\
               t.vs_alloca_next = s0.vs_alloca_next)
Proof
  rpt strip_tac >>
  drule transient_lock_structure >> strip_tac >>
  irule frag_exec_mem_run_inst_seq >> simp[] >>
  reverse conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  conj_tac
  >- (drule transient_lock_mem_ok >> simp[]) >>
  drule_all transient_lock_run >> strip_tac
  >- (disj1_tac >> goal_assum $ drule_at Any >>
      simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
      gvs[fresh_vars_wrt_def]) >>
  disj2_tac >> goal_assum $ drule_at Any >> simp[]
QED
