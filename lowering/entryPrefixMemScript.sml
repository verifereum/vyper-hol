(* Memory footprints of external entry prefixes. *)
Theory entryPrefixMem
Ancestors
  moduleLowering emitHelper compileEnv exprLoweringProps fragExec fragExecMem instMemFrontier venomInst list rich_list
  finite_map words venomExecSemantics venomState moduleLoweringProps
Libs
  wordsLib

Theorem compile_entry_checks_mem_ok:
  compile_entry_checks min_cds is_payable st = ((), st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem compile_entry_checks_pass_run[local]:
  compile_entry_checks min_cds is_payable st = ((), st') /\
  fresh_vars_wrt st s0 /\
  (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s0.vs_call_ctx.cc_calldata /\
  LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s0 = OK t /\
      vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0)
Proof
  strip_tac >>
  `min_cds < dimword (:256)` by decide_tac >>
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def] >>
  fs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[run_inst_seq_def, step_inst_base_def, mk_inst_def,
                   instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read0_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def] >>
  simp[vars_pc_only_def] >>
  (conj_tac
   >- (fs[fresh_vars_wrt_def] >> rpt strip_tac >> fs[]) >>
   rw[FLOOKUP_UPDATE] >> gvs[not_fresh_at_def])
QED

Theorem compile_entry_checks_structure[local]:
  compile_entry_checks min_cds is_payable st = ((), st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem compile_entry_checks_pass_mem:
  !min_cds is_payable st st' ctx s0.
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 /\
    (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
    min_cds <= LENGTH s0.vs_call_ctx.cc_calldata /\
    LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) ==>
    frag_exec_mem ctx st st' (\s. s = s0)
      (\t. vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0))
      (\r. F)
Proof
  rpt strip_tac >>
  drule compile_entry_checks_structure >> strip_tac >>
  (irule frag_exec_mem_run_inst_seq >> simp[] >>
   conj_tac >- metis_tac[compile_entry_checks_mem_ok] >>
   drule compile_entry_checks_pass_run >>
   disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
   qexists_tac `t` >>
   simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
   gvs[fresh_vars_wrt_def])
QED
