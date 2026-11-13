(* The default-return branch reads the actual returndata size. *)
Theory extcallReturnBranchMemory
Ancestors
  fragGasPathFrameMem exprSimConcatPath exprLoweringProps emitHelperProps
  exprLowering emitHelper compileEnv stmtSimProps loweringStateRelDefs
  fragExecMem fragGasSeqMem fragGasPathMem instMemFrontier memSafeRun
  venomExecSemantics venomState venomInst words list rich_list finite_map

val extcall_zero_test_statement =
  rhs (concl (SIMP_CONV bool_ss [LET_THM] ``emit_op RETURNDATASIZE [] sa = (rds,sm) /\
  emit_op ISZERO [rds] sm = (empty_op,sb) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  let x = STRING #"%" (toString sa.cs_next_var);
      y = STRING #"%" (toString (sa.cs_next_var+1));
      t = update_var y (bool_to_word (s.vs_returndata = []))
            (update_var x (n2w (LENGTH s.vs_returndata)) s)
  in
  empty_op = Var y /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id RETURNDATASIZE [] [x];
     mk_inst (sa.cs_next_id+1) ISZERO [Var x] [y]] /\
  run_inst_seq (emitted_insts sa sb) s = OK t``));

Theorem extcall_return_zero_test_run[local]:
  ^extcall_zero_test_statement
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read0_def, exec_pure1_def, bind_outputs_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, n2w_11, LENGTH_NIL]
QED

Theorem extcall_return_zero_test_mem:
  emit_op RETURNDATASIZE [] sa = (rds,sm) /\
  emit_op ISZERO [rds] sm = (empty_op,sb) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand empty_op t = SOME (bool_to_word (s.vs_returndata = [])) /\
    stmt_state_rel ctx func cenv cx es t /\ alloca_history func t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >> drule_all extcall_return_zero_test_run >>
  strip_tac >> gvs[] >>
  qabbrev_tac `u = update_var
    (STRING #"%" (toString (sa.cs_next_var+1)))
    (bool_to_word (s.vs_returndata = []))
    (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_returndata)) s)` >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> fs[same_blocks_def] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qspecl_then [`emitted_insts sa sb`, `s`, `u`, `ctx`, `func`, `bb`]
      mp_tac run_inst_seq_gas_path_mem >>
     fs[mk_inst_def, is_terminator_def, Abbr `u`]) >>
  suspend "frame"
QED

Resume extcall_return_zero_test_mem[frame]:
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (sa.cs_next_var+1)))` by
    (conj_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (simp[Abbr `u`] >> irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_update_var] >> rpt strip_tac >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    metis_tac[gas_path_mem_allocation_state] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, Abbr `u`, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >>
  fs[same_blocks_def, lookup_var_def, venom_state_component_equality, FLOOKUP_UPDATE]
QED

Finalise extcall_return_zero_test_mem

Theorem extcall_default_return_stages:
  compile_default_return_path ce rt dt buf result def addr skip mn mx info
    sa = (op,sb) ==>
  op = result /\
  ?rds empty_op dl cl xl sm sn s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 hi
   old_default old_decode old_exit.
    emit_op RETURNDATASIZE [] sa = (rds,sm) /\
    emit_op ISZERO [rds] sm = (empty_op,sn) /\
    fresh_label "extcall_default" sn = (dl,s1) /\
    fresh_label "extcall_decode" s1 = (cl,s2) /\
    fresh_label "extcall_exit" s2 = (xl,s3) /\
    emit_inst JNZ [empty_op; Label dl; Label cl] [] s3 = ((),s4) /\
    new_block dl s4 = (old_default,s5) /\
    compile_store_memory ce def result rt dt s5 = ((),s6) /\
    (if skip then comp_return () else compile_extcodesize_check addr)
      s6 = ((),s7) /\
    emit_inst JMP [Label xl] [] s7 = ((),s8) /\
    new_block cl s8 = (old_decode,s9) /\
    compile_return_value_decode mn mx s9 = (hi,s10) /\
    compile_abi_decode_to_buf result (Lit 0w) MLOAD buf hi info s10 = ((),s11) /\
    emit_inst JMP [Label xl] [] s11 = ((),s12) /\
    new_block xl s12 = (old_exit,sb)
Proof
  Cases_on `emit_op RETURNDATASIZE [] sa` >> rename1 `_ = (rds,sm)` >>
  Cases_on `emit_op ISZERO [rds] sm` >> rename1 `_ = (empty_op,sn)` >>
  Cases_on `fresh_label "extcall_default" sn` >> rename1 `_ = (dl,s1)` >>
  Cases_on `fresh_label "extcall_decode" s1` >> rename1 `_ = (cl,s2)` >>
  Cases_on `fresh_label "extcall_exit" s2` >> rename1 `_ = (xl,s3)` >>
  Cases_on `emit_inst JNZ [empty_op;Label dl;Label cl] [] s3` >>
  rename1 `_ = (ignored,s4)` >>
  Cases_on `new_block dl s4` >> rename1 `_ = (old_default,s5)` >>
  Cases_on `compile_store_memory ce def result rt dt s5` >>
  rename1 `_ = (ignored2,s6)` >>
  Cases_on `(if skip then comp_return () else compile_extcodesize_check addr) s6` >>
  rename1 `_ = (ignored3,s7)` >>
  Cases_on `emit_inst JMP [Label xl] [] s7` >> rename1 `_ = (ignored4,s8)` >>
  Cases_on `new_block cl s8` >> rename1 `_ = (old_decode,s9)` >>
  Cases_on `compile_return_value_decode mn mx s9` >> rename1 `_ = (hi,s10)` >>
  Cases_on `compile_abi_decode_to_buf result (Lit 0w) MLOAD buf hi info s10` >>
  rename1 `_ = (ignored5,s11)` >>
  Cases_on `emit_inst JMP [Label xl] [] s11` >> rename1 `_ = (ignored6,s12)` >>
  Cases_on `new_block xl s12` >>
  gvs[compile_default_return_path_def,comp_bind_def,comp_ignore_bind_def,
      comp_return_def] >> metis_tac[]
QED
