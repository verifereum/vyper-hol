(* Pointer-safe rejection before calldata decoding. *)
Theory entryChecksPtr
Ancestors
  ptrSafeRun ptrDiscipline fragExec entryChecksProps moduleLowering
  compileEnv emitHelper emitHelperProps venomExecSemantics venomInst venomState
  list finite_map words contextCodegenRel codegenRel

Theorem value_check_ptr_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id CALLVALUE [] [cv]) /\
  get_instruction bb (s.vs_inst_idx + 1) =
    SOME (mk_inst (id+1) ISZERO [Var cv] [nv]) /\
  get_instruction bb (s.vs_inst_idx + 2) =
    SOME (mk_inst (id+2) ASSERT [Var nv] []) /\
  cv <> nv /\ s.vs_call_ctx.cc_callvalue <> 0w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, exec_read0_def, update_var_def]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       exec_read0_def, is_terminator_def, ghost_step_def] >>
  simp[Once ptr_safe_block_def, update_var_def, arithmeticTheory.ADD1] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, exec_pure1_def, eval_operand_def,
           lookup_var_def, FLOOKUP_UPDATE, step_taint_def, op_taint_def,
           allocas_from_def, update_var_def, out_taint_def, set_var_taint_def] >>
      gvs[allocas_from_def]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       exec_pure1_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       is_terminator_def, ghost_step_def, update_var_def] >>
  qmatch_goalsub_abbrev_tac `ptr_safe_block _ _ _ _ _ _ G2 tn2 _ _` >>
  simp[Once ptr_safe_block_def] >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke, step_inst_base_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       Abbr `tn2`, step_taint_def, op_taint_def, out_taint_def,
       set_var_taint_def, update_var_def, allocas_from_def] >>
  gvs[allocas_from_def]
QED

Theorem compile_entry_checks_value_revert_ptr_safe:
  compile_entry_checks min_cds F st = ((), st') /\
  fn_has_code st st' fn /\ ~block_is_terminated st /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  s.vs_call_ctx.cc_callvalue <> 0w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  `?tail. st'.cs_current_bb = st.cs_current_bb /\
     st'.cs_current_insts = st.cs_current_insts ++
       [mk_inst st.cs_next_id CALLVALUE [] ["%" ++ toString st.cs_next_var];
        mk_inst (st.cs_next_id + 1) ISZERO [Var ("%" ++ toString st.cs_next_var)]
          ["%" ++ toString (st.cs_next_var + 1)];
        mk_inst (st.cs_next_id + 2) ASSERT [Var ("%" ++ toString (st.cs_next_var + 1))] []] ++ tail` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     Cases_on `4 < min_cds` >>
     simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_assum `!i. _` (qspec_then `0` assume_tac) >>
  qpat_assum `!i. _` (qspec_then `1` assume_tac) >>
  qpat_x_assum `!i. _` (qspec_then `2` assume_tac) >>
  gvs[] >>
  gen_tac >> irule value_check_ptr_safe >> simp[] >>
  qexistsl_tac [`"%" ++ toString st.cs_next_var`, `st.cs_next_id`,
                `"%" ++ toString (st.cs_next_var + 1)`] >>
  simp[ASCIInumbersTheory.toString_inj]
QED
