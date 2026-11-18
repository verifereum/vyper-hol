(* Installed nonpayable dispatch rejection, independent of source selection. *)
Theory dispatchedValuePrefix
Ancestors entryPrefixPtr fragGasOrigin fragGasPathMem gasCount memSafeRun
  instMemFrontier unitTransformDefs contextCodegenRel codegenRel entryValueRevertPtr entryDispatchPtr moduleLoweringProps moduleLowering
  compileEnv loweringStateRelDefs emitHelper fragExec ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState list finite_map words

Theorem installed_dispatch_value_reject_ptr:
  compile_selector_dispatch_linear selectors fallback st = ((),st') /\
  fn_has_code st st' fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = 0 /\ st.cs_current_insts = [] /\
  allocas_from lo ss /\ ~ctx_has_dalloca ctx /\
  ss.vs_call_ctx.cc_callvalue <> 0w /\
  compile_entry_checks min_cds F opened = ((),checked) /\
  fn_has_code opened checked fn /\ ~block_is_terminated opened /\
  opened.cs_current_insts = [] /\
  opened.cs_current_bb =
    linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback ==>
  !D PG G tn fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn ss
Proof
  strip_tac >> rpt gen_tac >>
  irule ptr_safe_blocks_nonphi_run >>
  reverse conj_tac
  >- (drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
      gvs[mk_inst_def]) >>
  gen_tac >> irule dispatch_nonpayable_check_ptr_safe >> simp[] >>
  qexistsl_tac [`checked`, `fallback`, `min_cds`, `opened`, `selectors`, `st`, `st'`] >>
  gvs[]
QED

Theorem scalar_edge_mem[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\ ~s.vs_halted /\
  step_inst_base inst s = OK t /\ ~t.vs_halted /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s ==>
  gas_path_mem_edge ctx fn s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> simp[gas_path_mem_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, mem_safe_step_non_invoke] >>
  metis_tac[]
QED


Theorem assert_revert_edge_mem[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ASSERT [Var nv] []) /\
  lookup_var nv s = SOME 0w /\ ~s.vs_halted ==>
  gas_path_mem ctx fn s 0
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >> irule (cj 3 gas_path_mem_rules) >>
  simp[exit_result_def, gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, gas_count_step_def, mem_safe_step_non_invoke,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       exit_result_def]
QED

Theorem value_check_origin_mem[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id CALLVALUE [] [cv]) /\
  get_instruction bb (s.vs_inst_idx + 1) =
    SOME (mk_inst (id+1) ISZERO [Var cv] [nv]) /\
  get_instruction bb (s.vs_inst_idx + 2) =
    SOME (mk_inst (id+2) ASSERT [Var nv] []) /\
  cv <> nv /\ s.vs_call_ctx.cc_callvalue <> 0w /\ ~s.vs_halted ==>
  ?preabort. vars_pc_only s preabort /\
    gas_path_mem ctx fn s 0
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var cv s.vs_call_ctx.cc_callvalue s with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = update_var nv 0w s1 with
    vs_inst_idx := SUC s1.vs_inst_idx` >>
  `gas_path_mem_edge ctx fn s 0 (OK s1)` by
    (simp[Abbr `s1`] >> irule scalar_edge_mem >>
     simp[update_var_def] >>
     simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
          exec_read0_def, update_var_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `gas_path_mem_edge ctx fn s1 0 (OK s2)` by
    (simp[Abbr `s2`] >> irule scalar_edge_mem >>
     simp[Abbr `s1`, update_var_def, arithmeticTheory.ADD1] >>
     simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure1_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `gas_path_mem ctx fn s2 0
      (Abort Revert_abort (revert_state (set_returndata [] s2)))` by
    (irule assert_revert_edge_mem >> simp[Abbr `s2`, Abbr `s1`, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1] >>
     qexistsl_tac [`id+2`, `nv`] >> simp[]) >>
  qexists_tac `s2` >> conj_tac
  >- simp[Abbr `s2`, Abbr `s1`, vars_pc_only_inst_idx,
          vars_pc_only_update_var, vars_pc_only_refl] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem installed_check_reject_mem[local]:
  compile_entry_checks mc F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  s.vs_current_bb = opened.cs_current_bb /\ s.vs_inst_idx = 0 /\
  s.vs_call_ctx.cc_callvalue <> 0w /\ ~s.vs_halted ==>
  ?preabort. vars_pc_only s preabort /\
    gas_path_mem ctx fn s 0
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))
Proof
  strip_tac >>
  `?tail. checked.cs_current_bb = opened.cs_current_bb /\
     checked.cs_current_insts = opened.cs_current_insts ++
       [mk_inst opened.cs_next_id CALLVALUE [] ["%" ++ toString opened.cs_next_var];
        mk_inst (opened.cs_next_id + 1) ISZERO
          [Var ("%" ++ toString opened.cs_next_var)]
          ["%" ++ toString (opened.cs_next_var + 1)];
        mk_inst (opened.cs_next_id + 2) ASSERT
          [Var ("%" ++ toString (opened.cs_next_var + 1))] []] ++ tail` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     Cases_on `4 < mc` >>
     simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `checked.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_assum `!i. _` (qspec_then `0` assume_tac) >>
  qpat_assum `!i. _` (qspec_then `1` assume_tac) >>
  qpat_x_assum `!i. _` (qspec_then `2` assume_tac) >>
  gvs[] >> irule value_check_origin_mem >> simp[] >>
  qexistsl_tac [`"%" ++ toString opened.cs_next_var`,
    `opened.cs_next_id`, `"%" ++ toString (opened.cs_next_var+1)`] >>
  simp[ASCIInumbersTheory.toString_inj]
QED

Theorem installed_dispatch_value_reject_origin:
  compile_selector_dispatch_linear selectors fallback st = ((),st') /\
  fn_has_code st st' fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = 0 /\ st.cs_current_insts = [] /\
  allocas_from lo ss /\ ~ctx_has_dalloca ctx /\
  ss.vs_call_ctx.cc_callvalue <> 0w /\
  compile_entry_checks min_cds F opened = ((),checked) /\
  fn_has_code opened checked fn /\ ~block_is_terminated opened /\
  opened.cs_current_insts = [] /\
  opened.cs_current_bb =
    linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback ==>
  ?preabort. vars_pc_only ss preabort /\
    gas_origin_path T explicit ctx fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))
Proof
  strip_tac >>
  `!bb. lookup_block
      (linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback)
      fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule_all compile_entry_checks_nonpayable_head >> strip_tac >>
     rpt strip_tac >> gvs[] >>
     Cases_on `bb.bb_instructions` >>
     gvs[get_instruction_def, phi_prefix_length_def]) >>
  `ss.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp ss)` by simp[] >>
  drule_all compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`ARB`, `ARB`, `ARB`] strip_assume_tac) >>
  `tt.vs_call_ctx = ss.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  `?preabort. vars_pc_only tt preabort /\
     gas_path_mem ctx fn tt 0
       (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    (irule installed_check_reject_mem >> simp[] >>
     qexistsl_tac [`checked`, `min_cds`, `opened`] >> simp[]) >>
  qexists_tac `preabort` >> conj_tac >- metis_tac[vars_pc_only_trans] >>
  irule gas_path_mem_zero_origin >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
