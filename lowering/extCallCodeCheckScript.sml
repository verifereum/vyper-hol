(* Code-presence checks shared by external-call and return-default paths. *)
Theory extCallCodeCheck
Ancestors
  fragGasSeqPtr fragGasOriginPtr ptrDiscipline ptrSafeRun memSafeRun
  fragExec instMemFrontier unitTransformDefs codegenRel contextCodegenRel
  exprSimSliceExtcode accountsRelProps vyperRuntimeAccounts
  exprLowering exprLoweringProps emitHelperProps emitHelper
  venomExecSemantics venomInst venomState compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vfmState list rich_list words finite_map

Theorem extcall_precheck_code_word:
  stmt_state_rel H ctx func cenv cx es s /\
  accounts_runtime_well_typed es.accounts ==>
  ((n2w (LENGTH (lookup_account target s.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_has_code target es.accounts)
Proof
  strip_tac >>
  `accounts_agree H cx es.accounts s.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `(lookup_account target es.accounts).code =
   (lookup_account target s.vs_accounts).code` by
    (drule accounts_agree_lookup >>
     disch_then (qspec_then `target` strip_assume_tac) >> simp[]) >>
  `LENGTH (lookup_account target es.accounts).code <= 24576` by
    fs[accounts_runtime_well_typed_def, account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target es.accounts).code < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  gvs[ext_call_has_code_def, NULL_EQ, wordsTheory.n2w_11,
      arithmeticTheory.LESS_MOD]
QED

Theorem extcall_codesize_check_run:
  compile_extcodesize_check addr_op sa = ((),sb) /\
  eval_operand addr_op s = SOME aw ==>
  ?t. t = update_var (STRING #"%" (toString sa.cs_next_var))
           (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s /\
    run_inst_seq (emitted_insts sa sb) s =
      if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w
      then Abort Revert_abort (revert_state (set_returndata [] t)) else OK t
Proof
  strip_tac >>
  qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       GSYM listTheory.APPEND_ASSOC] >>
  drule slice_extcodesize_step >>
  disch_then (qspecl_then [`STRING #"%" (toString sa.cs_next_var)`, `sa.cs_next_id`]
    assume_tac) >>
  qmatch_goalsub_abbrev_tac `update_var out cw s` >>
  `eval_operand (Var out) (update_var out cw s) = SOME cw` by
    simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `cw = 0w`
  >- (gvs[] >> drule_all step_ASSERT_revert >>
      disch_then (qspec_then `sa.cs_next_id + 1` assume_tac) >>
      gvs[run_inst_seq_def, mk_inst_def, is_terminator_def, Abbr `out`]) >>
  drule_all step_ASSERT_ok >>
  disch_then (qspec_then `sa.cs_next_id + 1` assume_tac) >>
  gvs[run_inst_seq_def, mk_inst_def, is_terminator_def, Abbr `out`, Abbr `cw`]
QED

Theorem extcall_codesize_check_shape:
  compile_extcodesize_check addr_op sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sb.cs_next_var = sa.cs_next_var + 1 /\ sb.cs_next_id = sa.cs_next_id + 2 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `cs_extends sa sb` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[listTheory.APPEND_ASSOC]) >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id EXTCODESIZE [addr_op]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `cs'.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def]
QED

Theorem extcall_extcodesize_exact_edge:
  emit_op EXTCODESIZE [addr] a = (op,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  ~ctx_has_dalloca ctx ==>
  ?out. op = Var out /\ ~not_fresh_at a out /\
    !D lo. allocas_from lo s ==> gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (update_var out
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst a.cs_next_id EXTCODESIZE [addr] [out])
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s),
       step_taint (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s) tn)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
    SOME (mk_inst a.cs_next_id EXTCODESIZE [addr]
      [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[not_fresh_at_def] >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `v = update_var (STRING #"%" (toString a.cs_next_var))
    (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s` >>
  `step_inst_base inst s = OK v` by
    simp[Abbr `inst`, Abbr `v`, slice_extcodesize_step] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (`inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, Abbr `v`, update_var_def] >>
     simp[Abbr `inst`, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def, Abbr `v`]
QED

