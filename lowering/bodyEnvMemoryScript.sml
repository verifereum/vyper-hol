(* Ordinary environment reads: actual no-memory opcode execution. *)
Theory bodyEnvMemory
Ancestors
  bodyUnopMemory bodyMemoryDefs bodyMemoryPreds exprSimDefs exprSimLeaves exprSimHyps
  fragExecMem instMemFrontier allocaHistoryFragment emitHelperProps
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec valueEncoding valueEncodingProofs vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperTyping vyperTypeSystem

Theorem body_env_read_frag_mem:
  emit_op opc [] sm = (dst,sn) /\ ~is_terminator opc /\ opc <> INVOKE /\
  (!s. inst_mem_below_frontier
    (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s) /\
  (!s. stmt_state_rel ctx func cenv cx es s ==>
    step_inst_base (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s)) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand dst s = SOME w /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand dst s = SOME w /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def] >>
  disj1_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `run_inst_seq (emitted_insts sm sn) entry = OK (update_var out w entry)` by
    simp[run_inst_seq_def, Abbr `out`] >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w entry)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  `(?bb rest. lookup_block entry.vs_current_bb func.fn_blocks = SOME bb /\
      DROP entry.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    entry.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def]) >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qexists_tac `update_var out w entry` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  gvs[Abbr `out`, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem body_env_frag_mem[local]:
  item <> PrevHash /\ item <> MsgGas /\
  compile_env_var item sa = (op,sb) /\
  evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME (val_to_w256 v) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                lookup_var z s = SOME w) /\
         s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
         s.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> Cases_on `item` >>
  gvs[compile_env_var_def, vyperContextTheory.evaluate_builtin_def] >>
  irule body_env_read_frag_mem >> simp[] >> HINT_EXISTS_TAC >>
  simp[is_terminator_def] >>
  rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
  gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
      val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem compile_env_body_sim_mem:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_mem_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[vyperContextTheory.evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  drule_all body_env_frag_mem >>
  disch_then (qspecl_then [`s0`, `ctx`, `expr_exit (INL v)`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >> disch_then irule >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       locals_kept_mem] >> rpt strip_tac >> simp[]
QED

Theorem compile_env_body_vv_sim_mem:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var item sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_env_body_sim_mem >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ENV_MEMORY_AUDIT OK\n"
     else raise Fail "environment memory inherited admission"
  end) [body_env_read_frag_mem, body_env_frag_mem,
        compile_env_body_sim_mem, compile_env_body_vv_sim_mem];
