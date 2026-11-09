(* Counted execution of emitted return sequences. *)
Theory bodyIntCallFamStmtReturnStackRun
Ancestors
  bodyIntCallFamStmtReturnStackPath emitHelper compileEnv fragExec
  stmtSimReturn stmtLowering exprLoweringProps
  venomExecSemantics venomState venomInst list rich_list

Theorem emitted_seq_values_ret_path:
  emit_inst RET (ops ++ [rpc]) [] sm = ((),sb) /\
  sm.cs_current_insts = sa.cs_current_insts ++ code /\
  sm.cs_current_bb = sa.cs_current_bb /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK u /\
  u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
  eval_operands ops u = SOME vals /\ eval_operand rpc u = SOME pc ==>
  gas_path ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|>
       (u with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
      (code ++ [mk_inst sm.cs_next_id RET (ops ++ [rpc]) []])` by
    gvs[emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
        APPEND_ASSOC] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (fs[fragExecTheory.fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[IS_PREFIX_APPEND]) >>
  irule run_inst_seq_values_ret_path >> simp[] >>
  qexistsl_tac [`sm.cs_next_id`, `ops`, `pc`, `rpc`] >>
  simp[] >> first_x_assum (qspec_then `LENGTH code` mp_tac) >>
  simp[EL_APPEND_EQN, GSYM arithmeticTheory.ADD_COMM] >> gvs[]
QED

Theorem compile_internal_return_stack_path:
  compile_internal_return ce (SOME src) rpc n ty sty tys buf sa = ((),sb) /\
  0 < n /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME w /\ eval_operand rpc s = SOME pc ==>
  ?k t. gas_path ctx func s k
      (IntRet <|iret_values := if tys = [] then [w]
                             else tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> Cases_on `tys = []`
  >- (gvs[compile_internal_return_def] >>
      `gas_path ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) []))
        (IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|>
           (s with vs_inst_idx := s.vs_inst_idx + LENGTH ([]:instruction list)))` by
        (irule emitted_seq_values_ret_path >> simp[run_inst_seq_def] >>
         qexistsl_tac [`[src]`, `pc`, `rpc`, `sa`, `sb`, `sa`] >>
         simp[run_inst_seq_def, eval_operands_def]) >>
      qpat_x_assum `s.vs_inst_idx = _` (SUBST_ALL_TAC o SYM) >>
      qexistsl_tac [`0`, `s`] >> gvs[venom_state_component_equality]) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_load_tuple_elements ce src tys 0 sa = (ops,sm)` >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  `eval_operand rpc t = SOME pc` by
    (`eval_operand rpc t = eval_operand rpc s` suffices_by simp[] >>
     irule eval_operand_old_vars >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted` by
    fs[same_blocks_def] >>
  drule_all emitted_seq_values_ret_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS)
                         (emitted_insts sa sm))`,
                `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)`] >>
  gvs[venom_state_component_equality, lookup_var_def]
QED
