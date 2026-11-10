(* Memory paths exposed at the internal-return compiler boundary. *)
Theory internalReturnCompileMem
Ancestors
  internalReturnSuffixMem internalReturnTupleMem internalReturnBytestringMem
  internalReturnPathMem stmtLowering compileEnv fragGasPathMem
  fragExec venomExecSemantics venomState stmtSimReturn emitHelperProps
  exprLoweringProps internalReturnTerminalMem stmtSimReturnWiden exprSimBufferStore valueCopyBytes list rich_list

Theorem compile_internal_return_memory_path_mem:
  compile_internal_return ce (SOME src) (Var rpc) 0 ty sty elems
    (SOME dst) sa = ((),sb) /\
  (sty = ty \/ is_bytestring_type ty /\ type_widens_to (get_tenv cx) sty ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx sty v src s /\ expr_store_bound cx sty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n d + type_memory_size tv + 64 < dimword (:256) /\
  eval_operand dst s = SOME d /\ lookup_var rpc s = SOME pc /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  not_fresh_at sa rpc /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  frag_exec ctx sa sb P (\t. F) R /\ P s ==>
  ?t. gas_path_mem ctx func s 0
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
      R (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s` by
    metis_tac[return_bytestring_expr_rel, internal_return_bytestring_store_bound] >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, compile_store_memory_bytestring_src,
       comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory ce src dst ty ty sa` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  drule_all internal_return_memory_suffix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  irule internal_return_path_post >> simp[exit_result_def] >>
  metis_tac[]
QED

Theorem compile_internal_return_void_path_mem:
  compile_internal_return ce NONE (Var rpc) cnt ty sty elems rb sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var rpc s = SOME pc /\
  frag_exec ctx sa sb P (\t. F) R /\ P s ==>
  gas_path_mem ctx func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s) /\
  R (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  `emit_inst RET ([] ++ [Var rpc]) [] sa = ((),sb)` by
    (gvs[compile_internal_return_def, AllCaseEqs()] >>
     Cases_on `rb` >> gvs[]) >>
  conj_asm1_tac
  >- (irule emit_internal_ret_path_mem >> simp[] >>
      qexistsl_tac [`[]`, `pc`, `rpc`, `sa`, `sb`] >>
      simp[eval_operands_def]) >>
  irule internal_return_path_post >> simp[exit_result_def] >> metis_tac[]
QED

Theorem compile_internal_return_word_path_mem:
  compile_internal_return ce (SOME src) (Var rpc) cnt ty sty [] rb sa = ((),sb) /\
  0 < cnt /\ eval_operand src s = SOME w /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var rpc s = SOME pc /\
  frag_exec ctx sa sb P (\t. F) R /\ P s ==>
  gas_path_mem ctx func s 0
    (IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|> s) /\
  R (IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  `emit_inst RET ([src] ++ [Var rpc]) [] sa = ((),sb)` by
    gvs[compile_internal_return_def] >>
  conj_asm1_tac
  >- (irule emit_internal_ret_path_mem >> simp[] >>
      qexistsl_tac [`[src]`, `pc`, `rpc`, `sa`, `sb`] >>
      simp[eval_operands_def]) >>
  irule internal_return_path_post >> simp[exit_result_def] >> metis_tac[]
QED

Theorem compile_internal_return_tuple_register_path_mem:
  compile_internal_return ce (SOME src) (Var rpc) cnt ty sty tys rb sa = ((),sb) /\
  0 < cnt /\ tys <> [] /\
  EVERY (\ty. type_memory_bytes ce ty = 32) tys /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa rpc /\
  eval_operand src s = SOME w /\ lookup_var rpc s = SOME pc /\
  w2n w + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + 32 * LENGTH tys <= dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?vs n. gas_path_mem ctx func s 0
    (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
              iret_adopt_fmp := NONE|>
      (s with <|vs_vars := vs; vs_inst_idx := n|>))
Proof
  strip_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def] >>
  Cases_on `compile_load_tuple_elements ce src tys 0 sa` >>
  rename1 `compile_load_tuple_elements _ _ _ _ _ = (ops,sm)` >>
  simp[] >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_load_tuple_elements_extends] >>
  `cs_extends sm sb` by metis_tac[cs_extends_emit_inst] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule internal_return_tuple_load_path_mem >>
  disch_then (qspecl_then [`w`, `s`, `func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t0)` >>
  `gas_path_mem ctx func t0 0
    (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
              iret_adopt_fmp := NONE|> t0)` by
    (irule emit_internal_ret_path_mem >> simp[Abbr `t0`] >>
     qexistsl_tac [`ops`, `pc`, `rpc`, `sm`, `sb`] >>
     gvs[same_blocks_def, eval_operands_vars_inst_idx, lookup_var_def]) >>
  `gas_path_mem ctx func s 0
    (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
              iret_adopt_fmp := NONE|> t0)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  metis_tac[Abbr `t0`]
QED

Theorem compile_internal_return_tuple_path_mem:
  compile_internal_return ce (SOME src) (Var rpc) cnt ty sty tys rb sa = ((),sb) /\
  0 < cnt /\ tys <> [] /\
  EVERY (\ty. type_memory_bytes ce ty = 32) tys /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa rpc /\
  eval_operand src s = SOME w /\ lookup_var rpc s = SOME pc /\
  w2n w + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + 32 * LENGTH tys <= dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  frag_exec ctx sa sb P (\t. F) R /\ P s ==>
  ?t. gas_path_mem ctx func s 0
    (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
              iret_adopt_fmp := NONE|> t) /\
    R (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >> drule_all compile_internal_return_tuple_register_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule internal_return_path_post >> simp[exit_result_def] >> metis_tac[]
QED

Theorem compile_internal_return_tuple_intret_mem:
  compile_internal_return ce (SOME src) (Var rpc) cnt ty sty tys rb sa = ((),sb) /\
  0 < cnt /\ tys <> [] /\
  EVERY (\ty. type_memory_bytes ce ty = 32) tys /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa rpc /\
  eval_operand src s = SOME w /\ lookup_var rpc s = SOME pc /\
  w2n w + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + 32 * LENGTH tys <= dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  state_rel func ce cx ee s /\
  intret_vals_match tv v (tuple_words ce w tys 0 s.vs_memory) ==>
  ?t. gas_path_mem ctx func s 0
    (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
              iret_adopt_fmp := NONE|> t) /\
    !tail. intret_q func ce cx tv v
      ((ee with gas_obs := tail) with scopes := [])
      (IntRet <|iret_values := tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >> drule_all compile_internal_return_tuple_register_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule internal_return_register_terminal >> simp[]
QED
