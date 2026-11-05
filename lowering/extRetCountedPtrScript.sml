Theory extRetCountedPtr
Ancestors
  extRetCountedProbePtr entryHaltPtr fragGasPathPtr fragExec
  stmtLowering compileEnv emitHelper contextCodegenRelProps
  loweringHalt ptrSafeRun ptrDiscipline gasCount venomExecSemantics
  fragExecPtr venomInst venomState

Theorem compile_return_none_external_gas_path_ptr:
  compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G tn
    (Halt (halt_state (s with vs_returndata := [])))
Proof
  strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_inst_def,
          fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule stop_gas_path_ptr >> simp[] >>
  qexists_tac `st.cs_next_id` >>
  qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]
QED

Theorem gas_path_ptr_halt_base:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = Halt t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (Halt t)
Proof
  strip_tac >> irule (cj 3 gas_path_ptr_rules) >>
  simp[exit_result_def] >>
  `step_inst 0 ctx i s = Halt t` by simp[step_inst_non_invoke] >>
  asm_rewrite_tac[gas_path_ptr_edge_def] >>
  qexistsl_tac [`0`, `bb`, `i`, `Halt t`] >>
  simp[gas_count_step_def, ptr_safe_step_def, exit_result_def]
QED

Theorem return_zero_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [op; Lit 0w] []) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (set_returndata [] s)))
Proof
  strip_tac >> irule gas_path_ptr_halt_base >> simp[] >>
  reverse conj_tac
  >- (irule ptr_inst_ok_return_zero >> simp[] >> metis_tac[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED

Theorem return_lit_size_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [Var p; Lit n] []) /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s (w2n n) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n w <= j /\ j < w2n w + w2n n ==> j NOTIN tn.t_mem) ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (set_returndata
      (TAKE (w2n n) (DROP (w2n w) s.vs_memory ++ REPLICATE (w2n n) 0w)) s)))
Proof
  strip_tac >> irule gas_path_ptr_halt_base >> simp[] >>
  reverse conj_tac
  >- (irule ptr_inst_ok_return >> simp[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED
