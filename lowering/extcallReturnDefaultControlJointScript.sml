(* Joint routing edges for the default-return shell. *)
Theory extcallReturnDefaultControlJoint
Ancestors
  extcallReturnDefaultWordJoint extcallReturnDefaultRouting fragGasCopyLoop
  externalEntryProps context emitHelper emitHelperProps fragExec fragExecPtr venomMemDefs venomState venomInst
  venomExecSemantics ptrDiscipline compileEnv ptrSafeRun contextCodegenRel codegenRel
  exprLoweringProps list fragGasSeqPtr fragExecMem bodyPtrDefs

Theorem return_default_join_joint:
  emit_inst JMP [Label lbl] [] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >> gen_tac >>
  drule_all emitted_jump_common_instruction >> strip_tac >>
  irule copy_jmp_origin_ptr >> simp[] >> qexists_tac `a.cs_next_id` >> simp[]
QED

Theorem return_default_select_joint:
  emit_inst JNZ [test;Label yes;Label no] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand test s = SOME (if empty then 1w else 0w) /\
  op_taint tn test = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if empty then yes else no) s),G,tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule copy_jump_origin_ptr >> simp[] >>
  qexists_tac `mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []` >>
  simp[mk_inst_def] >>
  conj_tac >- (Cases_on `empty` >> simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    allocas_from_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
    GSYM op_taint_def] >>
  conj_tac >- (gen_tac >> Cases_on `op = test` >> gvs[] >> Cases_on `op` >> gvs[op_taint_def]) >>
  Cases_on `empty` >> simp[GSYM mk_inst_def, step_inst_non_invoke,
    step_inst_base_opcode_eqs, mk_inst_def, jump_to_def]
QED

(* Both test instructions share one concrete operational and ghost run. *)
Theorem return_default_test_joint:
  emit_op RETURNDATASIZE [] a = (rds,m) /\
  emit_op ISZERO [rds] m = (test,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
    eval_operand test u = SOME (if s.vs_returndata = [] then 1w else 0w) /\
    op_taint tm test = {} /\
    H = DRESTRICT (DRESTRICT G
      (COMPL {STRING #"%" (toString a.cs_next_var)}))
      (COMPL {STRING #"%" (toString m.cs_next_var)}) /\
    tm = tn with t_var :=
      (tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})) |+
        (STRING #"%" (toString m.cs_next_var),{}) /\
    u = (update_var (STRING #"%" (toString m.cs_next_var))
      (if s.vs_returndata = [] then 1w else 0w)
      (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH s.vs_returndata)) s))
      with vs_inst_idx := LENGTH b.cs_current_insts
Proof
  strip_tac >>
  drule_all return_default_test_run >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `y = STRING #"%" (toString m.cs_next_var)` >>
  `rds = Var x /\ test = Var y /\
   b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id RETURNDATASIZE [] [x];
      mk_inst m.cs_next_id ISZERO [Var x] [y]] /\
   emitted_insts a b = [mk_inst a.cs_next_id RETURNDATASIZE [] [x];
      mk_inst m.cs_next_id ISZERO [Var x] [y]]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, Abbr `x`, Abbr `y`,
      emitted_insts_def] >>
     simp[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH b.cs_current_insts`,
    `DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})`,
    `tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})`] >>
  conj_tac >- suspend "path" >>
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
    eval_operand_def, lookup_var_def]
QED
Resume return_default_test_joint[path]:
  gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  conj_tac >- simp[] >>
  qexistsl_tac [`emitted_insts a b`, `a`] >> simp[is_terminator_def] >>
  conj_tac >- (simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_read0_def, exec_pure1_def,
    eval_operands_def, eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]) >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[mk_inst_def] >> simp[] >>
  qexists_tac `0` >> simp[] >>
  simp[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read0_def, exec_pure1_def, eval_operands_def, eval_operand_def,
    lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def,
    exec_pure1_def, eval_operands_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
    store_taint_def, imm_taint_def, range_bytes_def,
    finite_mapTheory.FLOOKUP_DEF, SF CONJ_ss] >>
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE, taint_component_equality]
QED
Finalise return_default_test_joint

Theorem return_default_shell_joint:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] a5 = ((),a6) /\
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
    H = DRESTRICT (DRESTRICT G
      (COMPL {STRING #"%" (toString a.cs_next_var)}))
      (COMPL {STRING #"%" (toString a1.cs_next_var)}) /\
    tm = tn with t_var :=
      (tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})) |+
        (STRING #"%" (toString a1.cs_next_var),{}) /\
    u = jump_to (if s.vs_returndata = [] then dl else cl)
      ((update_var (STRING #"%" (toString a1.cs_next_var))
        (if s.vs_returndata = [] then 1w else 0w)
        (update_var (STRING #"%" (toString a.cs_next_var))
          (n2w (LENGTH s.vs_returndata)) s))
        with vs_inst_idx := LENGTH a2.cs_current_insts)
Proof
  strip_tac >> drule_all return_default_test_joint >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`jump_to (if s.vs_returndata = [] then dl else cl) u`, `H`, `tm`] >>
  simp[] >> gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,H,tm) []
    (OK (jump_to (if s.vs_returndata = [] then dl else cl) u),H,tm)` by
    (irule return_default_select_joint >> simp[] >>
     qexistsl_tac [`a5`, `a6`, `test`] >> simp[] >>
     gvs[fresh_label_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
       update_var_def, allocas_from_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >> simp[] >>
  disch_then irule >> gvs[]
QED
