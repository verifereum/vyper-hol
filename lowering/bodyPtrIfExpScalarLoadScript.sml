Theory bodyPtrIfExpScalarLoad
Ancestors
  bodyPtrIfExpWordLocations exprSimPtrProps stmtAppendStorageRunPtr
  ptrSafeRun ptrDiscipline ghostPcTransportPtr venomInst venomState
  venomExecSemantics emitHelper exprLoweringProps contextCodegenRel
  compileEnv loweringStateRelDefs finite_map pred_set codegenRel fragExec bodyPtrDefs

Theorem ifexp_scalar_load_check:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ op_taint tn arg = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc [arg] [out]) s = OK (update_var out w s) ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [arg] [out]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> gvs[update_var_def]
QED

Theorem ifexp_scalar_load_taint:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) ==>
  step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem ifexp_emit_scalar_load_ptr_path:
  MEM opc [SLOAD;TLOAD;DLOAD] /\
  emit_op opc [arg] sm = (op,sb) /\ fn_has_code sm sb fn /\
  ~ctx_has_dalloca ctx /\ eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  step_inst_base
    (mk_inst sm.cs_next_id opc [arg] [STRING #"%" (toString sm.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s) ==>
  ?out G' tn'.
    op = Var out /\ out = STRING #"%" (toString sm.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                     op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id opc [arg] [STRING #"%" (toString sm.cs_next_var)]] /\
   op = Var (STRING #"%" (toString sm.cs_next_var)) /\
   (!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var))` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sm.cs_next_id opc [arg] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qexistsl [`out`,
    `step_prov PG G (mk_inst sm.cs_next_id opc [arg] [out]) (update_var out w s)`,
    `step_taint (mk_inst sm.cs_next_id opc [arg] [out]) s (update_var out w s) tn`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- (irule step_prov_out_none >> simp[mk_inst_def] >>
              irule out_prov_other_none >> gvs[mk_inst_def]) >>
  `step_taint (mk_inst sm.cs_next_id opc [arg] [out]) s (update_var out w s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule ifexp_scalar_load_taint >> metis_tac[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[scalar_step_old_prov]
QED

Resume ifexp_emit_scalar_load_ptr_path[path]:
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  irule gas_path_ptr_one_step >>
  simp[mk_inst_def, update_var_def] >>
  gvs[is_terminator_def] >>
  simp[GSYM mk_inst_def] >>
  irule ifexp_scalar_load_check >> simp[] >> metis_tac[]
QED

Finalise ifexp_emit_scalar_load_ptr_path
