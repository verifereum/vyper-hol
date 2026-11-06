(* External-source slice instructions: offsets are scalar source positions,
   not pointers into the runtime memory provenance map. *)
Theory bodyPtrBytestringBuiltinsExternalSlice
Ancestors
  bodyPtrBytestringBuiltinsSlice ptrDiscipline fragExecPtr venomInst
  venomExecSemantics venomState bodyPtrDefs list words finite_map
  ptrSafeRun memLocDefs codegenRel contextCodegenRel
  emitHelper emitHelperProps compileEnv freshWrites fragGasPathPtr fragExec
  exprSimPtrProps

Theorem ptr_inst_ok_external_copy:
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst; start; cnt_op]) \/
   (opc = EXTCODECOPY /\ ops = [addr; Var dst; start; cnt_op] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand start s = SOME a /\ eval_operand cnt_op s = SOME n /\
  op_taint tn start = {} /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    fixed_source_write_range_def, eval_operand_def, mem_write_ops_def,
    mem_read_ops_def, sized_source_write_range_def, mk_inst_def,
    step_inst_non_invoke] >>
  rpt strip_tac >> gvs[] >>
  TRY (qpat_x_assum `step_inst_base _ _ = Halt _` mp_tac >>
       PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
       simp[eval_operand_def] >> NO_TAC) >>
  TRY (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
       PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
       simp[eval_operand_def, write_memory_with_expansion_def,
         write_memory_def, expand_memory_def] >> strip_tac >> gvs[] >> NO_TAC) >>
  spose_not_then strip_assume_tac >> gvs[] >>
  Cases_on `op = Var dst` >> gvs[] >>
  Cases_on `op = start` >> gvs[] >>
  Cases_on `op = cnt_op` >> gvs[] >>
  Cases_on `op = addr` >> gvs[]
QED

Theorem external_copy_ghost_frame:
  (opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY) ==>
  step_prov PG G (mk_inst id opc ops []) t = G /\
  (step_taint (mk_inst id opc ops []) s t tn).t_var = tn.t_var /\
  (step_taint (mk_inst id opc ops []) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops []) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops []) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> gvs[step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, set_var_taint_def, out_taint_def, store_taint_def,
    imm_taint_def, adopt_reset_def, mem_taint_def, mk_inst_def,
    DRESTRICT_UNIV]
QED

(* Replay boundary: the semantic copy equation is supplied by the S1 run;
   pointer checks and counted execution are established independently. *)
Theorem emit_external_copy_counted:
  emit_void opc ops sa = ((),sb) /\ fn_has_code sa sb fn /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst; start; cnt_op]) \/
   (opc = EXTCODECOPY /\ ops = [addr; Var dst; start; cnt_op] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand start s = SOME a /\ eval_operand cnt_op s = SOME n /\
  op_taint tn start = {} /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s =
    OK (write_memory_with_expansion dest bytes s) ==>
  !D PG. ?t tn'.
    t = (write_memory_with_expansion dest bytes s) with
      vs_inst_idx := SUC s.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t) /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers G tn' root t cap) /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> rpt gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc ops []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst sa.cs_next_id opc ops []) s` by
    (irule ptr_inst_ok_external_copy >> metis_tac[]) >>
  `opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY` by metis_tac[] >>
  qabbrev_tac `u = write_memory_with_expansion dest bytes s` >>
  qabbrev_tac `tn' = step_taint (mk_inst sa.cs_next_id opc ops []) s u tn` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_prov PG G (mk_inst sa.cs_next_id opc ops []) u = G /\
   tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (simp_tac pure_ss [Abbr `tn'`] >> metis_tac[external_copy_ghost_frame]) >>
  `~u.vs_halted` by
    simp[Abbr `u`, write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t)` by
    (simp_tac pure_ss [Abbr `t`, Abbr `tn'`] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     `(mk_inst sa.cs_next_id opc ops []).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst sa.cs_next_id opc ops []).inst_opcode /\
      (mk_inst sa.cs_next_id opc ops []).inst_opcode <> GAS` by
       (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
     drule_all gas_path_ptr_one_step >>
     disch_then (qspec_then `PG` mp_tac) >> simp[mk_inst_def]) >>
  qexistsl_tac [`t`,`tn'`] >> simp[] >>
  simp[Abbr `t`, Abbr `u`, ptr_covers_def, op_taint_def, lookup_var_def,
    write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED


Theorem external_size_inst_check:
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem external_size_ghost:
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  LENGTH ops <= 1 ==>
  step_prov PG G (mk_inst id opc ops [out]) t = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s t tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, mem_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mk_inst_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, range_bytes_def,
    taint_component_equality] >>
  Cases_on `ops` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `eval_operand h s` >> simp[]
QED

Theorem emit_external_size_counted:
  emit_op opc ops sa = (op,sb) /\ fn_has_code sa sb fn /\
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  !D PG. ?out t G' tn'.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    t = (update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx /\
    G' = DRESTRICT G (COMPL {out}) /\
    tn' = (tn with t_var := tn.t_var |+ (out,{})) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand op t = SOME w /\ op_prov G' op = NONE /\ op_taint tn' op = {} /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (!p cap. p <> out /\ ptr_covers G tn p s cap ==> ptr_covers G' tn' p t cap)
Proof
  strip_tac >> rpt gen_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var out w s` >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id opc ops [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `u.vs_requests = s.vs_requests /\ ~u.vs_halted /\
   u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    simp[Abbr `u`, update_var_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst sa.cs_next_id opc ops [out]) s` by
    (irule external_size_inst_check >> metis_tac[]) >>
  `step_prov PG G (mk_inst sa.cs_next_id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst sa.cs_next_id opc ops [out]) s u tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule external_size_ghost >> simp[]) >>
  `(mk_inst sa.cs_next_id opc ops [out]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst sa.cs_next_id opc ops [out]).inst_opcode /\
   (mk_inst sa.cs_next_id opc ops [out]).inst_opcode <> GAS` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all gas_path_ptr_one_step >> disch_then (qspec_then `PG` mp_tac) >>
  simp[] >> strip_tac >>
  simp[Abbr `u`, Abbr `out`, eval_operand_def, update_var_def, lookup_var_def,
    op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[ptr_covers_def, op_taint_def, update_var_def, lookup_var_def,
    FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
