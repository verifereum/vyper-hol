(* External-source slice instructions: offsets are scalar source positions,
   not pointers into the runtime memory provenance map. *)
Theory bodyPtrBytestringBuiltinsExternalSlice
Ancestors
  bodyPtrBytestringBuiltinsSlice ptrDiscipline fragExecPtr venomInst
  venomExecSemantics venomState bodyPtrDefs list words finite_map
  ptrSafeRun memLocDefs codegenRel contextCodegenRel
  emitHelper emitHelperProps compileEnv freshWrites fragGasPathPtr fragExec
  exprSimPtrProps builtinBytes bodyPtrBytestringBuiltinsBuffer
  bodyPtrBytestringBuiltinsBounds bodyPtrBytestringBuiltinsSource

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
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s =
    OK (write_memory_with_expansion dest bytes s) ==>
  emit_void opc ops sa = ((),sb) /\ fn_has_code sa sb fn /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst; start; cnt_op]) \/
   (opc = EXTCODECOPY /\ ops = [addr; Var dst; start; cnt_op] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand start s = SOME a /\ eval_operand cnt_op s = SOME n /\
  op_taint tn start = {} /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
  ntac 2 strip_tac >> rpt gen_tac >>
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
    (!p cap. p <> out /\ ptr_covers G tn p s cap ==> ptr_covers G' tn' p t cap) /\
    (!x. x <> out ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t) /\
    sb.cs_next_var = SUC sa.cs_next_var /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ x <> out /\ lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (fresh_vars_wrt sa s ==> !arg v. eval_operand arg s = SOME v ==>
      eval_operand arg t = SOME v /\ op_prov G' arg = op_prov G arg /\
      op_taint tn' arg = op_taint tn arg) /\
    (fresh_vars_wrt sa s ==> !p cap. ptr_covers G tn p s cap ==>
      ptr_covers G' tn' p t cap) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> rpt gen_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sb.cs_next_var = SUC sa.cs_next_var /\
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
  simp[] >> strip_tac >> suspend "frames"
QED

Resume emit_external_size_counted[frames]:
  simp[Abbr `u`, Abbr `out`, eval_operand_def, update_var_def, lookup_var_def,
    op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[ptr_covers_def, op_taint_def, update_var_def, lookup_var_def,
    FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (gen_tac >> disch_tac >> fs[not_fresh_at_def] >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (disch_tac >> qx_gen_tac `arg` >> qx_gen_tac `v` >> disch_tac >>
      Cases_on `arg` >> gvs[eval_operand_def, lookup_var_def] >>
      rename1 `FLOOKUP s.vs_vars name = SOME v` >>
      `name <> STRING #"%" (toString sa.cs_next_var)` by
        (strip_tac >> gvs[fresh_vars_wrt_def] >>
         qpat_x_assum `!n. n >= sa.cs_next_var ==> _`
           (qspec_then `sa.cs_next_var` mp_tac) >> fs[FLOOKUP_DEF]) >>
      simp[FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[fresh_vars_wrt_def] >>
     qpat_x_assum `!n. n >= sa.cs_next_var ==> _`
       (qspec_then `sa.cs_next_var` mp_tac) >> fs[FLOOKUP_DEF]) >>
  simp[] >> metis_tac[]
QED
Finalise emit_external_size_counted

Theorem compile_slice_calldata_stages:
  compile_slice_calldata start len N sa = (out,sb) ==>
  ?s1 s2 s3 s4 data limit.
    compile_slice_out_buf N sa = ((out,data),s1) /\
    emit_op CALLDATASIZE [] s1 = (limit,s2) /\
    compile_assert_slice_bounds start len limit s2 = ((),s3) /\
    emit_void CALLDATACOPY [data; start; len] s3 = ((),s4) /\
    emit_void MSTORE [out; len] s4 = ((),sb) /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 s4 /\ cs_extends s4 sb
Proof
  simp[compile_slice_calldata_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  `cs_extends sa cs'` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def, slice_bounds_extends]
QED

Theorem compile_slice_code_stages:
  compile_slice_code start len N sa = (out,sb) ==>
  ?s1 s2 s3 s4 data limit.
    compile_slice_out_buf N sa = ((out,data),s1) /\
    emit_op CODESIZE [] s1 = (limit,s2) /\
    compile_assert_slice_bounds start len limit s2 = ((),s3) /\
    emit_void CODECOPY [data; start; len] s3 = ((),s4) /\
    emit_void MSTORE [out; len] s4 = ((),sb) /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 s4 /\ cs_extends s4 sb
Proof
  simp[compile_slice_code_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  `cs_extends sa cs'` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def, slice_bounds_extends]
QED

Theorem compile_slice_extcode_stages:
  compile_slice_extcode addr start len root data sa = (out,sb) ==>
  ?s1 s2 s3 limit.
    out = root /\ emit_op EXTCODESIZE [addr] sa = (limit,s1) /\
    compile_assert_slice_bounds start len limit s1 = ((),s2) /\
    emit_void EXTCODECOPY [addr; data; start; len] s2 = ((),s3) /\
    emit_void MSTORE [root; len] s3 = ((),sb) /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\
    cs_extends s2 s3 /\ cs_extends s3 sb
Proof
  simp[compile_slice_extcode_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def, slice_bounds_extends]
QED

(* These are the semantic query equations; they issue no requests. *)
Theorem external_size_step:
  ((opc = CALLDATASIZE /\ ops = [] /\ w = n2w (LENGTH s.vs_call_ctx.cc_calldata)) \/
   (opc = CODESIZE /\ ops = [] /\ w = n2w (LENGTH s.vs_code)) \/
   (opc = EXTCODESIZE /\ ops = [addr] /\ eval_operand addr s = SOME a /\
    w = n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code))) ==>
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s)
Proof
  strip_tac >> gvs[] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def, exec_read1_def]
QED

Theorem compile_slice_extcode_bounds_abort:
  compile_slice_extcode addr start len root data sa = (out,sb) /\
  emit_op EXTCODESIZE [addr] sa = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME wa /\
  eval_operand len s = SOME wn /\
  (!op. MEM op [addr;start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  q = (update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s) with
      vs_inst_idx := SUC s.vs_inst_idx /\
  run_inst_seq (emitted_insts sc sd) q = Abort ab u ==>
  ab = Revert_abort /\
  ?G' tn' j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> drule compile_slice_extcode_stages >> strip_tac >>
  `s1 = sc /\ s2 = sd` by metis_tac[pairTheory.PAIR_EQ] >> gvs[] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 s2 fn` by metis_tac[fn_has_code_split] >>
  `step_inst_base
    (mk_inst sa.cs_next_id EXTCODESIZE [addr] [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s)` by
    (irule external_size_step >> simp[] >> metis_tac[]) >>
  `MEM EXTCODESIZE [CALLDATASIZE;CODESIZE;EXTCODESIZE] /\ LENGTH [addr] <= 1 /\
   (!arg. MEM arg [addr] ==> op_taint tn arg = {})` by simp[] >>
  drule_all emit_external_size_counted >>
  disch_then (qspecl_then [`G`,`D`,`PG`] strip_assume_tac) >>
  suspend "bounds"
QED

Resume compile_slice_extcode_bounds_abort[bounds]:
  `run_inst_seq (emitted_insts s1 s2) t = Abort ab u` by gvs[] >>
  `fresh_vars_wrt s1 t` by simp[] >>
  `eval_operand start t = SOME wa /\ eval_operand len t = SOME wn` by metis_tac[] >>
  `!op. MEM op [start;len;limit] ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (gen_tac >> disch_tac >> Cases_on `op = limit` >- gvs[] >>
     `op = start \/ op = len` by fs[] >>
     `?v. eval_operand op s = SOME v` by metis_tac[] >>
     metis_tac[]) >>
  drule_all compile_assert_slice_bounds_counted_abort >>
  strip_tac >> suspend "compose"
QED
Resume compile_slice_extcode_bounds_abort[compose]:
  qpat_x_assum `!PG D. _` (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G'' tn''
    (Abort Revert_abort (u with vs_inst_idx := j))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >> qexistsl_tac [`G''`,`tn''`,`j`] >> gvs[] >>
  rpt strip_tac >> metis_tac[]
QED
Finalise compile_slice_extcode_bounds_abort

Theorem external_copy_step:
  ((opc = CALLDATACOPY /\ ops = [dst;start;len] /\ src = s.vs_call_ctx.cc_calldata) \/
   (opc = CODECOPY /\ ops = [dst;start;len] /\ src = s.vs_code) \/
   (opc = EXTCODECOPY /\ ops = [addr;dst;start;len] /\
    eval_operand addr s = SOME a /\ src = (lookup_account (w2w a) s.vs_accounts).code)) /\
  eval_operand dst s = SOME b /\ eval_operand start s = SOME wa /\
  eval_operand len s = SOME wn ==>
  step_inst_base (mk_inst id opc ops []) s =
    OK (write_memory_with_expansion (w2n b)
      (TAKE (w2n wn) (DROP (w2n wa) src ++ REPLICATE (w2n wn) 0w)) s)
Proof
  strip_tac >> gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def]
QED


Theorem ptr_covers_successful_transport:
  fresh_vars_wrt sa s /\
  (!x v. lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) ==>
  !p cap. ptr_covers G tn p s cap ==> ptr_covers H tm p t cap
Proof
  strip_tac >> rpt gen_tac >> simp[ptr_covers_def] >> strip_tac >>
  `not_fresh_at sa p` by
    (rw[not_fresh_at_def] >> metis_tac[fresh_vars_wrt_eval_operand,
      eval_operand_def, arithmeticTheory.GREATER_EQ]) >>
  metis_tac[]
QED

Theorem external_copy_store_counted:
  step_inst_base (mk_inst sc.cs_next_id opc ops []) r =
    OK (write_memory_with_expansion dest bytes r) ==>
  emit_void opc ops sc = ((),sd) /\ fn_has_code sc sd fn /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst; start; cnt_op]) \/
   (opc = EXTCODECOPY /\ ops = [addr; Var dst; start; cnt_op] /\
    (?wa. eval_operand addr r = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand start r = SOME a /\ eval_operand cnt_op r = SOME n /\
  op_taint tn start = {} /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst r (w2n n) /\ ~ctx_has_dalloca ctx /\ ~r.vs_halted /\
  r.vs_current_bb = sc.cs_current_bb /\ r.vs_inst_idx = LENGTH sc.cs_current_insts /\
  emit_void MSTORE [Var root;cnt_op] sd = ((),sb) /\ fn_has_code sd sb fn /\
  lookup_var root r = SOME b /\ 32 <= N /\ ptr_covers G tn root r N ==>
  !D PG. ?v t tm.
    v = (write_memory_with_expansion dest bytes r) with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n b) n v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn r 0 G tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers G tm root t N /\ mem_word_at (w2n b) t.vs_memory = n /\
    tm.t_var = tn.t_var /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  ntac 2 strip_tac >> rpt gen_tac >> gvs[] >>
  qpat_assum `step_inst_base _ r = _`
    (mp_then Any (mp_tac o SRULE []) emit_external_copy_counted) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  rename1 `tc.t_var = tn.t_var` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn r 0 G tc (OK v)` >>
  `ptr_covers G tc root v N` by
    (simp[Abbr `v`, ptr_covers_def, lookup_var_def] >> metis_tac[ptr_covers_def]) >>
  `ptr_covers G tc root v 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var root v = SOME b /\ eval_operand cnt_op v = SOME n /\
   op_taint tc cnt_op = {}` by
    (`!op. eval_operand op v = eval_operand op r /\
       op_taint tc op = op_taint tn op` by
       (Cases >> simp[eval_operand_def, op_taint_def] >>
        simp[Abbr `v`, write_memory_with_expansion_def, write_memory_def, expand_memory_def]) >>
     simp[]) >>
  `v.vs_current_bb = sd.cs_current_bb /\
   v.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~v.vs_halted` by simp[Abbr `v`] >>
  drule_all emit_scratch_word_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  rename1 `tm.t_var = tc.t_var` >>
  `gas_path_ptr D 0 ctx fn PG G tn r 0 G tm (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `ptr_covers G tm root t N` by metis_tac[] >>
  qexists_tac `tm` >> gvs[Abbr `v`]
QED
