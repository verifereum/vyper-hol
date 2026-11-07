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

Theorem external_copy_ghost_memory:
  (opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\ LENGTH ops = 3) \/
   (opc = EXTCODECOPY /\ LENGTH ops = 4)) ==>
  (step_taint (mk_inst id opc ops []) s t tn).t_mem =
    tn.t_mem DIFF range_bytes (source_memory_write_ranges (mk_inst id opc ops []) s)
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, mem_taint_def, step_writes_def, mk_inst_def] >>
  namedCases_on `ops` ["", "x xs"] >> gvs[] >>
  namedCases_on `xs` ["", "y ys"] >> gvs[] >>
  namedCases_on `ys` ["", "z zs"] >> gvs[] >>
  namedCases_on `zs` ["", "w ws"] >> gvs[] >>
  simp[written_taint_def, mk_inst_def]
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
    tn'.t_mem = tn.t_mem DIFF
      range_bytes (source_memory_write_ranges (mk_inst sa.cs_next_id opc ops []) s) /\
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
  `tn'.t_mem = tn.t_mem DIFF
     range_bytes (source_memory_write_ranges (mk_inst sa.cs_next_id opc ops []) s)` by
    (simp_tac pure_ss [Abbr `tn'`] >> irule external_copy_ghost_memory >>
     simp[Abbr `u`, write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
     gvs[]) >>
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
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = (tn.t_mem DIFF
      range_bytes (source_memory_write_ranges (mk_inst sc.cs_next_id opc ops []) r))
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
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

Theorem external_copy_store_apply[local]:
  emit_void opc ops sc = ((),sd) ==>
  step_inst_base (mk_inst sc.cs_next_id opc ops []) r =
    OK (write_memory_with_expansion dest bytes r) ==>
  fn_has_code sc sd fn /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\ ops = [Var dst;start;cnt_op]) \/
   (?addr. opc = EXTCODECOPY /\ ops = [addr;Var dst;start;cnt_op] /\
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
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = (tn.t_mem DIFF
      range_bytes (source_memory_write_ranges (mk_inst sc.cs_next_id opc ops []) r))
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  ntac 3 strip_tac >> rpt gen_tac >> gvs[] >>
  qpat_assum `step_inst_base _ r = _`
    (mp_then Any (mp_tac o SRULE []) external_copy_store_counted) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`D`,`PG`] mp_tac) >> simp[]
QED

(* Successful evaluation, unlike arbitrary name lookup, excludes fresh outputs. *)
Theorem successful_operand_ghost_frame:
  fresh_vars_wrt sa s /\
  (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) ==>
  !op v. eval_operand op s = SOME v ==>
    eval_operand op t = SOME v /\ op_prov H op = op_prov G op /\
    op_taint tm op = op_taint tn op
Proof
  strip_tac >> rpt gen_tac >> disch_tac >> simp[] >>
  Cases_on `op` >> simp[op_prov_def, op_taint_def] >>
  rename1 `eval_operand (Var name) s = SOME v` >>
  `not_fresh_at sa name` by
    (rw[not_fresh_at_def] >> metis_tac[fresh_vars_wrt_eval_operand,
      arithmeticTheory.GREATER_EQ]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[op_taint_def]
QED

Theorem reserved_operand_ghost_frame:
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) ==>
  !op. (!z. op = Var z ==> not_fresh_at sa z) ==>
    eval_operand op t = eval_operand op s /\ op_prov H op = op_prov G op /\
    op_taint tm op = op_taint tn op
Proof
  strip_tac >> Cases >> simp[eval_operand_def, op_prov_def, op_taint_def]
QED

Theorem external_query_bounds_reserved_counted_abort:
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) wl s) ==>
  emit_op opc ops sa = (limit,sc) /\ fn_has_code sa sc fn /\
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\ fn_has_code sc sd fn /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) wl s) with
      vs_inst_idx := SUC s.vs_inst_idx) = Abort ab u ==>
  ab = Revert_abort /\ ?H tm j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  ntac 2 strip_tac >> drule_all emit_external_size_counted >>
  disch_then (qspecl_then [`G`,`D`,`PG`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sc sd) t = Abort ab u` by gvs[] >>
  `!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
    eval_operand op t = eval_operand op s /\ op_prov G' op = op_prov G op /\
    op_taint tn' op = op_taint tn op` by
    (gen_tac >> disch_tac >> irule reserved_operand_ghost_frame >>
     reverse conj_tac >- simp[update_var_def] >>
     qexists_tac `sa` >> metis_tac[]) >>
  `eval_operand start t = SOME wa /\ eval_operand len t = SOME wn` by
    (fs[MEM] >> metis_tac[]) >>
  `!op z. MEM op [start;len;limit] /\ op = Var z ==> not_fresh_at sc z` by
    (rpt strip_tac >> Cases_on `op = limit`
     >- (gvs[] >> simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
     `op = start \/ op = len` by fs[] >> fs[MEM] >> metis_tac[]) >>
  `!op. MEM op [start;len;limit] ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (gen_tac >> disch_tac >> Cases_on `op = limit` >- gvs[] >>
     `op = start \/ op = len` by fs[] >>
     `?v. eval_operand op s = SOME v` by metis_tac[] >> fs[] >> metis_tac[]) >>
  drule_all compile_assert_slice_bounds_reserved_counted_abort >> strip_tac >>
  qpat_x_assum `!PG D. _` (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G'' tn''
    (Abort Revert_abort (u with vs_inst_idx := j))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >> qexistsl_tac [`G''`,`tn''`,`j`] >> gvs[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem external_query_bounds_reserved_counted_ok:
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) wl s) ==>
  emit_op opc ops sa = (limit,sc) /\ fn_has_code sa sc fn /\
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\ fn_has_code sc sd fn /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) wl s) with
      vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  ?r H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK r) /\
    r.vs_current_bb = sd.cs_current_bb /\ r.vs_inst_idx = LENGTH sd.cs_current_insts /\
    ~r.vs_halted /\ (fresh_vars_wrt sa s ==> fresh_vars_wrt sd r) /\
    w2n wa + w2n wn <= w2n wl /\
    (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op r = eval_operand op s /\
      op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op) /\
    (!p cap. not_fresh_at sa p /\ ptr_covers G tn p s cap ==>
      ptr_covers H tm p r cap) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    r.vs_accounts = s.vs_accounts /\ r.vs_memory = s.vs_memory /\
    r.vs_code = s.vs_code /\ r.vs_call_ctx = s.vs_call_ctx /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  ntac 2 strip_tac >> drule_all emit_external_size_counted >>
  disch_then (qspecl_then [`G`,`D`,`PG`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sc sd) t = OK u` by gvs[] >>
  `!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
    eval_operand op t = eval_operand op s /\ op_prov G' op = op_prov G op /\
    op_taint tn' op = op_taint tn op` by
    (gen_tac >> disch_tac >> irule reserved_operand_ghost_frame >>
     reverse conj_tac >- simp[update_var_def] >>
     qexists_tac `sa` >> metis_tac[]) >>
  `eval_operand start t = SOME wa /\ eval_operand len t = SOME wn` by
    (fs[MEM] >> metis_tac[]) >>
  `!op z. MEM op [start;len;limit] /\ op = Var z ==> not_fresh_at sc z` by
    (rpt strip_tac >> Cases_on `op = limit`
     >- (gvs[] >> simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
     `op = start \/ op = len` by fs[] >> fs[MEM] >> metis_tac[]) >>
  `!op. MEM op [start;len;limit] ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (gen_tac >> disch_tac >> Cases_on `op = limit` >- gvs[] >>
     `op = start \/ op = len` by fs[] >>
     `?v. eval_operand op s = SOME v` by metis_tac[] >> fs[] >> metis_tac[]) >>
  drule_all compile_assert_slice_bounds_reserved_counted_ok >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `r = u with vs_inst_idx := LENGTH sd.cs_current_insts` >>
  `!op. eval_operand op r = eval_operand op u` by
    (Cases >> simp[Abbr `r`, eval_operand_def, lookup_var_def]) >>
  suspend "reserved_frames"
QED

Resume external_query_bounds_reserved_counted_ok[reserved_frames]:
  `!op. (!z. op = Var z ==> not_fresh_at sc z) ==>
    eval_operand op r = eval_operand op t /\ op_prov G'' op = op_prov G' op /\
    op_taint tn'' op = op_taint tn' op` by
    (gen_tac >> disch_tac >> simp[] >>
     Cases_on `op` >> simp[op_prov_def, op_taint_def] >> metis_tac[]) >>
  `!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
    eval_operand op r = eval_operand op s /\ op_prov G'' op = op_prov G op /\
    op_taint tn'' op = op_taint tn op` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> FLOOKUP G'' x = FLOOKUP G x /\
    op_taint tn'' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `!p cap. not_fresh_at sa p /\ ptr_covers G tn p s cap ==>
    ptr_covers G'' tn'' p r cap` by
    (rpt gen_tac >> simp[ptr_covers_def] >> strip_tac >>
     qpat_assum `!op. (!z. op = Var z ==> not_fresh_at sa z) ==> _`
       (qspec_then `Var p` mp_tac) >>
     simp[eval_operand_def, op_prov_def] >> strip_tac >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G'' tn'' (OK r)` by
    (drule_all gas_path_ptr_then >> simp[Abbr `r`]) >>
  `~u.vs_halted /\ u.vs_accounts = s.vs_accounts /\ u.vs_memory = s.vs_memory /\
    u.vs_code = s.vs_code /\ u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `u = t with vs_vars := _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_accounts,z.vs_memory,z.vs_code,z.vs_call_ctx)`) >>
     simp[update_var_def]) >>
  qexistsl_tac [`r`,`G''`,`tn''`] >>
  simp[Abbr `r`, fresh_vars_wrt_def] >> fs[fresh_vars_wrt_def]
QED


Finalise external_query_bounds_reserved_counted_ok

(* Compatibility at fresh entry points; reserved callers use the boundaries above. *)
Theorem external_query_bounds_counted_abort:
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) wl s) ==>
  emit_op opc ops sa = (limit,sc) /\ fn_has_code sa sc fn /\
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\ fn_has_code sc sd fn /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) wl s) with
      vs_inst_idx := SUC s.vs_inst_idx) = Abort ab u ==>
  ab = Revert_abort /\ ?H tm j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  ntac 2 strip_tac >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z` by
    (fs[MEM] >> rpt strip_tac >> rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_query_bounds_reserved_counted_abort) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem external_query_bounds_counted_ok:
  step_inst_base
    (mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) wl s) ==>
  emit_op opc ops sa = (limit,sc) /\ fn_has_code sa sc fn /\
  MEM opc [CALLDATASIZE; CODESIZE; EXTCODESIZE] /\ LENGTH ops <= 1 /\
  (!arg. MEM arg ops ==> op_taint tn arg = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\ fn_has_code sc sd fn /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) wl s) with
      vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  ?r H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK r) /\
    r.vs_current_bb = sd.cs_current_bb /\ r.vs_inst_idx = LENGTH sd.cs_current_insts /\
    ~r.vs_halted /\ fresh_vars_wrt sd r /\ w2n wa + w2n wn <= w2n wl /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op r = SOME v /\
      op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op) /\
    (!p cap. ptr_covers G tn p s cap ==> ptr_covers H tm p r cap) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    r.vs_accounts = s.vs_accounts /\ r.vs_memory = s.vs_memory /\
    r.vs_code = s.vs_code /\ r.vs_call_ctx = s.vs_call_ctx /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  ntac 2 strip_tac >>
  `!op w z. eval_operand op s = SOME w /\ op = Var z ==> not_fresh_at sa z` by
    (rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]) >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z` by
    (fs[MEM] >> metis_tac[]) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_query_bounds_reserved_counted_ok) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!p cap. ptr_covers G tn p s cap ==> ptr_covers H tm p r cap` by
    (rpt strip_tac >> `not_fresh_at sa p` by
       (fs[ptr_covers_def] >> metis_tac[eval_operand_def]) >> metis_tac[]) >>
  qexistsl_tac [`r`,`H`,`tm`] >> gvs[] >> metis_tac[]
QED

Theorem external_slice_fragment_counted_ok:
  emit_op sizeopc sizeops sa = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  emit_void copyopc copyops sd = ((),se) /\
  emit_void MSTORE [Var root;len] se = ((),sb) /\
  fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
  fn_has_code sd se fn /\ fn_has_code se sb fn /\
  ((sizeopc = CALLDATASIZE /\ sizeops = [] /\ copyopc = CALLDATACOPY /\
      copyops = [Var data;start;len] /\ src = s.vs_call_ctx.cc_calldata) \/
   (sizeopc = CODESIZE /\ sizeops = [] /\ copyopc = CODECOPY /\
      copyops = [Var data;start;len] /\ src = s.vs_code) \/
   (sizeopc = EXTCODESIZE /\ sizeops = [addr] /\ copyopc = EXTCODECOPY /\
      copyops = [addr;Var data;start;len] /\ eval_operand addr s = SOME a /\
      op_prov G addr = NONE /\ op_taint tn addr = {} /\
      src = (lookup_account (w2w a) s.vs_accounts).code)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op ([start;len;Var root;Var data] ++ sizeops) /\ op = Var z ==>
    not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  lookup_var root s = SOME b /\ lookup_var data s = SOME d /\
  32 <= N /\ ptr_covers G tn root s N /\ ptr_covers G tn data s (w2n wn) /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (LENGTH src)) s)
       with vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n d)
      (TAKE (w2n wn) (DROP (w2n wa) src ++ REPLICATE (w2n wn) 0w)) r)
        with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n b) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n b) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = (tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n wn})
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base (mk_inst sa.cs_next_id sizeopc sizeops
     [STRING #"%" (toString sa.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (LENGTH src)) s)` by
    (irule external_size_step >> metis_tac[]) >>
  `MEM sizeopc [CALLDATASIZE;CODESIZE;EXTCODESIZE] /\ LENGTH sizeops <= 1 /\
   (!arg. MEM arg sizeops ==> op_taint tn arg = {})` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z` by
    (fs[MEM] >> metis_tac[]) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_query_bounds_reserved_counted_ok) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!op. MEM op ([start;len;Var root;Var data] ++ sizeops) ==>
    eval_operand op r = eval_operand op s /\ op_prov H op = op_prov G op /\
    op_taint tm op = op_taint tn op` by metis_tac[] >>
  `eval_operand start r = SOME wa /\ eval_operand len r = SOME wn /\
   lookup_var root r = SOME b /\ lookup_var data r = SOME d /\
   op_taint tm start = {} /\ op_taint tm len = {}` by
    (qpat_assum `!op. MEM op (_ ++ sizeops) ==> _`
       (fn th => map_every (fn opq => qspec_then opq mp_tac th)
         [`start`,`len`,`Var root`,`Var data`]) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_covers H tm root r N /\ ptr_covers H tm data r (w2n wn)` by
    (fs[MEM] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `((copyopc = CALLDATACOPY \/ copyopc = CODECOPY) /\ copyops = [Var data;start;len]) \/
     (?ad. copyopc = EXTCODECOPY /\ copyops = [ad;Var data;start;len] /\
       (?w. eval_operand ad r = SOME w) /\ op_taint tm ad = {})` assume_tac
  >- (qpat_x_assum `r = _` kall_tac >>
      qpat_x_assum `_ \/ _ \/ _` strip_assume_tac >> gvs[MEM] >> metis_tac[]) >>
  `step_inst_base (mk_inst sd.cs_next_id copyopc copyops []) r =
   OK (write_memory_with_expansion (w2n d)
     (TAKE (w2n wn) (DROP (w2n wa) src ++ REPLICATE (w2n wn) 0w)) r)` by
    (qpat_x_assum `r = _` kall_tac >>
     qpat_x_assum `(_ /\ _) \/ (?ad. _)` kall_tac >>
     qpat_x_assum `_ \/ _ \/ _` strip_assume_tac >> gvs[] >>
     irule external_copy_step >> simp[eval_operand_def] >> metis_tac[]) >>
  `range_bytes (source_memory_write_ranges (mk_inst sd.cs_next_id copyopc copyops []) r) =
     {i | w2n d <= i /\ i < w2n d + w2n wn}` by
    (qpat_x_assum `r = _` kall_tac >>
     `eval_operand start r = SOME wa /\ eval_operand len r = SOME wn` by metis_tac[] >>
     qpat_x_assum `!op. MEM op (_ ++ sizeops) ==> _` kall_tac >>
     qpat_x_assum `(_ /\ _) \/ (?ad. _)` strip_assume_tac >>
     gvs[source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, mk_inst_def, eval_operand_def, lookup_var_def]) >>
  suspend "copy_store"
QED

Resume external_slice_fragment_counted_ok[copy_store]:
  qpat_assum `emit_void copyopc copyops sd = _` (mp_then Any mp_tac external_copy_store_apply) >>
  disch_then drule >> disch_then drule_all >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm' (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> op_taint tm' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\ _`
       (qspec_then `x` strip_assume_tac) >> fs[op_taint_def]) >>
  qexistsl_tac [`r`,`v`,`t`,`H`,`tm'`] >>
  rpt conj_tac >> simp[op_taint_def]
QED

Finalise external_slice_fragment_counted_ok

Theorem compile_slice_extcode_counted_ok:
  compile_slice_extcode addr start len (Var root) (Var data) sa = (out,sb) /\
  emit_op EXTCODESIZE [addr] sa = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\ eval_operand addr s = SOME a /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  lookup_var root s = SOME b /\ lookup_var data s = SOME d /\
  32 <= N /\ ptr_covers G tn root s N /\ ptr_covers G tn data s (w2n wn) /\
  (!op. MEM op [addr;start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s) with
       vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  out = Var root /\ ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n d)
      (TAKE (w2n wn) (DROP (w2n wa) (lookup_account (w2w a) s.vs_accounts).code ++
         REPLICATE (w2n wn) 0w)) r) with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n b) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n b) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = (tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n wn})
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  strip_tac >> drule compile_slice_extcode_stages >> strip_tac >>
  `s1 = sc /\ s2 = sd` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1 = sc` SUBST_ALL_TAC >> qpat_x_assum `s2 = sd` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
   fn_has_code sd s3 fn /\ fn_has_code s3 sb fn` by metis_tac[fn_has_code_split] >>
  `op_prov G addr = NONE /\ op_taint tn addr = {}` by (fs[] >> metis_tac[]) >>
  `!op. op = start \/ op = len ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (fs[] >> metis_tac[]) >>
  `!z. (Var z = start \/ Var z = len \/ z = root \/ z = data) \/ Var z = addr ==>
    not_fresh_at sa z` by
    (rpt strip_tac >> rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, eval_operand_def, arithmeticTheory.GREATER_EQ]) >>
  conj_tac >- simp[] >>
  qpat_assum `emit_op EXTCODESIZE _ _ = _`
    (mp_then Any (mp_tac o SRULE []) external_slice_fragment_counted_ok) >>
  simp[] >> disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
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
  `s1 = sc /\ s2 = sd` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1 = sc` SUBST_ALL_TAC >> qpat_x_assum `s2 = sd` SUBST_ALL_TAC >>
  qpat_x_assum `q = _` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by metis_tac[fn_has_code_split] >>
  `step_inst_base
    (mk_inst sa.cs_next_id EXTCODESIZE [addr] [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s)` by
    (irule external_size_step >> simp[] >> metis_tac[]) >>
  `MEM EXTCODESIZE [CALLDATASIZE;CODESIZE;EXTCODESIZE] /\ LENGTH [addr] <= 1 /\
   (!arg. MEM arg [addr] ==> op_taint tn arg = {})` by simp[] >>
  `!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_query_bounds_counted_abort) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

(* Replay the allocation at the semantic witness supplied by S1. *)
Theorem slice_out_buf_counted_replay[local]:
  compile_slice_out_buf N sa = ((Var root,Var data),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) ==>
  ?H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t0) /\
    ptr_covers H tm root t0 N /\ ptr_covers H tm data t0 (N - 32) /\
    t0.vs_current_bb = sb.cs_current_bb /\ t0.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t0.vs_halted /\ (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t0) /\
    sa.cs_next_var <= sb.cs_next_var /\
    not_fresh_at sb root /\ not_fresh_at sb data /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t0 = eval_operand op s /\ op_prov H op = op_prov G op /\
      op_taint tm op = op_taint tn op) /\
    t0.vs_call_ctx = s.vs_call_ctx /\ t0.vs_code = s.vs_code /\
    lookup_var root t0 = SOME a /\ lookup_var data t0 = SOME (a + 32w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = tn.t_mem UNION new_site_bytes s u0 /\
    w2n a + N < dimword (:256)
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\
   not_fresh_at sb root /\ not_fresh_at sb data` by
    (qpat_x_assum `compile_slice_out_buf _ _ = _` mp_tac >>
     simp[compile_slice_out_buf_def, contextTheory.compile_alloc_buffer_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[not_fresh_at_def]) >>
  drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  gvs[] >> qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> simp[op_taint_def]
  >~ [`_.t_mem = _`]
  >- (simp[step_taint_def, mem_taint_def, step_writes_def,
        source_memory_write_ranges_def, written_taint_def, range_bytes_def, mk_inst_def] >>
      simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
        pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  first_x_assum drule >> simp[op_taint_def]
QED

Theorem external_slice_two_source_counted_ok[local]:
  emit_op sizeopc [] sa = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  emit_void copyopc [Var data;start;len] sd = ((),se) /\
  emit_void MSTORE [Var root;len] se = ((),sb) /\
  fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
  fn_has_code sd se fn /\ fn_has_code se sb fn /\
  ((sizeopc = CALLDATASIZE /\ copyopc = CALLDATACOPY /\ src = s.vs_call_ctx.cc_calldata) \/
   (sizeopc = CODESIZE /\ copyopc = CODECOPY /\ src = s.vs_code)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op [start;len;Var root;Var data] /\ op = Var z ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  lookup_var root s = SOME b /\ lookup_var data s = SOME d /\
  32 <= N /\ ptr_covers G tn root s N /\ ptr_covers G tn data s (w2n wn) /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (LENGTH src)) s)
      with vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n d)
      (TAKE (w2n wn) (DROP (w2n wa) src ++ REPLICATE (w2n wn) 0w)) r)
        with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n b) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n b) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = (tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n wn})
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op z. MEM op ([start;len;Var root;Var data] ++ []) /\ op = Var z ==>
    not_fresh_at sa z` by simp[] >>
  Q.SUBGOAL_THEN
  `((sizeopc = CALLDATASIZE /\ ([]:operand list) = [] /\ copyopc = CALLDATACOPY /\
      [Var data;start;len] = [Var data;start;len] /\ src = s.vs_call_ctx.cc_calldata) \/
    (sizeopc = CODESIZE /\ ([]:operand list) = [] /\ copyopc = CODECOPY /\
      [Var data;start;len] = [Var data;start;len] /\ src = s.vs_code) \/
    (sizeopc = EXTCODESIZE /\ [] = [(Lit 0w)] /\ copyopc = EXTCODECOPY /\
      [Var data;start;len] = [(Lit 0w);Var data;start;len] /\
      eval_operand (Lit 0w) s = SOME 0w /\ op_prov G (Lit 0w) = NONE /\
      op_taint tn (Lit 0w) = {} /\
      src = (lookup_account (w2w (0w:bytes32)) s.vs_accounts).code))` assume_tac
  >- simp[] >>
  qpat_assum `emit_op sizeopc [] sa = _`
    (mp_then Any mp_tac external_slice_fragment_counted_ok) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem external_slice_alloc_counted_ok:
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op sizeopc [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  emit_void copyopc [Var data;start;len] sd = ((),se) /\
  emit_void MSTORE [Var root;len] se = ((),sb) /\
  fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn /\
  fn_has_code sd se fn /\ fn_has_code se sb fn /\
  ((sizeopc = CALLDATASIZE /\ copyopc = CALLDATACOPY /\ src = s.vs_call_ctx.cc_calldata) \/
   (sizeopc = CODESIZE /\ copyopc = CODECOPY /\ src = s.vs_code)) /\
  stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\ w2n wn <= N - 32 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var)) (n2w (LENGTH src)) t0)
      with vs_inst_idx := SUC t0.vs_inst_idx) = OK u ==>
  ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n (a + 32w))
      (TAKE (w2n wn) (DROP (w2n wa) src ++ REPLICATE (w2n wn) 0w)) r)
        with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n a) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n a) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = ((tn.t_mem UNION new_site_bytes s u0)
      DIFF {i | w2n (a + 32w) <= i /\ i < w2n (a + 32w) + w2n wn})
      DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    w2n a + N < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all slice_out_buf_counted_replay >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `!op. MEM op [start;len] ==> !x. op = Var x ==> not_fresh_at sa x` by
    metis_tac[] >>
  `eval_operand start t0 = SOME wa /\ eval_operand len t0 = SOME wn /\
   (!op. MEM op [start;len] ==> op_prov H op = NONE /\ op_taint tm op = {})` by
    (qpat_x_assum `t0 = _` kall_tac >> fs[] >> metis_tac[]) >>
  `ptr_covers H tm data t0 (w2n wn)` by
    (fs[ptr_covers_def] >> qexistsl_tac [`a + 32w`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  Q.SUBGOAL_THEN
    `((sizeopc = CALLDATASIZE /\ copyopc = CALLDATACOPY /\ src = t0.vs_call_ctx.cc_calldata) \/
      (sizeopc = CODESIZE /\ copyopc = CODECOPY /\ src = t0.vs_code))` assume_tac
  >- (qpat_x_assum `t0 = _` kall_tac >> metis_tac[]) >>
  `!op z. MEM op [start;len;Var root;Var data] /\ op = Var z ==>
    not_fresh_at s1 z` by
    (fs[MEM] >> rpt strip_tac >> gvs[] >>
     irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `emit_op sizeopc _ _ = _`
    (mp_then Any mp_tac external_slice_two_source_counted_ok) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> disch_tac >>
  qexistsl_tac [`H'`,`tm'`] >>
  qpat_x_assum `t0 = _` kall_tac >> gvs[] >> rpt strip_tac >>
  `not_fresh_at s1 x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `!x. not_fresh_at s1 x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED

Theorem compile_slice_calldata_counted_ok:
  compile_slice_calldata start len N sa = (Var root,sb) /\
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op CALLDATASIZE [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\ w2n wn <= N - 32 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) t0) with
      vs_inst_idx := SUC t0.vs_inst_idx) = OK u ==>
  ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n (a + 32w))
      (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata ++
        REPLICATE (w2n wn) 0w)) r) with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n a) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n a) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = ((tn.t_mem UNION new_site_bytes s u0)
      DIFF {i | w2n (a + 32w) <= i /\ i < w2n (a + 32w) + w2n wn})
      DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    w2n a + N < dimword (:256)
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `s1' = s1 /\ data' = Var data /\ s2 = sc /\ limit' = limit /\ s3 = sd` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  qpat_x_assum `data' = Var data` SUBST_ALL_TAC >>
  qpat_x_assum `s2 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `limit' = limit` SUBST_ALL_TAC >>
  qpat_x_assum `s3 = sd` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb /\ cs_extends s1 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn /\
   fn_has_code sd s4 fn /\ fn_has_code s4 sb fn` by
    (qpat_assum `fn_has_code sa sb fn` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`cs_extends sa s1`, `cs_extends s1 sc`, `cs_extends sc sd`,
        `cs_extends sd s4`, `cs_extends s4 sb`, `cs_extends sd sb`,
        `cs_extends sc sb`, `cs_extends s1 sb`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fn_has_code_split]) >>
  qpat_x_assum `t0 = _` SUBST_ALL_TAC >> fs[NoAsms] >>
  qpat_assum `emit_op CALLDATASIZE _ _ = _`
    (mp_then Any (mp_tac o SRULE []) external_slice_alloc_counted_ok) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem compile_slice_code_counted_ok:
  compile_slice_code start len N sa = (Var root,sb) /\
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op CODESIZE [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\ w2n wn <= N - 32 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fresh_vars_wrt sa s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_code)) t0) with vs_inst_idx := SUC t0.vs_inst_idx) = OK u ==>
  ?r v t H tm.
    r = u with vs_inst_idx := LENGTH sd.cs_current_insts /\
    v = (write_memory_with_expansion (w2n (a + 32w))
      (TAKE (w2n wn) (DROP (w2n wa) s.vs_code ++
        REPLICATE (w2n wn) 0w)) r) with vs_inst_idx := SUC r.vs_inst_idx /\
    t = (mstore (w2n a) wn v) with vs_inst_idx := SUC v.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ ptr_covers H tm root t N /\ mem_word_at (w2n a) t.vs_memory = wn /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = ((tn.t_mem UNION new_site_bytes s u0)
      DIFF {i | w2n (a + 32w) <= i /\ i < w2n (a + 32w) + w2n wn})
      DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    w2n a + N < dimword (:256)
Proof
  strip_tac >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z` by
    (rpt strip_tac >> gvs[MEM] >> rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]) >>
  drule compile_slice_code_stages >> strip_tac >>
  `s1' = s1 /\ data' = Var data /\ s2 = sc /\ limit' = limit /\ s3 = sd` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  qpat_x_assum `data' = Var data` SUBST_ALL_TAC >>
  qpat_x_assum `s2 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `limit' = limit` SUBST_ALL_TAC >>
  qpat_x_assum `s3 = sd` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb /\ cs_extends s1 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn /\
   fn_has_code sd s4 fn /\ fn_has_code s4 sb fn` by
    (qpat_assum `fn_has_code sa sb fn` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`cs_extends sa s1`, `cs_extends s1 sc`, `cs_extends sc sd`,
        `cs_extends sd s4`, `cs_extends s4 sb`, `cs_extends sd sb`,
        `cs_extends sc sb`, `cs_extends s1 sb`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fn_has_code_split]) >>
  qpat_x_assum `t0 = _` SUBST_ALL_TAC >> fs[NoAsms] >>
  qpat_assum `emit_op CODESIZE _ _ = _`
    (mp_then Any (mp_tac o SRULE []) external_slice_alloc_counted_ok) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem external_slice_alloc_counted_abort:
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op sizeopc [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn /\
  ((sizeopc = CALLDATASIZE /\ src = s.vs_call_ctx.cc_calldata) \/
   (sizeopc = CODESIZE /\ src = s.vs_code)) /\
  stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var)) (n2w (LENGTH src)) t0)
      with vs_inst_idx := SUC t0.vs_inst_idx) = Abort ab u ==>
  ab = Revert_abort /\ ?H tm j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all slice_out_buf_counted_replay >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `!op. MEM op [start;len] ==> !x. op = Var x ==> not_fresh_at sa x` by
    metis_tac[] >>
  `eval_operand start t0 = SOME wa /\ eval_operand len t0 = SOME wn /\
   (!op. MEM op [start;len] ==> op_prov H op = NONE /\ op_taint tm op = {})` by
    (qpat_x_assum `t0 = _` kall_tac >> fs[] >> metis_tac[]) >>
  `step_inst_base (mk_inst s1.cs_next_id sizeopc []
     [STRING #"%" (toString s1.cs_next_var)]) t0 =
   OK (update_var (STRING #"%" (toString s1.cs_next_var)) (n2w (LENGTH src)) t0)` by
    (irule external_size_step >> qpat_x_assum `t0 = _` kall_tac >> metis_tac[]) >>
  `MEM sizeopc [CALLDATASIZE;CODESIZE;EXTCODESIZE] /\ LENGTH ([]:operand list) <= 1 /\
   (!arg. MEM arg ([]:operand list) ==> op_taint tm arg = {})` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[] >> metis_tac[]) >>
  qpat_assum `step_inst_base _ t0 = _`
    (mp_then Any mp_tac external_query_bounds_reserved_counted_abort) >>
  disch_then drule_all >> disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> disch_tac >>
  simp[] >> qexistsl_tac [`H'`,`tm'`,`j`] >>
  qpat_x_assum `t0 = _` kall_tac >> gvs[] >> rpt strip_tac >>
  `not_fresh_at s1 x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `!x. not_fresh_at s1 x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED

Theorem compile_slice_calldata_bounds_abort:
  compile_slice_calldata start len N sa = (Var root,sb) /\
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op CALLDATASIZE [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  (!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) t0) with
      vs_inst_idx := SUC t0.vs_inst_idx) = Abort ab u ==>
  ab = Revert_abort /\ ?H tm j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `s1' = s1 /\ data' = Var data /\ s2 = sc /\ limit' = limit /\ s3 = sd` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  qpat_x_assum `data' = Var data` SUBST_ALL_TAC >>
  qpat_x_assum `s2 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `limit' = limit` SUBST_ALL_TAC >>
  qpat_x_assum `s3 = sd` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb /\ cs_extends s1 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn` by
    (qpat_assum `fn_has_code sa sb fn` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`cs_extends sa s1`, `cs_extends s1 sc`, `cs_extends sc sd`,
        `cs_extends sd sb`, `cs_extends sc sb`, `cs_extends s1 sb`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fn_has_code_split]) >>
  qpat_x_assum `t0 = _` SUBST_ALL_TAC >> fs[NoAsms] >>
  qpat_assum `emit_op CALLDATASIZE _ _ = _`
    (mp_then Any (mp_tac o SRULE []) external_slice_alloc_counted_abort) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem compile_slice_code_bounds_abort:
  compile_slice_code start len N sa = (Var root,sb) /\
  compile_slice_out_buf N sa = ((Var root,Var data),s1) /\
  emit_op CODESIZE [] s1 = (limit,sc) /\
  compile_assert_slice_bounds start len limit sc = ((),sd) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fresh_vars_wrt sa s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u0 /\
  lookup_var root u0 = SOME a /\
  t0 = ((update_var data (a + 32w) u0) with vs_inst_idx := s.vs_inst_idx + 2) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  (!op. MEM op [start;len] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sc sd)
    ((update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_code)) t0) with vs_inst_idx := SUC t0.vs_inst_idx) = Abort ab u ==>
  ab = Revert_abort /\ ?H tm j.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!op z. MEM op [start;len] /\ op = Var z ==> not_fresh_at sa z` by
    (rpt strip_tac >> gvs[MEM] >> rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]) >>
  drule compile_slice_code_stages >> strip_tac >>
  `s1' = s1 /\ data' = Var data /\ s2 = sc /\ limit' = limit /\ s3 = sd` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  qpat_x_assum `data' = Var data` SUBST_ALL_TAC >>
  qpat_x_assum `s2 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `limit' = limit` SUBST_ALL_TAC >>
  qpat_x_assum `s3 = sd` SUBST_ALL_TAC >>
  `cs_extends sd sb /\ cs_extends sc sb /\ cs_extends s1 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sc fn /\ fn_has_code sc sd fn` by
    (qpat_assum `fn_has_code sa sb fn` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`cs_extends sa s1`, `cs_extends s1 sc`, `cs_extends sc sd`,
        `cs_extends sd sb`, `cs_extends sc sb`, `cs_extends s1 sb`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fn_has_code_split]) >>
  qpat_x_assum `t0 = _` SUBST_ALL_TAC >> fs[NoAsms] >>
  qpat_assum `emit_op CODESIZE _ _ = _`
    (mp_then Any (mp_tac o SRULE []) external_slice_alloc_counted_abort) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED
