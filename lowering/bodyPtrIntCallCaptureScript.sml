Theory bodyPtrIntCallCapture
Ancestors
  bodyPtrIntCallEntryContracts ptrSafeRun ptrDiscipline venomExecSemantics
  venomState finite_map words list fragGasSeqPtr ASCIInumbers
  venomInst codegenRel contextCodegenRel bodyPtrPrecompileBuiltinsSeq
  exprLoweringProps intCallCallee loweringStateRelDefs emitHelperProps

Theorem intcall_param_capture_ghost:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH PG /\
  step_inst fuel ctx inst s = OK t ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) out = EL (w2n idx) PG /\
  op_taint (SND (ghost_step fuel ctx PG G tn inst s)) (Var out) = {}
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all ghost_step_non_invoke >> disch_then (qspecl_then [`PG`,`G`,`tn`] SUBST1_TAC) >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def] >>
  Cases_on `EL (w2n idx) PG` >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, eval_operand_def]
QED

Theorem intcall_capture_inst_ptr:
  MEM opc [PARAM; RETPC_PARAM] /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc [Lit idx] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, step_inst_def] >>
  simp[Once step_inst_base_def] >>
  simp[Once step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), update_var_def]
QED

Theorem intcall_capture_step_taint:
  MEM opc [PARAM; RETPC_PARAM] /\ t.vs_allocas = s.vs_allocas /\
  t.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id opc [Lit idx] [out]) s t tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, set_var_taint_def, out_taint_def, mk_inst_def,
       eval_operand_def, taint_component_equality, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

(* Consecutively named captures preserve all previously captured names.
   G is arbitrary: a NONE parameter actively removes its output's tag. *)
Theorem intcall_params_sequence_ptr:
  !n id idx nv s G tn.
    idx + n <= LENGTH s.vs_params /\ LENGTH s.vs_params < dimword (:256) /\
    LENGTH PG = LENGTH s.vs_params /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ?t H un.
      run_inst_seq
        (GENLIST (\i. mk_inst (id+i) PARAM [Lit (n2w (idx+i))]
          [STRING #"%" (toString (nv+i))]) n) s = OK t /\
      (!k. inst_seq_ptr D lo ctx fn PG G tn
        (GENLIST (\i. mk_inst (id+i) PARAM [Lit (n2w (idx+i))]
          [STRING #"%" (toString (nv+i))]) n)
        (s with vs_inst_idx := k) H un) /\
      t = s with vs_vars := t.vs_vars /\
      un = tn with t_var := un.t_var /\
      (!i. i < n ==>
        lookup_var (STRING #"%" (toString (nv+i))) t = SOME (EL (idx+i) s.vs_params) /\
        FLOOKUP H (STRING #"%" (toString (nv+i))) = EL (idx+i) PG /\
        op_taint un (Var (STRING #"%" (toString (nv+i)))) = {}) /\
      (!x. (!i. i < n ==> x <> STRING #"%" (toString (nv+i))) ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint un (Var x) = op_taint tn (Var x))
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[run_inst_seq_def, inst_seq_ptr_def, venom_state_component_equality,
           taint_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  `idx + n <= LENGTH s.vs_params` by decide_tac >>
  first_x_assum drule_all >>
  disch_then (qspecl_then [`id`,`nv`,`G`,`tn`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK t` >>
  qabbrev_tac `out = STRING #"%" (toString (nv+n))` >>
  qabbrev_tac `inst = mk_inst (id+n) PARAM [Lit (n2w (idx+n))] [out]` >>
  qabbrev_tac `u = update_var out (EL (idx+n) s.vs_params) t` >>
  `step_inst_base inst t = OK u` by
    (simp[Abbr `inst`, Abbr `u`, Once step_inst_base_def, mk_inst_def] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `GENLIST (\i. mk_inst (id+i) PARAM [Lit (n2w (idx+i))]
      [STRING #"%" (toString (nv+i))]) (SUC n) = code ++ [inst]` by
    simp[GENLIST, SNOC_APPEND, Abbr `code`, Abbr `inst`, Abbr `out`] >>
  qexistsl_tac [`u`,`step_prov PG H inst u`,`un with t_var := un.t_var |+ (out,{})`] >>
  qpat_x_assum `GENLIST _ (SUC n) = _` (fn th => pure_rewrite_tac[th]) >>
  conj_tac >- (drule run_inst_seq_append >>
    disch_then (qspec_then `[inst]` mp_tac) >> simp[run_inst_seq_def]) >>
  conj_tac >- suspend "path" >>
  conj_tac >- (simp[Abbr `u`, update_var_def] >>
    qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  conj_tac >- (qpat_x_assum `un = tn with t_var := _` SUBST1_TAC >> simp[]) >>
  suspend "outputs"
QED

Resume intcall_params_sequence_ptr[path]:
  irule inst_seq_ptr_append_cursors >>
  reverse conj_tac
  >- simp[Abbr `code`, EVERY_GENLIST, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`H`,`t`,`un`] >> simp[] >>
  gen_tac >> simp[inst_seq_ptr_def] >>
  conj_tac >- (simp[Abbr `inst`] >> irule intcall_capture_inst_ptr >>
    simp[] >> qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
    fs[allocas_from_def] >> metis_tac[]) >>
  simp[Abbr `inst`, Once step_inst_base_def, mk_inst_def] >>
  `idx+n < LENGTH t.vs_params /\ idx+n < dimword (:256)` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[] >>
  simp[inst_seq_ptr_def, step_prov_def, out_prov_def, mk_inst_def,
       intcall_capture_step_taint, update_var_def, Abbr `u`] >>
  rewrite_tac[GSYM mk_inst_def] >> simp[intcall_capture_step_taint]
QED
Resume intcall_params_sequence_ptr[outputs]:
  `idx+n < dimword (:256)` by decide_tac >>
  simp[Abbr `inst`, step_prov_def, out_prov_def, mk_inst_def] >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases_on `i = n`
      >- (gvs[Abbr `out`, Abbr `u`, update_var_def, lookup_var_def,
               set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
          Cases_on `EL (i+idx) PG` >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
      `i < n` by decide_tac >>
      `STRING #"%" (toString (nv+i)) <> out` by simp[Abbr `out`] >>
      simp[Abbr `u`, update_var_def, lookup_var_def, op_taint_def,
           set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      Cases_on `EL (idx+n) PG` >>
      gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, lookup_var_def, op_taint_def,
          arithmeticTheory.ADD_COMM]) >>
  gen_tac >> strip_tac >>
  `x <> out` by (fs[Abbr `out`, arithmeticTheory.ADD_COMM]) >>
  `lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)` by
    (first_x_assum irule >> rpt strip_tac >>
     `i < SUC n` by decide_tac >> fs[arithmeticTheory.ADD_COMM]) >>
  Cases_on `EL (idx+n) PG` >>
  gvs[Abbr `u`, update_var_def, lookup_var_def, set_prov_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED
Finalise intcall_params_sequence_ptr

Theorem intcall_retpc_sequence_ptr:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  run_inst_seq [mk_inst id RETPC_PARAM [Lit idx] [out]] s =
    OK (update_var out s.vs_return_pc_token s) /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id RETPC_PARAM [Lit idx] [out]] (s with vs_inst_idx := k)
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{})))
Proof
  strip_tac >> conj_tac
  >- simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
  gen_tac >> simp[inst_seq_ptr_def] >> conj_tac
  >- (irule intcall_capture_inst_ptr >> fs[allocas_from_def] >> metis_tac[]) >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def, inst_seq_ptr_def,
       mk_inst_def, update_var_def] >>
  rewrite_tac[GSYM mk_inst_def] >> simp[intcall_capture_step_taint]
QED

Theorem intcall_capture_sequence_ptr:
  n <= LENGTH s.vs_params /\ LENGTH s.vs_params < dimword (:256) /\
  LENGTH PG = LENGTH s.vs_params /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?t H un.
    run_inst_seq
      (GENLIST (\i. mk_inst (id+i) PARAM [Lit (n2w i)]
        [STRING #"%" (toString (nv+i))]) n ++
       [mk_inst (id+n) RETPC_PARAM [Lit (n2w n)] [STRING #"%" (toString (nv+n))]]) s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      (GENLIST (\i. mk_inst (id+i) PARAM [Lit (n2w i)]
        [STRING #"%" (toString (nv+i))]) n ++
       [mk_inst (id+n) RETPC_PARAM [Lit (n2w n)] [STRING #"%" (toString (nv+n))]])
      (s with vs_inst_idx := k) H un) /\
    t = s with vs_vars := t.vs_vars /\ un = tn with t_var := un.t_var /\
    (!i. i < n ==>
      lookup_var (STRING #"%" (toString (nv+i))) t = SOME (EL i s.vs_params) /\
      FLOOKUP H (STRING #"%" (toString (nv+i))) = EL i PG /\
      op_taint un (Var (STRING #"%" (toString (nv+i)))) = {}) /\
    lookup_var (STRING #"%" (toString (nv+n))) t = SOME s.vs_return_pc_token /\
    FLOOKUP H (STRING #"%" (toString (nv+n))) = NONE /\
    op_taint un (Var (STRING #"%" (toString (nv+n)))) = {} /\
    (!x. (!i. i <= n ==> x <> STRING #"%" (toString (nv+i))) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qspecl_then [`n`,`id`,`0`,`nv`,`s`,`G`,`tn`] mp_tac intcall_params_sequence_ptr >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK t` >>
  qabbrev_tac `out = STRING #"%" (toString (nv+n))` >>
  `allocas_from lo t` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> fs[allocas_from_def] >> metis_tac[]) >>
  drule_all intcall_retpc_sequence_ptr >>
  disch_then (qspecl_then [`un`,`out`,`n2w n`,`id+n`,`fn`,`PG`,`H`,`D`] strip_assume_tac) >>
  qexistsl_tac [`update_var out t.vs_return_pc_token t`,
                `DRESTRICT H (COMPL {out})`,`un with t_var := un.t_var |+ (out,{})`] >>
  conj_tac >- (qpat_assum `run_inst_seq code s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
    disch_then (qspec_then `[mk_inst (id+n) RETPC_PARAM [Lit (n2w n)] [out]]` mp_tac) >>
    simp[Abbr `out`, arithmeticTheory.ADD_COMM]) >>
  conj_tac >- suspend "path" >>
  conj_tac >- (simp[update_var_def] >>
    qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  conj_tac >- (qpat_x_assum `un = tn with t_var := _` SUBST1_TAC >> simp[]) >>
  suspend "outputs"
QED
Resume intcall_capture_sequence_ptr[path]:
  irule inst_seq_ptr_append_cursors >> reverse conj_tac
  >- simp[Abbr `code`, EVERY_GENLIST, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`H`,`t`,`un`] >>
  fs[Abbr `out`, arithmeticTheory.ADD_COMM]
QED
Resume intcall_capture_sequence_ptr[outputs]:
  conj_tac
  >- (gen_tac >> strip_tac >>
      `STRING #"%" (toString (nv+i)) <> out` by simp[Abbr `out`] >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
          op_taint_def, arithmeticTheory.ADD_COMM]) >>
  `t.vs_return_pc_token = s.vs_return_pc_token` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[Abbr `out`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, arithmeticTheory.ADD_COMM] >>
  gen_tac >> strip_tac >>
  `x <> STRING #"%" (toString (n+nv))` by fs[] >>
  `lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)` by
    (first_x_assum irule >> rpt strip_tac >>
     `i <= n` by decide_tac >> fs[arithmeticTheory.ADD_COMM]) >>
  gvs[lookup_var_def, op_taint_def]
QED
Finalise intcall_capture_sequence_ptr

Theorem intcall_capture_path_ptr:
  (has_rb ==> emit_op PARAM [Lit 0w] st0 = (rb,stb)) /\
  (~has_rb ==> stb = st0) /\ idx = (if has_rb then 1 else 0) /\
  compile_internal_param_decls params idx stb = ((caps,next),stp) /\
  emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,stc) /\
  fresh_vars_wrt st0 s /\ idx + LENGTH params <= LENGTH s.vs_params /\
  LENGTH s.vs_params < dimword (:256) /\ LENGTH PG = LENGTH s.vs_params /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st0 stc) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un.
    run_inst_seq (emitted_insts st0 stc) s = OK t /\
    gas_path_ptr D lo ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st0 stc))) /\
    t = s with vs_vars := t.vs_vars /\ un = tn with t_var := un.t_var /\
    fresh_vars_wrt stc t /\ LENGTH caps = LENGTH params /\
    (!i. i < LENGTH params ==> ?p.
      EL i caps = (FST (EL i params),SND (EL i params),Var p) /\
      lookup_var p t = SOME (EL (idx+i) s.vs_params) /\
      FLOOKUP H p = EL (idx+i) PG /\ op_taint un (Var p) = {}) /\
    (?p. rpc = Var p /\ lookup_var p t = SOME s.vs_return_pc_token /\
      FLOOKUP H p = NONE /\ op_taint un (Var p) = {}) /\
    (has_rb ==> ?p. rb = Var p /\ lookup_var p t = SOME (HD s.vs_params) /\
      FLOOKUP H p = HD PG /\ op_taint un (Var p) = {}) /\
    (!x. not_fresh_at st0 x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule compile_internal_param_decls_shape >> strip_tac >>
  `emitted_insts st0 stc =
    GENLIST (\i. mk_inst (st0.cs_next_id+i) PARAM [Lit (n2w i)]
      [STRING #"%" (toString (st0.cs_next_var+i))]) (idx+LENGTH params) ++
    [mk_inst (st0.cs_next_id+(idx+LENGTH params)) RETPC_PARAM
      [Lit (n2w (idx+LENGTH params))]
      [STRING #"%" (toString (st0.cs_next_var+(idx+LENGTH params)))]] /\
    stc.cs_next_var = st0.cs_next_var + (idx+LENGTH params) + 1 /\
    rpc = Var (STRING #"%" (toString (st0.cs_next_var+(idx+LENGTH params)))) /\
    (!i. i < LENGTH params ==>
      EL i caps = (FST (EL i params),SND (EL i params),
        Var (STRING #"%" (toString (st0.cs_next_var+(idx+i)))))) /\
    (has_rb ==> rb = Var (STRING #"%" (toString st0.cs_next_var)))` by
      suspend "shape" >>
  qspecl_then [`idx+LENGTH params`,`st0.cs_next_id`,`st0.cs_next_var`] mp_tac
    (Q.GENL [`n`,`id`,`nv`] intcall_capture_sequence_ptr) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`t`,`H`,`un`] >> conj_tac >- metis_tac[] >>
  conj_tac >- suspend "gas" >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- fs[] >>
  conj_tac >- suspend "params" >>
  conj_tac >- (qexists_tac `STRING #"%" (toString (st0.cs_next_var+(idx+LENGTH params)))` >> simp[]) >>
  conj_tac >- suspend "buffer" >>
  suspend "frame"
QED
Resume intcall_capture_path_ptr[shape]:
  drule emitted_insts_emit_op >> strip_tac >>
  Cases_on `has_rb` >> gvs[]
  >- (qpat_assum `emit_op PARAM _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
      simp[emitted_insts_def, DROP_APPEND] >>
      once_rewrite_tac[GSYM arithmeticTheory.ADD1] >>
      simp[listTheory.GENLIST_CONS, combinTheory.o_DEF,
           arithmeticTheory.ADD_CLAUSES] >>
      `LENGTH st0.cs_current_insts - SUC (LENGTH st0.cs_current_insts) = 0` by decide_tac >>
      `LENGTH st0.cs_current_insts - SUC (LENGTH st0.cs_current_insts + LENGTH params) = 0` by decide_tac >>
      simp[] ) >>
  simp[emitted_insts_def, DROP_APPEND] >>
  `LENGTH st0.cs_current_insts - (LENGTH st0.cs_current_insts + LENGTH params) = 0` by decide_tac >> simp[]
QED
Resume intcall_capture_path_ptr[params]:
  gen_tac >> strip_tac >>
  qexists_tac `STRING #"%" (toString (st0.cs_next_var + (idx+i)))` >>
  simp[] >> first_x_assum (qspec_then `idx+i` mp_tac) >> simp[]
QED
Resume intcall_capture_path_ptr[buffer]:
  strip_tac >> qexists_tac `STRING #"%" (toString st0.cs_next_var)` >>
  gvs[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED
Resume intcall_capture_path_ptr[fresh]:
  pure_rewrite_tac[fresh_vars_wrt_def] >> gen_tac >> strip_tac >>
  `!i. i <= idx + LENGTH params ==>
    STRING #"%" (toString n) <> STRING #"%" (toString (st0.cs_next_var+i))` by
    (rpt strip_tac >> fs[] >> decide_tac) >>
  qpat_x_assum `!x. (!i. _) ==> _` (qspec_then `STRING #"%" (toString n)` mp_tac) >>
  simp[lookup_var_def] >> strip_tac >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by
    (fs[fresh_vars_wrt_def] >> first_x_assum irule >> decide_tac) >>
  gvs[FLOOKUP_DEF]
QED
Resume intcall_capture_path_ptr[gas]:
  `!i. MEM i (emitted_insts st0 stc) ==> i.inst_opcode <> GAS` by
    (simp[MEM_APPEND, MEM_GENLIST] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st0 stc)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st0 stc)` by
    simp[EVERY_APPEND, EVERY_GENLIST, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_gas_path_ptr >> simp[] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >> gvs[]
QED
Resume intcall_capture_path_ptr[frame]:
  gen_tac >> strip_tac >>
  qpat_x_assum `!x. (!i. _) ==> _` irule >>
  rpt strip_tac >> fs[not_fresh_at_def] >>
  first_x_assum irule >> decide_tac
QED
Finalise intcall_capture_path_ptr
