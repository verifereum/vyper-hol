Theory bodyPtrIntCallCapture
Ancestors
  bodyPtrIntCallEntryContracts ptrSafeRun ptrDiscipline venomExecSemantics
  venomState finite_map words list fragGasSeqPtr ASCIInumbers
  venomInst codegenRel contextCodegenRel bodyPtrPrecompileBuiltinsSeq
  exprLoweringProps

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
