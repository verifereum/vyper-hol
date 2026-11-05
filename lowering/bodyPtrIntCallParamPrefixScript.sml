Theory bodyPtrIntCallParamPrefix
Ancestors
  bodyPtrIntCallAuxEntry fragGasSeqPtr fragGasPathPtr fragGasSeqAbort intCallCallee moduleLowering
  emitHelper compileEnv emitHelperProps ptrDiscipline venomExecSemantics venomInst venomState
  finite_map list rich_list words arithmetic ptrSafeRun codegenRel contextCodegenRel pred_set
  bodyPtrIntCallJoint exprLoweringProps fragExec

(* Only the output names and emitted code are absent from the exported
   internal_param_decls_projection. *)
Theorem intcall_param_decls_code:
  !ps idx st caps next st'.
    compile_internal_param_decls ps idx st = ((caps,next),st') ==>
    LENGTH caps = LENGTH ps /\
    (!j. j < LENGTH ps ==>
      EL j caps = (FST (EL j ps), SND (EL j ps),
        Var (STRING #"%" (toString (st.cs_next_var+j))))) /\
    st'.cs_next_var = st.cs_next_var + LENGTH ps /\
    st'.cs_current_insts = st.cs_current_insts ++
      GENLIST (\j. mk_inst (st.cs_next_id+j) PARAM [Lit (n2w (idx+j))]
        [STRING #"%" (toString (st.cs_next_var+j))]) (LENGTH ps)
Proof
  Induct
  >- simp[compile_internal_param_decls_def, comp_return_def] >>
  Cases >> rpt gen_tac >>
  simp[compile_internal_param_decls_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  PairCases_on `rest_result` >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rpt strip_tac >~ [`EL j _ = _`]
  >- (Cases_on `j` >> gvs[ADD1]) >>
  simp[GENLIST_CONS, combinTheory.o_DEF, ADD1] >>
  simp[GENLIST_FUN_EQ]
QED

Theorem intcall_param_taint:
  step_taint (mk_inst id PARAM [Lit idx] [p]) s (update_var p w s) tn =
    tn with t_var := set_var_taint tn.t_var [p] {}
Proof
  simp[step_taint_def, mk_inst_def, mem_taint_def, out_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       taint_component_equality, new_site_bytes_def, step_writes_def,
       written_taint_def, update_var_def, eval_operand_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem intcall_param_safe:
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id PARAM [Lit idx] [p]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       allocas_from_def, step_inst_non_invoke, step_inst_base_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, update_var_def, AllCaseEqs()]
QED

Theorem intcall_param_edge:
  idx < LENGTH s.vs_params /\ idx < LENGTH PG /\ idx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id PARAM [Lit (n2w idx)] [p]) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (set_prov G [p] (EL idx PG))
    (tn with t_var := set_var_taint tn.t_var [p] {})
    (OK ((update_var p (EL idx s.vs_params) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id PARAM [Lit (n2w idx)] [p]) s =
     OK (update_var p (EL idx s.vs_params) s)` by
    simp[Once step_inst_base_def, mk_inst_def, w2n_n2w] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id PARAM [Lit (n2w idx)] [p]) s` by
    simp[intcall_param_safe] >>
  `(mk_inst id PARAM [Lit (n2w idx)] [p]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id PARAM [Lit (n2w idx)] [p]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[intcall_param_step_prov, intcall_param_taint, w2n_n2w,
       mk_inst_def, is_terminator_def]
QED

Theorem intcall_params_path:
  !n id idx nv s G tn.
  idx+n <= LENGTH s.vs_params /\ idx+n <= LENGTH PG /\
  idx+n < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX
    (GENLIST (\j. mk_inst (id+j) PARAM [Lit (n2w (idx+j))]
      [STRING #"%" (toString (nv+j))]) n)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx+n /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn' with t_var := tn.t_var = tn /\
    (!j. j < n ==>
      lookup_var (STRING #"%" (toString (nv+j))) t = SOME (EL (idx+j) s.vs_params) /\
      FLOOKUP G' (STRING #"%" (toString (nv+j))) = EL (idx+j) PG /\
      op_taint tn' (Var (STRING #"%" (toString (nv+j)))) = {}) /\
    (!p. (!j. j < n ==> p <> STRING #"%" (toString (nv+j))) ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    run_inst_seq (GENLIST (\j. mk_inst (id+j) PARAM [Lit (n2w (idx+j))]
      [STRING #"%" (toString (nv+j))]) n) s =
      OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_path_ptr_rules, run_inst_seq_def, venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  `GENLIST (\j. mk_inst (id+j) PARAM [Lit (n2w (idx+j))]
      [STRING #"%" (toString (nv+j))]) (SUC n) =
   mk_inst id PARAM [Lit (n2w idx)] [STRING #"%" (toString nv)] ::
   GENLIST (\j. mk_inst (id+1+j) PARAM [Lit (n2w (idx+1+j))]
      [STRING #"%" (toString (nv+1+j))]) n` by
    simp[GENLIST_CONS, combinTheory.o_DEF, ADD1, GENLIST_FUN_EQ] >>
  qpat_x_assum `GENLIST _ (SUC n) = _` SUBST_ALL_TAC >>
  drule instruction_prefix_cursor >> strip_tac >>
  `idx < LENGTH s.vs_params /\ idx < LENGTH PG /\ idx < dimword (:256)` by
    decide_tac >>
  drule_all intcall_param_edge >>
  disch_then (qspecl_then [`tn`,`G`,`D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ G1 tn1 _` >>
  first_x_assum (qspecl_then [`id+1`,`idx+1`,`nv+1`,`u`] mp_tac) >>
  disch_then (qspecl_then [`G1`,`tn1`] mp_tac) >>
  impl_tac
  >- (simp[Abbr `u`, update_var_def, ADD1] >> conj_tac
      >- (qpat_x_assum `ctx_has_dalloca _ ==> _` mp_tac >>
          simp[allocas_below_fmp_def] >> metis_tac[]) >>
      qpat_x_assum `isPREFIX (GENLIST _ _) _` mp_tac >> simp[ADD1]) >>
  strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> conj_tac
  >- (drule_all (cj 2 gas_path_ptr_rules) >> simp[]) >>
  conj_tac
  >- simp[Abbr `u`, update_var_def, ADD1] >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
      simp[Abbr `u`, update_var_def, venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `tn' with t_var := _ = _` mp_tac >>
      simp[Abbr `tn1`, taint_component_equality]) >>
  conj_tac
  >- suspend "pointwise" >>
  conj_tac
  >- suspend "frame" >>
  conj_tac >- simp[] >>
  suspend "raw"
QED

Resume intcall_params_path[pointwise]:
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = _` kall_tac >>
  qpat_x_assum `tn' with t_var := _ = _` kall_tac >>
  qpat_x_assum `isPREFIX (_::_) _` kall_tac >>
  qpat_x_assum `isPREFIX (GENLIST _ _) _` kall_tac >>
  qpat_x_assum `get_instruction _ _ = _` kall_tac >>
  Cases >> strip_tac
  >- (Cases_on `EL idx PG` >>
      qpat_x_assum `!p. (!j. _ ==> _) ==> _`
        (qspec_then `STRING #"%" (toString nv)` mp_tac) >>
      simp[ASCIInumbersTheory.toString_inj] >>
      simp[Abbr `u`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
           update_var_def, set_prov_def, set_var_taint_def,
           op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, AllCaseEqs()]) >>
  qpat_x_assum `!j. j < n ==> _` (qspec_then `n'` mp_tac) >>
  simp[Abbr `u`, update_var_def, ADD1]
QED

Resume intcall_params_path[frame]:
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = _` kall_tac >>
  qpat_x_assum `tn' with t_var := _ = _` kall_tac >>
  qpat_x_assum `isPREFIX (_::_) _` kall_tac >>
  qpat_x_assum `isPREFIX (GENLIST _ _) _` kall_tac >>
  qpat_x_assum `get_instruction _ _ = _` kall_tac >>
  qx_gen_tac `p` >> strip_tac >>
  qpat_x_assum `!p. (!j. _ ==> _) ==> _` (qspec_then `p` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_assum `!j. j < SUC n ==> _` (qspec_then `SUC j` mp_tac) >>
      gvs[ADD1]) >>
  strip_tac >>
  qpat_assum `!j. j < SUC n ==> _` (qspec_then `0` assume_tac) >>
  Cases_on `EL idx PG` >>
  gvs[Abbr `u`, Abbr `G1`, Abbr `tn1`, lookup_var_def, update_var_def,
       set_prov_def, set_var_taint_def, op_taint_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, AllCaseEqs()] >>
  Cases_on `FLOOKUP tn.t_var p` >> gvs[]
QED

Resume intcall_params_path[raw]:
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = _` kall_tac >>
  qpat_x_assum `tn' with t_var := _ = _` kall_tac >>
  qpat_x_assum `isPREFIX (_::_) _` kall_tac >>
  qpat_x_assum `isPREFIX (GENLIST _ _) _` kall_tac >>
  `run_inst_seq [mk_inst id PARAM [Lit (n2w idx)]
     [STRING #"%" (toString nv)]] s = OK (u with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
         w2n_n2w, Abbr `u`, update_var_def] >>
  irule intcall_run_cursor_cons >> conj_tac
  >- (qexists_tac `u` >> simp[]) >>
  simp[EVERY_GENLIST, mk_inst_def, is_terminator_def]
QED
Finalise intcall_params_path

Theorem intcall_param_decls_path:
  compile_internal_param_decls params idx st = ((caps,next),st') /\
  idx + LENGTH params <= LENGTH s.vs_params /\
  idx + LENGTH params <= LENGTH PG /\
  idx + LENGTH params < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH params /\
    (!j. j < LENGTH caps ==> ?name stack p.
      EL j caps = (name,stack,Var p) /\
      lookup_var p t = SOME (EL (idx+j) s.vs_params) /\
      op_taint tn' (Var p) = {} /\ FLOOKUP G' p = EL (idx+j) PG) /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn' with t_var := tn.t_var = tn /\
    (!p. ~(?name stack. MEM (name,stack,Var p) caps) ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s =
      OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >> drule intcall_param_decls_code >> strip_tac >>
  qpat_x_assum `isPREFIX (DROP _ _) _` mp_tac >>
  simp[DROP_APPEND] >> strip_tac >>
  qpat_x_assum `compile_internal_param_decls _ _ _ = _` kall_tac >>
  qpat_x_assum `st'.cs_next_var = _` kall_tac >>
  qspecl_then [`LENGTH params`,`st.cs_next_id`,`idx`,`st.cs_next_var`]
    mp_tac intcall_params_path >>
  disch_then (qspecl_then [`s`,`G`,`tn`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!j. j < LENGTH params ==> lookup_var _ _ = _ /\ _`
        (qspec_then `j` strip_assume_tac) >> gvs[]) >>
  reverse conj_tac >- fs[ADD_COMM] >>
  qx_gen_tac `p` >> strip_tac >>
  qpat_x_assum `!p. (!j. _ ==> _) ==> _` (qspec_then `p` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_assum `!j. j < LENGTH params ==> EL j caps = _`
        (qspec_then `j` mp_tac) >>
      `MEM (EL j caps) caps` by simp[EL_MEM] >>
      gvs[] >> metis_tac[]) >>
  simp[]
QED

(* Consumer-side compiler freshness uses only the non-output lookup frame;
   no second execution argument is needed. *)
Theorem intcall_param_decls_fresh:
  compile_internal_param_decls params idx st = ((caps,next),st') /\
  fresh_vars_wrt st s /\
  (!p. ~(?name stack. MEM (name,stack,Var p) caps) ==>
    lookup_var p t = lookup_var p s) ==>
  fresh_vars_wrt st' t
Proof
  strip_tac >> drule intcall_param_decls_code >> strip_tac >>
  qpat_x_assum `compile_internal_param_decls _ _ _ = _` kall_tac >>
  qpat_x_assum `st'.cs_current_insts = _` kall_tac >>
  simp[fresh_vars_wrt_def] >> qx_gen_tac `k` >> strip_tac >>
  `~(?name stack. MEM (name,stack,Var (STRING #"%" (toString k))) caps)` by
    (strip_tac >> gvs[MEM_EL] >>
     qpat_x_assum `!j. j < LENGTH params ==> _` drule >>
     simp[ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `lookup_var (STRING #"%" (toString k)) t =
   lookup_var (STRING #"%" (toString k)) s` by metis_tac[] >>
  `STRING #"%" (toString k) NOTIN FDOM s.vs_vars` by
    (fs[fresh_vars_wrt_def] >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `!p. _ ==> lookup_var p t = _`
    (qspec_then `STRING #"%" (toString k)` mp_tac) >>
  simp[lookup_var_def, FLOOKUP_DEF] >>
  Cases_on `STRING #"%" (toString k) IN FDOM t.vs_vars` >>
  gvs[lookup_var_def, FLOOKUP_DEF]
QED

Theorem intcall_param_decls_alloc_bound:
  compile_internal_param_decls params idx st = ((caps,next),st') /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s ==>
  (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id)
Proof
  strip_tac >> drule internal_param_decls_projection >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_allocas`) >> simp[]) >>
  rpt strip_tac >>
  `aid IN FDOM s.vs_allocas` by metis_tac[] >>
  `aid < st.cs_next_id` by metis_tac[] >> decide_tac
QED
