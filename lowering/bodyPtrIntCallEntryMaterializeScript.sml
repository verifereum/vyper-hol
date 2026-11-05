Theory bodyPtrIntCallEntryMaterialize
Ancestors
  bodyPtrIntCallParamPrefix bodyPtrIntCallMaterializeList
  fragGasSeqPtr fragGasPathPtr fragGasSeqAbort ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map words arithmetic pred_set contextCodegenRel codegenRel list rich_list intCallCallee
  bodyPtrDefs valueEncoding compileEnv emitHelper

Theorem intcall_retpc_taint:
  step_taint (mk_inst id RETPC_PARAM [Lit idx] [p]) s
    (update_var p s.vs_return_pc_token s) tn =
    tn with t_var := set_var_taint tn.t_var [p] {}
Proof
  simp[step_taint_def, mk_inst_def, mem_taint_def, out_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       taint_component_equality, new_site_bytes_def, step_writes_def,
       written_taint_def, update_var_def, eval_operand_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem intcall_retpc_edge:
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id RETPC_PARAM [Lit idx] [p]) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (set_prov G [p] NONE)
    (tn with t_var := set_var_taint tn.t_var [p] {})
    (OK ((update_var p s.vs_return_pc_token s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id RETPC_PARAM [Lit idx] [p]) s =
     OK (update_var p s.vs_return_pc_token s)` by
    simp[Once step_inst_base_def, mk_inst_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id RETPC_PARAM [Lit idx] [p]) s` by
    simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
         allocas_from_def, step_inst_non_invoke, step_inst_base_def,
         codegenRelTheory.source_memory_write_ranges_def,
         source_memory_read_ranges_def,
         op_taint_def, update_var_def, AllCaseEqs()] >>
  `(mk_inst id RETPC_PARAM [Lit idx] [p]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id RETPC_PARAM [Lit idx] [p]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[step_prov_def, out_prov_def, intcall_retpc_taint,
       mk_inst_def, is_terminator_def]
QED

Theorem intcall_retpc_path:
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id RETPC_PARAM [Lit idx] [p]) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    lookup_var p t = SOME s.vs_return_pc_token /\
    FLOOKUP G' p = NONE /\ op_taint tn' (Var p) = {} /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    tn' with t_var := tn.t_var = tn /\
    (!q. q <> p ==> lookup_var q t = lookup_var q s /\
      FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule_all intcall_retpc_edge >> strip_tac >>
  qexistsl_tac [`(update_var p s.vs_return_pc_token s) with
                  vs_inst_idx := SUC s.vs_inst_idx`,
               `set_prov G [p] NONE`,
               `tn with t_var := set_var_taint tn.t_var [p] {}`] >>
  conj_tac
  >- (qpat_x_assum `!tn PG G D. _`
        (qspecl_then [`tn`,`PG`,`G`,`D`] assume_tac) >>
      drule (cj 2 gas_path_ptr_rules) >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[gas_path_ptr_rules, update_var_def]) >>
  simp[lookup_var_def, update_var_def, set_prov_def, set_var_taint_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> Cases_on `FLOOKUP tn.t_var q` >> simp[]
QED

(* Indexed capture connects the semantic argument package to pending locals.
   Memory robustness is an independent pointer input, not an S1 consequence. *)
Theorem intcall_captured_pending:
  internal_args_rel ce params src argbase args frontier mem /\
  LENGTH caps = LENGTH params /\
  (!i. i < LENGTH params ==> ?p.
    EL i caps = (FST (EL i params), SND (EL i params), Var p) /\
    lookup_var p s = SOME (EL (argbase+i) args) /\
    op_taint tn (Var p) = {} /\
    (~SND (EL i params) ==> !entry off sz.
      FLOOKUP src (FST (EL i params)) = SOME entry /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
      ptr_covers G tn p s sz /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory entry.type entry.value (w2n (EL (argbase+i) args)) m))) /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) /\
  s.vs_alloca_next = frontier ==>
  intcall_pending src ce caps G tn s
Proof
  strip_tac >> simp[intcall_pending_def, EVERY_EL] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
  qpat_x_assum `internal_args_rel _ _ _ _ _ _ _` mp_tac >>
  simp[internal_args_rel_def] >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH params ==> ?off sz entry. _`
    drule >> strip_tac >>
  simp[] >> qexists_tac `EL (argbase+i) args` >>
  simp[eval_operand_def] >>
  Cases_on `SND (EL i params)` >> gvs[] >>
  simp[intcall_local_value_def] >>
  `val_footprint entry.type entry.value <= sz` by metis_tac[] >>
  `ptr_covers G tn p s sz /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory entry.type entry.value (w2n (EL (argbase+i) args)) m)`
    by metis_tac[] >>
  simp[]
QED

Theorem intcall_captured_ready:
  internal_args_rel ce params src argbase args frontier mem /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  intcall_pending src ce caps G tn s /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) ==>
  intcall_mat_ready src FEMPTY ce caps st G tn s
Proof
  strip_tac >>
  `MAP FST caps = MAP FST params` by
    (qpat_x_assum `MAP _ caps = params` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, ETA_THM]) >>
  `ALL_DISTINCT (MAP FST caps) /\ FDOM src = set (MAP FST caps)` by
    fs[internal_args_rel_def] >>
  simp[intcall_mat_ready_def, intcall_completed_def,
       intcall_coverage_def] >> conj_tac
  >- simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
  simp[intcall_pending_sizes_def, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> simp[] >> metis_tac[]
QED

Theorem intcall_entry_prefix_split:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) ==>
  ?rb st0 st1 next.
    (if has_rb then
       do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st = (rb,st0) /\
    compile_internal_param_decls params (if has_rb then 1 else 0) st0 =
      ((caps,next),st1) /\
    emit_op RETPC_PARAM [Lit (n2w next)] st1 = (rpc,stm) /\
    ce1 = ce with <|ce_return_buf :=
      (case (rb,ce.ce_return_buf) of
         (SOME p,SOME (MemLoc off sz)) => SOME (PtrVar p sz)
       | _ => ce.ce_return_buf);
      ce_return_pc := SOME (PtrVar rpc 0)|>
Proof
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  PairCases_on `pr` >> gvs[] >> metis_tac[]
QED

Theorem intcall_capture_retpc_path:
  emit_op RETPC_PARAM [Lit idx] st = (rpc,st') /\
  fresh_vars_wrt st s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn' p.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    rpc = Var p /\ not_fresh_at st' p /\
    lookup_var p t = SOME s.vs_return_pc_token /\
    FLOOKUP G' p = NONE /\ op_taint tn' rpc = {} /\
    fresh_vars_wrt st' t /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    tn' with t_var := tn.t_var = tn /\
    (!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id RETPC_PARAM [Lit idx]
       [STRING #"%" (toString st.cs_next_var)])` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     pure_rewrite_tac[DROP_LENGTH_APPEND] >> strip_tac >>
     drule instruction_prefix_cursor >> simp[]) >>
  drule_all intcall_retpc_path >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  simp[fresh_vars_wrt_def] >> qx_gen_tac `k` >> strip_tac >>
      `STRING #"%" (toString k) <> STRING #"%" (toString st.cs_next_var)`
        by simp[ASCIInumbersTheory.toString_inj] >>
      `lookup_var (STRING #"%" (toString k)) t =
       lookup_var (STRING #"%" (toString k)) s` by metis_tac[] >>
      `STRING #"%" (toString k) NOTIN FDOM s.vs_vars` by
        (fs[fresh_vars_wrt_def] >> first_x_assum irule >> decide_tac) >>
      qpat_x_assum `!q. q <> _ ==> _`
        (qspec_then `STRING #"%" (toString k)` mp_tac) >>
      simp[ASCIInumbersTheory.toString_inj] >>
      Cases_on `STRING #"%" (toString k) IN FDOM t.vs_vars` >>
      gvs[lookup_var_def, FLOOKUP_DEF]
QED

Theorem intcall_capture_return_buffer_path:
  (if has_rb then
     do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
   else return NONE) st = (rb,st') /\
  fresh_vars_wrt st s /\
  (has_rb ==> s.vs_params <> [] /\ PG <> []) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    (has_rb ==> ?p. rb = SOME (Var p) /\ not_fresh_at st' p /\
      lookup_var p t = SOME (HD s.vs_params) /\
      FLOOKUP G' p = HD PG /\ op_taint tn' (Var p) = {}) /\
    (~has_rb ==> rb = NONE) /\ fresh_vars_wrt st' t /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    t.vs_inst_idx = s.vs_inst_idx + (if has_rb then 1 else 0) /\
    tn' with t_var := tn.t_var = tn /\
    st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id /\
    (!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  reverse (Cases_on `has_rb`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >> simp[gas_path_ptr_rules]) >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id PARAM [Lit 0w]
       [STRING #"%" (toString st.cs_next_var)])` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     pure_rewrite_tac[DROP_LENGTH_APPEND] >> strip_tac >>
     drule instruction_prefix_cursor >> simp[]) >>
  `0 < LENGTH s.vs_params /\ 0 < LENGTH PG /\ 0 < dimword (:256)` by
    (Cases_on `s.vs_params` >> Cases_on `PG` >> gvs[]) >>
  drule_all intcall_param_edge >>
  disch_then (qspecl_then [`tn`,`G`,`D`] assume_tac) >>
  qexistsl_tac [`(update_var (STRING #"%" (toString st.cs_next_var))
                    (HD s.vs_params) s) with vs_inst_idx := SUC s.vs_inst_idx`,
               `set_prov G [STRING #"%" (toString st.cs_next_var)] (HD PG)`,
               `tn with t_var := set_var_taint tn.t_var
                  [STRING #"%" (toString st.cs_next_var)] {}`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[EL, HD] >> strip_tac >>
      drule (cj 2 gas_path_ptr_rules) >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[gas_path_ptr_rules, update_var_def]) >>
  Cases_on `HD PG` >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj,
       lookup_var_def, update_var_def, set_prov_def, set_var_taint_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, fresh_vars_wrt_def] >>
  rpt strip_tac >> fs[fresh_vars_wrt_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* All PARAMs in the entry header form one consecutive indexed block,
   including the optional return-buffer capture. RETPC_PARAM is separate. *)
Theorem intcall_entry_prefix_code:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) ==>
  ?rid idx.
    LENGTH caps = LENGTH params /\
    MAP (\c. (FST c,FST (SND c))) caps = params /\
    (!i. i < LENGTH params ==> EL i caps =
      (FST (EL i params), SND (EL i params),
       Var (STRING #"%" (toString (st.cs_next_var + (if has_rb then 1 else 0) + i))))) /\
    rpc = Var (STRING #"%" (toString
      (st.cs_next_var + (if has_rb then 1 else 0) + LENGTH params))) /\
    stm.cs_next_var = st.cs_next_var + (if has_rb then 1 else 0) + LENGTH params + 1 /\
    st.cs_next_id <= stm.cs_next_id /\
    stm.cs_current_insts = st.cs_current_insts ++
      GENLIST (\j. mk_inst (st.cs_next_id+j) PARAM [Lit (n2w j)]
        [STRING #"%" (toString (st.cs_next_var+j))])
        ((if has_rb then 1 else 0) + LENGTH params) ++
      [mk_inst rid RETPC_PARAM [Lit idx]
        [STRING #"%" (toString
          (st.cs_next_var + (if has_rb then 1 else 0) + LENGTH params))]] /\
    ce1 = ce with <|ce_return_buf :=
      (if has_rb then
         case ce.ce_return_buf of
           SOME (MemLoc off sz) => SOME (PtrVar (Var
             (STRING #"%" (toString st.cs_next_var))) sz)
         | _ => ce.ce_return_buf
       else ce.ce_return_buf);
      ce_return_pc := SOME (PtrVar rpc 0)|>
Proof
  strip_tac >> drule intcall_entry_prefix_split >> strip_tac >>
  drule intcall_param_decls_code >> strip_tac >>
  drule internal_param_decls_projection >> strip_tac >>
  qpat_x_assum `compile_internal_entry_prefix _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_internal_param_decls _ _ _ = _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  qpat_x_assum `ce1 = _` SUBST_ALL_TAC >>
  Cases_on `has_rb` >>
  qpat_x_assum `(if _ then _ else _) st = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, NoAsms] >> strip_tac >>
  qpat_x_assum `_ = st0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `(_:operand option) = _` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _; cs_current_insts := _|> = _`
    (SUBST_ALL_TAC o SYM) >>
  qexistsl_tac [`st1.cs_next_id`,`n2w next`] >>
  simp[GSYM ADD1, GENLIST_CONS, combinTheory.o_DEF, GENLIST_FUN_EQ] >>
  rpt strip_tac >> simp[ADD1]
QED

Theorem intcall_header_path:
  n <= LENGTH s.vs_params /\ n <= LENGTH PG /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (GENLIST (\j. mk_inst (id+j) PARAM [Lit (n2w j)]
      [STRING #"%" (toString (nv+j))]) n ++
    [mk_inst rid RETPC_PARAM [Lit idx] [STRING #"%" (toString (nv+n))]])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx+n+1 /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn' with t_var := tn.t_var = tn /\
    (!j. j < n ==>
      lookup_var (STRING #"%" (toString (nv+j))) t = SOME (EL j s.vs_params) /\
      FLOOKUP G' (STRING #"%" (toString (nv+j))) = EL j PG /\
      op_taint tn' (Var (STRING #"%" (toString (nv+j)))) = {}) /\
    lookup_var (STRING #"%" (toString (nv+n))) t = SOME s.vs_return_pc_token /\
    FLOOKUP G' (STRING #"%" (toString (nv+n))) = NONE /\
    op_taint tn' (Var (STRING #"%" (toString (nv+n)))) = {} /\
    (!p. (!j. j <= n ==> p <> STRING #"%" (toString (nv+j))) ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `isPREFIX (GENLIST (\j. mk_inst (id+j) PARAM [Lit (n2w j)]
      [STRING #"%" (toString (nv+j))]) n)
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  qspecl_then [`n`,`id`,`0`,`nv`,`s`,`G`,`tn`] mp_tac intcall_params_path >>
  impl_tac >- fs[ADD_COMM] >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
   t.vs_return_pc_token = s.vs_return_pc_token` by
    (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `get_instruction bb t.vs_inst_idx = SOME
    (mk_inst rid RETPC_PARAM [Lit idx] [STRING #"%" (toString (nv+n))])` by
    (qpat_x_assum `isPREFIX (_ ++ [_]) _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     `DROP t.vs_inst_idx bb.bb_instructions =
       DROP n (DROP s.vs_inst_idx bb.bb_instructions)` by simp[DROP_DROP_T, ADD_COMM] >>
     `isPREFIX [mk_inst rid RETPC_PARAM [Lit idx]
        [STRING #"%" (toString (nv+n))]]
        (DROP t.vs_inst_idx bb.bb_instructions)` by
       (asm_rewrite_tac[] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, IS_PREFIX_APPEND]) >>
     drule instruction_prefix_cursor >> simp[]) >>
  `~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all intcall_retpc_path >>
  disch_then (qspecl_then [`tn'`,`PG`,`G'`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t'`,`G''`,`tn''`] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  suspend "finish"
QED

Resume intcall_header_path[finish]:
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `isPREFIX (_ ++ _) _` kall_tac >>
  qpat_x_assum `isPREFIX (GENLIST _ _) _` kall_tac >>
  qpat_x_assum `get_instruction _ _ = _` kall_tac >>
  conj_tac >- simp[ADD1] >>
  conj_tac
  >- (qpat_x_assum `t' with <|vs_vars := _; vs_inst_idx := _|> = t` mp_tac >>
      qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `tn'' with t_var := _ = tn'` mp_tac >>
      qpat_x_assum `tn' with t_var := _ = tn` mp_tac >>
      simp[taint_component_equality]) >>
  simp[]
QED
Finalise intcall_header_path

Theorem intcall_entry_prefix_path:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH PG /\
  (if has_rb then 1 else 0) + LENGTH params < dimword (:256) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) stm.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    fresh_vars_wrt stm t /\
    (!aid. aid IN FDOM t.vs_allocas ==> aid < stm.cs_next_id) /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn' with t_var := tn.t_var = tn /\
    t.vs_inst_idx = s.vs_inst_idx + (if has_rb then 1 else 0) + LENGTH params + 1 /\
    (!i. i < LENGTH params ==> ?p.
      EL i caps = (FST (EL i params), SND (EL i params), Var p) /\
      lookup_var p t = SOME (EL ((if has_rb then 1 else 0)+i) s.vs_params) /\
      FLOOKUP G' p = EL ((if has_rb then 1 else 0)+i) PG /\
      op_taint tn' (Var p) = {}) /\
    eval_operand rpc t = SOME s.vs_return_pc_token /\ op_taint tn' rpc = {} /\
    (!p k. ce1.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at stm p) /\
    (has_rb ==> not_fresh_at stm (STRING #"%" (toString st.cs_next_var)) /\
      lookup_var (STRING #"%" (toString st.cs_next_var)) t = SOME (HD s.vs_params) /\
      FLOOKUP G' (STRING #"%" (toString st.cs_next_var)) = HD PG /\
      op_taint tn' (Var (STRING #"%" (toString st.cs_next_var))) = {}) /\
    (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule intcall_entry_prefix_code >> strip_tac >>
  qpat_x_assum `compile_internal_entry_prefix _ _ _ _ = _` kall_tac >>
  qpat_x_assum `isPREFIX (DROP _ _) _` mp_tac >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, GSYM ADD_ASSOC] >> strip_tac >>
  drule_all intcall_header_path >>
  disch_then (qspecl_then [`tn`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> simp[] >>
  suspend "endpoint"
QED

Resume intcall_entry_prefix_path[endpoint]:
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  qpat_x_assum `stm.cs_current_insts = _` kall_tac >>
  qpat_x_assum `ce1 = _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH params ==> EL i caps = _` kall_tac >>
  qpat_x_assum `rpc = _` kall_tac >>
  qpat_x_assum `MAP _ caps = params` kall_tac >>
  conj_tac >- suspend "fresh" >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
      simp[venom_state_component_equality] >> rpt strip_tac >>
      first_x_assum drule >> decide_tac) >>
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >>
      qpat_x_assum `!j. j < _ ==> _`
        (qspec_then `i + if has_rb then 1 else 0` mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `lookup_var _ t = SOME s.vs_return_pc_token` mp_tac >>
      simp[NoAsms, eval_operand_def, AC ADD_ASSOC ADD_COMM]) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  conj_tac >- decide_tac >>
  reverse (Cases_on `has_rb`) >- simp[] >>
  qpat_x_assum `!j. j < _ ==> _` (qspec_then `0` mp_tac) >> simp[EL]
QED

Resume intcall_entry_prefix_path[fresh]:
  simp[fresh_vars_wrt_def] >> qx_gen_tac `k` >> strip_tac >>
  `(!j. j <= (if has_rb then 1 else 0) + LENGTH params ==>
     STRING #"%" (toString k) <> STRING #"%" (toString (st.cs_next_var+j)))` by
    (simp[ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     Cases_on `has_rb` >> fs[] >> decide_tac) >>
  qpat_x_assum `!p. (!j. j <= _ ==> _) ==> _` drule >> strip_tac >>
  `STRING #"%" (toString k) NOTIN FDOM s.vs_vars` by
    (fs[fresh_vars_wrt_def] >> first_x_assum irule >>
     Cases_on `has_rb` >> fs[] >> decide_tac) >>
  fs[lookup_var_def, FLOOKUP_DEF] >>
  Cases_on `STRING #"%" (toString k) IN FDOM t.vs_vars` >> gvs[]
QED
Finalise intcall_entry_prefix_path
