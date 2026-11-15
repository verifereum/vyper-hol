(* Joint pointer and memory certificates for the caller's result stores. *)
Theory intCallResultFull
Ancestors
  intCallResult bodyPtrMakeArrayCopyStep compileEnv
  valueEncodingDefs
  fragGasOriginPtrLoop instSeqComposePtr typedCopyPtr
  exprLowering exprLoweringProps emitHelper emitHelperProps freshWrites
  fragExecMem bodyPtrDefs loweringStateRelDefs ptrDiscipline venomState venomExecSemantics
  venomInst finite_map words arithmetic list rich_list pred_set
  fragGasSeqPtr memSafeRun unitTransformDefs ptrSafetyTransport

Theorem ptr_inst_ok_result_add_conditional:
  op_taint tn left = {} /\ op_taint tn right = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id ADD [left;right] [tmp]) s
Proof
  rpt strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ptr_inst_ok_result_mstore_conditional:
  ptr_covers G tn p s 32 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p;v] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[memLocDefsTheory.mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem store_result_head_checked[local]:
  emit_op ADD [Var root; Lit (n2w off)] sa = (dst,sm) /\
  emit_void MSTORE [dst;op] sm = ((),sb) /\
  not_fresh_at sa root /\ (!x. op = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME b /\ eval_operand op s = SOME w /\
  ptr_covers G tn root s cap /\ op_taint tn op = {} /\
  off + 32 <= cap /\ w2n b + cap < dimword (:256) /\
  w2n b + cap <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s ==>
  ?u H qt.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
            (s with vs_inst_idx := k) H qt) /\
    u.vs_memory = (mstore (w2n b + off) w s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    qt.t_mem = tn.t_mem DIFF {i | w2n b + off <= i /\ i < w2n b + off + 32} /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[] >>
  qabbrev_tac `tmp = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> tmp` by
    (simp[Abbr `tmp`, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `w2n (b + n2w off) = w2n b + off` by
    ((bossLib.simp [wordsTheory.word_add_def , wordsTheory.w2n_n2w])) >>
  qabbrev_tac `u = update_var tmp (b + n2w off) s` >>
  `eval_operand op u = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def, Abbr `u`, lookup_var_update_var] >>
     metis_tac[]) >>
  qabbrev_tac `ia = mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [tmp]` >>
  qabbrev_tac `im = mk_inst (sa.cs_next_id+1) MSTORE [Var tmp;op] []` >>
  `step_inst_base ia s = OK u` by
    simp[Abbr `ia`, Abbr `u`, step_inst_base_def, mk_inst_def,
         exec_pure2_def, eval_operand_def] >>
  `lookup_var tmp u = SOME (b + n2w off)` by
    simp[Abbr `u`, lookup_var_update_var] >>
  `step_inst_base im u = OK (mstore (w2n b + off) w u)` by
    simp[Abbr `im`, step_inst_base_def, mk_inst_def, exec_write2_def,
         eval_operand_def] >>
  qabbrev_tac `H = step_prov PG G ia u` >>
  qabbrev_tac `tm = step_taint ia s u tn` >>
  `ptr_covers H tm tmp (u with vs_inst_idx := SUC s.vs_inst_idx) 32` by
    (gvs[ptr_covers_def] >>
     simp[ptr_covers_def, Abbr `H`, Abbr `tm`, Abbr `ia`, Abbr `u`,
          copy_len_binop_ghost_frame, lookup_var_update_var,
          step_prov_def, set_prov_def, out_prov_def, first_prov_def,
          op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `emitted_insts sa sb = [ia;im]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `step_inst_base im (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (mstore (w2n b + off) w u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `im`, step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, mstore_def]) >>
  qexistsl_tac [`mstore (w2n b + off) w u`, `H`,
    `step_taint im u (mstore (w2n b + off) w u) tm`] >>
  conj_tac >- (simp[run_inst_seq_def] >>
    simp[Abbr `ia`, Abbr `im`, mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (simp[run_inst_seq_mem_ok_def] >>
      simp[Abbr `ia`, Abbr `im`, mk_inst_def,
           codegenRelTheory.fixed_source_write_range_def,
           inst_mem_below_frontier_def, inst_dload_in_section_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def,
           eval_operand_def] >>
      simp[Abbr `u`, update_var_def] >> decide_tac) >>
  conj_tac
  >- (map_every qx_gen_tac [`D`,`k`] >>
      `!j. step_inst_base ia (s with vs_inst_idx := j) =
             OK (u with vs_inst_idx := j)` by
        simp[instIdxIndepTheory.step_inst_inst_idx_indep,
             Abbr `ia`, mk_inst_def, is_terminator_def, instIdxIndepTheory.exec_result_map_def] >>
      `!j. step_inst_base im (u with vs_inst_idx := j) =
             OK (mstore (w2n b+off) w u with vs_inst_idx := j)` by
        simp[instIdxIndepTheory.step_inst_inst_idx_indep,
             Abbr `im`, mk_inst_def, is_terminator_def, instIdxIndepTheory.exec_result_map_def] >>
      simp[inst_seq_ptr_def,
           ghostPcTransportPtrTheory.step_prov_inst_idx,
           ghostPcTransportPtrTheory.step_taint_inst_idx] >>
      simp[Abbr `im`, mk_inst_def, Abbr `H`, Abbr `tm`,
           step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
      conj_tac
      >- (simp[Abbr `ia`] >> irule ptr_inst_ok_lower_bound_transport >>
     (conj_tac >- (fs[allocas_from_def, Abbr `u`, update_var_def] >> metis_tac[])) >>
     qexists `0` >>
     simp[] >>
     irule ptr_inst_ok_result_add_conditional >>
          gvs[ptr_covers_def, eval_operand_def, op_taint_def,
              allocas_below_fmp_def] >> metis_tac[]) >>
      simp[GSYM mk_inst_def] >> irule ptr_inst_ok_lower_bound_transport >>
     (conj_tac >- (fs[allocas_from_def, Abbr `u`, update_var_def] >> metis_tac[])) >>
     qexists `0` >>
      simp[] >>
      irule ptr_inst_ok_result_mstore_conditional >>
      gvs[Abbr `ia`, step_prov_def, set_prov_def, ptr_covers_def,
          allocas_below_fmp_def, Abbr `u`, update_var_def] >> metis_tac[]) >>
  `op_taint tm op = {}` by
    (Cases_on `op` >> gvs[] >>
     simp[Abbr `tm`, Abbr `ia`, Abbr `u`, copy_len_binop_ghost_frame,
          op_taint_def, step_taint_def, set_var_taint_def, mk_inst_def,
          FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[op_taint_def]) >>
  `(step_taint im u (mstore (w2n b+off) w u) tm).t_var = tm.t_var /\
    (step_taint im u (mstore (w2n b+off) w u) tm).t_mem =
       tm.t_mem DIFF {i | w2n b+off <= i /\ i < w2n b+off+32} /\
    (step_taint im u (mstore (w2n b+off) w u) tm).t_stor = tm.t_stor /\
    (step_taint im u (mstore (w2n b+off) w u) tm).t_trans = tm.t_trans /\
    (step_taint im u (mstore (w2n b+off) w u) tm).t_imm = tm.t_imm` by
    (qpat_assum `lookup_var tmp u = _`
       (mp_then Any mp_tac mstore_raw_ghost_frame) >>
     disch_then drule >>
     simp[Abbr `im`]) >>
  simp[op_taint_def] >>
  simp[Abbr `H`, Abbr `tm`, Abbr `ia`, Abbr `u`,
       copy_len_binop_ghost_frame] >>
  simp[mstore_def, update_var_def, venom_state_component_equality,
       lookup_var_def, FLOOKUP_UPDATE] >>
  simp[step_taint_def, set_var_taint_def, imm_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem store_multi_results_checked[local]:
  !ops root off sa sb s b cap G tn.
    store_multi_results (Var root) ops off sa = ((),sb) /\
    not_fresh_at sa root /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    lookup_var root s = SOME b /\
    (!op. MEM op ops ==> ?w. eval_operand op s = SOME w) /\
    ptr_covers G tn root s cap /\
    EVERY (\op. op_taint tn op = {}) ops /\
    off + 32 * LENGTH ops <= cap /\
    w2n b + cap < dimword (:256) /\
    w2n b + cap <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s ==>
    ?u H qt.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
             (s with vs_inst_idx := k) H qt) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint qt (Var x) = op_taint tn (Var x)) /\
      qt.t_mem = tn.t_mem DIFF
        {i | w2n b + off <= i /\ i < w2n b + off + 32 * LENGTH ops} /\
      qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
      EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct
  >- (rpt strip_tac >>
      gvs[store_multi_results_def, comp_return_def, emitted_insts_def] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[run_inst_seq_def, run_inst_seq_mem_ok_def, inst_seq_ptr_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `store_multi_results _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (z,post)` >> Cases_on `z` >>
  `?w. eval_operand h s = SOME w` by metis_tac[MEM] >>
  `!x. h = Var x ==> not_fresh_at sa x` by metis_tac[MEM] >>
  `off + 32 <= cap /\ op_taint tn h = {}` by gvs[] >>
  drule_all store_result_head_checked >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `sa.cs_next_var <= post.cs_next_var /\
   post.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa post` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at post x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `lookup_var root u = SOME b /\ ptr_covers H qt root u cap` by
    gvs[ptr_covers_def] >>
  `!op. MEM op ops ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >> irule store_result_operand_frame >>
     simp[] >> qexists `sa` >> simp[] >> metis_tac[MEM]) >>
  `EVERY (\op. op_taint qt op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `op_taint tn op = {}` by metis_tac[] >>
     Cases_on `op` >> simp[op_taint_def] >>
     `not_fresh_at sa s'` by metis_tac[MEM] >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
     gvs[op_taint_def]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_alloca_next``) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o AP_TERM ``\z. (z.vs_initial_fmp,z.vs_fmp,z.vs_allocas)``) >>
     simp[allocas_below_fmp_def] >> metis_tac[allocas_below_fmp_def]) >>
  `allocas_from lo u` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >>
     simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  qpat_x_assum `!root off sa sb s b cap G tn. _` drule >>
  disch_then (qspecl_then [`u`,`b`,`cap`,`H`,`qt`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[MEM, MULT_CLAUSES] >> metis_tac[])) >>
  strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa post) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa post)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `post.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `mid.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  qexistsl [`u'`,`H'`,`qt'`] >>
  conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac >- (simp[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  conj_tac >- (gen_tac >> simp[] >> irule inst_seq_ptr_uniform_append >>
               conj_tac >- (qexistsl [`H`,`u`,`qt`] >> simp[]) >> simp[]) >>
  conj_tac >- gvs[venom_state_component_equality] >>
  conj_tac >- metis_tac[] >>
  simp[EVERY_APPEND] >> simp[EXTENSION, IN_DIFF, MULT_CLAUSES] >> gen_tac >>
  Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac
QED

Theorem store_multi_results_origin_ptr:
  store_multi_results (Var root) ops off sa = ((),sb) /\
  not_fresh_at sa root /\
  (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
  lookup_var root s = SOME b /\
  MAP (\op. eval_operand op s) ops = MAP SOME ws /\
  ptr_covers G tn root s cap /\ EVERY (\op. op_taint tn op = {}) ops /\
  off + 32 * LENGTH ops <= cap /\ w2n b + cap < dimword (:256) /\
  w2n b + cap <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u H qt.
    (!D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),H,qt)) /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    qt.t_mem = tn.t_mem DIFF
      {i | w2n b + off <= i /\ i < w2n b + off + 32 * LENGTH ops} /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!mem i. mem_agree_outside qt.t_mem u.vs_memory mem /\ i < LENGTH ws ==>
      mem_word_at (w2n b + off + 32 * i) mem = EL i ws) /\
    (!a len. a + len <= w2n b + off \/
             w2n b + off + 32 * LENGTH ops <= a ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  `!op. MEM op ops ==> ?w. eval_operand op s = SOME w` by
    (rpt strip_tac >>
     `MEM (eval_operand op s) (MAP SOME ws)` by
       (qpat_x_assum `MAP _ ops = _` (fn th => pure_rewrite_tac[GSYM th]) >>
        simp[MEM_MAP] >> qexists `op` >> simp[]) >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  drule_all store_multi_results_checked >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `eval_operand (Var root) s = SOME (n2w (w2n b))` by
    simp[eval_operand_def] >>
  `w2n b + off + 32 * LENGTH ops < dimword (:256)` by decide_tac >>
  drule store_multi_results_run >>
  disch_then (qspecl_then [`s`,`w2n b`,`ws`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t = u` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  `LENGTH ws = LENGTH ops` by
    (qpat_x_assum `MAP _ ops = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qexistsl [`u`,`H`,`qt`] >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
      conj_tac >- simp[] >> qexists `sa` >>
      drule store_multi_results_shape >> strip_tac >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H qt` by
        (qpat_x_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
           (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
      simp[inst_extends_def] >> fs[same_blocks_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >> reverse conj_tac >- fs[] >> rpt strip_tac >>
  `mem_bytes_at (w2n b + off + 32 * i) 32 u.vs_memory =
   mem_bytes_at (w2n b + off + 32 * i) 32 mem` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < 32` >>
     `mem_bytes_at (w2n b + off + 32 * i + j) 1 u.vs_memory =
      mem_bytes_at (w2n b + off + 32 * i + j) 1 mem` by
       (fs[mem_agree_outside_def] >>
        first_x_assum irule >> simp[IN_DIFF] >> decide_tac) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = _` mp_tac >>
     simp[LIST_EQ_REWRITE, valueEncodingProofsTheory.EL_mem_bytes_at]) >>
  gvs[mem_word_at_def, mem_bytes_at_def] >> metis_tac[]
QED
