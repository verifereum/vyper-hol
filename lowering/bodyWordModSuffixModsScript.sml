(* Linked ASSERT/ADDMOD and ASSERT/MULMOD tails.  The physical endpoint
   is shared by all storage horizons; only the dead mask varies. *)
Theory bodyWordModSuffixMods
Ancestors
  bodyForRangeScalarFrameMods stateRelProj bodyPtrDefs bodyFullShadowBodyInv bodyFullPostsMods
  allocasBelowFmpUpdatesProps
  fragGasSeqPtr fragGasOriginPtr fragGasEmitCtrl exprSimWordBuiltins exprSimWordArgs exprSimDefs exprLoweringProps
  emitHelperProps emitHelper builtinMath fragExec allocaHistory instMemFrontier
  ptrDisciplineEmptyTaint lowerDloadPtrScalar decoderGhostFramePtr ptrDiscipline ptrSafeRun
  venomExecSemantics venomState venomInst venomMemDefs venomMemProofs memSafeRun compileEnv
  unitTransformDefs contextCodegenRel codegenRel
  vyperInterpreter vyperContext vyperStorageFootprint loweringStateRelDefs
  builtinSimple builtinMisc bodyPtrWordBuiltinsModularSource list rich_list finite_map words

Theorem modular_layout[local]:
  (bt = AddMod \/ bt = MulMod) /\
  (if bt = AddMod then compile_addmod else compile_mulmod) x y z sm = (op,sb) ==>
  let out = STRING #"%" (toString sm.cs_next_var);
      i = mk_inst sm.cs_next_id ASSERT [z] [];
      j = mk_inst (sm.cs_next_id + 1) (if bt = AddMod then ADDMOD else MULMOD)
            [x;y;z] [out]
  in
    emitted_insts sm sb = [i;j] /\ op = Var out /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ [i;j]
Proof
  Cases_on `bt = AddMod` >> simp[] >> strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  simp[compile_addmod_def, compile_mulmod_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem modular_assert[local]:
  i = mk_inst id ASSERT [z] [] /\
  eval_operand z t = SOME vc /\ op_taint tn z = {} /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME i /\ ~t.vs_halted /\
  fn_inst_ids_distinct func /\ alloca_history func t /\ alloca_inv t /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  let t1 = t with vs_inst_idx := SUC t.vs_inst_idx in
  (vc = 0w ==> !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (t,G,tn) [] (Abort Revert_abort (revert_state (set_returndata [] t)),G,tn)) /\
  (vc <> 0w ==> alloca_history func t1 /\
     !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK t1,G,tn))
Proof
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn (mk_inst id ASSERT [z] []) t` by
    (gen_tac >> Cases_on `vc = 0w` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  Cases_on `vc = 0w` >> simp[]
  >- (gen_tac >> irule exit_inst_origin_ptr >> simp[exit_result_def] >>
      simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
           exit_result_def, mem_safe_step_non_invoke, inst_mem_below_frontier_def,
           inst_dload_in_section_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, gasEventsTheory.gas_events_step_def,
           gasCountTheory.gas_count_step_def]) >>
  `step_inst_base (mk_inst id ASSERT [z] []) t = OK t` by
    simp[mk_inst_def, step_inst_base_opcode_eqs] >>
  conj_tac
  >- (`step_inst_base i t = OK t` by simp[] >>
      drule_all_then mp_tac alloca_history_base_step >>
      simp[mk_inst_def, is_terminator_def]) >>
  `step_prov PG G (mk_inst id ASSERT [z] []) t = G /\
   step_taint (mk_inst id ASSERT [z] []) t t tn = tn` by
    simp[mk_inst_def, step_prov_def, out_prov_def, set_prov_def,
         step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
         adopt_reset_def, step_writes_def, source_memory_write_ranges_def,
         range_bytes_def, set_var_taint_def, new_site_bytes_def,
         written_taint_def, DRESTRICT_UNIV, taint_component_equality,
         FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gen_tac >>
  mp_tac (Q.INST [`i` |-> `mk_inst id ASSERT [z] []`, `s` |-> `t`, `u` |-> `t`,
      `G` |-> `G`, `tn` |-> `tn`, `lo` |-> `lo`, `D` |-> `D`]
    straight_line_origin_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  disch_then irule >> simp[mk_inst_def]
QED

Theorem modular_apply[local]:
  (bt = AddMod \/ bt = MulMod) /\
  j = mk_inst id (if bt = AddMod then ADDMOD else MULMOD) [x;y;z] [out] /\
  eval_operand x t1 = SOME va /\ eval_operand y t1 = SOME vb /\
  eval_operand z t1 = SOME vc /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ op_taint tn z = {} /\
  lookup_block t1.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t1.vs_inst_idx = SOME j /\ ~t1.vs_halted /\
  fn_inst_ids_distinct func /\ alloca_history func t1 /\ alloca_inv t1 /\ allocas_from lo t1 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t1) ==>
  let w = (if bt = AddMod then addmod else mulmod) va vb vc;
      u = update_var out w t1;
      t2 = u with vs_inst_idx := SUC t1.vs_inst_idx;
      G' = step_prov PG G j u;
      tn' = tn with t_var := tn.t_var |+ (out,{})
  in
    alloca_history func t2 /\ op_prov G' (Var out) = NONE /\
    (!old. old <> out ==> FLOOKUP G' old = FLOOKUP G old) /\
    (!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t1,G,tn) [] (OK t2,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[LET_THM] >>
  qabbrev_tac `w = (if bt = AddMod then addmod else mulmod) va vb vc` >>
  qabbrev_tac `u = update_var out w t1` >>
  `step_inst_base j t1 = OK u` by
    (Cases_on `bt = AddMod` >>
     simp[Abbr `u`, Abbr `w`, mk_inst_def, step_inst_base_opcode_eqs, exec_pure3_def]) >>
  conj_tac
  >- (drule_all_then mp_tac alloca_history_base_step >>
      Cases_on `bt = AddMod` >> simp[mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> Cases_on `bt = AddMod` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule step_prov_other_output >> simp[mk_inst_def]) >>
  `out_taint tn j t1 = {} /\ written_taint tn j t1 = {}` by
    (Cases_on `bt = AddMod` >>
     (conj_tac
      >- (irule out_taint_opcode_exclusion >> simp[mk_inst_def]) >>
      irule written_taint_opcode_exclusion >> simp[mk_inst_def])) >>
  `step_taint j t1 u tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (`new_site_bytes t1 u = {}` by
       (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
     Cases_on `bt = AddMod` >>
     simp[step_taint_def, mem_taint_def, set_var_taint_def,
          mk_inst_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def, store_taint_def, imm_taint_def, adopt_reset_def,
          taint_component_equality]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn j t1` by
    (gen_tac >>
     `step_inst 0 ctx j t1 = OK u` by
       (Cases_on `bt = AddMod` >> simp[step_inst_non_invoke, mk_inst_def]) >>
     Cases_on `bt = AddMod` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def] >>
     gvs[Abbr `u`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  gen_tac >>
  mp_tac (Q.INST [`i` |-> `j`, `s` |-> `t1`, `u` |-> `u`,
      `G` |-> `G`, `tn` |-> `tn`, `lo` |-> `lo`, `D` |-> `D`]
    straight_line_origin_ptr_edge) >>
  Cases_on `bt = AddMod` >>
  simp[mk_inst_def,is_terminator_def,inst_mem_below_frontier_def,
       inst_dload_in_section_def,source_memory_read_ranges_def,source_memory_write_ranges_def] >>
  disch_then irule >> simp[mk_inst_def]
QED

Theorem modular_suffix_mods:
  !DF lo explicit ctx func PG d cenv cx st0 ee sm sb bt x y z op t G1 tn1 ann ts (va:bytes32) (vb:bytes32) (vc:bytes32).
    (bt = AddMod \/ bt = MulMod) /\
    (if bt = AddMod then compile_addmod else compile_mulmod) x y z sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    eval_operand z t = SOME vc /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\ op_taint tn1 z = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ local_ptrs_reserved cenv sm /\
    (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) ==>
    ?r t' G2 tn2.
      (vc = 0w ==>
        r = Abort Revert_abort t' /\ G2 = G1 /\ tn2 = tn1 /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INR (Error (RuntimeError (if bt = AddMod then
            "AddMod division by zero" else "MulMod division by zero"))) /\
        exit_result r /\
        expr_exit (builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)]) r) /\
      (vc <> 0w ==>
        r = OK t' /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INL (IntV (&w2n ((if bt = AddMod then addmod else mulmod) va vb vc))) /\
        eval_operand op t' = SOME ((if bt = AddMod then addmod else mulmod) va vb vc) /\
        op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
        ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t' /\
        t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
        t'.vs_fmp = t.vs_fmp /\
        t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
        t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
        t'.vs_immutables = t.vs_immutables /\ t'.vs_data_section = t.vs_data_section /\
        t'.vs_gas_readings = t.vs_gas_readings /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
        tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
        tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
        (!q. not_fresh_at sm q ==>
          lookup_var q t' = lookup_var q t /\
          FLOOKUP G2 q = FLOOKUP G1 q /\
          op_taint tn2 (Var q) = op_taint tn1 (Var q)) /\
        ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G1,tn1) [] (r,G2,tn2) /\
        (vc <> 0w ==>
          stmt_state_rel H ctx func cenv cx ee t' /\
          immutable_frame_mods func cenv cx ee t' /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t'))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ASSERT [z] []` >>
  qabbrev_tac `j = mk_inst (sm.cs_next_id + 1) (if bt = AddMod then ADDMOD else MULMOD)
    [x;y;z] [out]` >>
  `emitted_insts sm sb = [i;j] /\ op = Var out /\
   sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [i;j]` by
    (qpat_x_assum `_ x y z sm = (op,sb)` mp_tac >>
     Cases_on `bt = AddMod` >> simp[] >> strip_tac >> gvs[] >>
     pop_assum mp_tac >>
     simp[compile_addmod_def, compile_mulmod_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
          emit_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME i /\
   get_instruction bb (SUC t.vs_inst_idx) = SOME j` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `alloca_inv t /\ allocas_from lo t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     fs[ghost_inv_at_mods_def]) >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `i = mk_inst sm.cs_next_id ASSERT [z] []` by simp[Abbr `i`] >>
  drule_all_then (qspecl_then [`explicit`,`PG`,`G1`] strip_assume_tac o
                  SIMP_RULE bool_ss [LET_THM])
    (Q.INST [`G` |-> `G1`, `tn` |-> `tn1`, `explicit` |-> `explicit`, `PG` |-> `PG`]
      modular_assert) >>
  `builtin_result cx ee.accounts ann bt ts
       [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
   if vc = 0w then INR (Error (RuntimeError (if bt = AddMod then
     "AddMod division by zero" else "MulMod division by zero")))
   else INL (IntV (&w2n ((if bt = AddMod then addmod else mulmod) va vb vc)))` by
    (qpat_assum `bt = AddMod \/ bt = MulMod` strip_assume_tac >>
     simp[SRULE [] (Q.INST [`is_mul` |-> `F`] word_modular_source_words),
          SRULE [] (Q.INST [`is_mul` |-> `T`] word_modular_source_words)]) >>
  Cases_on `vc = 0w`
  >- (qexistsl_tac [`Abort Revert_abort (revert_state (set_returndata [] t))`,
                   `revert_state (set_returndata [] t)`, `G1`, `tn1`] >>
      simp[exit_result_def, expr_exit_def]) >>
  suspend "normal"
QED

Resume modular_suffix_mods[normal]:
  qabbrev_tac `t1 = t with vs_inst_idx := SUC t.vs_inst_idx` >>
  `alloca_history func t1 /\ (!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (t,G1,tn1) [] (OK t1,G1,tn1))` by simp[Abbr `t1`] >>
  `alloca_inv t1` by simp[Abbr `t1`, alloca_inv_set_inst_idx] >>
  `allocas_from lo t1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t1)` by
    (conj_tac
     >- (qpat_assum `allocas_from lo t` mp_tac >>
         qunabbrev_tac `t1` >> simp[NoAsms, allocas_from_def]) >>
     simp[Abbr `t1`, allocas_below_fmp_updates]) >>
  `lookup_block t1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb t1.vs_inst_idx = SOME j /\ ~t1.vs_halted /\
   eval_operand x t1 = SOME va /\ eval_operand y t1 = SOME vb /\
   eval_operand z t1 = SOME vc` by
    (simp[Abbr `t1`, eval_operand_inst_idx] >>
     qpat_assum `t.vs_inst_idx = LENGTH _` (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `j = mk_inst (sm.cs_next_id + 1) (if bt = AddMod then ADDMOD else MULMOD)
        [x;y;z] [out]` by simp[Abbr `j`] >>
  qabbrev_tac `w = (if bt = AddMod then addmod else mulmod) va vb vc` >>
  qabbrev_tac `u = update_var out w t1` >>
  qabbrev_tac `t2 = u with vs_inst_idx := SUC t1.vs_inst_idx` >>
  qabbrev_tac `G2 = step_prov PG G1 j u` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (out,{})` >>
  `step_inst_base j t1 = OK u` by
    (Cases_on `bt = AddMod`
     >- (qpat_assum `bt = AddMod` (fn th =>
       qpat_assum `eval_operand x t = SOME va` (fn hx =>
       qpat_assum `eval_operand y t = SOME vb` (fn hy =>
       qpat_assum `eval_operand z t = SOME vc` (fn hz =>
         simp[NoAsms, th, hx, hy, hz, Abbr `j`, Abbr `u`, Abbr `w`, Abbr `t1`,
              mk_inst_def, step_inst_base_opcode_eqs, exec_pure3_def])))))
     >- (qpat_assum `bt <> AddMod` (fn th =>
       qpat_assum `eval_operand x t = SOME va` (fn hx =>
       qpat_assum `eval_operand y t = SOME vb` (fn hy =>
       qpat_assum `eval_operand z t = SOME vc` (fn hz =>
         simp[NoAsms, th, hx, hy, hz, Abbr `j`, Abbr `u`, Abbr `w`, Abbr `t1`,
              mk_inst_def, step_inst_base_opcode_eqs, exec_pure3_def])))))) >>
  `alloca_history func t2` by
    (drule_all_then mp_tac alloca_history_base_step >>
     Cases_on `bt = AddMod`
     >- (qpat_assum `bt = AddMod` (fn th =>
           simp[NoAsms, th, Abbr `t2`, Abbr `u`, Abbr `t1`, Abbr `j`,
                mk_inst_def, is_terminator_def]))
     >- (qpat_assum `bt <> AddMod` (fn th =>
           simp[NoAsms, th, Abbr `t2`, Abbr `u`, Abbr `t1`, Abbr `j`,
                mk_inst_def, is_terminator_def]))) >>
  `op_prov G2 (Var out) = NONE` by
    (qunabbrev_tac `G2` >> irule step_prov_out_none >> simp[Abbr `u`, Abbr `j`, mk_inst_def] >>
     irule out_prov_other_none >> Cases_on `bt = AddMod` >> simp[]) >>
  `!old. old <> out ==> FLOOKUP G2 old = FLOOKUP G1 old` by
    (rpt strip_tac >> qunabbrev_tac `G2` >> irule step_prov_other_output >>
     simp[Abbr `j`, mk_inst_def]) >>
  `out_taint tn1 j t1 = {} /\ written_taint tn1 j t1 = {}` by
    (Cases_on `bt = AddMod`
     >- (qpat_assum `bt = AddMod` (fn th =>
           conj_tac
           >- (irule out_taint_opcode_exclusion >>
               simp[NoAsms, th, Abbr `j`, mk_inst_def])
           >- (irule written_taint_opcode_exclusion >>
               simp[NoAsms, th, Abbr `j`, mk_inst_def])))
     >- (qpat_assum `bt <> AddMod` (fn th =>
           conj_tac
           >- (irule out_taint_opcode_exclusion >>
               simp[NoAsms, th, Abbr `j`, mk_inst_def])
           >- (irule written_taint_opcode_exclusion >>
               simp[NoAsms, th, Abbr `j`, mk_inst_def]))) ) >>
  `step_taint j t1 u tn1 = tn2` by
    (`new_site_bytes t1 u = {}` by
       (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
     Cases_on `bt = AddMod`
     >- ((qpat_assum `bt = AddMod` (fn th =>
           qpat_assum `new_site_bytes t1 u = {}` (fn hn =>
             qpat_assum `out_taint tn1 j t1 = {}` (fn ho =>
               qpat_assum `written_taint tn1 j t1 = {}` (fn hw =>
                 simp[NoAsms, th, hn, ho, hw, Abbr `tn2`, step_taint_def,
                      mem_taint_def, set_var_taint_def, mk_inst_def,
                      step_writes_def, source_memory_write_ranges_def,
                      range_bytes_def, store_taint_def, imm_taint_def,
                      adopt_reset_def, taint_component_equality] >>
                 simp[NoAsms, hw, ho, Abbr `j`, mk_inst_def]))))) >> (simp[]))
     >- (qpat_assum `bt <> AddMod` (fn th =>
           qpat_assum `new_site_bytes t1 u = {}` (fn hn =>
             qpat_assum `out_taint tn1 j t1 = {}` (fn ho =>
               qpat_assum `written_taint tn1 j t1 = {}` (fn hw =>
                 simp[NoAsms, th, hn, ho, hw, Abbr `tn2`, step_taint_def,
                      mem_taint_def, set_var_taint_def, mk_inst_def,
                      step_writes_def, source_memory_write_ranges_def,
                      range_bytes_def, store_taint_def, imm_taint_def,
                      adopt_reset_def, taint_component_equality] >>
                 simp[NoAsms, hw, ho, Abbr `j`, mk_inst_def])))))) >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 j t1` by
    (gen_tac >>
     `step_inst 0 ctx j t1 = OK u` by
       (Cases_on `bt = AddMod` >> simp[step_inst_non_invoke, mk_inst_def]) >>
     Cases_on `bt = AddMod` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          mk_inst_def] >>
     gvs[Abbr `u`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (t1,G1,tn1) [] (OK t2,G2,tn2)` by
    (gen_tac >>
     mp_tac (Q.INST [`i` |-> `j`, `s` |-> `t1`, `u` |-> `u`,
       `G` |-> `G1`, `tn` |-> `tn1`, `lo` |-> `lo`, `D` |-> `D`]
       straight_line_origin_ptr_edge) >>
     Cases_on `bt = AddMod` >>
     simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
     disch_then irule >> simp[mk_inst_def]) >>
  `!q. not_fresh_at sm q ==>
     lookup_var q t2 = lookup_var q t /\ FLOOKUP G2 q = FLOOKUP G1 q /\
     op_taint tn2 (Var q) = op_taint tn1 (Var q)` by
    (gen_tac >> disch_tac >>
     `q <> out` by
       (qpat_assum `not_fresh_at sm q`
          (qspec_then `sm.cs_next_var` mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
        simp[Abbr `out`]) >>
     simp[Abbr `t2`, Abbr `u`, Abbr `t1`, Abbr `tn2`, update_var_def,
          lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2` by
    (simp[ghost_kept_at_def, Abbr `tn2`] >> rpt strip_tac >>
     first_x_assum drule >> simp[Abbr `tn2`]) >>
  `~t2.vs_halted` by simp[Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK t2,G2,tn2)` by
    (let
       val cons_nil = REWRITE_RULE [APPEND_NIL] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
         (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))
     in
       gen_tac >> irule cons_nil >>
       qpat_assum `!D. gas_origin_ptr_edge _ (t,G1,tn1) _ _` (irule_at Any) >>
       irule cons_nil >>
       qpat_assum `!D. gas_origin_ptr_edge _ (t1,G1,tn1) _ _` (irule_at Any) >>
       simp[gas_origin_ptr_path_rules]
     end) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t2 /\
       immutable_frame_mods func cenv cx ee t2 /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t2` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac
     >- (simp[Abbr `t2`, Abbr `u`, Abbr `t1`, stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >> simp[Abbr `out`, stmt_state_rel_inst_idx] >>
         irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
     conj_tac
     >- (irule immutable_frame_mods_exterior_frame >>
         qexistsl_tac [`ee`,`t`,`sm`] >>
         simp[Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def] >>
         rpt strip_tac >> `x' <> out` by fs[not_fresh_at_def, Abbr `out`] >>
         simp[lookup_var_def, FLOOKUP_UPDATE]) >>
     irule ghost_inv_at_mods_exterior_frame >>
     qexistsl_tac [`G1`,`ee`,`t`,`sm`,`tn1`] >> simp[] >>
     simp[Abbr `t2`, Abbr `u`, Abbr `t1`, Abbr `tn2`, update_var_def] >>
     rpt strip_tac >> `x' <> out` by fs[not_fresh_at_def, Abbr `out`] >>
     simp[lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`OK t2`,`t2`,`G2`,`tn2`] >>
  conj_tac >- (qpat_assum `vc <> 0w` (fn th => simp[NoAsms,th])) >>
  reverse conj_tac
  >- (gen_tac >> strip_tac >> conj_tac >- first_assum irule >>
      disch_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  disch_tac >>
  `builtin_result cx ee.accounts ann bt ts
    [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] = INL (IntV (&w2n w))` by
    (qpat_assum `builtin_result _ _ _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `vc <> 0w` (fn th => simp[NoAsms, th])) >>
  `t2.vs_current_bb = sb.cs_current_bb /\ t2.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `t.vs_current_bb = sm.cs_current_bb` (fn a =>
     qpat_assum `sb.cs_current_bb = sm.cs_current_bb` (fn b =>
     qpat_assum `t.vs_inst_idx = LENGTH sm.cs_current_insts` (fn c =>
     qpat_assum `sb.cs_current_insts = _` (fn e =>
       simp[NoAsms, a,b,c,e, Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def,
            arithmeticTheory.ADD1]))))) >>
  `eval_operand op t2 = SOME w /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE` by
    (qpat_assum `op = Var out` (fn th => once_rewrite_tac[th]) >>
     conj_tac >- simp[NoAsms, Abbr `t2`, Abbr `u`, Abbr `t1`, eval_operand_def,
                      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- simp[NoAsms, Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t2` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     simp[NoAsms, Abbr `t2`, Abbr `u`, Abbr `t1`, allocas_below_fmp_updates]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[NoAsms, Abbr `t2`, Abbr `u`, Abbr `t1`, Abbr `tn2`, update_var_def])
QED

Finalise modular_suffix_mods
