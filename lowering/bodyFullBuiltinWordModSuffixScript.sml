(* ASSERT followed by ADDMOD or MULMOD, with one endpoint for every horizon. *)
Theory bodyFullBuiltinWordModSuffix
Ancestors
  bodyFullGhostFrame bodySimFull bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr fragGasEmitCtrl exprSimWordBuiltins exprSimWordArgs exprSimDefs exprLoweringProps
  emitHelperProps emitHelper builtinMath fragExec allocaHistory
  ptrDisciplineEmptyTaint lowerDloadPtrScalar decoderGhostFramePtr ptrDiscipline ptrSafeRun
  venomExecSemantics venomState venomInst venomMemDefs venomMemProofs memSafeRun compileEnv
  unitTransformDefs contextCodegenRel codegenRel
  vyperInterpreter vyperContext vyperStorageFootprint loweringStateRelDefs
  builtinSimple builtinMisc bodyPtrWordBuiltinsModularSource list rich_list finite_map words

Theorem modular_suffix_full:
  !DF lo explicit ctx func PG d cenv cx st0 ee sm sb bt x y z op t G1 tn1 ann ts (va:bytes32) (vb:bytes32) (vc:bytes32).
    (bt = AddMod \/ bt = MulMod) /\
    (if bt = AddMod then compile_addmod else compile_mulmod) x y z sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    eval_operand z t = SOME vc /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\ op_taint tn1 z = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sm /\
    (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
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
        t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
        t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
        t'.vs_immutables = t.vs_immutables /\
        t'.vs_gas_readings = t.vs_gas_readings /\
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
          ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t'))
Proof
  rpt gen_tac >> strip_tac >>
  (
  qabbrev_tac `opc = if bt = AddMod then ADDMOD else MULMOD` >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ASSERT [z] []` >>
  qabbrev_tac `j = mk_inst (sm.cs_next_id + 1) opc [x;y;z] [out]` >>
  `emitted_insts sm sb = [i;j] /\ op = Var out /\
   sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [i;j]` by
    (Cases_on `bt = AddMod` >> gvs[] >>
     qpat_x_assum `_ x y z sm = (op,sb)` mp_tac >>
     simp[compile_addmod_def, compile_mulmod_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, Abbr `i`, Abbr `j`, Abbr `opc`,
       Abbr `out`, DROP_LENGTH_APPEND]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME i /\
   get_instruction bb (SUC t.vs_inst_idx) = SOME j` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t`
    by metis_tac[] >>
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) _ _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP (cj 2 (iffLR stmt_state_rel_def)))) >>
  `ghost_inv_at (DF (storage_trace_horizon ee.storage_trace))
     lo d cenv cx ee G1 tn1 t` by metis_tac[] >>
  `allocas_from lo t` by
    (qpat_assum `ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP (cj 7 (iffLR ghost_inv_at_def)))) >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 i t` by
    (gen_tac >> Cases_on `vc = 0w` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       Abbr `i`, mk_inst_def, step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs]) >>
  Cases_on `vc = 0w`
  >- (`builtin_result cx ee.accounts ann bt ts
         [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
       INR (Error (RuntimeError (if bt = AddMod then
         "AddMod division by zero" else "MulMod division by zero")))` by
        (Cases_on `bt = AddMod` >> gvs[] >>
         simp[builtin_result_def, evaluate_builtin_def]) >>
      qabbrev_tac `abort_t = revert_state (set_returndata [] t)` >>
      qexistsl_tac [`Abort Revert_abort abort_t`, `abort_t`, `G1`, `tn1`] >>
      simp[fragExecTheory.exit_result_def, expr_exit_def] >>
      rpt strip_tac >> irule exit_inst_origin_ptr >>
      conj_tac >- simp[fragExecTheory.exit_result_def] >>
      conj_tac >- asm_rewrite_tac[] >>
      qexistsl_tac [`bb`, `i`] >>
      simp[Abbr `i`, mk_inst_def, step_inst_non_invoke,
        Abbr `abort_t`, step_inst_base_opcode_eqs,
        fragExecTheory.exit_result_def, mem_safe_step_non_invoke,
        inst_mem_below_frontier_def, inst_dload_in_section_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def,
        gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def]) >>
  qabbrev_tac `t1 = t with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `w = (if bt = AddMod then addmod else mulmod) va vb vc` >>
  qabbrev_tac `u = update_var out w t1` >>
  qabbrev_tac `t2 = u with vs_inst_idx := SUC t1.vs_inst_idx` >>
  `step_inst_base i t = OK t /\
   step_prov PG G1 i t = G1 /\ step_taint i t t tn1 = tn1` by
    simp[Abbr `i`, mk_inst_def, step_inst_base_opcode_eqs,
      step_prov_def, out_prov_def, set_prov_def,
      step_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, step_writes_def, source_memory_write_ranges_def,
      range_bytes_def, set_var_taint_def, new_site_bytes_def,
      written_taint_def, DRESTRICT_UNIV, taint_component_equality,
      FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `step_inst_base j t1 = OK u` by
    (Cases_on `bt = AddMod` >>
     simp[Abbr `j`, Abbr `opc`, Abbr `u`, Abbr `w`, Abbr `t1`,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure3_def, eval_operand_def, lookup_var_def]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 j t1` by
    (gen_tac >>
     `step_inst 0 ctx j t1 = OK u` by
       simp[step_inst_non_invoke, Abbr `j`, mk_inst_def, Abbr `opc`] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       Abbr `j`, Abbr `opc`, mk_inst_def] >>
     gvs[Abbr `u`, Abbr `t1`, update_var_def, allocas_from_def] >>
     metis_tac[]) >>
  `out_taint tn1 j t1 = {} /\ written_taint tn1 j t1 = {}` by
    (conj_tac
     >- (irule out_taint_opcode_exclusion >> simp[Abbr `j`, Abbr `opc`, mk_inst_def]) >>
     irule written_taint_opcode_exclusion >> simp[Abbr `j`, Abbr `opc`, mk_inst_def]) >>
  `step_taint j t1 u tn1 = tn1 with t_var := tn1.t_var |+ (out,{})` by
    (`new_site_bytes t1 u = {}` by
       (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
     simp[step_taint_def, mem_taint_def, set_var_taint_def,
       Abbr `j`, Abbr `opc`, mk_inst_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, taint_component_equality]) >>
  `alloca_history func t1` by
    (`~is_terminator i.inst_opcode` by simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     qspecl_then [`func`, `t`, `bb`, `i`, `t`] mp_tac alloca_history_base_step >>
     simp[Abbr `t1`]) >>
  `alloca_history func t2` by
    (`~is_terminator j.inst_opcode` by simp[Abbr `j`, Abbr `opc`, mk_inst_def, is_terminator_def] >>
     `alloca_inv t1` by
       (simp[Abbr `t1`] >>
        irule venomMemProofsTheory.alloca_inv_set_inst_idx >> first_assum ACCEPT_TAC) >>
     `lookup_block t1.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `t1`] >>
     `get_instruction bb t1.vs_inst_idx = SOME j` by
       (qpat_x_assum `get_instruction bb (SUC t.vs_inst_idx) = SOME j` mp_tac >>
        simp[Abbr `t1`]) >>
     qspecl_then [`func`, `t1`, `bb`, `j`, `u`] mp_tac alloca_history_base_step >>
     simp[Abbr `t2`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t2` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee t` by
       (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     simp[Abbr `t2`, Abbr `u`, Abbr `t1`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[Abbr `out`, stmt_state_rel_inst_idx] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `op_prov (step_prov PG G1 j u) op = NONE` by
    (simp[] >> irule step_prov_out_none >> simp[Abbr `j`, Abbr `opc`, mk_inst_def] >>
     irule out_prov_other_none >> simp[]) >>
  `!old. not_fresh_at sm old ==>
    lookup_var old t2 = lookup_var old t /\
    FLOOKUP (step_prov PG G1 j u) old = FLOOKUP G1 old /\
    op_taint (step_taint j t1 u tn1) (Var old) = op_taint tn1 (Var old)` by
    (qx_gen_tac `old` >> strip_tac >>
     `old <> out` by gvs[not_fresh_at_def, Abbr `out`] >>
     simp[Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, op_taint_def] >>
     irule step_prov_other_output >> simp[Abbr `j`, mk_inst_def]) >>
  `ghost_kept_at lo cenv ee sm G1 tn1 t
    (step_prov PG G1 j u) (step_taint j t1 u tn1)` by
    (simp[ghost_kept_at_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
      (OK t2,step_prov PG G1 j u,step_taint j t1 u tn1)` by
    (rpt strip_tac >>
     `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
        (OK t1,G1,tn1)` by
       (mp_tac (straight_line_origin_ptr_edge |> Q.INST
         [`i` |-> `i`, `u` |-> `t`, `s` |-> `t`,
          `G` |-> `G1`, `tn` |-> `tn1`,
          `D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`]) >>
        simp[Abbr `i`, mk_inst_def, Abbr `t1`, is_terminator_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
      `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t1,G1,tn1) []
        (OK t2,step_prov PG G1 j u,step_taint j t1 u tn1)` by
       (mp_tac (straight_line_origin_ptr_edge |> Q.INST
         [`i` |-> `j`, `u` |-> `u`, `s` |-> `t1`,
          `G` |-> `G1`, `tn` |-> `tn1`,
          `D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`]) >>
        simp[Abbr `j`, Abbr `opc`, mk_inst_def, Abbr `u`, Abbr `t2`, Abbr `t1`,
          is_terminator_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
        disch_then irule >>
        qpat_x_assum `get_instruction bb (SUC t.vs_inst_idx) = SOME _` mp_tac >>
        simp[mk_inst_def]) >>
      `~t2.vs_halted` by simp[Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def] >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee
      (step_prov PG G1 j u) (step_taint j t1 u tn1) t2` by
    (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G1`, `ee`, `t`, `sm`, `tn1`] >>
     simp[Abbr `t2`, Abbr `u`, Abbr `t1`, update_var_def] >> metis_tac[]) >>
  `builtin_result cx ee.accounts ann bt ts
      [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] = INL (IntV (&w2n w))` by
    (mp_tac (Q.INST [`is_mul` |-> `bt = MulMod`, `a` |-> `va`, `b` |-> `vb`,
       `c` |-> `vc`, `ac` |-> `(ee : evaluation_state).accounts`] word_modular_source_words) >>
     Cases_on `bt = AddMod` >> gvs[Abbr `w`]) >>
  qexistsl_tac [`OK t2`, `t2`, `step_prov PG G1 j u`, `step_taint j t1 u tn1`] >>
  simp[Abbr `t2`, Abbr `u`, Abbr `t1`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, op_taint_def])
QED
