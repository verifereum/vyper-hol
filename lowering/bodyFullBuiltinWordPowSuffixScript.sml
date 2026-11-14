(* The single Exp instruction, with one endpoint for all storage horizons. *)
Theory bodyFullBuiltinWordPowSuffix
Ancestors
  bodyFullGhostFrame bodySimFull bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr exprSimWordBuiltins exprSimWordArgs exprLoweringProps
  emitHelperProps emitHelper builtinMath fragExec allocaHistory
  ptrDisciplineEmptyTaint lowerDloadPtrScalar decoderGhostFramePtr ptrDiscipline ptrSafeRun
  venomExecSemantics venomState venomInst compileEnv
  unitTransformDefs contextCodegenRel codegenRel
  vyperInterpreter vyperContext vyperStorageFootprint loweringStateRelDefs
  builtinSimple builtinMisc vyperTypeBuiltins list rich_list finite_map words

Theorem pow_mod256_suffix_full:
  compile_pow_mod256 x y sm = (op,sb) /\
  eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
  op_taint tn1 x = {} /\ op_taint tn1 y = {} /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sm /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
  ?t' G2 tn2.
    builtin_result cx ee.accounts ann PowMod256 ts
      [IntV (&w2n va); IntV (&w2n vb)] =
      INL (IntV (&w2n (word_exp va vb))) /\
    eval_operand op t' = SOME (word_exp va vb) /\
    op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
    ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
    t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t' /\
    t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
    t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
    t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
    t'.vs_immutables = t.vs_immutables /\ t'.vs_gas_readings = t.vs_gas_readings /\
    tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    (!z. not_fresh_at sm z ==>
      lookup_var z t' = lookup_var z t /\
      FLOOKUP G2 z = FLOOKUP G1 z /\
      op_taint tn2 (Var z) = op_taint tn1 (Var z)) /\
    ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2 /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK t',G2,tn2) /\
      stmt_state_rel H ctx func cenv cx ee t' /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t')
Proof
  strip_tac >>
  `emit_op Exp [x;y] sm = (op,sb)` by fs[compile_pow_mod256_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    gvs[compile_pow_mod256_def, emit_op_def, comp_bind_def, fresh_var_def,
        fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
        emitted_insts_def, DROP_LENGTH_APPEND] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME
    (mk_inst sm.cs_next_id Exp [x;y] [STRING #"%" (toString sm.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `u = update_var out (word_exp va vb) t` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `step_inst_base inst t = OK u` by
    simp[Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t`
    by metis_tac[] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `ghost_inv_at (DF (storage_trace_horizon ee.storage_trace))
     lo d cenv cx ee G1 tn1 t` by metis_tac[] >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 inst t` by
    (gen_tac >>
     `step_inst 0 ctx inst t = OK u` by
       simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def, Abbr `u`,
            step_inst_base_opcode_eqs, exec_pure2_def] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       Abbr `inst`, mk_inst_def] >>
     gvs[Abbr `u`, update_var_def] >> metis_tac[]) >>
  `out_taint tn1 inst t = {} /\ written_taint tn1 inst t = {}` by
    (conj_tac
     >- (irule out_taint_opcode_exclusion >> simp[Abbr `inst`, mk_inst_def]) >>
     irule written_taint_opcode_exclusion >> simp[Abbr `inst`, mk_inst_def]) >>
  `step_taint inst t u tn1 = tn1 with t_var := tn1.t_var |+ (out,{})` by
    (`new_site_bytes t u = {}` by
       (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
     simp[step_taint_def, mem_taint_def, set_var_taint_def,
       Abbr `inst`, Abbr `out`, mk_inst_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, taint_component_equality]) >>
  `alloca_history func z` by
    (`~is_terminator inst.inst_opcode` by
       simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all alloca_history_base_step >> simp[Abbr `z`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z` by
    (rpt strip_tac >> simp[Abbr `z`, Abbr `u`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[Abbr `out`] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `op_prov (step_prov PG G1 inst u) op = NONE` by
    (simp[] >> irule step_prov_out_none >> simp[Abbr `inst`, mk_inst_def] >>
     irule out_prov_other_none >> simp[mk_inst_def]) >>
  `!old. not_fresh_at sm old ==>
    lookup_var old z = lookup_var old t /\
    FLOOKUP (step_prov PG G1 inst u) old = FLOOKUP G1 old /\
    op_taint (step_taint inst t u tn1) (Var old) = op_taint tn1 (Var old)` by
    (qx_gen_tac `old` >> strip_tac >>
     `old <> out` by gvs[not_fresh_at_def, Abbr `out`] >>
     simp[Abbr `z`, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, op_taint_def] >>
     irule step_prov_other_output >> simp[Abbr `inst`, mk_inst_def]) >>
  `ghost_kept_at lo cenv ee sm G1 tn1 t
    (step_prov PG G1 inst u) (step_taint inst t u tn1)` by
    (simp[ghost_kept_at_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
      (OK z,step_prov PG G1 inst u,step_taint inst t u tn1)` by
    (rpt strip_tac >>
     `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
        (OK z,step_prov PG G1 inst u,step_taint inst t u tn1)` by
       (mp_tac (straight_line_origin_ptr_edge |> Q.INST
         [`i` |-> `inst`, `u` |-> `u`, `s` |-> `t`,
          `G` |-> `G1`, `tn` |-> `tn1`,
          `D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`]) >>
        simp[Abbr `inst`, Abbr `u`, Abbr `z`, Abbr `out`, mk_inst_def,
             is_terminator_def, inst_mem_below_frontier_def,
             source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
     `~z.vs_halted` by simp[Abbr `z`, Abbr `u`, update_var_def] >>
     metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee
      (step_prov PG G1 inst u) (step_taint inst t u tn1) z` by
    (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G1`, `ee`, `t`, `sm`, `tn1`] >>
     simp[Abbr `z`, Abbr `u`, update_var_def] >> metis_tac[]) >>
  `builtin_result cx ee.accounts ann PowMod256 ts
     [IntV (&w2n va); IntV (&w2n vb)] =
     INL (IntV (&w2n (word_exp va vb)))` by
    simp[builtin_result_def, evaluate_builtin_def, word_exp_modexp,
         dimword_def, modexp_lt] >>
  qexistsl_tac [`z`, `step_prov PG G1 inst u`, `step_taint inst t u tn1`] >>
  simp[Abbr `z`, Abbr `u`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, op_taint_def]
QED
