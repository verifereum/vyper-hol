(* One EXP step: retaining the qualified immutable frame and linked ghost. *)
Theory bodyWordPowSuffixMods
Ancestors
  bodyFullBuiltinWordPowSuffix bodyForRangeScalarFrameMods
  ptrDiscipline memSafeRun vyperInterpreter vyperContext vyperTypeBuiltins
  codegenRel bodyFullShadowBodyInv
  ptrDisciplineEmptyTaint lowerDloadPtrScalar decoderGhostFramePtr ptrSafeRun
  bodyFullGhostFrame bodyPtrDefs fragGasSeqPtr fragGasOriginPtr
  builtinMath builtinSimple builtinMisc exprSimWordArgs exprSimWordBuiltins
  emitHelperProps emitHelper allocaHistory exprLoweringProps fragExec
  compileEnv loweringStateRelDefs unitTransformDefs contextCodegenRel
  venomState venomInst venomExecSemantics vyperStorageFootprint rich_list
  finite_map words list

Theorem pow_suffix_layout[local]:
  compile_pow_mod256 x y sm = (op,sb) ==>
  op = Var (STRING #"%" (toString sm.cs_next_var)) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++
    [mk_inst sm.cs_next_id Exp [x;y] [STRING #"%" (toString sm.cs_next_var)]]
Proof
  simp[compile_pow_mod256_def] >> strip_tac >>
  drule_then strip_assume_tac emitted_insts_emit_op >> simp[] >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def]
QED

Theorem pow_step_ptr[local]:
  eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
  op_taint tn x = {} /\ op_taint tn y = {} /\
  alloca_inv t /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid Exp [x;y] [out]) t
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst iid Exp [x;y] [out]) t =
   OK (update_var out (word_exp va vb) t)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure2_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mk_inst_def, update_var_def] >> metis_tac[]
QED

Theorem pow_step_taint[local]:
  step_taint (mk_inst iid Exp [x;y] [out]) t (update_var out w t) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  `new_site_bytes t (update_var out w t) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  `out_taint tn (mk_inst iid Exp [x;y] [out]) t = {}` by
    (irule out_taint_opcode_exclusion >> simp[mk_inst_def]) >>
  `written_taint tn (mk_inst iid Exp [x;y] [out]) t = {}` by
    (irule written_taint_opcode_exclusion >> simp[mk_inst_def]) >>
  simp[step_taint_def, mem_taint_def, set_var_taint_def, mk_inst_def,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def,
       store_taint_def, imm_taint_def, adopt_reset_def, taint_component_equality]
QED

Theorem pow_step_edge[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid Exp [x;y] [out]) /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid Exp [x;y] [out]) s /\
  step_inst_base (mk_inst iid Exp [x;y] [out]) s = OK u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst iid Exp [x;y] [out]) u,
     step_taint (mk_inst iid Exp [x;y] [out]) s u tn)
Proof
  strip_tac >>
  ` (if (mk_inst iid Exp [x;y] [out]).inst_opcode = GAS then
      [(func.fn_name,(mk_inst iid Exp [x;y] [out]).inst_id) IN explicit]
     else []) = []` by simp[mk_inst_def] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  irule straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  qexists_tac `bb` >> simp[mk_inst_def]
QED

Theorem pow_mod256_suffix_mods:
  !DF lo explicit ctx func PG d cenv cx st0 ee sm sb x y op t G1 tn1 ann ts
      (va:bytes32) (vb:bytes32).
    compile_pow_mod256 x y sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ local_ptrs_reserved cenv sm /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\
         immutable_frame_mods func cenv cx ee t /\
         ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) ==>
    ?t' G2 tn2.
      builtin_result cx ee.accounts ann PowMod256 ts
        [IntV (&w2n va); IntV (&w2n vb)] =
        INL (IntV (&w2n (word_exp va vb))) /\
      eval_operand op t' = SOME (word_exp va vb) /\
      op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
      ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t' /\
      t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
      t'.vs_fmp = t.vs_fmp /\
      t'.vs_memory = t.vs_memory /\ t'.vs_call_ctx = t.vs_call_ctx /\
      t'.vs_accounts = t.vs_accounts /\ t'.vs_transient = t.vs_transient /\
      t'.vs_immutables = t.vs_immutables /\
      t'.vs_gas_readings = t.vs_gas_readings /\
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
         immutable_frame_mods func cenv cx ee t' /\
         ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t')
Proof
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac pow_suffix_layout >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id Exp [x;y] [out]` >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `u = update_var out (word_exp va vb) t` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `step_inst_base inst t = OK u` by
    simp[Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `alloca_inv t /\ allocas_from lo t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_def, ghost_inv_at_mods_def]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 inst t` by
    (simp[Abbr `inst`] >> gen_tac >> irule pow_step_ptr >> simp[] >>
     metis_tac[]) >>
  `alloca_history func z` by
    (drule_all alloca_history_base_step >>
     simp[Abbr `z`, Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `G2 = step_prov PG G1 inst u` >>
  qabbrev_tac `tn2 = step_taint inst t u tn1` >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (out,{})` by
    simp[Abbr `tn2`, Abbr `inst`, Abbr `u`, pow_step_taint] >>
  `!old. not_fresh_at sm old ==>
     lookup_var old z = lookup_var old t /\ FLOOKUP G2 old = FLOOKUP G1 old /\
     op_taint tn2 (Var old) = op_taint tn1 (Var old)` by
    (qx_gen_tac `old` >> strip_tac >>
     `old <> out` by gvs[not_fresh_at_def, Abbr `out`] >>
     simp[Abbr `z`, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, op_taint_def, Abbr `G2`] >>
     irule step_prov_other_output >> simp[Abbr `inst`, mk_inst_def]) >>
  suspend "finish"
QED

Resume pow_mod256_suffix_mods[finish]:
  `op_prov G2 op = NONE` by
    (simp[Abbr `G2`] >> irule step_prov_out_none >>
     simp[Abbr `inst`, mk_inst_def] >>
     irule out_prov_other_none >> simp[mk_inst_def]) >>
  `ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2` by
    (simp[ghost_kept_at_def] >> metis_tac[]) >>
  `!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
          (OK z,G2,tn2)` by
    (gen_tac >>
     `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
          (OK z,G2,tn2)` by
       (qunabbrev_tac `G2` >> qunabbrev_tac `tn2` >>
        simp[NoAsms, Abbr `z`, Abbr `inst`] >>
        irule pow_step_edge >> gvs[]) >>
     `~z.vs_halted` by simp[Abbr `z`, Abbr `u`, update_var_def] >>
     metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\
    immutable_frame_mods func cenv cx ee z /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (simp[Abbr `z`, Abbr `u`, stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >> simp[Abbr `out`] >>
         irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
     conj_tac
     >- (irule immutable_frame_mods_exterior_frame >>
         qexistsl_tac [`ee`,`t`,`sm`] >>
         simp[Abbr `z`, Abbr `u`, update_var_def] >> metis_tac[]) >>
     irule ghost_inv_at_mods_exterior_frame >>
     qexistsl_tac [`G1`,`ee`,`t`,`sm`,`tn1`] >>
     simp[Abbr `z`, Abbr `u`, update_var_def] >> metis_tac[]) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> conj_tac
  >- simp[builtin_result_def, evaluate_builtin_def, word_exp_modexp,
          dimword_def, modexp_lt] >>
  simp[Abbr `z`, Abbr `u`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  gvs[update_var_def]
QED

Finalise pow_mod256_suffix_mods
