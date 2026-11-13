(* Single-load full Len suffix. *)
Theory bodyFullBuiltinEnvLenScalar
Ancestors
  bodySimFull bodyFullGhostFrame exprSimLen exprSimSource exprSimHypsDefs
  exprPtrCtorImmStore representationCleanPtr exprSimBopRestWordLoadSafety
  assignBasePtrStoragePath
  exprSimUnwrap exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr gasOutcomeFullCompose gasShadowState
  vyperStorageFootprint vyperTypeSystem vyperTypeBuiltins vyperAST
  loweringStateRelDefs ptrDiscipline codegenRel contextCodegenRel
  instMemFrontier allocaHistory emitHelperProps compileEnv
  vyperInterpreter vyperState venomState venomInst list finite_map

Theorem len_full_load_finish:
  !DF lo d explicit ctx func PG cenv cx e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op n z G2 tn2 inst.
    result_array_length cx tv ee = (INL n,ee) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    op = Var (STRING #"%" (toString sm.cs_next_var)) /\
    z = (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t)
          with vs_inst_idx := SUC t.vs_inst_idx /\
    sb.cs_current_bb = sm.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
    inst.inst_opcode <> ALLOCA /\
    (!bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb ==>
      get_instruction bb (LENGTH sm.cs_current_insts) = SOME inst) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
      (!x. not_fresh_at sm x ==>
        FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
      tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
      tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
      op_taint tn2 op = {} /\ op_prov G2 op = NONE) ==>
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
      expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
        es sa sb s0 ee (IntV (&n)) op z /\
      expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
      z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts + 1 /\
      alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
      ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  conj_tac
  >- (`~z.vs_halted` by gvs[venomStateTheory.update_var_def] >>
      qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
      qpat_x_assum `~z.vs_halted` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_stack >> qexists_tac `BaseT (UintT 256)` >>
      irule len_vv_post_load >> conj_tac
      >- gvs[venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
             venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      conj_tac
      >- (gvs[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
          irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
          reverse conj_tac >- gvs[vv_post_def] >>
          irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sm` >>
          simp[not_fresh_at_def]) >>
      qexistsl_tac [`t`, `sm`, `tv`, `vv`] >>
      gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[exprSimMemDefsTheory.expr_store_bound_def, compileEnvTheory.is_word_type_def] >>
  `alloca_history func z` by
    (gvs[venomStateTheory.update_var_def, allocaHistoryTheory.alloca_history_def] >>
     rpt strip_tac >> Cases_on `k = LENGTH sm.cs_current_insts`
     >- (gvs[] >> first_x_assum drule >> simp[]) >>
     `k < LENGTH sm.cs_current_insts` by decide_tac >> metis_tac[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z` by
    (irule ghost_inv_at_exterior_frame >> qexistsl_tac [`G`, `ee`, `t`, `sm`, `tn`] >>
     gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[ptr_val_ok_def, compileEnvTheory.is_word_type_def,
      venomStateTheory.update_var_def, ghost_kept_at_def] >> metis_tac[]
QED

Theorem len_full_suffix_scalar:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op pvt tvt.
    ~(cenv.ce_is_ctor /\ (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode) /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?n z G2 tn2.
      result_array_length cx tv ee = (INL n,ee) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e es sa sm s0 ee tv vv t` by
    metis_tac[] >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee t` by
    gvs[vv_post_def] >>
  drule_all vv_holds_sized_length_success_widens >> strip_tac >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by simp[] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
    gvs[vv_post_def] >>
  drule_all vv_holds_len_header_widens >> strip_tac >>
  `(case vv_location vv of NONE => LocMemory | SOME l => l) <> LocCalldata` by
    (Cases_on `vv` >> simp[contextTheory.vv_location_def] >>
     rename1 `LocatedValue _ p` >> Cases_on `p.ptr_location` >>
     gvs[vv_holds_def, contextTheory.vv_location_def]) >>
  `!v. 32 <= val_store_size tvt v /\ ~is_word_type (expr_type e)` by
    (drule sized_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         compileEnvTheory.is_word_type_def] >>
     Cases_on `v` >> simp[exprSimPropsTheory.val_store_size_def,
                            valueEncodingTheory.type_memory_size_def]) >>
  `is_sized_type (post_value_type cenv e)` by
    metis_tac[sized_type_widens_source] >>
  `!v. 32 <= val_footprint pvt v /\ ~is_word_type (post_value_type cenv e)` by
    (qpat_x_assum `is_sized_type (post_value_type cenv e)` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP sized_type_cases) >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         compileEnvTheory.is_word_type_def] >>
     Cases_on `v` >> simp[val_footprint_def, valueEncodingTheory.type_memory_size_def]) >>
  Cases_on `(case vv_location vv of NONE => LocMemory | SOME l => l)` >>
  gvs[builtinSimpleTheory.compile_builtin_len_def, contextTheory.compile_ptr_load_def,
      contextTheory.compile_imm_load_word_runtime, builtinPropsTheory.ptr_load_val_def]
  >~ [`emit_op MLOAD [vv_operand vv] sm = (op,sb)`]
  >- (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t` >>
  qexistsl_tac [`u with vs_inst_idx := SUC t.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst t u tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  irule len_full_load_finish >>
  simp[Abbr `u`] >>
  conj_tac >- simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  qexistsl_tac [`st0`, `tv`, `vv`] >>
  simp[] >>
  qx_gen_tac `H'` >> strip_tac >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t` >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (
       (mp_tac (Q.INST [`i` |-> `inst`, `u` |-> `u`, `s` |-> `t`, `D` |-> `DF (H' : (bool # 256 word # type_value) list # num list)`] straight_line_origin_ptr_edge) >>
        simp[Abbr `inst`, Abbr `u`, venomInstTheory.mk_inst_def,
             venomInstTheory.is_terminator_def] >>
        impl_tac >- (
          simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
               memSafeRunTheory.inst_dload_in_section_def,
               contextCodegenRelTheory.source_memory_read_ranges_def,
               codegenRelTheory.source_memory_write_ranges_def] >>
          conj_tac
          >- (Cases_on `vv` >>
              gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
                  vv_holds_def, expr_val_rel_def, exprSimMemDefsTheory.vv_store_bound_def] >>
              qpat_x_assum `!v. 32 <= val_store_size tvt v /\ _`
                (qspec_then `v` strip_assume_tac) >> decide_tac) >>
          reverse conj_tac
          >- (rewrite_tac[GSYM venomInstTheory.mk_inst_def] >>
              metis_tac[emitHelperPropsTheory.step_MLOAD]) >>
          `?v. ptr_val_ok cx (post_value_type cenv e) v (vv_operand vv) G tn t` by
            (Cases_on `vv` >>
             gvs[ptr_vv_ok_def, ptr_val_ok_def, contextTheory.vv_location_def,
                 contextTheory.vv_operand_def] >> metis_tac[]) >>
          `?p. vv_operand vv = Var p /\ ptr_covers G tn p t 32` by
            (irule representationCleanPtrTheory.ptr_val_ok_read_covers >>
             conj_tac >- metis_tac[] >>
             qexistsl_tac [`cx`, `pvt`, `post_value_type cenv e`, `v`] >> simp[] >>
             qpat_x_assum `!v. 32 <= val_footprint pvt v /\ _`
               (qspec_then `v` strip_assume_tac) >> decide_tac) >>
          gvs[] >> rewrite_tac[GSYM venomInstTheory.mk_inst_def] >>
          irule exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo >>
          gvs[ghost_inv_at_def]) >> simp[]) >>
  all_tac) >>
  `!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  drule assign_base_mload_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `sm.cs_next_id`,
    `STRING #"%" (toString sm.cs_next_var)`] mp_tac) >>
  simp[Abbr `inst`, Abbr `u`, venomStateTheory.update_var_def] >> strip_tac >>
  `?v. read_result cx tv ee = (INL v,ee) /\
    !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory pvt v (w2n w) mem` by
    (Cases_on `vv` >>
     gvs[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
         contextTheory.vv_location_def, contextTheory.vv_operand_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      mem_word_at (w2n w) mem = n2w n` by
    (rpt strip_tac >>
     `val_in_memory pvt v (w2n w) mem` by metis_tac[] >>
     `value_has_type tvt v` by metis_tac[] >>
     `result_array_length cx (Value v) ee = (INL n,ee)` by
       metis_tac[sized_read_result_length] >>
     qpat_x_assum `val_in_memory pvt v (w2n w) mem` mp_tac >>
     qpat_x_assum `result_array_length cx (Value v) ee = (INL n,ee)` mp_tac >>
     qpat_x_assum `value_has_type tvt v` mp_tac >>
     qpat_x_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` mp_tac >>
     qpat_x_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt` mp_tac >>
     qpat_x_assum `type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e)` mp_tac >>
     qpat_x_assum `is_sized_type (post_value_type cenv e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[type_widens_to_def]
     >- (drule_all sized_memory_header >>
         disch_then (qspecl_then [`cx`,`ee`] strip_assume_tac) >> gvs[]) >>
     qpat_x_assum `is_sized_type (post_value_type cenv e)` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP sized_type_cases) >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >>
     gvs[valueEncodingDefsTheory.val_in_memory_def, result_array_length_def,
         read_result_def, vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >>
     gvs[valueEncodingDefsTheory.val_in_memory_def, result_array_length_def,
         read_result_def, vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def] >>
     Cases_on `expr_type e` >>
     gvs[arg_type_fits_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rename1 `arg_type_fits (ArrayT _ _) (ArrayT _ bd)` >>
     Cases_on `bd` >>
     gvs[arg_type_fits_def, vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         vyperTypingTheory.value_has_type_def]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[ptrDisciplineTheory.mem_word_taint_def, pred_setTheory.EXTENSION] >>
     gen_tac >> Cases_on `x < 32` >> simp[] >>
     qpat_x_assum `!i. w2n w <= i /\ i < w2n w + 32 ==> _`
       (qspec_then `x + w2n w` mp_tac) >> simp[]) >>
  gvs[ptr_val_ok_def, ptrDisciplineTheory.op_taint_def,
      ptrDisciplineTheory.op_prov_def, compileEnvTheory.is_word_type_def,
      finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t` >>
  qexistsl_tac [`u with vs_inst_idx := SUC t.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst t u tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  irule len_full_load_finish >> simp[Abbr `u`] >>
  conj_tac >- simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  qexistsl_tac [`st0`, `tv`, `vv`] >> simp[] >>
  qx_gen_tac `H'` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >>
  conj_tac
  >- (qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t` >>
      mp_tac (Q.INST [`i` |-> `inst`, `u` |-> `u`, `s` |-> `t`,
        `D` |-> `DF (H' : (bool # 256 word # type_value) list # num list)`]
        straight_line_origin_ptr_edge) >>
      simp[Abbr `inst`, Abbr `u`, venomInstTheory.mk_inst_def,
           venomInstTheory.is_terminator_def] >>
      impl_tac >- (
        `op_taint tn (vv_operand vv) = {}` by
          (Cases_on `vv` >>
           gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def, ptr_vv_ok_def]) >>
        simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def] >>
        rpt conj_tac
        >~ [`step_inst_base _ _ = _`]
        >- simp[venomExecSemanticsTheory.step_inst_base_def,
                venomExecSemanticsTheory.exec_read1_def] >>
        gvs[ghost_inv_at_def, ptrSafeRunTheory.ptr_inst_ok_def,
            ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
            contextCodegenRelTheory.source_memory_read_ranges_def,
            codegenRelTheory.source_memory_write_ranges_def,
            venomExecSemanticsTheory.step_inst_non_invoke,
            venomExecSemanticsTheory.step_inst_base_def,
            venomExecSemanticsTheory.exec_read1_def, venomStateTheory.update_var_def] >>
        Cases_on `vv` >>
        gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def, vv_holds_def] >>
        drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >>
        simp[]) >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `0 < type_slot_size pvt` by
    (drule sized_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         vyperValueTheory.type_slot_size_def]) >>
  `vv_location vv <> SOME LocCode ==> !b. b < 32 ==> (w,b) NOTIN
       (if vv_location vv = SOME LocStorage then tn.t_stor else tn.t_trans)` by
    (strip_tac >> Cases_on `vv` >>
     gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def, ptr_vv_ok_def] >>
     rpt strip_tac >> spose_not_then assume_tac >>
     first_x_assum (qspecl_then [`w`, `b`] mp_tac) >> simp[] >>
     strip_tac >> drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  gvs[Abbr `inst`, ptrDisciplineTheory.step_prov_def,
      ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.out_taint_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def,
      ptrDisciplineTheory.set_var_taint_def, venomInstTheory.mk_inst_def,
      ptrDisciplineTheory.key_taint_def, ptrDisciplineTheory.set_prov_def,
      ptrDisciplineTheory.out_prov_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DRESTRICT] >>
  simp[ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.store_taint_def,
       ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.adopt_reset_def,
       pred_setTheory.EXTENSION] >>
  conj_tac >- (rpt strip_tac >>
    `x <> STRING #"%" (toString sm.cs_next_var)` by
      (strip_tac >> gvs[]) >> simp[]) >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
      ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
      ptrDisciplineTheory.range_bytes_def, venomStateTheory.update_var_def,
      ptrDisciplineTheory.written_taint_def,
      codegenRelTheory.source_memory_write_ranges_def,
      finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[])
QED
