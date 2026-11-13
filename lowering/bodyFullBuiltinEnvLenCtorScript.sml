(* Fixed-endpoint constructor immutable Len suffix. *)
Theory bodyFullBuiltinEnvLenCtor
Ancestors
  bodySimFull bodyFullGhostFrame exprSimLen exprSimSource exprSimHypsDefs
  exprSimUnwrap exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr gasOutcomeFullCompose gasShadowState
  vyperStorageFootprint vyperTypeSystem vyperTypeBuiltins vyperAST
  loweringStateRelDefs ptrDiscipline codegenRel contextCodegenRel
  instMemFrontier allocaHistory emitHelperProps compileEnv representationCleanPtr
  vyperInterpreter vyperState venomState venomInst list finite_map

Theorem len_ctor_header_clean[local]:
  !cenv cx env e es pvt tvt v a tn t.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    is_sized_type (expr_type e) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    value_has_type tvt v /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
       val_in_memory pvt v a mem) ==>
    !i. a <= i /\ i < a + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperTypeSystemTheory.type_widens_to_def]
  >- (gen_tac >> disch_tac >> irule robust_mem_word_at_clean >>
      qexistsl [`a`, `t.vs_memory`] >> simp[] >>
      `val_in_memory pvt v a t.vs_memory` by
        simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
      drule_all sized_memory_header >>
      disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
      qexists_tac `n2w n` >> rpt strip_tac >>
      `val_in_memory pvt v a mem'` by metis_tac[] >>
      drule_all sized_memory_header >>
      disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]) >>
  drule sized_type_cases >> strip_tac >>
  Cases_on `post_value_type cenv e` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def,
      vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
  >- (Cases_on `b` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def] >>
      Cases_on `a'` >> gvs[vyperTypingTheory.value_has_type_def] >>
      gen_tac >> disch_tac >> irule robust_mem_word_at_clean >>
      qexistsl [`a`, `t.vs_memory`] >> simp[] >>
      gvs[valueEncodingDefsTheory.val_in_memory_def] >> metis_tac[]) >>
  gen_tac >> disch_tac >> irule robust_mem_word_at_clean >>
  qexistsl [`a`, `t.vs_memory`] >> simp[] >>
  gvs[valueEncodingDefsTheory.val_in_memory_def] >> metis_tac[]
QED

Theorem len_full_suffix_ctor:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op pvt tvt.
    cenv.ce_is_ctor /\
    (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode /\
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
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> gvs[]) >>
  `op_taint tn (vv_operand vv) = {} /\ op_prov G (vv_operand vv) = NONE` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     simp[] >> strip_tac >> Cases_on `vv` >>
     gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def, ptr_vv_ok_def]) >>
  `32 <= type_memory_size pvt` by
    (`is_sized_type (post_value_type cenv e)` by
       metis_tac[sized_type_widens_source] >>
     drule sized_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         valueEncodingTheory.type_memory_size_def]) >>
  `w2n w + 32 <= lo` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     simp[] >> strip_tac >> res_tac >> decide_tac) >>
  Cases_on `cenv.ce_imm_alloca` >>
  gvs[builtinSimpleTheory.compile_builtin_len_def, contextTheory.compile_ptr_load_def,
      contextTheory.compile_imm_load_word_def]
  >- suspend "direct" >>
  suspend "base"
QED

Resume len_full_suffix_ctor[direct]:
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t` >>
  qexistsl [`u with vs_inst_idx := SUC t.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst t u tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (`gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) []
         (OK (u with vs_inst_idx := SUC t.vs_inst_idx),
          step_prov PG G inst u, step_taint inst t u tn)` by
        (mp_tac (Q.INST [`i` |-> `inst`, `u` |-> `u`, `s` |-> `t`,
                         `D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`]
                    straight_line_origin_ptr_edge) >>
         simp[Abbr `inst`, Abbr `u`, venomInstTheory.mk_inst_def,
              venomInstTheory.is_terminator_def] >>
         impl_tac >- (
           simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
                memSafeRunTheory.inst_dload_in_section_def,
                contextCodegenRelTheory.source_memory_read_ranges_def,
                codegenRelTheory.source_memory_write_ranges_def] >>
           `lo <= t.vs_alloca_next /\ allocas_from lo t` by
             gvs[ghost_inv_at_def] >>
           `mload (w2n w) t = n2w n` by
             gvs[builtinPropsTheory.ptr_load_val_def] >>
           simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
                memLocDefsTheory.mem_read_ops_def, contextCodegenRelTheory.source_memory_read_ranges_def,
                codegenRelTheory.source_memory_write_ranges_def,
                venomExecSemanticsTheory.step_inst_non_invoke,
                venomExecSemanticsTheory.step_inst_base_opcode_eqs,
                venomExecSemanticsTheory.exec_read1_def,
                venomStateTheory.update_var_def]) >> simp[]) >>
      `~(u with vs_inst_idx := SUC t.vs_inst_idx).vs_halted` by
        simp[Abbr `u`, update_var_def] >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  `!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    simp[not_fresh_at_def] >>
  `stmt_state_rel H ctx func cenv cx ee
     (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     `not_local_ptr cenv ee.scopes (STRING #"%" (toString sm.cs_next_var))` by
       (irule exprSimOperandsTheory.fresh_not_local_ptr >>
        qexists_tac `sm` >> simp[not_fresh_at_def]) >>
     metis_tac[stmt_state_rel_update_var, vv_post_def]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_stack >>
      qexists_tac `BaseT (UintT 256)` >>
      irule len_vv_post_load >>
      simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE] >>
      qexistsl [`t`, `sm`, `tv`, `vv`] >>
      simp[] >> metis_tac[]) >>
  `alloca_history func (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (mp_tac (Q.INST [`inst` |-> `inst`, `t` |-> `u`, `s` |-> `t`]
       (SPEC_ALL alloca_history_base_step)) >>
     simp[Abbr `inst`, Abbr `u`, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def] >>
     impl_tac >- (gvs[vv_post_def, stmt_state_rel_def,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_read1_def,
          builtinPropsTheory.ptr_load_val_def]) >> simp[]) >>
  simp[exprSimMemDefsTheory.expr_store_bound_word,
       is_word_type_def, Abbr `u`, update_var_def] >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem` by
    (`value_has_type tvt val` by metis_tac[] >>
     metis_tac[len_ctor_header_clean]) >>
  `new_site_bytes t (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w n) t) = {}` by
    (simp[update_var_def, new_site_bytes_def,
          pred_setTheory.EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl [`G`, `ee`, `t`, `sm`, `tn`] >>
      simp[Abbr `inst`, venomInstTheory.mk_inst_def,
           step_prov_def, step_taint_def, set_var_taint_def, op_taint_def,
           step_taint_def, mem_taint_def,
           step_writes_def, written_taint_def, range_bytes_def,
           store_taint_def, imm_taint_def, adopt_reset_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def,
           lookup_var_def, FLOOKUP_UPDATE, set_prov_def, out_prov_def,
           finite_mapTheory.FLOOKUP_DRESTRICT] >>
      gvs[update_var_def]) >>
  conj_tac
  >- (simp[ptr_val_ok_def, op_prov_def, op_taint_def,
           Abbr `inst`, venomInstTheory.mk_inst_def,
           step_prov_def, set_prov_def, out_prov_def,
           step_taint_def, set_var_taint_def, mem_taint_def,
           range_bytes_def, FLOOKUP_UPDATE] >>
      simp[is_word_type_def, FLOOKUP_DRESTRICT, out_taint_def,
           mem_taint_def, range_bytes_def] >>
      simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
      rpt strip_tac >> Cases_on `x < 32` >> simp[] >>
      first_x_assum irule >> decide_tac) >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sm.cs_next_var)` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_at_def, Abbr `inst`, venomInstTheory.mk_inst_def,
       step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def,
       mem_taint_def, step_writes_def, written_taint_def, range_bytes_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gvs[update_var_def] >> metis_tac[]
QED

Resume len_full_suffix_ctor[base]:
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  `eval_operand ib t = SOME 0w` by
    gvs[stmt_state_rel_def, immutable_base_zero_def] >>
  `op_taint tn ib = {} /\ op_prov G ib = NONE` by
    (`ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G tn t` by
       metis_tac[] >>
     Cases_on `ib` >> gvs[op_taint_def, op_prov_def, ghost_inv_at_def]) >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out1 = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `out2 = STRING #"%" (toString (sm.cs_next_var + 1))` >>
  qabbrev_tac `i1 = mk_inst sm.cs_next_id ADD [vv_operand vv; ib] [out1]` >>
  qabbrev_tac `i2 = mk_inst (sm.cs_next_id + 1) ILOAD [Var out1] [out2]` >>
  drule fragExecTheory.fn_has_code_same_block >>
  disch_then (qspec_then `[i1;i2]` mp_tac) >>
  (impl_tac >- simp[APPEND_ASSOC]) >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) = SOME i1 /\
   get_instruction bb (LENGTH sm.cs_current_insts + 1) = SOME i2` by
    (first_assum (qspec_then `0` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  qabbrev_tac `u1 = update_var out1 w t` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `u2 = update_var out2 (n2w n) s1` >>
  qabbrev_tac `G1 = step_prov PG G i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 t u1 tn` >>
  qexistsl [`u2 with vs_inst_idx := SUC s1.vs_inst_idx`,
            `step_prov PG G1 i2 u2`, `step_taint i2 s1 u2 tn1`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `lo <= t.vs_alloca_next /\ allocas_from lo t` by gvs[ghost_inv_at_def] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) []
      (OK s1,G1,tn1)` by
    (simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`] >>
     mp_tac (Q.INST [`i` |-> `i1`, `u` |-> `u1`, `s` |-> `t`,
                     `D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`]
                    straight_line_origin_ptr_edge) >>
     simp[Abbr `i1`, Abbr `u1`, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def] >>
     (impl_tac >- simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       memLocDefsTheory.mem_read_ops_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def, update_var_def,
       wordsTheory.WORD_ADD_0] >> metis_tac[]) >> simp[]) >>
  `eval_operand (Var out1) s1 = SOME w` by
    simp[Abbr `s1`, Abbr `u1`, update_var_def, eval_operand_def,
         lookup_var_def, FLOOKUP_UPDATE] >>
  `op_taint tn1 (Var out1) = {} /\ op_prov G1 (Var out1) = NONE` by
    simp[Abbr `tn1`, Abbr `G1`, Abbr `i1`, venomInstTheory.mk_inst_def,
         step_taint_def, set_var_taint_def, out_taint_def,
         step_prov_def, set_prov_def, out_prov_def, op_taint_def,
         op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `mload (w2n w) s1 = n2w n` by
    gvs[Abbr `s1`, Abbr `u1`, update_var_def,
        builtinPropsTheory.ptr_load_val_def, mload_def] >>
  FAIL_TAC "second edge"
QED

Finalise len_full_suffix_ctor
