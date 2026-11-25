(* Covered, untainted memory Len load at a linked VV landing. *)
Theory bodyLenMemoryRunCoreMods
Ancestors
  bodyFullPostsMods bodyFullGhostFrame decoderNavigationPtr wordLoadStorePtr
  decoderGhostFramePtr instMemFrontier memSafeRun allocaHistory fragExec
  representationCleanPtr exprPtrCtorImmStore bodyPtrDefs exprSimLen
  emitHelperProps emitHelper
  loweringStateRelDefs builtinSimple context compileEnv
  venomState venomInst fragGasOriginPtr ptrDiscipline
  vyperStorageFootprint valueEncodingDefs vyperTypeSystem vyperTyping
  list finite_map words arithmetic pred_set

Theorem len_memory_run_core_mods:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op n pvt tvt a w.
    (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory /\
    a = vv_operand vv /\
    is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca a LocMemory sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    eval_operand a t = SOME w /\
    mload (w2n w) t = n2w n /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       mem_word_at (w2n w) m = n2w n) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?z G2 tn2.
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2)) /\
      eval_operand op z = SOME (n2w n) /\
      op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (alloca_history func t ==> alloca_history func z) /\
      z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
        FLOOKUP G2 x = FLOOKUP G x /\
        op_taint tn2 (Var x) = op_taint tn (Var x)) /\
      tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
      tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  `emit_op MLOAD [a] sm = (op,sb)` by
    (qpat_x_assum `compile_builtin_len _ _ _ _ _ = _` mp_tac >>
     simp[builtinSimpleTheory.compile_builtin_len_def,
          contextTheory.compile_ptr_load_def,
          contextTheory.compile_imm_load_word_runtime]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.emit_def] >>
  qabbrev_tac `x = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MLOAD [a] [x]` >>
  qabbrev_tac `raw = update_var x (mload (w2n w) t) t` >>
  qabbrev_tac `z = raw with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `G2 = step_prov PG G i raw` >>
  qabbrev_tac `tn2 = step_taint i t raw tn` >>
  qexistsl_tac [`z`,`G2`,`tn2`] >>
  simp[Abbr `z`,Abbr `G2`,Abbr `tn2`,Abbr `raw`,Abbr `i`,Abbr `x`] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn
         (mk_inst sm.cs_next_id MLOAD [a]
           [STRING #"%" (toString sm.cs_next_var)]) t /\
       w2n w + 32 <= t.vs_alloca_next` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
     `allocas_from lo t` by fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
     `vv_holds_mods cenv cx (post_value_type cenv e) tv vv ee t` by
       fs[vv_post_mods_def] >>
     `is_sized_type (post_value_type cenv e)` by
       metis_tac[sized_type_widens_source] >>
     `~is_word_type (post_value_type cenv e)` by
       (qpat_x_assum `is_sized_type (post_value_type cenv e)` mp_tac >>
        disch_then (strip_assume_tac o MATCH_MP sized_type_cases) >>
        gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
            compileEnvTheory.is_word_type_def]) >>
     `?v. ptr_val_ok cx (post_value_type cenv e) v a G tn t` by
       (Cases_on `vv`
        >- (gvs[ptr_vv_ok_def, vv_holds_mods_def, loweringPostsTheory.vv_holds_def,
               contextTheory.vv_location_def, contextTheory.vv_operand_def,
               ptr_val_ok_def] >> qexists_tac `v` >> simp[])
        >- (rename1 `LocatedValue t' p` >>
            `p.ptr_location = LocMemory` by
              (qpat_x_assum `_ = LocMemory` mp_tac >>
               simp[contextTheory.vv_location_def]) >>
            gvs[ptr_vv_ok_def, vv_holds_mods_def, loweringPostsTheory.vv_holds_def,
                contextTheory.vv_location_def, contextTheory.vv_operand_def,
                ptr_val_ok_def] >> qexists_tac `v` >> simp[])) >>
     `!v. 32 <= val_footprint pvt v /\
             ~is_word_type (post_value_type cenv e)` by
       (qx_gen_tac `v0` >>
        qpat_x_assum `is_sized_type (post_value_type cenv e)` mp_tac >>
        disch_then (strip_assume_tac o MATCH_MP sized_type_cases) >>
        gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
            compileEnvTheory.is_word_type_def] >>
        Cases_on `v0` >>
        simp[loweringPostsTheory.val_footprint_def,
             valueEncodingTheory.type_memory_size_def]) >>
     reverse conj_tac
     >- (`!v. 32 <= val_store_size pvt v` by
           (qx_gen_tac `vv0` >> irule LESS_EQ_TRANS >>
            qexists_tac `val_footprint pvt vv0` >>
            simp[exprSimPropsTheory.val_footprint_le_store_size]) >>
         Cases_on `vv` >>
         gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
             vv_holds_mods_def, loweringPostsTheory.vv_holds_def,
             loweringPostsTheory.expr_val_rel_def,
             exprSimMemDefsTheory.vv_store_bound_def] >>
         rename1 `read_result cx tv ee = (INL loaded,ee)` >>
         qpat_x_assum `!v. 32 <= val_store_size pvt v`
           (qspec_then `loaded` assume_tac) >> decide_tac) >>
     `?v. ptr_val_ok cx (post_value_type cenv e) v a G tn t /\
          32 <= val_footprint pvt v` by metis_tac[] >>
     `?p. a = Var p /\ ptr_covers G tn p t 32` by
       (irule representationCleanPtrTheory.ptr_val_ok_read_covers >>
        conj_tac >- metis_tac[] >>
        qexistsl_tac [`cx`,`pvt`,`post_value_type cenv e`,`v'`] >> simp[] >>
        qpat_x_assum `!v. 32 <= val_footprint pvt v`
          (qspec_then `v'` strip_assume_tac) >> decide_tac) >>
     gvs[] >>
     qpat_x_assum `Var p = vv_operand vv`
       (fn th => rewrite_tac[SYM th]) >>
     irule exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo >>
     simp[]) >>
  `!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `a = vv_operand vv` SUBST_ALL_TAC >>
  conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> ptr_inst_ok _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      qpat_assum `t.vs_inst_idx = _` (pure_rewrite_tac o single o SYM) >>
      irule decoderNavigationPtrTheory.navigation_instruction_origin >>
      drule_then (fn th => simp[instMemFrontierTheory.below_frontier_MLOAD,th])
        step_MLOAD >>
      simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
           memSafeRunTheory.inst_dload_in_section_other,
           unitTransformDefsTheory.dalloca_no_wrap_def] >>
      qexistsl_tac [`sm`,`sb`] >> simp[venomInstTheory.mk_inst_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id MLOAD [vv_operand vv] [out]` >>
  qabbrev_tac `u = update_var out (n2w n) t` >>
  qabbrev_tac `tn1 = step_taint inst t u tn` >>
  `op_taint tn1 (Var out) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `inst`, Abbr `u`] >>
     qpat_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule wordLoadStorePtrTheory.mload_ghost_clean >> simp[]) >>
  `tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `inst`, venomInstTheory.mk_inst_def,
         decoderGhostFramePtrTheory.step_taint_nonmemory_frame] >>
  `op_prov (step_prov PG G inst u) (Var out) = NONE` by
    simp[Abbr `inst`, mk_inst_def, op_prov_def, step_prov_def,
         out_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[allocaHistoryTheory.alloca_history_def] >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      rename1 `get_instruction _ k = SOME j` >>
      Cases_on `k < LENGTH sm.cs_current_insts`
      >- metis_tac[] >>
      `k = LENGTH sm.cs_current_insts` by decide_tac >>
      gvs[Abbr `inst`, mk_inst_def]) >>
  qx_gen_tac `q` >> disch_tac >>
  `q <> out` by
    (simp[Abbr `out`] >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  simp[Abbr `tn1`, Abbr `inst`, mk_inst_def,
       decoderGhostFramePtrTheory.step_prov_other_output,
       decoderGhostFramePtrTheory.step_taint_other_output]
QED
