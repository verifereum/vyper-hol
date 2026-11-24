(* The source and offset are forced at distinct compiler sites. *)
Theory entryCreateExtract32
Ancestors
  entryCreateAdminSequence entryCreateReplayBind entryCreateScopedBind
  entryCreateNativeFirstExit entryCreatePathScope entryCreateFocusSpec
  entryCreateRawStageJoins entryCreateIntervalLayout createSizeTypeBuiltinCode
  entryCreateCompletedCut gasExemptCert stmtSimProps exprSimProps haltExitProj
  typeBuiltinPrereqs exprSimExtract32Source exprSimHypsDefs
  bodyFullExtract32Prepare bodyFullExtract32Suffix bodyFullExtract32JoinFrame
  bodyPtrSignedConvertSourceCompile bodyPtrTypeBuiltinsSavedOperand
  exprSimExtract32Post exprSimWordArgs wordArgsPtr
  gasShadowCompileStmtHelpers
  extract32PrepareFrame createSizeOperandCode createSizeCutCode
  gasShadowCompileBuiltinBytes gasShadowCompileContext gasShadowState
  vyperTypeSystem vyperStorageFootprint vyperStorageTrace
  builtinBytes fragGasOriginPtrExec fragGasSeqPtr exprSimExtract32Read
  exprOpenFirstOperand exprSimSource exprOperandVar freshWrites bodyPtrDefs
  exprSimAbiGasBridge abiEncoderProps emitHelperProps s1PrefixDefs
  fragExec list venomInst fragGasOriginPtr fragGasOrigin
  exprSimFullBundleProps exprLoweringProps loweringPosts compileEnv
  vyperValue vyperState venomState exprSimMemDefs
  bodySim bodyFullIfExpReach bodyFullHashKeccakFixed bodyMemoryDefs gasSummary

Triviality extract32_site_shape:
  expr_body_pre ce cx env (TypeBuiltin ann Extract32 ret args) es ==>
  ?src off m k bt. args = [src;off] /\
    expr_type src = BaseT (BytesT (Dynamic m)) /\
    expr_type off = BaseT (UintT k) /\
    ret = BaseT bt /\ extract32_result_base_ok bt /\ ann = ret
Proof
  strip_tac >> drule extract32_body_pre_shape >> strip_tac >> gvs[] >>
  fs[expr_body_pre_def,well_typed_expr_def,well_typed_type_builtin_args_def,
     is_uint_type_def] >> metis_tac[]
QED

Triviality extract32_argument_splits:
  compile_expr ce ty (TypeBuiltin ann Extract32 ret [src;off]) a = (vv,b) /\
  compile_expr (gas_shadow_env T ce) ty
    (TypeBuiltin ann Extract32 ret [gas_shadow_expr src;gas_shadow_expr off]) ha = (vv,hb) /\
  gas_shadow_state a ha /\ fn_has_code a b fnc /\ fn_has_code ha hb hfn ==>
  ?x s1 len data s2 y s3 raw s4 out h1 h2 h3.
    lower_value compile_expr ce (expr_type src) src a = (x,s1) /\
    compile_bytestring_src x s1 = ((len,data),s2) /\
    lower_value compile_expr ce ty off s2 = (y,s3) /\
    compile_extract32_load len data y s3 = (raw,s4) /\
    compile_clamp_basetype raw ret s4 = (out,b) /\ vv = StackValue ann out /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type src) (gas_shadow_expr src) ha = (x,h1) /\
    compile_bytestring_src x h1 = ((len,data),h2) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr off) h2 = (y,h3) /\
    gas_shadow_state s1 h1 /\ gas_shadow_state s2 h2 /\ gas_shadow_state s3 h3 /\
    ci_mono a s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
    fn_has_code a s1 fnc /\ fn_has_code s1 s2 fnc /\ fn_has_code s2 s3 fnc /\
    fn_has_code s1 b fnc /\ fn_has_code s2 b fnc /\ fn_has_code s3 b fnc /\
    fn_has_code ha h1 hfn /\ fn_has_code h2 h3 hfn
Proof
  strip_tac >>
  qpat_assum `compile_expr ce ty (TypeBuiltin _ _ _ [src;off]) _ = _`
    (strip_assume_tac o MATCH_MP extract32_compile_equations) >> gvs[] >>
  drule_all extract32_compile_cuts >> strip_tac >>
  `?h1. lower_value compile_expr (gas_shadow_env T ce) (expr_type src)
              (gas_shadow_expr src) ha = (src_op,h1) /\ gas_shadow_state s1 h1` by
    (mp_tac (Q.INST [`cenv` |-> `ce`,`e` |-> `src`,`ty` |-> `expr_type src`,
                     `sd` |-> `T`] gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`,`ha`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type src)
       (gas_shadow_expr src) ha` >> simp[]) >>
  `?h2. compile_bytestring_src src_op h1 = ((len,data),h2) /\ gas_shadow_state s2 h2` by
    (mp_tac (Q.INST [`src_ptr` |-> `src_op`] gas_shadow_compiles_bytestring_src) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`h1`] mp_tac) >> simp[] >>
     Cases_on `compile_bytestring_src src_op h1` >> simp[]) >>
  `?h3. lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr off) h2 =
              (off_op,h3) /\ gas_shadow_state s3 h3` by
    (mp_tac (Q.INST [`cenv` |-> `ce`,`e` |-> `off`,`sd` |-> `T`]
       gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`,`h2`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) ty
       (gas_shadow_expr off) h2` >> simp[]) >>
  qpat_assum `compile_expr _ _ (TypeBuiltin _ _ _ [gas_shadow_expr src;_]) _ = _`
    (strip_assume_tac o MATCH_MP extract32_compile_equations) >>
  gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`src` |-> `gas_shadow_expr src`] extract32_compile_cuts)) >> simp[]
QED

Triviality extract32_source_arg_pre:
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Extract32 ret [src;off]) es (st,a,b,ha,hb,vv,z,G,tn) /\
  lower_value compile_expr ce (expr_type src) src a = (x,s1) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type src) (gas_shadow_expr src) ha = (x,h1) /\
  gas_shadow_state s1 h1 /\ fn_has_code a s1 f /\ fn_has_code ha h1 shf ==>
  expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx (expr_type src) src es
    (st,a,s1,ha,h1,x,z,G,tn)
Proof
  strip_tac >>
  fs[expr_vv_sim_full_pre_def,expr_sim_full_pre_def] >>
  metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) extract32_vv_first_admissible]
QED

Triviality extract32_snapshot_cut_code:
  compile_bytestring_src op a = ((len,data),b) ==>
  create_cut_code {} a b
Proof
  strip_tac >>
  `create_cut_code {} a (SND (compile_bytestring_src op a))` by
    (simp[compile_bytestring_src_def, NoAsms] >>
     irule create_cut_code_bind >>
     simp[create_cut_code_emit_op,create_cut_targets_def] >>
     irule create_cut_code_bind >> simp[create_cut_code_emit_op,create_cut_targets_def]) >>
  metis_tac[pairTheory.SND]
QED

Triviality extract32_snapshot_inventory:
  compile_bytestring_src (Var sv) a = ((len,data),b) /\ not_fresh_at a sv /\
  fn_has_code a b f ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >> drule_all extract32_prepare_site >> strip_tac >> simp[] >>
  drule_at (Pos (el 2)) extract32_read_code_shape >> simp[extract32_read_prepare] >> strip_tac >>
  `!i. MEM i (emitted_insts a b) ==> i.inst_id IN frag_ids a b` by
    (drule extract32_snapshot_cut_code >>
     simp[create_cut_code_def,frag_code_def,emitted_blocks_def] >> metis_tac[]) >>
  `(EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (emitted_insts a b))` by
    (drule_all compile_bytestring_src_shape_fresh >> strip_tac >> simp[mk_inst_def,is_terminator_def]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* The snapshot is a real MLOAD/ADD interval and uses the source child's
   own physical state. The existential ghosts are chosen before H. *)
Triviality extract32_snapshot_at:
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Extract32 ret [src;off]) es (st,a,b,ha,hb,vv,z,G0,tn0) /\
  expr_body_pre ce cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  lower_value compile_expr ce (expr_type src) src a = (x,s1) /\ ci_mono a s1 /\
  compile_bytestring_src x s1 = ((len,data),s2) /\ fn_has_code s1 s2 f /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st mid.storage_trace /\ ~s.vs_halted /\
  (!H. valid_horizon cx st H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,D,C,f) ce cx src (es,a,s1,z,x,G0,tn0)
      H (INL v) mid G1 tn1 s) ==>
  expr_body_pre ce cx env off mid /\
  ?sv bs u G2 tn2 p l d.
    x = Var sv /\ v = BytesV bs /\ len = Var l /\ data = Var d /\
    not_fresh_at s1 sv /\ not_fresh_at s2 sv /\ not_fresh_at s2 l /\ not_fresh_at s2 d /\
    eval_operand (Var sv) u = SOME (n2w p) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\ eval_operand data u = SOME (n2w (p+32)) /\
    op_taint tn2 len = {} /\ op_prov G2 len = NONE /\
    p+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\ p+32+LENGTH bs <= u.vs_alloca_next /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 d u n) /\
    create_operand_at s2 u /\ alloca_history f u /\ z.vs_alloca_next <= u.vs_alloca_next /\
    create_operand_full_scope s1 s2 (gas_explicit_sites C shC) C f s [] (OK u) /\
    (!H. valid_horizon cx st H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG) (s,G1,tn1) [] (OK u,G2,tn2) /\
      expr_post H C f ce cx src es a s2 z mid (BytesV bs) (Var sv) u /\
      expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) u /\
      ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
      ptr_buf_ok ce src (Var sv) G2 u /\ ghost_inv_at (DF H) lo D ce cx mid G2 tn2 u /\
      ghost_kept_at lo ce es a G0 tn0 z G2 tn2)
Proof
  strip_tac >>
  `expr_body_pre ce cx env (TypeBuiltin ann Extract32 ret [src;off]) (es with gas_obs := gs)`
    by simp[] >>
  conj_tac >- (drule_all extract32_offset_body_pre >> simp[]) >>
  `expr_body_pre ce cx env src (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_type_builtin_head] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_source_value) >> strip_tac >> gvs[] >>
  `post_value_type ce src = expr_type src` by
    simp[post_value_type_bytestring,is_bytestring_type_def] >>
  `~is_word_type (post_value_type ce src)` by simp[is_word_type_def] >>
  `valid_horizon cx st (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_sim_full_post_def,expr_sim_full_endpoint_def])) >> gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre ce cx env src es` (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def,AllCaseEqs()]) >>
  `expr_store_bound cx (expr_type src) (BytesV bs) x s` by simp[] >>
  `?p. eval_operand x s = SOME (n2w p)` by
    (drule_all extract32_source_post_alloca_bound >> metis_tac[]) >>
  `?sv. x = Var sv` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def,ptr_mem_ok_def,is_word_type_def] >> strip_tac >>
     `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic m))) =
        SOME (BaseTV (BytesT (Dynamic m)))` by metis_tac[] >>
     qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [val_footprint_def])) >>
     metis_tac[]) >>
  gvs[] >>
  suspend "produce"
QED

Resume extract32_snapshot_at[produce]:
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `a.cs_next_var <= s1.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    metis_tac[not_fresh_at_mono] >>
  `not_fresh_at s1 sv` by metis_tac[compile_lower_value_var] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    simp[evaluate_type_def] >>
  `alloca_inv s` by fs[expr_post_def,stmt_state_rel_def] >>
  `!H. valid_horizon cx st H mid.storage_trace ==>
      expr_post H C f ce cx src es a s1 z mid (BytesV bs) (Var sv) s /\
      expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) s /\
      ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G1 tn1 s /\
      ptr_buf_ok ce src (Var sv) G1 s /\ ghost_inv_at (DF H) lo D ce cx mid G1 tn1 s /\
      ghost_kept_at lo ce es a G0 tn0 z G1 tn1` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [expr_sim_full_post_def])) >>
     gvs[is_word_type_def]) >>
  drule_all extract32_prepare_observed >>
  disch_then (qspecl_then [`gas_explicit_sites C shC`,`PG`]
    (qx_choose_then `src_base` (qx_choose_then `u` (qx_choose_then `G2`
      (qx_choose_then `tn2` (qx_choose_then `lv` (qx_choose_then `dv` strip_assume_tac))))))) >>
  `create_operand_at s1 s` by simp[create_operand_at_def] >>
  drule_all extract32_snapshot_inventory >> strip_tac >>
  `create_operand_full_scope s1 s2 (gas_explicit_sites C shC) C f s [] (OK u)` by
    (qpat_assum `u = raw with vs_inst_idx := _` SUBST1_TAC >>
     irule create_admin_sequence_scope >> fs[EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`u`,`G2`,`tn2`,`src_base`,`lv`,`dv`] >>
  simp[create_operand_at_def] >> rpt strip_tac >> res_tac >> gvs[]
QED

Finalise extract32_snapshot_at

Triviality extract32_offset_arg_pre:
  body_inv tops C ce cx /\
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Extract32 ret [src;off]) es (st,a,b,ha,hb,vv,z,G0,tn0) /\
  a.cs_next_var <= s2.cs_next_var /\
  lower_value compile_expr ce ty off s2 = (y,s3) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr off) h2 = (y,h3) /\
  gas_shadow_state s2 h2 /\ gas_shadow_state s3 h3 /\
  fn_has_code s2 s3 f /\ fn_has_code h2 h3 shf /\
  expr_body_pre ce cx env off mid /\ storage_trace_domain cx st mid.storage_trace /\
  create_operand_at s2 u /\ alloca_history f u /\ z.vs_alloca_next <= u.vs_alloca_next /\
  (!H. valid_horizon cx st H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG) (z,G0,tn0) marks (OK u,G2,tn2) /\
    expr_post H C f ce cx src es a s2 z mid v x u /\ ghost_inv_at (DF H) lo D ce cx mid G2 tn2 u) ==>
  expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty off mid (st,s2,s3,h2,h3,y,u,G2,tn2)
Proof
  strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `valid_horizon cx st (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `return_buf_frame D ce s2 u` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`z`,`a`] >> gvs[expr_post_def]) >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst t. frag_reachable C f u fn inst t ==> dalloca_fmp_headroom inst t` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st H mid.storage_trace ==>
     stmt_state_rel H C f ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo D ce cx mid G2 tn2 u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[expr_post_def]) >>
  `ctx_has_dalloca C ==> allocas_below_fmp u` by
    (fs[expr_post_def] >> metis_tac[stmt_state_rel_allocas_below_fmp]) >>
  `~u.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `local_ptrs_reserved ce s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    metis_tac[not_fresh_at_mono] >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_gas_admissible) >> strip_tac >>
  qpat_assum `create_operand_at s2 u` (strip_assume_tac o REWRITE_RULE [create_operand_at_def]) >>
  simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC
QED

Triviality extract32_result_bounds:
  expr_body_pre ce cx env (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es ==>
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
     BytesT (Fixed k) => k <= 32 | _ => T)
Proof
  simp[expr_body_pre_def,well_typed_expr_def,NoAsms] >> strip_tac >>
  qpat_x_assum `well_formed_type _ (BaseT bt)` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `bt` >> simp[well_formed_type_def,evaluate_type_def] >>
  rpt CASE_TAC >> gvs[] >> decide_tac
QED

Triviality extract32_read_horizon:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (r,ee) /\
  valid_horizon cx st H ee.storage_trace ==> valid_horizon cx st H es.storage_trace
Proof
  strip_tac >>
  `valid_horizon cx st H (es with gas_obs := gs).storage_trace` suffices_by simp[] >>
  irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
  qexistsl [`bind (eval_expr cx e) (read_result cx)`,`r`,`ee`] >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
QED

Triviality extract32_offset_landing_ready:
  expr_body_pre ce cx env (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es /\
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es
    (st,a,b,ha,hb,StackValue (BaseT bt) op,z,G0,tn0) /\
  extract32_result_base_ok bt /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\ expr_type off = BaseT (UintT k) /\
  lower_value compile_expr ce ty off s2 = (y,s3) /\
  compile_extract32_load (Var l) (Var d) y s3 = (raw,s4) /\
  compile_clamp_basetype raw (BaseT bt) s4 = (op,b) /\ fn_has_code s3 b f /\
  ci_mono a s2 /\ ci_mono s2 s3 /\
  expr_body_pre ce cx env off mid /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL (BytesV bs),mid) /\
  bind (eval_expr cx off) (read_result cx) (mid with gas_obs := gt) = (r,ee) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st ee.storage_trace /\ ~t.vs_halted /\
  not_fresh_at s2 sv /\ not_fresh_at s2 l /\ not_fresh_at s2 d /\
  eval_operand (Var sv) u = SOME (n2w p) /\
  eval_operand (Var l) u = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var d) u = SOME (n2w (p+32)) /\
  p+32 < dimword(:256) /\ p+32+LENGTH bs <= u.vs_alloca_next /\
  op_taint tn2 (Var l) = {} /\ op_prov G2 (Var l) = NONE /\
  (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 d u n) /\
  z.vs_alloca_next <= u.vs_alloca_next /\
  (!H. valid_horizon cx st H mid.storage_trace ==>
    expr_post H C f ce cx src es a s2 z mid (BytesV bs) (Var sv) u /\
    ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
    ghost_kept_at lo ce es a G0 tn0 z G2 tn2) /\
  (!H. valid_horizon cx st H ee.storage_trace ==>
    expr_sim_full_post (DF,lo,D,C,f) ce cx off (mid,s2,s3,u,y,G2,tn2) H r ee G3 tn3 t) ==>
  ?i. r = INL (IntV i) /\
    extract32_suffix_ready (DF,lo,D,C,f) ce cx st (src,off,bt)
      (es,a,z,G0,tn0) (s3,b,op) (ee,t,G3,tn3) (bs,m,p,i,l,d,y,raw,s4,Var sv)
Proof
  strip_tac >>
  `valid_horizon cx st (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st H ee.storage_trace ==> valid_horizon cx st H mid.storage_trace` by
    (rpt strip_tac >> drule_all extract32_read_horizon >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def,expr_sim_full_endpoint_def])) >>
  gvs[] >>
  `?i. v = IntV i /\ 0 <= i` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_offset_value) >>
     qexistsl [`ce`,`cx`,`off`,`env`,`mid with gas_obs := gt`,`ee`] >> simp[is_uint_type_def]) >>
  gvs[] >>
  `0 <= i /\ Num i < dimword(:256)` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_offset_bounds) >>
     qpat_assum `bind (eval_expr cx off) _ _ = _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  simp[extract32_suffix_ready_def] >>
  `expr_body_pre ce cx env src es` by metis_tac[expr_body_pre_type_builtin_head] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre ce cx env src es` (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def,AllCaseEqs()]) >>
  `evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k))` by
    (qpat_assum `expr_body_pre ce cx env off mid` (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def,AllCaseEqs()]) >>
  `expr_sim_inv ce cx env mid` by fs[expr_body_pre_def] >>
  `expr_post (storage_trace_horizon ee.storage_trace) C f ce cx src es a s2 z mid (BytesV bs) (Var sv) u /\
   ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- metis_tac[]) >> simp[ptr_val_ok_def,is_word_type_def]) >>
  drule_all extract32_source_post_view >> strip_tac >>
  `p < dimword(:256) /\ p' < dimword(:256)` by decide_tac >>
  `p = p'` by fs[wordsTheory.n2w_11,arithmeticTheory.LESS_MOD] >> gvs[] >>
  suspend "preserve"
QED

Resume extract32_offset_landing_ready[preserve]:
  `expr_post (storage_trace_horizon ee.storage_trace) C f ce cx src es a s2 z mid (BytesV bs) (Var sv) u` by
    metis_tac[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p t.vs_memory /\
   eval_operand (Var l) t = SOME (n2w (LENGTH bs)) /\
   eval_operand (Var d) t = SOME (n2w (p+32)) /\
   eval_operand (Var sv) t = SOME (n2w p) /\ eval_operand y t = SOME (n2w (Num i))` by
    (irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`src_op` |-> `Var sv`,`len` |-> `Var l`,`dp` |-> `Var d`]
         (INST_TYPE [alpha |-> ``:256``] extract32_offset_post_view))) >>
     `LENGTH bs < dimword(:256) /\ p+32+LENGTH bs < dimword(:256)` by decide_tac >>
     simp[] >> metis_tac[]) >>
  `ghost_kept ce mid s2 G2 tn2 u G3 tn3` by
    (qpat_assum `ghost_kept_at lo ce mid s2 _ _ _ _ _`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     simp[ghost_kept_def,ghost_kept_at_def] >> metis_tac[]) >>
  `op_prov G3 (Var l) = NONE /\ op_taint tn3 (Var l) = {}` by
    (qpat_assum `ghost_kept_at lo ce mid s2 _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (qspec_then `l` mp_tac) >> gvs[ptrDisciplineTheory.op_prov_def]) >>
  `!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G3 tn3 d t span` by
    (rpt strip_tac >>
     qpat_assum `ghost_kept_at lo ce mid s2 _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (qspec_then `d` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 d u n`
       (qspec_then `span` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then assume_tac >>
     fs[ptr_covers_def,eval_operand_def] >> gvs[] >> decide_tac) >>
  `expr_val_at ce cx (expr_type src) a s2 mid (BytesV bs) (Var sv) u` by
    (qpat_assum `expr_post _ _ _ _ _ src es a s2 z mid _ _ u`
       (mp_tac o REWRITE_RULE [expr_post_def]) >>
     simp[post_value_type_bytestring,is_bytestring_type_def]) >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G3 tn3 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] saved_ptr_mem_ok) >>
     qpat_assum `expr_post _ _ _ _ _ off mid s2 s3 u ee _ _ t` (irule_at Any) >>
     simp[is_word_type_def,exprSimPropsTheory.dynarray_free_base] >>
     metis_tac[]) >>
  `(!v. y = Var v ==> not_fresh_at s3 v) /\ (!v. y <> Label v)` by
    (`is_word_type (expr_type off)` by simp[is_word_type_def] >>
     drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `post_value_type ce off = expr_type off` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `op_prov G3 y = NONE /\ op_taint tn3 y = {}` by gvs[ptr_val_ok_def,is_word_type_def] >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `alloca_inv t` by fs[expr_post_def,stmt_state_rel_def] >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `a.cs_next_var <= s3.cs_next_var /\ a.cs_next_id <= s2.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce s3` by metis_tac[local_ptrs_reserved_next_var] >>
  `p+32+LENGTH bs <= t.vs_alloca_next` by decide_tac >>
  simp[] >> conj_tac >- (irule extract32_result_bounds >> metis_tac[]) >>
  `s2.cs_next_var <= s3.cs_next_var` by fs[ci_mono_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  suspend "frames"
QED

Resume extract32_offset_landing_ready[frames]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx src) _ _ = (INL _,mid)` mp_tac >>
     disch_then (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st H mid.storage_trace` by metis_tac[] >>
  `valid_horizon cx st H es.storage_trace` by
    (irule extract32_read_horizon >>
     qpat_assum `bind (eval_expr cx src) _ _ = (INL _,mid)` (irule_at Any) >> simp[]) >>
  `stmt_state_rel H C f ce cx es z` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `wb_frame ce es ee a z t` by
    (irule (INST_TYPE [alpha |-> ``:256``] extract32_join_wb_frame) >>
     qpat_assum `expr_post H _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_post H _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[ci_mono_def] >> fs[ci_mono_def]) >>
  simp[] >>
  conj_tac >- fs[expr_post_def] >> conj_tac >- fs[expr_post_def] >>
  conj_tac
  >- (strip_tac >> irule (SIMP_RULE (srw_ss()) [expr_has_effect_thm]
       (INST_TYPE [alpha |-> ``:256``] extract32_join_pure_frame)) >>
      qpat_assum `expr_post H _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `wb_frame ce es mid a z u` by metis_tac[expr_post_frame] >>
  irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
  qpat_assum `stmt_state_rel H _ _ _ _ es z` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo ce mid s2 G2 tn2 u G3 tn3` (irule_at Any) >>
  qpat_assum `wb_frame ce es mid a z u` (irule_at Any) >> fs[ci_mono_def]
QED

Finalise extract32_offset_landing_ready

(* Common bind rules at Extract32's three handoffs. The cut sees the
   source equation from the same scoped normal witness, not a new run. *)
Triviality extract32_bind_landing:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st a m source (es,s,G,tn) P
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st a m source (es,s,G,tn)
    (\H r mid A ta u. P H r mid A ta u /\ create_operand_at m u /\ mid.gas_obs = [] /\
      storage_trace_domain cx st mid.storage_trace /\
      (?xs. source (es with gas_obs := xs) = (r,mid)))
    (\H r mid gt q. ?exc. r = INR exc /\
      create_operand_exit_post C cx H (INR exc : eval_result + exception) mid gt q)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[]
      >- (disj1_tac >> conj_tac >- fs[create_operand_full_scope_def,create_operand_at_def] >>
          qexists `gas_explicit marks s.vs_gas_readings` >> metis_tac[APPEND_NIL]) >>
      disj2_tac >> Cases_on `res` >>
      fs[create_operand_exit_post_def,expr_exit_INR_type,halt_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Triviality extract32_bind_scoped_cut:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_layout a b /\
  create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code a b f /\
  create_operand_at a s /\ ~s.vs_halted /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st a m
    (source : evaluation_state -> value evaluation_result) (es,s,G,tn) P (create_operand_exit_post C cx) /\
  create_operand_cut a m E C f tops cx st source (es,s) /\
  (!H r mid A ta u. P H r mid A ta u ==> ?v. r = INL v) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!left v mid A ta u xs.
    source (es with gas_obs := xs) = (INL v,mid) /\ mid.gas_obs = [] /\
    storage_trace_domain cx st mid.storage_trace /\ create_operand_at m u /\
    (!H. valid_horizon cx st H mid.storage_trace ==>
      P H (INL v) mid A ta u /\ gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) left (OK u,A,ta)) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st m b
      ((next : value -> evaluation_state -> eval_result evaluation_result) v)
      (mid,u,A,ta) Q (create_operand_exit_post C cx) /\
    create_operand_cut m b E C f tops cx st (next v) (mid,u)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st a b (bind source next)
    (es,s,G,tn) Q (create_operand_exit_post C cx) /\
  create_operand_cut a b E C f tops cx st (bind source next) (es,s)
Proof
  strip_tac >> drule_all raw_create_scope_at_split >>
  disch_then (qspec_then `E` strip_assume_tac) >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `fn_has_code a m f /\ fn_has_code m b f` by
    (irule fn_has_code_split >> fs[create_cut_code_def] >> metis_tac[]) >>
  drule extract32_bind_landing >> strip_tac >>
  qmatch_assum_abbrev_tac `scoped_operand_outcome _ _ _ _ a m _ _ Pc Rc` >>
  suspend "bind_scoped"
QED

Resume extract32_bind_scoped_cut[bind_scoped]:
  conj_tac
  >- (irule scoped_operand_bind_all_mixed >> simp[] >>
      conj_tac >- (rpt strip_tac >>
                   simp[vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_assoc] >>
                   ho_match_mp_tac gas_exempt_cert_bind_value >>
                   qexistsl [`v`,`mid`,`t`] >> fs[vyperStateTheory.ignore_bind_def]) >>
      conj_tac >- (rpt strip_tac >>
                   simp[vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_assoc] >>
                   irule gas_exempt_cert_error_value >> fs[vyperStateTheory.ignore_bind_def]) >>
        (qexistsl [`Pc`,`m`] >> simp[] >> reverse conj_tac
         >- (fs[Abbr `Rc`] >> conj_tac >> first_assum ACCEPT_TAC) >>
         rpt gen_tac >> strip_tac >>
         `valid_horizon cx st (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
           fs[storage_trace_domain_def] >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Pc _ _ _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
         fs[Abbr `Pc`] >> metis_tac[])) >>
  irule create_operand_cut_bind_replay >> simp[] >>
  qexistsl [`DF`,`G`,`PG`,`Pc`,`lo`,`m`,`tn`] >>
  conj_tac >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[]) >>
  reverse conj_tac >-
    (conj_tac >- (simp[Abbr `Pc`] >> metis_tac[]) >>
     conj_tac >- (drule_all scoped_outcome_completed_operand >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  qx_genl_tac [`H0`,`front`,`v`,`mid`,`A`,`ta`,`t`] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ Pc _ _ _ _ _ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  fs[Abbr `Pc`] >>
  qpat_assum `!left v mid A ta u xs. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`create_cut_marks E front`,`v`,`mid with gas_obs := []`,`A`,`ta`,`t`,`xs`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Finalise extract32_bind_scoped_cut

(* The administrative snapshot does not change the Vyper value or consume
   observations. Its native witness is nevertheless the real MLOAD/ADD. *)
Triviality extract32_snapshot_scoped:
  e.gas_obs = [] /\ storage_trace_domain cx st e.storage_trace /\
  create_operand_full_scope a b E C f s [] (OK u) /\
  (!H. valid_horizon cx st H e.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK u,A,ta)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st a b (return (v:value)) (e,s,G,tn)
    (\H r ee B tb t. r = INL v /\ ee = e /\ B = A /\ tb = ta /\ t = u)
    (create_operand_exit_post C cx)
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists `[]` >>
  disj2_tac >> disj1_tac >> qexistsl [`INL v`,`e`,`OK u`,`A`,`ta`] >>
  `e with gas_obs := [] = e` by simp[evaluation_state_component_equality] >>
  simp[vyperStateTheory.return_def,gas_explicit_def]
QED

Theorem create_extract32_vv_from_tail:
  body_inv (cx_tops cx) C ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Extract32 ret args) es /\
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Extract32 ret args) es (st,a,b,ha,hb,vv,z,G0,tn0) /\
  create_layout a b /\
  (!e ty' ee sa sb sha shb x s G tn. MEM e args /\
    expr_body_pre ce cx env e ee /\ create_layout sa sb /\
    expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty' e ee (st,sa,sb,sha,shb,x,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st sa sb
      (bind (eval_expr cx e) (read_result cx)) (ee,s,G,tn)
      (expr_sim_full_post (DF,lo,D,C,f) ce cx e (ee,sa,sb,s,x,G,tn)) (create_operand_exit_post C cx) /\
    create_operand_cut sa sb (gas_explicit_sites C shC) C f (cx_tops cx) cx st
      (bind (eval_expr cx e) (read_result cx)) (ee,s)) /\
  (!src off bt op s3 mid t G tn bs m p i l d y raw s4 srcop.
    extract32_suffix_ready (DF,lo,D,C,f) ce cx st (src,off,bt)
      (es,a,z,G0,tn0) (s3,b,op) (mid,t,G,tn) (bs,m,p,i,l,d,y,raw,s4,srcop) ==>
    let e = TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off];
        source = bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
          [expr_type src;expr_type off] [BytesV bs;IntV i])) (\v. return (Value v))
    in scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st
         s3 b source (mid,t,G,tn)
         (\H res ee A ta u. create_operand_vv_post (DF,lo,D,C,f) ce cx e
           (es,a,b,z,StackValue (BaseT bt) op,G0,tn0) H res ee A ta u /\ create_operand_at b u)
         (create_operand_exit_post C cx) /\
       create_operand_cut s3 b (gas_explicit_sites C shC) C f (cx_tops cx) cx st source (mid,t)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st a b
    (eval_expr cx (TypeBuiltin ann Extract32 ret args)) (es,z,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,D,C,f) ce cx (TypeBuiltin ann Extract32 ret args)
      (es,a,b,z,vv,G0,tn0) H res ee G tn t /\ create_operand_at b t) (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f (cx_tops cx) cx st
    (eval_expr cx (TypeBuiltin ann Extract32 ret args)) (es,z)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> drule extract32_site_shape >> strip_tac >> gvs[] >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  qpat_assum `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr _) ha = _`
    (assume_tac o SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def]) >>
  drule_all extract32_argument_splits >> strip_tac >> gvs[] >>
  qabbrev_tac `E = gas_explicit_sites C shC` >>
  `create_cut_code {} a s1 /\ create_cut_code {} s1 s2 /\
   create_cut_code {} s2 s3 /\ create_cut_code {} s3 b` by
    metis_tac[create_operand_cut_code,pairTheory.SND,extract32_snapshot_cut_code,extract32_tail_cut_code] >>
  `create_cut_code {} s2 b /\ create_cut_code {} s1 b` by metis_tac[create_cut_code_join] >>
  `create_layout a s1 /\ create_layout s1 b /\ create_layout s2 s3 /\ create_layout s2 b` by
    (fs[create_cut_code_def] >> rpt conj_tac >> irule create_layout_subinterval >>
     metis_tac[cs_extends_refl,cs_extends_trans]) >>
  `expr_body_pre ce cx env src es` by metis_tac[expr_body_pre_type_builtin_head] >>
  `expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx (expr_type src) src es
     (st,a,s1,ha,h1,x,z,G0,tn0)` by
    (irule extract32_source_arg_pre >> simp[] >> metis_tac[]) >>
  qpat_assum `!e tym ee sa sb sha shb x s G tn. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`src`,`expr_type src`,`es`,`a`,`s1`,`ha`,`h1`,`x`,`z`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  pure_rewrite_tac[CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_extract32_vv_bind] >>
  suspend "source_bind"
QED

Resume create_extract32_vv_from_tail[source_bind]:
  `create_operand_at a z` by simp[create_operand_at_def] >>
  irule extract32_bind_scoped_cut >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_lifts,storage_trace_frame_return] >>
  conj_tac >- (qexists `ce` >> first_assum ACCEPT_TAC) >>
  qexistsl [`expr_sim_full_post (DF,lo,D,C,f) ce cx src (es,a,s1,z,x,G0,tn0)`,`s1`] >>
  simp[] >> reverse conj_tac >- (simp[expr_sim_full_post_def,CaseEq "sum"] >> metis_tac[]) >>
  qx_genl_tac [`left`,`v`,`mid`,`G1`,`tn1`,`s`,`gs`] >> strip_tac >>
  `valid_horizon cx st (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~s.vs_halted` by
    (qpat_assum `!H. _ ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac gas_origin_ptr_path_exec >> fs[exit_result_def]) >>
  `lower_value compile_expr ce (expr_type src) src a = (x,s1)` by simp[] >>
  `!H. valid_horizon cx st H mid.storage_trace ==>
     expr_sim_full_post (DF,lo,D,C,f) ce cx src (es,a,s1,z,x,G0,tn0) H (INL v : value + exception) mid G1 tn1 s` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. _ ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  drule_all extract32_snapshot_at >> strip_tac >>
  gvs[] >>
  `ci_mono a s2` by metis_tac[ci_mono_trans] >>
  `a.cs_next_var <= s2.cs_next_var` by fs[ci_mono_def] >>
  `!H. valid_horizon cx st H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (z,G0,tn0) left (OK u,G2,tn2) /\
       expr_post H C f ce cx src es a s2 z mid (BytesV bs) (Var sv) u /\
       ghost_inv_at (DF H) lo D ce cx mid G2 tn2 u` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (z,G0,tn0) left _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     simp[] >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  `expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty off mid
     (st,s2,s3,h2,h3,y,u,G2,tn2)` by
    (irule extract32_offset_arg_pre >> fs[Abbr `E`] >> metis_tac[]) >>
  drule_all extract32_snapshot_inventory >> strip_tac >>
  `create_operand_cut s1 s2 E C f (cx_tops cx) cx st (return (BytesV bs)) (mid,s)` by
    (irule create_admin_sequence_cut >> fs[EVERY_MEM]) >>
  qmatch_goalsub_abbrev_tac `scoped_operand_outcome _ _ _ _ s1 b ksrc _ _ _` >>
  `bind (return (BytesV bs)) (\v. ksrc) = ksrc` by simp[vyperStateTheory.bind_return] >>
  pop_assum (once_rewrite_tac o single o GSYM) >>
  suspend "snapshot_continue"
QED

Resume create_extract32_vv_from_tail[snapshot_continue]:
  `storage_trace_frame ksrc` by
    simp[Abbr `ksrc`,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_read_result,storage_trace_frame_lifts,storage_trace_frame_return] >>
  `scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st s1 s2
     (return (BytesV bs)) (mid,s,G1,tn1)
     (\H r ee B tb t. r = INL (BytesV bs) /\ ee = mid /\ B = G2 /\ tb = tn2 /\ t = u)
     (create_operand_exit_post C cx)` by
    (irule extract32_snapshot_scoped >> simp[] >> metis_tac[]) >>
  irule extract32_bind_scoped_cut >> simp[storage_trace_frame_return] >>
  conj_tac >- (qexists `ce` >> first_assum ACCEPT_TAC) >>
  qexistsl [`\H r ee B tb t. (r : value + exception) = INL (BytesV bs) /\
               ee = mid /\ B = G2 /\ tb = tn2 /\ t = u`,`s2`] >>
  simp[] >> qx_genl_tac [`adm_marks`,`admin_v`,`ee`,`B`,`tb`,`t`,`gl`] >> strip_tac >>
  `valid_horizon cx st (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> _ /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  gvs[Abbr `ksrc`] >>
  suspend "offset_bind"
QED

Resume create_extract32_vv_from_tail[offset_bind]:
  qpat_assum `!e tym rr sa sb sha shb x s G tn. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`off`,`ty`,`ee`,`s2`,`s3`,`h2`,`h3`,`y`,`t`,`B`,`tb`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `~t.vs_halted` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac gas_origin_ptr_path_exec >> fs[exit_result_def]) >>
  irule extract32_bind_scoped_cut >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_lifts,storage_trace_frame_return] >>
  conj_tac >- (qexists `ce` >> first_assum ACCEPT_TAC) >>
  qexistsl [`expr_sim_full_post (DF,lo,D,C,f) ce cx off (ee,s2,s3,t,y,B,tb)`,`s3`] >>
  simp[] >> reverse conj_tac >- (simp[expr_sim_full_post_def,CaseEq "sum"] >> metis_tac[]) >>
  qx_genl_tac [`right`,`w`,`ef`,`G3`,`tn3`,`t3`,`gt`] >> strip_tac >>
  `valid_horizon cx st (storage_trace_horizon ef.storage_trace) ef.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~t3.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H ef.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac gas_origin_ptr_path_exec >> fs[exit_result_def]) >>
  `!H. valid_horizon cx st H ef.storage_trace ==>
     expr_sim_full_post (DF,lo,D,C,f) ce cx off (ee,s2,s3,t,y,B,tb) H
       (INL w : value + exception) ef G3 tn3 t3` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ef.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  `p+32+LENGTH bs <= t.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st H ee.storage_trace ==>
     expr_post H C f ce cx src es a s2 z ee (BytesV bs) (Var sv) t /\
     ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) B tb t /\
     ghost_kept_at lo ce es a G0 tn0 z B tb` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) >>
  drule_all extract32_offset_landing_ready >> strip_tac >> gvs[] >>
  qpat_assum `!src off bt op s3 mid t G tn bs m p i l d y raw s4 srcop.
      extract32_suffix_ready _ _ _ _ _ _ _ _ _ ==> _`
    (drule_then mp_tac) >> simp[]
QED

Finalise create_extract32_vv_from_tail
