(* The source and offset are forced at distinct compiler sites. *)
Theory entryCreateExtract32
Ancestors
  entryCreateAdminSequence entryCreateReplayBind entryCreateScopedBind
  entryCreateNativeFirstExit entryCreatePathScope entryCreateFocusSpec
  typeBuiltinPrereqs exprSimExtract32Source exprSimHypsDefs
  bodyFullExtract32Prepare bodyPtrSignedConvertSourceCompile
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
