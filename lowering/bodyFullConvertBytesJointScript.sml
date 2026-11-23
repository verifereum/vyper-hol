Theory bodyFullConvertBytesJoint
Ancestors
  bodyFullShadowBodyInv
  haltExitProj stateRelProj bodyFullHashKeccakFixed
  bodyFullPreds bodySimFull bodyFullConvertChildRead bodyFullPathHistory
  bodyFullConvertCopyRun bodyFullConvertCopyPosts bodyFullConvertEndpointPosts
  bodyFullConvertCastOrigin bodyPtrTypeBuiltinsMemoryInterface
  bodyPtrTypeBuiltinsMemoryBounds bodyPtrTypeBuiltinsMemoryOperandResources
  assignTuplePtrBytesResources bodyPtrIfExpCopyHeader exprOperandVar
  exprSimConvertBytes exprSimConvert exprSimHyps exprSimSource
  bodyPtrSignedConvertSourceTyping
  gasShadowCompile gasShadowState exprLowering exprLoweringProps compileEnv
  vyperContext vyperInterpreter vyperState vyperAST bodyFullEmptyLeafData

(* The memory result carries the extra buffer coverage needed by clients of
   the located VV. Keep it with the physical endpoint of the conversion. *)
Definition convert_bytes_vv_post_def:
  convert_bytes_vv_post (DF,lo,d,ctx,func) ce cx ann e
    (es,sa,sb,s0,out,G0,tn0) H res ee G tn t <=>
    expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx (TypeBuiltin ann Convert ann [e])
      (es,sa,sb,s0,LocatedValue ann (mk_ptr out LocMemory),G0,tn0) H res ee G tn t /\
    ptr_buf_ok ce (TypeBuiltin ann Convert ann [e]) out G t
End

Definition convert_bytes_vv_suffix_def:
  convert_bytes_vv_suffix (DF,lo,d,ctx,func,explicit,PG) ce cx ann e st0
      (es,sa,sm,sb,s0,out,G0,tn0) (v,mid,t,G1,tn1) <=>
    ?G2 tn2 r res.
      res = sum_CASE (convert_result cx (expr_type e) ann v) (\w. INL (Value w)) INR /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (r,G2,tn2)) /\
      ((?u raw. r = OK u /\
          run_inst_seq (emitted_insts sm sb) t = OK raw /\
          u = raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
          !H. valid_horizon cx st0 H mid.storage_trace ==>
              convert_bytes_vv_post (DF,lo,d,ctx,func) ce cx ann e
                (es,sa,sb,s0,out,G0,tn0) H res mid G2 tn2 u) \/
       (?u raw msg. r = Abort Revert_abort u /\ res = INR (Error (RuntimeError msg)) /\
          run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort raw))
End

Theorem convert_memory_vv_post[local]:
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s /\ storage_well_formed_on cx ee (FST H) /\
  ~is_word_type typ ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee (Value v) (LocatedValue typ (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  irule (SIMP_RULE (srw_ss()) [loweringPostsTheory.post_value_type_def, expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin typ Convert typ [e]`]
      exprSimStackTheory.vv_post_stack_as_memory)) >>
  simp[] >> metis_tac[dynamic_word_vv_post]
QED

Theorem convert_memory_store_bound[local]:
  ~is_word_type ty ==>
  (vv_store_bound cx ty lt es tv (LocatedValue ty (mk_ptr op LocMemory)) s <=>
   vv_store_bound cx ty lt es tv (StackValue ty op) s)
Proof
  strip_tac >> simp[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.mk_ptr_def]
QED

Theorem widen_copy_same_endpoint[local]:
  emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb /\
  emit_void MCOPY [Var dst;Var src;Lit (n2w k)] sc = ((),sb) /\
  k < dimword(:256) /\
  run_inst_seq (emitted_insts sm sb) t = OK u /\
  run_inst_seq (emitted_insts sm sc) t = OK r /\
  z = r with vs_inst_idx := LENGTH sc.cs_current_insts /\
  lookup_var dst z = SOME dw /\ lookup_var src z = SOME a /\
  q = u with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  q = (mcopy (w2n dw) (w2n a) k z) with
        vs_inst_idx := LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `lookup_var dst r = SOME dw /\ lookup_var src r = SOME a` by
    gvs[venomStateTheory.lookup_var_def] >>
  `run_inst_seq (emitted_insts sc sb) r =
      OK (mcopy (w2n dw) (w2n a) k r)` by
    (drule exprSimBufferStoreTheory.buffer_emit_mcopy_run >>
     disch_then (qspecl_then [`dw`,`a`,`n2w k`,`r`] mp_tac) >>
     simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w]) >>
  `u = mcopy (w2n dw) (w2n a) k r` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sc) t = OK r`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sc sb` mp_tac) >>
     qpat_x_assum `emitted_insts sm sb = _` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  gvs[venomExecSemanticsTheory.mcopy_def,
      venomStateTheory.write_memory_with_expansion_def]
QED

Theorem widen_endpoint_ghosts_from_child[local]:
  expr_post H ctx func cenv cx e es sa sm s0 ee v0 op t /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ lo <= t.vs_alloca_next /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx ee z /\
  z with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
  allocas_from lo z /\ t.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
       (t.vs_alloca_next <= i /\ i < w2n dw+cap)) /\
  (!aid b n. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint (w2n dw) cap b n) /\
  (!name b n. local_region cenv ee.scopes z name b n ==>
       regions_disjoint (w2n dw) cap b n) /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,cap) /\
  k <= cap /\ cap < dimword(:256) /\
  lookup_var dst z = SOME dw /\ lookup_var src z = SOME a /\
  ptr_covers Ga tna dst z cap /\
  q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := idx /\
  Gf = step_prov PG Ga (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] [])
         (mcopy (w2n dw) (w2n a) k z) /\
  tnf = step_taint (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] []) z
         (mcopy (w2n dw) (w2n a) k z) tna /\
  w2n dw+cap <= z.vs_alloca_next /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME rt /\
  val_wf rt v /\ val_footprint rt v <= k /\ val_store_size rt v <= cap /\
  type_memory_bytes cenv ty <= cap /\ type_memory_size rt <= cap /\
  w2n a+k <= t.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n a) m) ==>
  ghost_inv_at D lo d cenv cx ee Gf tnf q /\
  ptr_val_ok cx ty v (Var dst) Gf tnf q /\
  (!e. lowered_value_type cenv e = ty ==> ptr_buf_ok cenv e (Var dst) Gf q) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf /\
  vv_store_bound cx ty ty ee (Value v) (StackValue ty (Var dst)) q
Proof
  strip_tac >>
  `wb_frame cenv es ee sa s0 t` by
    (fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ee t` by fs[loweringPostsTheory.expr_post_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name b n. local_region cenv es.scopes s0 name b n ==>
      local_region cenv ee.scopes z name b n` by
    (rpt strip_tac >>
     `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
       fs[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >>
     `local_region cenv es.scopes z name b n` suffices_by
       metis_tac[tupleMemoryFrameTheory.local_region_scopes_domain] >>
     qpat_x_assum `local_region cenv es.scopes s0 name b n` mp_tac >>
     simp[loweringStateRelDefsTheory.local_region_def] >> rpt strip_tac >>
     `not_fresh_at sa p` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     `lookup_var p t = SOME w` by
       metis_tac[loweringPostsTheory.wb_frame_def] >>
     `lookup_var p z = SOME w` by metis_tac[] >>
     metis_tac[]) >>
  `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id ==>
     b+n <= t.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (b,n)` by
       metis_tac[loweringPostsTheory.wb_frame_def] >>
     `b+n <= s0.vs_alloca_next` by
       (fs[exprLoweringPropsTheory.stmt_state_rel_def,
           venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
        metis_tac[]) >>
     conj_tac >- decide_tac >>
     qpat_x_assum `!aid b n. aid < sm.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[] >> decide_tac) >>
  `!name b n. local_region cenv es.scopes s0 name b n ==>
     b+n <= t.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n` by
    (rpt gen_tac >> strip_tac >>
     `b+n <= s0.vs_alloca_next` by
        metis_tac[abiCallerLocalScratchTheory.abi_caller_local_end,
                  stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     conj_tac >- decide_tac >> metis_tac[]) >>
  `lo <= w2n dw` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
  drule_all convert_widen_copy_endpoint_ghosts >> simp[]
QED

Theorem cast_endpoint_vv_posts[local]:
  expr_post H ctx func cenv cx e es sa sm s0 ee v (Var src) t /\
  expr_store_bound cx (expr_type e) v (Var src) t /\
  ptr_val_ok cx (expr_type e) v (Var src) G tn t /\
  ptr_buf_ok cenv e (Var src) G t /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  storage_well_formed_on cx ee (FST H) /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type rty v /\
  convert_result cx (expr_type e) dst v = INL vout /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  type_memory_size tout <= type_memory_size ltv /\
  (!w. eval_operand (Var src) t = SOME w ==>
       w2n w + type_memory_size ltv <= t.vs_alloca_next) /\
  lookup_var src t = SOME a /\ not_fresh_at sm src /\
  local_ptrs_reserved cenv sm /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z t /\
    FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  alloca_history func u /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post H ctx func cenv cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 ee
    (Value vout) (LocatedValue dst (mk_ptr (Var src) LocMemory)) u /\
  vv_store_bound cx dst dst ee (Value vout)
    (LocatedValue dst (mk_ptr (Var src) LocMemory)) u /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee Gf tnf u /\
  ptr_vv_ok cx dst (Value vout)
    (LocatedValue dst (mk_ptr (Var src) LocMemory)) ee Gf tnf u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `~is_word_type dst` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `u = (t with vs_inst_idx := u.vs_inst_idx) with vs_vars := u.vs_vars` by
    metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\ u.vs_accounts = t.vs_accounts /\
   u.vs_call_ctx = t.vs_call_ctx /\ u.vs_transient = t.vs_transient /\
   u.vs_immutables = t.vs_immutables` by (pop_assum SUBST1_TAC >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (irule assignTuplePtrLoadStepTheory.stmt_state_rel_old_vars_frame_ptr >>
     qexistsl_tac [`t`,`sm`] >> fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx e es sa sb s0 ee v (Var src) u` by
    (irule convert_readonly_expr_post >>
     conj_tac >- simp[] >>
     qexistsl_tac [`a`,`t`,`sm`,`Var src`] >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx (TypeBuiltin dst Convert dst [e])
      es sa sb s0 ee vout (Var src) u` by
    (irule convert_bytestring_expr_post >>
     simp[expr_type_def] >>
     qexistsl_tac [`e`,`rty`,`v`] >>
     simp[]) >>
  conj_tac
  >- (irule convert_memory_vv_post >> simp[]) >>
  `ghost_inv_at D lo d cenv cx ee Gf tnf u` by
    (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`ee`,`t`,`sm`,`tn`] >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` mp_tac >>
     pure_rewrite_tac [bodyPtrDefsTheory.ghost_kept_at_def] >> strip_tac >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by
           (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
         metis_tac[]) >> metis_tac[]) >>
  `val_wf tout vout` by (irule convert_bytestring_wf >> metis_tac[]) >>
  `eval_operand (Var src) u = SOME a /\ eval_operand (Var src) t = SOME a` by
    (simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (simp[convert_memory_store_bound, exprSimMemDefsTheory.vv_store_bound_def,
           read_result_def, return_def] >>
      rpt strip_tac >> gvs[] >>
      drule exprSimPropsTheory.val_store_size_le >> strip_tac >>
      decide_tac) >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.mk_ptr_def,
       read_result_def, return_def] >>
  `op_taint tnf (Var src) = op_taint tn (Var src) /\
   FLOOKUP Gf src = FLOOKUP G src` by metis_tac[] >>
  drule_all convert_bytestring_memory >> strip_tac >>
  fs[bodyPtrDefsTheory.ptr_val_ok_def, valueCopyBytesTheory.is_bytestring_word_type] >>
  simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
      simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  strip_tac >>
  `val_store_size tout vout <= type_memory_size ltv` by
    (drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  `type_memory_size ltv <> 0` by
    (spose_not_then assume_tac >>
     `val_store_size tout vout = 0` by decide_tac >>
     mp_tac (Q.SPECL [`tout`,`vout`] exprSimPropsTheory.val_footprint_le_store_size) >>
     fs[] >> metis_tac[]) >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> strip_tac >>
  qexistsl_tac [`b`,`sz`] >> simp[] >> decide_tac
QED

Theorem convert_bytes_vv_sim_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\ is_bytestring_type dst ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `is_bytestring_type (expr_type e)` by metis_tac[valid_conversion_to_bytestring] >>
  `~is_word_type ann /\ (!n. ann <> FlagT n)` by
    (Cases_on `ann` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `?out. vv = LocatedValue ann (mk_ptr out LocMemory) /\
    (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann
     then compile_bytestring_widen_copy (type_memory_bytes cenv ann) x
       (type_memory_bytes cenv (lowered_value_type cenv e)) sm
     else compile_type_convert x (mk_convert_op (expr_type e) ann) sm) = (out,sb)` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann` >>
     gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
     metis_tac[pairTheory.PAIR]) >> gvs[] >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
       (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann` >>
     gs[oneline as_ptr_val_def, AllCaseEqs()] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels,
       cj 1 externalEntryShapeTheory.compile_bytestring_widen_copy_labels, pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (gvs[body_expr_full_ok_def] >> metis_tac[]) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64` by
    metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok] >>
  qpat_assum `expr_body_pre _ _ _ e _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME rty` >>
  `!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[convert_operand_admissible,
      exprSimStackTheory.eval_expr_force_admissible, eval_expr_type_builtin_value] >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`] (SPEC_ALL expr_sim_full_of_vv_post_buffer_exit)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `eval_expr cx (TypeBuiltin ann Convert ann [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) ann v)
         (\w. INL (Value w)) INR, ee))` by
    (simp[FUN_EQ_THM] >> gen_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
     simp[Once evaluate_def, bind_def, return_def] >>
     Cases_on `eval_expr cx e x'` >> rename1 `_ = (raw,ee)` >>
     Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
     Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
     Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
     simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
     Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val ann` >>
     simp[return_def, raise_def]) >>
  pop_assum SUBST1_TAC >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  rpt conj_tac
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> conj_tac
  >- suspend "continuation" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`] >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type, halt_exit_INR_type]
QED

Theorem convert_bytes_selected_suffix:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  valid_conversion (expr_type e) ann /\
  is_bytestring_type ann /\ is_bytestring_type (expr_type e) /\ ~is_word_type ann /\
  (!n. ann <> FlagT n) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann then
     compile_bytestring_widen_copy (type_memory_bytes cenv ann) x
       (type_memory_bytes cenv (lowered_value_type cenv e)) sm
   else compile_type_convert x (mk_convert_op (expr_type e) ann) sm) = (out,sb) /\
  cs_extends sa sm /\ cs_extends sm sb /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
        H (INL v) mid G1 tn1 t /\
      (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
             eval_operand x t = SOME w ==>
             type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)) ==>
  convert_bytes_vv_suffix (DF,lo,d,ctx,func,explicit,PG) cenv cx ann e st0
    (es,sa,sm,sb,s0,out,G0,tn0) (v,mid,t,G1,tn1)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  fs[exprSimFullBundlePropsTheory.expr_sim_full_post_def,
     exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
        qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
        simp[vyperStorageTraceTheory.storage_trace_frame_bind,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     `storage_well_formed_on cx es (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     irule dynamic_read_storage_well_formed >>
     conj_tac >- (qexists_tac `st0` >> simp[]) >>
     qexistsl_tac [`cenv`,`e`,`env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`v`] >>
     simp[] >>
     qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     strip_tac >> rpt gen_tac >>
     `get_storage cx (es with gas_obs := gas_explicit marks s0.vs_gas_readings) b =
      get_storage cx es b` by
       (Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     simp[]) >>
  drule_at (Pat `bind _ _ _ = _`)
    (SRULE [SF ETA_ss] body_source_read_lowered_layout) >>
  disch_then (qspecl_then [`tops`,`env`,`ctx`,`cenv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `value_has_type rty v` by
    (qpat_x_assum `!gs tv ee v. _` irule >>
     qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs(), NoAsms] >> rpt strip_tac >>
     drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann`
  >- suspend "widen" >>
  suspend "cast"
QED

Resume convert_bytes_selected_suffix[cast]:
  markerLib.RESUME_TAC >> (gvs[] >>
  `~is_word_type (expr_type e)` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[bytestring_memory_header_bound] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> (expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx mid t`
       (ACCEPT_TAC o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `ptr_buf_ok cenv e x G1 t` by simp[] >>
  drule convert_memory_operand_resources >>
  disch_then (qspecl_then [`rty`,`tn1`,`G1`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`expr_type e`,`ann`] memory_convert_shapes) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `i` (qx_choose_then `n` assume_tac)) >>
  `mk_convert_op (expr_type e) ann = ConvBytestringCast n i` by metis_tac[] >>
  `?L. L <= i /\ ((?bs. v = BytesV bs /\ L = LENGTH bs) \/
                         (?str. v = StringV str /\ L = LENGTH str))` by
    (mp_tac (Q.INST [`ty` |-> `expr_type e`, `tv` |-> `rty`, `tenv` |-> `get_tenv cx`]
       bytestring_typed_value_view) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[] >> fs[] >> metis_tac[]) >>
  `mload (w2n a) t = n2w L /\
   (!j. w2n a <= j /\ j < w2n a+32 ==> j NOTIN tn1.t_mem)` by
    (irule robust_bytestring_header >>
     qexistsl [`rty`,`expr_type e`,`get_tenv cx`,`v`] >> simp[] >> metis_tac[]) >>
  `w2n a+32 <= t.vs_alloca_next` by
    (qpat_x_assum `!w. eval_operand (Var src) t = _ ==> _` (qspec_then `a` mp_tac) >>
     simp[venomStateTheory.eval_operand_def] >> decide_tac) >>
  `not_fresh_at sm src` by (qpat_assum `lower_value _ _ _ e sa = _` mp_tac >>
     disch_then (mp_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac compile_lower_value_var) >> simp[]) >>
  `type_alloc_ok cenv (expr_type e) /\ type_alloc_ok cenv ann` by
    (fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     metis_tac[alloc_limits_expr_type_alloc_ok, expr_type_def]) >>
  `i < dimword(:256) /\ n < dimword(:256)` by
    metis_tac[bytestring_alloc_capacity_bound] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def, NoAsms] >>
     (impl_tac >- simp[]) >> rpt strip_tac >> simp[]) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `compile_type_convert (Var src) (ConvBytestringCast n i) sm = (out,sb)` by metis_tac[] >>
  drule_at (Pat `compile_type_convert _ (ConvBytestringCast _ _) _ = _`)
    convert_cast_origin_path_observed >>
  disch_then (qspecl_then [`tn1`,`t`,`lo`,`func`,`explicit`,`ctx`,
    `type_memory_size tv`,`a`,`PG`,`L`,`G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "cast_dispatch")
QED

Resume convert_bytes_selected_suffix[cast_dispatch]:
  markerLib.RESUME_TAC >> (Cases_on `L <= n`
  >- suspend "cast_success" >>
  `?exc. convert_result cx (expr_type e) ann v = INR exc /\
          (?msg. exc = Error (RuntimeError msg))` by
    (qpat_assum `(expr_type e = _ \/ _) /\ _` mp_tac >>
     rpt strip_tac >> gvs[exprSimConvertBytesTheory.convert_result_bytes_to_bytestring,
       exprSimConvertBytesTheory.convert_result_string_to_bytestring]) >>
  `n < L` by decide_tac >>
  qpat_x_assum `n < L ==> _` drule >> strip_tac >>
  simp[convert_bytes_vv_suffix_def] >>
  qexistsl_tac [`H`,`th`,`Abort Revert_abort t'`] >> metis_tac[])
QED

Resume convert_bytes_selected_suffix[cast_success]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `L <= n ==> _` drule >> strip_tac >>
  `?vout. convert_result cx (expr_type e) ann v = INL vout` by
    (qpat_assum `(expr_type e = _ \/ _) /\ _` mp_tac >>
     rpt strip_tac >> simp
       [exprSimConvertBytesTheory.convert_result_bytes_to_bytestring,
        exprSimConvertBytesTheory.convert_result_string_to_bytestring]) >>
  rewrite_tac[convert_bytes_vv_suffix_def] >>
  qexistsl_tac [`H`,`th`,`OK t'`,`INL (Value vout)`] >>
  conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
  disj1_tac >> qexistsl_tac [`t'`,`raw`] >>
  conj_tac >- REFL_TAC >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `t' = raw with vs_inst_idx := _` kall_tac >>
  qx_gen_tac `H'` >> strip_tac >>
  simp[convert_bytes_vv_post_def, expr_vv_sim_full_post_def,
       exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >> (
    `?tout. evaluate_type (get_tenv cx) ann = SOME tout /\
       type_memory_bytes cenv ann = type_memory_size tout` by
      (`IS_SOME (evaluate_type (get_tenv cx) ann)` by
         metis_tac[expr_body_pre_type_evaluates, expr_type_def] >>
       fs[optionTheory.IS_SOME_EXISTS] >>
       metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok, expr_type_def]) >>
    `alloca_inv t` by
      fs[loweringPostsTheory.expr_post_def, stmt_state_rel_def] >>
    `alloca_history func t'` by
      (irule body_full_path_alloca_history >> metis_tac[]) >>
    `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
      (conj_tac >- metis_tac[compile_expr_grows] >>
       metis_tac[convert_cast_grows]) >>
    `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
    `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
      metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
    `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
      metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
    `expr_post H' ctx func cenv cx e es sa sm s0 mid v (Var src) t /\
     ghost_inv_at (DF H') lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
    `type_memory_size tout <= type_memory_size tv` by decide_tac >>
    `!w. eval_operand (Var src) t = SOME w ==>
         w2n w + type_memory_size tv <= t.vs_alloca_next` by metis_tac[arithmeticTheory.ADD_COMM] >>
    `post_value_type cenv e = expr_type e` by simp[] >>
    `storage_well_formed_on cx mid (FST H')` by metis_tac[] >>
    drule_all cast_endpoint_vv_posts >> strip_tac >>
    `eval_operand (Var src) t' = eval_operand (Var src) t /\
     FLOOKUP H src = FLOOKUP G1 src` by
      (simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
    `ptr_buf_ok cenv (TypeBuiltin ann Convert ann [e]) (Var src) H t'` by
      (qpat_x_assum `ptr_buf_ok cenv e (Var src) G1 t` mp_tac >>
       simp[bodyPtrDefsTheory.ptr_buf_ok_def, lowered_value_type_def, expr_type_def] >>
       rpt strip_tac >>
       qpat_x_assum `!w. eval_operand (Var src) t = SOME w ==> ?b sz. _`
         (qspec_then `w` mp_tac) >> simp[] >>
       strip_tac >> qexistsl_tac [`b`,`sz`] >> simp[] >> decide_tac) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
      (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ t'`
         (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
       first_assum (ACCEPT_TAC o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
    gvs[lowered_value_type_def, expr_type_def, contextTheory.vv_location_def,
        contextTheory.vv_operand_def, contextTheory.mk_ptr_def]) >> simp[])
QED

Resume convert_bytes_selected_suffix[widen]:
  markerLib.RESUME_TAC >> gvs[] >>
  `~is_word_type (expr_type e)` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[bytestring_memory_header_bound] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> (expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `ptr_buf_ok cenv e x G1 t` by simp[] >>
  drule convert_memory_operand_resources >>
  disch_then (qspecl_then [`rty`,`tn1`,`G1`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >> gvs[] >>
  `not_fresh_at sm src` by (qpat_assum `lower_value _ _ _ e sa = _` mp_tac >>
     disch_then (mp_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac compile_lower_value_var) >> simp[]) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var, compile_expr_grows] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def, NoAsms] >>
     (impl_tac >- simp[]) >> rpt strip_tac >> simp[]) >>
  `type_memory_bytes cenv ann < dimword(:256)` by
    (`?tout. evaluate_type (get_tenv cx) ann = SOME tout` by
       metis_tac[expr_body_pre_type_evaluates, expr_type_def, optionTheory.IS_SOME_EXISTS] >>
     `type_memory_bytes cenv ann = type_memory_size tout /\
      type_memory_size tout < 18446744073709551616` by
       (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _` mp_tac >>
        qpat_assum `evaluate_type (get_tenv cx) ann = SOME tout` mp_tac >>
        qpat_assum `~is_word_type ann` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        rpt strip_tac >>
        drule exprSimHypsTheory.expr_body_pre_copy_ok >>
        disch_then (qspec_then `tout` mp_tac) >> simp[expr_type_def]) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `0 < type_memory_size tv /\ type_memory_size tv <= type_memory_bytes cenv ann` by decide_tac >>
  `w2n a + type_memory_size tv <= t.vs_alloca_next` by
    (qpat_x_assum `!w. eval_operand (Var src) t = _ ==> _` (qspec_then `a` mp_tac) >>
     simp[venomStateTheory.eval_operand_def] >> decide_tac) >>
  drule_all (INST_TYPE
    (map (fn ty => ty |-> ``:256``)
      (type_vars_in_term (concl convert_widen_copy_origin_ptr_path)))
    convert_widen_copy_origin_ptr_path) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `?tout. evaluate_type (get_tenv cx) ann = SOME tout` by
    metis_tac[expr_body_pre_type_evaluates, expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  `val_footprint rty v <= type_memory_size tv` by
    metis_tac[valueCopyBytesTheory.bytestring_val_footprint_le] >>
  `?vout. convert_result cx (expr_type e) ann v = INL vout` by
    (irule convert_bytestring_lowered_widen_success >> metis_tac[]) >>
  `val_wf tout vout` by (irule convert_bytestring_wf >> metis_tac[]) >>
  drule_all convert_bytestring_memory >>
  disch_then (qspecl_then [`w2n a`,`t.vs_memory`] strip_assume_tac) >>
  `val_footprint tout vout <= type_memory_size tv` by simp[] >>
  rewrite_tac[convert_bytes_vv_suffix_def] >>
  qexistsl_tac [`Gf`,`tnf`,`OK q`,`INL (Value vout)`] >>
  conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
  disj1_tac >> qexistsl_tac [`q`,`u`] >>
  conj_tac >- REFL_TAC >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `q = u with vs_inst_idx := _` (fn th => mk_asm "q_raw" th) >>
  qx_gen_tac `H` >> strip_tac >>
  simp[convert_bytes_vv_post_def, expr_vv_sim_full_post_def,
       exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid v (Var src) t /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H)` by
    (fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `val_in_memory tout vout (w2n a) t.vs_memory` by
    (simp[] >> first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) mid sm sb t
     mid vout (Var dst) q` by
    (irule convert_widen_copy_endpoint_post >>
     asm "q_raw" (fn th => simp[expr_type_def,th]) >>
     qexistsl_tac [`a`,`type_memory_bytes cenv ann`,`type_memory_size tv`,`Var src`] >>
     simp[venomStateTheory.eval_operand_def]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (`valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
        qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
        simp[vyperStorageTraceTheory.storage_trace_frame_bind,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     metis_tac[]) >>
  `expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
     mid vout (Var dst) q` by
    (qpat_assum `expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac convert_expr_post_compose) >>
     disch_then irule >>
     simp[loweringPostsTheory.expr_has_effect_thm] >>
     `ci_mono sa sm` by
       (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`] ci_mono_lower_value_compile_expr) >> simp[]) >>
     fs[exprLoweringPropsTheory.ci_mono_def, loweringPostsTheory.expr_post_def,
        loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def]) >>
  `lookup_var src z = SOME a` by metis_tac[] >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (qpat_assum `compile_alloc_buffer _ sm = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_return_def, NoAsms] >>
     pairarg_tac >> simp[NoAsms] >> strip_tac >> gvs[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
     irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  `q = (mcopy (w2n dw) (w2n a) (type_memory_size tv) z) with
       vs_inst_idx := LENGTH sb.cs_current_insts` by
    (`type_memory_size tv < dimword(:256)` by decide_tac >>
     asm_x "q_raw" assume_tac >> drule_all widen_copy_same_endpoint >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size tout` by
    metis_tac[expr_type_def, exprSimHypsTheory.expr_body_pre_copy_ok] >>
  `val_store_size tout vout <= type_memory_bytes cenv ann` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
       val_in_memory tout vout (w2n a) m` by
    (rpt strip_tac >> drule_all convert_bytestring_memory >>
     disch_then (qspecl_then [`w2n a`,`m`] mp_tac) >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[compile_expr_grows, ci_mono_lower_value_compile_expr,
              exprLoweringPropsTheory.ci_mono_def] >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (first_assum match_mp_tac >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid z`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     qpat_assum `q = (mcopy _ _ _ z) with vs_inst_idx := _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def,
          venomExecSemanticsTheory.mcopy_def, venomStateTheory.write_memory_with_expansion_def] >>
     metis_tac[]) >>
  `type_memory_size tout <= type_memory_bytes cenv ann` by simp[] >>
  qpat_assum `expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac widen_endpoint_ghosts_from_child) >>
  disch_then (fn th => qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `q = (mcopy _ _ _ z) with vs_inst_idx := _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `Gf = step_prov _ _ _ _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `tnf = step_taint _ z _ tna`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type (get_tenv cx) ann = SOME tout`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `val_wf tout vout`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`tn0`,`type_memory_bytes cenv ann`,`G0`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qpat_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _` mp_tac >> simp[])
    >> qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _` mp_tac >> simp[])) >>
  strip_tac >>
  `ptr_buf_ok cenv (TypeBuiltin ann Convert ann [e]) (Var dst) Gf
     (mcopy (w2n dw) (w2n a) (type_memory_size tv) z)` by
    (qpat_assum `!e. lowered_value_type cenv e = ann ==> _`
       (qspec_then `TypeBuiltin ann Convert ann [e]` mp_tac) >>
     qpat_assum `q = (mcopy _ _ _ z) with vs_inst_idx := _` SUBST1_TAC >>
     simp[lowered_value_type_def, expr_type_def,
          bodyPtrIfExpAllocSourceTheory.ptr_buf_ok_inst_idx, NoAsms]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[lowered_value_type_def, expr_type_def, contextTheory.vv_location_def,
       bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.vv_operand_def,
       contextTheory.mk_ptr_def, convert_memory_vv_post, convert_memory_store_bound] >>
  qpat_assum `vv_store_bound _ _ _ _ _ _ q` mp_tac >>
  qpat_assum `ptr_val_ok cx ann vout _ _ _ q` mp_tac >>
  qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
  qpat_assum `t.vs_alloca_next <= q.vs_alloca_next` mp_tac >>
  simp[lowered_value_type_def, expr_type_def, vyperStateTheory.read_result_def] >>
  gvs[vyperStateTheory.return_def, bodyPtrDefsTheory.ptr_val_ok_def,
      exprSimMemDefsTheory.vv_store_bound_def, contextTheory.mk_ptr_def]
QED

Finalise convert_bytes_selected_suffix

Resume convert_bytes_vv_sim_full[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `childQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t /\
    ~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `childQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~is_word_type (expr_type e)` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t` by
       (res_tac >> fs[loweringPostsTheory.expr_post_def]) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx mid t`
        (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
      H (INL v) mid G1 tn1 t /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand x t = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)` by
    (rpt strip_tac >> res_tac >>
     fs[exprSimFullBundlePropsTheory.expr_sim_full_post_def,
         exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
     metis_tac[]) >>
  `convert_bytes_vv_suffix (DF,lo,d,ctx,func,gas_explicit_sites ctx shadow_ctx,PG)
    cenv cx ann e st0 (es,sa,sm,sb,s0,out,G0,tn0) (v,mid,t,G1,tn1)` by
    (irule convert_bytes_selected_suffix >>
     simp[loweringPostsTheory.post_value_type_def] >> rpt conj_tac >> metis_tac[]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum `convert_bytes_vv_suffix _ _ _ _ _ _ _ _` mp_tac >>
  simp[convert_bytes_vv_suffix_def] >> strip_tac >> gvs[]
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G2`,`mid`,`sum_CASE (convert_result cx (expr_type e) ann v)
        (\w. INL (Value w)) INR`,`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`tn2`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> convert_bytes_vv_post _ _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
          [convert_bytes_vv_post_def, expr_vv_sim_full_post_def,
           exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def,
           contextTheory.mk_ptr_def, contextTheory.vv_location_def])) >>
      gvs[loweringPostsTheory.post_value_type_def, expr_type_def,
          contextTheory.mk_ptr_def, contextTheory.vv_location_def]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G2`,`mid`,`Abort Revert_abort u`,`INR (Error (RuntimeError msg))`,`tn2`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def, halt_exit_not_halt]
QED

Finalise convert_bytes_vv_sim_full
