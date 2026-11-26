(* Materialized result of the checked calldata slice, at fixed endpoints. *)
Theory bodyCalldataSliceValuePostMods
Ancestors
  bodyFullPostsMods exprSimCalldataSlice exprSimHash exprSimProps exprSimWordArgs
  bodyPtrAttributeFields bodyPtrDefs reasonCodeResourcesPtr exprSimMemDefs
  wordArgsPtr bodyFullHashKeccakFixed stateRelProj localPtrsProps
  materializeSeparation compileEnv context venomState venomInst
  valueEncoding valueEncodingDefs valueTypingMemoryProps loweringPosts
  loweringStateRelDefs exprLoweringProps exprLowering vyperState vyperAST list words
  vfmConstants vyperValue vyperInterpreter finite_map vyperExprEffects arithmetic
Libs monadsyntax

Triviality calldata_slice_encoding:
  n <= m /\ a+n <= LENGTH cx.txn.calldata /\ m < dimword (:256) /\
  N = type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) /\ N < dimword (:256) /\
  v = BytesV (TAKE n (DROP a cx.txn.calldata)) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) z.vs_memory ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic m))) =
    SOME (BaseTV (BytesT (Dynamic m))) /\
  type_memory_size (BaseTV (BytesT (Dynamic m))) = N /\
  val_wf (BaseTV (BytesT (Dynamic m))) v /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) v (w2n w) z.vs_memory /\
  val_footprint (BaseTV (BytesT (Dynamic m))) v = 32+n /\
  val_store_size (BaseTV (BytesT (Dynamic m))) v <= N /\ 32+n <= N
Proof
  strip_tac >>
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by simp[LENGTH_TAKE_EQ] >>
  `word_size n <= word_size m` by (irule exprSimPropsTheory.word_size_monotone >> simp[]) >>
  `m <= 32 * word_size m` by simp[word_size_capacity] >>
  gvs[type_memory_bytes_def, GSYM word_size_def, evaluate_type_def, type_slot_size_def,
     type_memory_size_def, val_wf_def, val_in_memory_def, val_footprint_def,
     val_store_size_def, GSYM dimword_def] >> decide_tac
QED

Triviality calldata_slice_post_linked:
  vv_post H ctx func cenv cx e es sa sb s0 mid (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z /\
  immutable_frame_mods func cenv cx mid z ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 mid (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,
       vv_place_ptr_def,mk_ptr_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem calldata_slice_value_post_mods:
  let ann = BaseT (BytesT (Dynamic m));
      E = Builtin ann (CalldataSlice n) [e];
      v = BytesV (TAKE n (DROP a cx.txn.calldata));
      vv = LocatedValue ann (mk_ptr (Var p) LocMemory)
  in
  n <= m /\ m < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  N = type_memory_bytes cenv ann /\ N < dimword (:256) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL (IntV (&a)),mid) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_slice_calldata x (Lit (n2w n)) N sm = (Var p,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid (IntV (&a)) x s /\
  (stmt_state_rel H ctx func cenv cx mid s ==> stmt_state_rel H ctx func cenv cx mid z) /\
  lookup_var p z = SOME w /\ ptr_covers HG tm p z N /\
  FLOOKUP z.vs_allocas (sm.cs_next_id+7) = SOME (w2n w,N) /\
  w2n w+N <= z.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) z.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sm.cs_next_id ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory) /\
  locals_kept cenv mid mid s z /\ pure_frame cenv func mid sm s z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 s HG tm /\
  immutable_frame_mods func cenv cx mid z /\ ghost_inv_at_mods D lo d cenv cx mid HG tm z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= z.vs_alloca_next ==>
  vv_post_mods H ctx func cenv cx E es sa sb s0 mid (Value v) vv z /\
  vv_store_bound cx (post_value_type cenv E) (lowered_value_type cenv E) mid (Value v) vv z /\
  ptr_vv_ok cx (post_value_type cenv E) (Value v) vv mid HG tm z /\
  ptr_buf_ok cenv E (Var p) HG z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods D lo d cenv cx mid HG tm z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm /\
  ~is_word_type ann /\ read_result cx (Value v) mid = (INL v,mid) /\
  ptr_mem_ok cx ann v (Var p) HG tm z
Proof
  simp[LET_THM] >> rpt (disch_then (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `v = BytesV (TAKE n (DROP a cx.txn.calldata))` >>
  qabbrev_tac `ann = BaseT (BytesT (Dynamic m))` >>
  qabbrev_tac `E = Builtin ann (CalldataSlice n) [e]` >>
  qabbrev_tac `vv = LocatedValue ann (mk_ptr (Var p) LocMemory)` >>
  suspend "value"
QED

Resume calldata_slice_value_post_mods[value]:
  `N = type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) /\
   v = BytesV (TAKE n (DROP a cx.txn.calldata))` by simp[Abbr `ann`,Abbr `v`] >>
  drule_all_then strip_assume_tac calldata_slice_encoding >>
  `~is_word_type ann /\ is_bytestring_type ann` by
    simp[Abbr `ann`,is_word_type_def,is_bytestring_type_def] >>
  `post_value_type cenv E = ann /\ lowered_value_type cenv E = ann /\ expr_type E = ann` by
    simp[Abbr `E`,post_value_type_def,lowered_value_type_def,expr_type_def] >>
  `ptr_mem_ok cx ann v (Var p) HG tm z` by
    (irule clean_memory_representation_ptr >>
     qexistsl_tac [`w`,`N`,`BaseTV (BytesT (Dynamic m))`] >>
     simp[Abbr `ann`]) >>
  `ptr_vv_ok cx ann (Value v) vv mid HG tm z` by
    (simp[NoAsms,Abbr `vv`] >> irule ptr_vv_ok_memory >>
     simp[NoAsms,mk_ptr_def,read_result_def,return_def] >>
     conj_tac >- (qpat_assum `ptr_covers HG tm p z N` mp_tac >> simp[NoAsms,ptr_covers_def]) >>
     first_assum ACCEPT_TAC) >>
  `vv_store_bound cx ann ann mid (Value v) vv z` by
    (simp[NoAsms,Abbr `vv`,Abbr `ann`,vv_store_bound_def,mk_ptr_def,read_result_def,
       return_def,eval_operand_def] >>
     qpat_assum `lookup_var p z = SOME w` (pure_rewrite_tac o single) >>
     qpat_assum `evaluate_type _ (BaseT (BytesT (Dynamic m))) = _`
       (simp_tac (srw_ss()) o cons NoAsms o single) >>
     qpat_assum `val_store_size _ v <= N` mp_tac >>
     qpat_assum `type_memory_size _ = N` (pure_rewrite_tac o single) >>
     qpat_assum `N+w2n w <= z.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `ptr_buf_ok cenv E (Var p) HG z` by
    (qpat_assum `ptr_covers HG tm p z N`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_buf_ok_def,eval_operand_def] >>
     qexistsl_tac [`b`,`sz`] >> simp[]) >>
  suspend "suffix"
QED

Resume calldata_slice_value_post_mods[suffix]:
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H)` by
    (qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac slice_calldata_shape >>
  qabbrev_tac `q = STRING #"%" (toString (sm.cs_next_var+6))` >>
  qabbrev_tac `ai = mk_inst (sm.cs_next_id+7) ALLOCA [Lit (n2w N)] [q]` >>
  `MEM ai (fn_insts func)` by
    (irule materializeSeparationTheory.fn_has_code_current_instruction >>
     qexistsl_tac [`sm`,`sb`] >> simp[Abbr `ai`,Abbr `q`]) >>
  `ai.inst_outputs = [q] /\ ai.inst_id = sm.cs_next_id+7` by
    simp[NoAsms,Abbr `ai`,mk_inst_def] >>
  `FLOOKUP z.vs_allocas ai.inst_id = SOME (w2n w,N)` by
    (qpat_assum `ai.inst_id = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `not_local_ptr cenv mid.scopes q` by
    (simp[NoAsms,Abbr `q`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sm` >> simp[]) >>
  qpat_assum `stmt_state_rel H _ _ _ _ mid z`
    (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `!nm b len. local_region cenv mid.scopes z nm b len ==>
     regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC local_ptrs_rel_alloca_disjoint) >>
  `wb_frame cenv mid mid sm s z` by
    (pure_rewrite_tac[wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _` (drule_then SUBST1_TAC) >>
         first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!aid b len. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
     first_assum ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx E mid sm sb s mid (Value v) vv z` by
    (simp[NoAsms,Abbr `vv`] >>
     qpat_assum `expr_type E = ann` (pure_rewrite_tac o single o SYM) >>
     irule vv_post_allocated_memory_intro >>
     simp[NoAsms,eval_operand_def,mk_ptr_def,GSYM regions_disjoint_def] >>
     qpat_assum `expr_type E = ann` (pure_rewrite_tac o single) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (disch_tac >> first_assum ACCEPT_TAC) ORELSE
       (qexistsl_tac [`sm.cs_next_id+7`,`w2n w`,`N`,
           `BaseTV (BytesT (Dynamic m))`,`w`] >>
        qpat_assum `sb.cs_next_id = _` (fn th => simp[NoAsms,Abbr `ann`,th]) >>
        rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
          (qpat_assum `val_footprint _ v = 32+n` (pure_rewrite_tac o single) >>
           qpat_assum `32+n <= N` mp_tac >> decide_tac))))) >>
  suspend "prefix"
QED

Resume calldata_slice_value_post_mods[prefix]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule_then strip_assume_tac (cj 2 compile_expr_grows) >> simp[]) >>
  `(~expr_has_effect E ==> pure_frame cenv func es sa s0 s)` by
    (simp[Abbr `E`,expr_has_effect_thm] >> strip_tac >>
     drule_then irule expr_post_pure_frame >> simp[]) >>
  drule_then assume_tac expr_post_frame >>
  `vv_post H ctx func cenv cx E es sa sb s0 mid (Value v) vv z` by
    (qpat_assum `vv_post _ _ _ _ _ E mid sm _ s _ _ _ _`
      (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) irule vv_post_prefix_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `vv_post_mods H ctx func cenv cx E es sa sb s0 mid (Value v) vv z` by
    (simp[NoAsms,Abbr `vv`] >> irule calldata_slice_post_linked >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
    (qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 s HG tm`
       (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) irule
         (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans)) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qexists_tac `mid` >> first_assum ACCEPT_TAC) ORELSE
       (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC))) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid z`
      (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  qpat_assum `expr_type E = ann` (pure_rewrite_tac o single) >>
  qpat_assum `lowered_value_type cenv E = ann` (pure_rewrite_tac o single) >>
  simp[NoAsms,read_result_def,return_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise calldata_slice_value_post_mods
