(* Successful post for code Slice at the reached copy endpoint. *)
Theory bodySliceCodeSuffixPostMods
Ancestors
  bodyCalldataSliceLinkedFrameMods bodyFullPostsMods bodyPtrDefs
  exprSimHash exprSimSliceExtcodeEntry exprSimProps exprSimMemDefs
  bodyPtrAttributeFields reasonCodeResourcesPtr rawCallBufferPtr
  bodyPtrBytestringBuiltinsBuffer fragExec emitHelperProps
  wordArgsPtr stateRelProj exprBopSimProps localPtrsProps typeLayoutProps
  vfmConstants compileEnv loweringPosts exprLoweringProps exprLowering
  loweringStateRelDefs venomState venomInst vyperState vyperValue vyperAST
  valueEncoding valueEncodingDefs context words list arithmetic

Theorem slice_code_suffix_post_mods:
  let ann = BaseT (BytesT (Dynamic n));
      e = Builtin ann (Slice n) args;
      v = BytesV (TAKE k (DROP i code));
      vv = LocatedValue ann (mk_ptr (Var p) LocMemory)
  in
  k <= n /\ i+k <= LENGTH code /\ 32+n <= N /\ N < dimword (:256) /\
  N = type_memory_bytes cenv ann /\
  compile_slice_out_buf N sd = ((Var p,data),se) /\
  emit_void copy_op copy_ops se = ((),sf) /\
  emit_void MSTORE [Var p;cnt] sf = ((),sb) /\
  fn_has_code sd sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sd /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
  zb = s with <|vs_vars := zb.vs_vars; vs_inst_idx := LENGTH sd.cs_current_insts|> /\
  tb.t_mem = tn.t_mem /\ tb.t_stor = tn.t_stor /\
  tb.t_trans = tn.t_trans /\ tb.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==>
      lookup_var x zb = lookup_var x s /\ FLOOKUP Gb x = FLOOKUP G x /\
      op_taint tb (Var x) = op_taint tn (Var x)) /\
  (!(H:(bool # bytes32 # type_value) list # num list).
     stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es zb) /\
  (!(H:(bool # bytes32 # type_value) list # num list).
     stmt_state_rel H ctx func cenv cx es zb ==> stmt_state_rel H ctx func cenv cx es t) /\
  lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
  FLOOKUP t.vs_allocas sd.cs_next_id = SOME (w2n w,N) /\ w2n w+N <= t.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) t.vs_memory /\
  (!j. w2n w <= j /\ j < w2n w+32+k ==> j NOTIN tm.t_mem) /\
  (!x. not_fresh_at sd x ==>
      lookup_var x t = lookup_var x zb /\ FLOOKUP HG x = FLOOKUP Gb x /\
      op_taint tm (Var x) = op_taint tb (Var x)) /\
  (!aid entry. FLOOKUP zb.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b len. FLOOKUP zb.vs_allocas aid = SOME (b,len) /\ aid < sd.cs_next_id ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len zb.vs_memory) /\
  (!name b len. local_region cenv es.scopes zb name b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len zb.vs_memory /\
    (!j. b <= j /\ j < b+len /\ j IN tm.t_mem ==> j IN tb.t_mem)) /\
  (!j. j < lo /\ j IN tm.t_mem ==> j IN tb.t_mem) /\
  tm.t_stor = tb.t_stor /\ tm.t_trans = tb.t_trans /\ tm.t_imm = tb.t_imm /\
  ghost_kept_at lo cenv es sd Gb tb zb HG tm /\
  locals_kept cenv es es zb t /\ pure_frame cenv func es sd zb t /\
  t.vs_accounts = zb.vs_accounts /\ t.vs_transient = zb.vs_transient /\
  t.vs_call_ctx = zb.vs_call_ctx /\ t.vs_immutables = zb.vs_immutables /\
  t.vs_data_section = zb.vs_data_section /\ LENGTH zb.vs_memory <= LENGTH t.vs_memory /\
  zb.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
     FLOOKUP zb.vs_allocas aid = SOME (b,len) \/ zb.vs_alloca_next <= b) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sb s es (Value v) vv t /\
    vv_store_bound cx ann ann es (Value v) vv t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t /\
    ptr_vv_ok cx ann (Value v) vv es HG tm t /\ ptr_buf_ok cenv e (Var p) HG t /\
    ghost_kept_at lo cenv es sa G tn s HG tm
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qabbrev_tac `ann = BaseT (BytesT (Dynamic n))` >>
  qabbrev_tac `v = BytesV (TAKE k (DROP i code))` >>
  qabbrev_tac `e = Builtin ann (Slice n) args` >>
  qabbrev_tac `vv = LocatedValue ann (mk_ptr (Var p) LocMemory)` >>
  suspend "scalar_frame"
QED

Resume slice_code_suffix_post_mods[scalar_frame]:
  `zb.vs_memory = s.vs_memory /\ zb.vs_allocas = s.vs_allocas /\
   zb.vs_alloca_next = s.vs_alloca_next /\ zb.vs_accounts = s.vs_accounts /\
   zb.vs_transient = s.vs_transient /\ zb.vs_call_ctx = s.vs_call_ctx /\
   zb.vs_immutables = s.vs_immutables /\ zb.vs_data_section = s.vs_data_section` by
    (qpat_assum `zb = s with <|vs_vars := _; vs_inst_idx := _|>`
       (pure_once_rewrite_tac o single) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (gen_tac >> strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      local_region cenv es.scopes zb name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[]) >>
  `pure_frame cenv func es sa s zb` by simp[pure_frame_def] >>
  `pure_frame cenv func es sa s t` by
    (irule pure_frame_trans >> simp[] >> qexistsl_tac [`es`,`sd`,`zb`] >> simp[] >>
     rpt strip_tac >> simp[]) >>
  `locals_kept cenv es es s zb` by simp[locals_kept_mem] >>
  `locals_kept cenv es es s t` by
    (irule locals_kept_trans >> qexistsl_tac [`es`,`sa`,`zb`] >> simp[] >>
     rpt strip_tac >> simp[]) >>
  `wb_frame cenv es es sa s t` by
    (simp_tac bool_ss [wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (drule_then strip_assume_tac) >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     conj_tac >-
       (rpt strip_tac >> qpat_assum `!aid b len. FLOOKUP zb.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
        simp[] >> disch_then irule >> qexists_tac `aid` >> simp[] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  suspend "linked_frames"
QED

Resume slice_code_suffix_post_mods[linked_frames]:
  `stmt_state_rel H ctx func cenv cx es zb` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` (drule_then ACCEPT_TAC)) >>
  `stmt_state_rel H ctx func cenv cx es t` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ zb ==> _` (drule_then ACCEPT_TAC)) >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx es HG tm t /\
   immutable_frame_mods func cenv cx es t` by
    (irule calldata_slice_linked_frame_mods >> qexistsl_tac [`G`,`s`,`sa`,`tn`] >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> _`
           (drule_then assume_tac) >>
         qpat_assum `!name b len. local_region cenv es.scopes zb name b len ==> _`
           (drule_then strip_assume_tac) >>
         conj_tac >- (qpat_assum `zb.vs_memory = s.vs_memory`
           (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
         qpat_assum `tb.t_mem = tn.t_mem` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qpat_assum `zb.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single o SYM) >>
         qpat_assum `zb.vs_alloca_next = s.vs_alloca_next` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `tb.t_mem = tn.t_mem` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `zb.vs_memory = s.vs_memory` (pure_rewrite_tac o single o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G tn s Gb tb` by
    (simp_tac bool_ss [ghost_kept_at_def] >> simp[]) >>
  `wb_frame cenv es es sa s zb` by
    (simp[wb_frame_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s HG tm` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >> simp[] >>
     conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`Gb`,`es`,`es`,`zb`,`sd`,`tb`] >> simp[]) >>
  suspend "representation"
QED

Resume slice_code_suffix_post_mods[representation]:
  `LENGTH (TAKE k (DROP i code)) = k` by simp[LENGTH_TAKE_EQ] >>
  `n < dimword (:256)` by decide_tac >>
  `word_size k <= word_size n` by simp[exprSimPropsTheory.word_size_monotone] >>
  `n <= 32 * word_size n` by simp[valueTypingMemoryPropsTheory.word_size_capacity] >>
  `evaluate_type (get_tenv cx) ann = SOME (BaseTV (BytesT (Dynamic n)))` by
    (qpat_assum `N < dimword (:256)` mp_tac >>
     qpat_assum `N = type_memory_bytes cenv ann` (pure_rewrite_tac o single) >>
     simp[NoAsms,Abbr `ann`,evaluate_type_def,type_slot_size_def,GSYM dimword_def,
          type_memory_bytes_def,GSYM word_size_def] >> decide_tac) >>
  `type_memory_size (BaseTV (BytesT (Dynamic n))) = N` by
    (qpat_assum `evaluate_type _ ann = _` mp_tac >> simp[Abbr `ann`] >>
     drule_then (qspec_then `cenv` mp_tac) type_memory_bytes_base_evaluated >>
     disch_then (ACCEPT_TAC o SYM)) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) v /\
   val_footprint (BaseTV (BytesT (Dynamic n))) v = 32+k /\
   val_store_size (BaseTV (BytesT (Dynamic n))) v <= N` by
    (qpat_assum `type_memory_size (BaseTV (BytesT (Dynamic n))) = N` (SUBST1_TAC o SYM) >>
     simp[Abbr `v`,val_wf_def,val_footprint_def,val_store_size_def,type_memory_size_def,
          GSYM word_size_def,Abbr `ann`,type_memory_bytes_def] >> decide_tac) >>
  `ptr_mem_ok cx ann v (Var p) HG tm t` by
    (irule clean_memory_representation_ptr >> qexistsl_tac [`w`,`N`,`BaseTV (BytesT (Dynamic n))`] >>
     simp[]) >>
  `ptr_vv_ok cx ann (Value v) vv es HG tm t` by
    (simp[NoAsms,Abbr `vv`] >> irule ptr_vv_ok_memory >>
     simp[NoAsms,mk_ptr_def,vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
     qpat_assum `ptr_covers HG tm p t N` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[]) >>
  `ptr_buf_ok cenv e (Var p) HG t` by
    (irule ptr_buf_ok_from_covers >> qexistsl_tac [`N`,`tm`] >>
     simp[Abbr `e`,lowered_value_type_def,expr_type_def]) >>
  `vv_store_bound cx ann ann es (Value v) vv t` by
    (simp[vv_store_bound_def,Abbr `vv`,mk_ptr_def,vyperStateTheory.read_result_def,
          vyperStateTheory.return_def,eval_operand_def] >> decide_tac) >>
  suspend "allocated_post"
QED

Resume slice_code_suffix_post_mods[allocated_post]:
  `cs_extends sd se` by
    (drule_then strip_assume_tac compile_slice_out_buf_compiler_parts >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends se sf /\ cs_extends sf sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `fn_has_code sd se func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  `ci_mono sd se` by (qspecl_then [`N`,`sd`] mp_tac ci_mono_compile_slice_out_buf >> simp[]) >>
  `sd.cs_next_id < sb.cs_next_id` by
    (qpat_assum `emit_void copy_op _ se = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     fs[ci_mono_def] >> decide_tac) >>
  qabbrev_tac `q = STRING #"%" (toString sd.cs_next_var)` >>
  qabbrev_tac `ai = mk_inst sd.cs_next_id ALLOCA [Lit (n2w N)] [q]` >>
  `MEM ai (fn_insts func)` by
    (simp[NoAsms,Abbr `ai`,Abbr `q`] >> drule_all_then ACCEPT_TAC slice_extcode_out_owner_inst) >>
  `ai.inst_outputs = [q] /\ ai.inst_id = sd.cs_next_id` by simp[Abbr `ai`,mk_inst_def] >>
  `not_local_ptr cenv es.scopes q` by
    (simp[NoAsms,Abbr `q`] >> irule local_ptrs_reserved_fresh >> qexists_tac `sd` >> simp[]) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es t`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!name b len. local_region cenv es.scopes t name b len ==>
      w2n w+N <= b \/ b+len <= w2n w` by
    (simp_tac bool_ss [GSYM regions_disjoint_def] >> rpt strip_tac >>
     irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`,`func`,`ai`,`name`,`q`,`es.scopes`,`t`] >> simp[]) >>
  `vv_post H ctx func cenv cx e es sa sb s es (Value v) vv t` by
    (simp[NoAsms,Abbr `vv`] >>
     `expr_type e = ann` by simp[Abbr `e`,expr_type_def] >>
     pop_assum (pure_rewrite_tac o single o SYM) >>
     irule vv_post_allocated_memory_intro >>
     `expr_type e = ann /\ post_value_type cenv e = ann /\ ~is_word_type ann` by
       simp[Abbr `e`,Abbr `ann`,expr_type_def,post_value_type_def,is_word_type_def] >>
     simp[mk_ptr_def,eval_operand_def] >>
     qexistsl_tac [`sd.cs_next_id`,`w2n w`,`N`] >>
     simp[] >> qpat_assum `N = type_memory_bytes cenv ann` (pure_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `vv_post_mods H ctx func cenv cx e es sa sb s es (Value v) vv t` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,Abbr `vv`,vv_post_def,vv_post_mods_def,vv_holds_mods_def,
          vv_place_ptr_mods_def,mk_ptr_def,vv_place_ptr_def] >>
     strip_tac >> simp[] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise slice_code_suffix_post_mods
