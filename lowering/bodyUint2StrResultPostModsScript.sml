(* The decimal result at the endpoint of the linked Uint2Str run. *)
Theory bodyUint2StrResultPostMods
Ancestors
  bodyFullPostsMods exprSimUint2Str exprSimHash exprSimProps exprSimWordArgs
  exprLowering exprLoweringProps ptrDiscipline
  bodyPtrBytestringBuiltinsUintGhost bodyPtrDefs exprSimMemDefs loweringHalt
  bodyFullHashKeccakFixed assignEffectfulIndexSnapshotSeparation
  loweringPosts loweringStateRelDefs allocaHistory compileEnv context freshWrites
  vyperValue vyperState vyperAST vyperExprEffects valueEncoding valueEncodingDefs
  valueTypingMemoryProps venomState venomInst words finite_map list arithmetic

Triviality uint2str_pointer_post:
  let ann = BaseT (StringT n);
      tv = BaseTV (StringT n);
      str = num_to_dec_string X;
      at = b+n-LENGTH str;
      vv = LocatedValue ann (mk_ptr (Var out) LocMemory)
  in
    LENGTH str <= n /\ b+(N+n) < dimword(:256) /\
    type_memory_size tv = N /\ val_wf tv (StringV str) /\
    LENGTH str + 32 <= N /\ b+(N+n) <= t.vs_alloca_next /\
    eval_operand (Var out) t = SOME (n2w at) /\
    val_in_memory tv (StringV str) at t.vs_memory /\
    FLOOKUP Gf out = SOME (b,N+n) /\ op_taint tf (Var out) = {} /\
    (!i. at <= i /\ i < b+n+32 ==> i NOTIN tf.t_mem) /\
    type_memory_bytes ce (lowered_value_type ce (Builtin ann (Uint2Str n) [e])) = N ==>
    vv_store_bound cx ann ann mid (Value (StringV str)) vv t /\
    ptr_vv_ok cx ann (Value (StringV str)) vv mid Gf tf t /\
    vv_location vv = SOME LocMemory /\
    ptr_buf_ok ce (Builtin ann (Uint2Str n) [e]) (vv_operand vv) Gf t
Proof
  simp[LET_THM] >> strip_tac >>
  qabbrev_tac `v = StringV (num_to_dec_string X)` >>
  qabbrev_tac `at = b+n-LENGTH (num_to_dec_string X)` >>
  `b <= at /\ at + N <= b+(N+n) /\ at < dimword(:256)` by
    (simp[Abbr `at`] >> decide_tac) >>
  `w2n (n2w at : 256 word) = at` by simp[w2n_n2w] >>
  `val_store_size (BaseTV (StringT n)) v <= N` by
    (irule LESS_EQ_TRANS >> qexists_tac `type_memory_size (BaseTV (StringT n))` >>
     simp[val_store_size_le]) >>
  conj_tac
  >- (simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def,evaluate_type_def] >>
      decide_tac) >>
  conj_tac
  >- (simp[ptr_vv_ok_def,mk_ptr_def,read_result_def,return_def,ptr_mem_ok_def,evaluate_type_def] >>
      rpt strip_tac >> simp[Abbr `v`] >> irule uint_string_clean_robust >> simp[] >>
      qexistsl_tac [`tf.t_mem`,`t.vs_memory`] >> simp[] >>
      rpt strip_tac >> qpat_assum `!j. _ ==> j NOTIN tf.t_mem` (qspec_then `i` mp_tac) >>
      simp[] >> gvs[Abbr `at`] >> decide_tac) >>
  simp[vv_location_def,vv_operand_def,mk_ptr_def,ptr_buf_ok_def]
QED

Triviality uint2str_result_linked:
  vv_post H ctx fn ce cx e es sa sb s0 mid (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) t /\
  immutable_frame_mods fn ce cx mid t ==>
  vv_post_mods H ctx fn ce cx e es sa sb s0 mid (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) t
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,
       vv_place_ptr_def,mk_ptr_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem uint2str_result_post_mods:
  let ann = BaseT (StringT n);
      E = Builtin ann (Uint2Str n) [e];
      tv = BaseTV (StringT n);
      str = num_to_dec_string X;
      at = b+n-LENGTH str;
      out = Var (u2s_var a 2)
  in
    N = type_memory_bytes ce ann /\
    compile_alloc_buffer (N+n) sm = (ba,a) /\ ba.buf_operand = Var p /\
    u2s_layout a op (Var p) n sb /\ fn_has_code sm sb fn /\
    as_ptr_val ann LocMemory (compile_uint2str op n N sm) = (vv,sb) /\
    inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (N+n))] [p] /\ MEM inst (fn_insts fn) /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
    expr_post_mods H ctx fn ce cx e es sa sm s0 mid (IntV (&X)) op s /\
    u2s_safe H ctx fn ce cx mid a (Var p) b (N+n) inst ready t /\
    ready.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x ready = lookup_var x s) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP ready.vs_allocas aid = SOME row) /\
    alloca_history fn ready /\ allocas_from lo ready /\ lo <= b /\
    s.vs_alloca_next <= ready.vs_alloca_next /\ b+(N+n) <= ready.vs_alloca_next /\
    b+(N+n) < dimword(:256) /\ LENGTH str <= n /\
    type_memory_size tv = N /\ val_wf tv (StringV str) /\
    LENGTH str + 32 <= N /\ val_footprint tv (StringV str) <= N /\
    eval_operand out t = SOME (n2w at) /\ val_in_memory tv (StringV str) at t.vs_memory /\
    FLOOKUP Gf (u2s_var a 2) = SOME (b,N+n) /\ op_taint tf out = {} /\
    (!i. at <= i /\ i < b+n+32 ==> i NOTIN tf.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    immutable_frame_mods fn ce cx mid t ==>
    vv_post_mods H ctx fn ce cx E es sa sb s0 mid (Value (StringV str)) vv t /\
    vv_store_bound cx (post_value_type ce E) (lowered_value_type ce E)
      mid (Value (StringV str)) vv t /\
    ptr_vv_ok cx (post_value_type ce E) (Value (StringV str)) vv mid Gf tf t /\
    vv_location vv = SOME LocMemory /\ ptr_buf_ok ce E (vv_operand vv) Gf t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history fn t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[LET_THM] >> strip_tac >>
  qabbrev_tac `ann = BaseT (StringT n)` >>
  qpat_x_assum `N = _` (assume_tac o SYM) >>
  qabbrev_tac `E = Builtin ann (Uint2Str n) [e]` >>
  qabbrev_tac `v = StringV (num_to_dec_string X)` >>
  qabbrev_tac `out = Var (u2s_var a 2)` >>
  qabbrev_tac `at = b+n-LENGTH (num_to_dec_string X)` >>
  `post_value_type ce E = ann /\ lowered_value_type ce E = ann /\ expr_type E = ann` by
    simp[Abbr `E`,post_value_type_def,lowered_value_type_def,expr_type_def] >>
  `compile_uint2str op n N sm = (out,sb)` by
    (qpat_assum `u2s_layout a _ _ _ _` (strip_assume_tac o REWRITE_RULE [u2s_layout_def]) >>
     simp[Abbr `out`] >> drule compile_uint2str_layout_eq >> simp[]) >>
  `vv = LocatedValue ann (mk_ptr out LocMemory)` by fs[as_ptr_val_def] >>
  qpat_assum `u2s_safe H _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [u2s_safe_def]) >>
  qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  suspend "machine"
QED

Resume uint2str_result_post_mods[machine]:
  `inst.inst_id = sm.cs_next_id /\ inst.inst_opcode = ALLOCA` by simp[mk_inst_def] >>
  `sm.cs_next_id < sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> fs[u2s_layout_def,u2s_end_def]) >>
  qpat_assum `u2s_frame a _ _ ready t`
    (strip_assume_tac o REWRITE_RULE [u2s_frame_def]) >>
  `t.vs_allocas = ready.vs_allocas /\ t.vs_alloca_next = ready.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row` by simp[] >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at a x` by
       (drule compile_alloc_buffer_parts >> strip_tac >> simp[]) >> simp[]) >>
  `!off len. off+len <= b \/ b+(N+n) <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `ready.vs_memory = _` (pure_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  suspend "frames"
QED

Resume uint2str_result_post_mods[frames]:
  `wb_frame ce es mid sa s0 s` by drule_then ACCEPT_TAC expr_post_frame >>
  `!nm lb len. local_region ce mid.scopes s nm lb len ==>
     b+(N+n) <= lb \/ lb+len <= b` by
    (rpt strip_tac >>
     `local_region ce mid.scopes t nm lb len` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s`,`sm`,`mid.scopes`] >>
        simp[] >> drule local_ptrs_reserved_next_var >> disch_then irule >> simp[]) >>
     first_x_assum drule >> simp[]) >>
  `wb_frame ce es mid sa s0 t` by
    (irule wb_frame_allocating_tail >> simp[] >>
     qexistsl_tac [`s`,`mid.scopes`,`sm`] >> simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
         qpat_assum `!nm lb len. local_region ce mid.scopes s nm lb len ==> _` drule >>
         disch_tac >> decide_tac) >>
     rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas id = SOME (off,len)` >>
     `FLOOKUP t.vs_allocas id = SOME (off,len)` by simp[] >>
     `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,N+n)` by
       (qpat_assum `inst.inst_id = _` (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
     `regions_disjoint off len b (N+n)` by
       (qpat_assum `stmt_state_rel H ctx fn ce cx mid t` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas sm.cs_next_id = _` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas id = _` mp_tac >>
        qpat_assum `id < sm.cs_next_id` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        metis_tac[Q.INST [`origin` |-> `sm`] snapshot_origin_allocations_disjoint, LESS_EQ_REFL]) >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
     fs[regions_disjoint_def]) >>
  `~expr_has_effect E ==> pure_frame ce fn es sa s0 t` by
    (strip_tac >>
     `~expr_has_effect e` by fs[Abbr `E`,expr_has_effect_thm] >>
     drule_all_then assume_tac expr_post_pure_frame >>
     irule pure_frame_buffer_tail >>
     qexistsl_tac [`b`,`N+n`,`inst`,`s`] >> simp[regions_disjoint_def] >>
     conj_tac >> rpt strip_tac
     >- (`local_region ce mid.scopes t n' lb lsz` by
           (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
            simp[] >> metis_tac[wb_frame_vars]) >> first_x_assum drule >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  suspend "pack"
QED

Resume uint2str_result_post_mods[pack]:
  `storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
  `w2n (n2w at : 256 word) = at /\ b <= at /\ at + N <= b+(N+n)` by
    (simp[w2n_n2w,Abbr `at`] >> decide_tac) >>
  `vv_post H ctx fn ce cx E es sa sb s0 mid (Value v) vv t` by
    (qpat_assum `vv = _` (SUBST1_TAC) >>
     qpat_assum `expr_type E = ann` (pure_rewrite_tac o single o SYM) >>
     irule vv_post_allocated_memory_intro >>
     qpat_assum `expr_type E = ann` (pure_rewrite_tac o single) >>
     simp[Abbr `ann`,mk_ptr_def,evaluate_type_def,is_word_type_def] >>
     qexistsl_tac [`sm.cs_next_id`,`b`,`N+n`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!nm lb lsz. local_region ce mid.scopes t nm lb lsz ==> _` drule >>
         disch_tac >> decide_tac) >>
     conj_tac
     >- (qpat_assum `t.vs_allocas = ready.vs_allocas` (pure_rewrite_tac o single o SYM) >>
         qpat_assum `inst.inst_id = _` (pure_rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `type_memory_size (BaseTV (StringT n)) = N` mp_tac >>
     qpat_assum `_ < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[type_memory_size_def,type_slot_size_def] >> decide_tac) >>
  conj_tac
  >- (qpat_assum `vv = _` SUBST1_TAC >> irule uint2str_result_linked >>
      qpat_assum `vv = _` (pure_rewrite_tac o single o SYM) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  `vv_store_bound cx ann ann mid (Value v) vv t /\
   ptr_vv_ok cx ann (Value v) vv mid Gf tf t /\
   vv_location vv = SOME LocMemory /\ ptr_buf_ok ce E (vv_operand vv) Gf t` by
    (qpat_assum `vv = _` SUBST1_TAC >>
     simp[Abbr `ann`,Abbr `out`,Abbr `v`,Abbr `E`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] uint2str_pointer_post) >>
     simp[] >> qexistsl_tac [`N`,`b`] >> fs[Abbr `at`,AC ADD_ASSOC ADD_COMM]) >>
  simp[] >> suspend "control"
QED

Resume uint2str_result_post_mods[control]:
  `alloca_history fn t` by (irule alloca_history_jump >> simp[] >> qexists_tac `ready` >> simp[]) >>
  `sb.cs_current_bb = u2s_label a 5 /\ sb.cs_current_insts = []` by
    fs[u2s_layout_def,u2s_end_def] >>
  `allocas_from lo t` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = ready.vs_allocas` (pure_rewrite_tac o single) >>
     qpat_assum `allocas_from lo ready` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> gvs[]
QED

Finalise uint2str_result_post_mods
