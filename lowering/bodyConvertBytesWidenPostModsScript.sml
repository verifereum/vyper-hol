(* Posts at the already reached ALLOCA/MCOPY endpoint of bytestring Convert. *)
Theory bodyConvertBytesWidenPostMods
Ancestors
  bodyFullConvertCopyPosts bodyFullConvertEndpointPosts bodyFullPostsMods
  exprSimWordArgs wordArgsPtr exprSimStack loweringSlice placeMemoryTypedPrimitive
  bodyFullHashKeccakFixed abiCallerLocalScratch tupleMemoryFrame
  valueEncodingProps valueCopyBytes exprLoweringProps stateRelProj
  bodyFullShadowBodyInv fragExecPtr venomExecSemantics venomMemDefs words
  venomState finite_map pred_set context exprLowering loweringPosts bodyPtrDefs
  loweringStateRelDefs exprSimMemDefs exprSimProps vyperAST vyperState
  bodyInvSplit exprSimConvertBytes compileEnv ptrDiscipline

Theorem widen_alloc_fields[local]:
  z with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t ==>
  z.vs_memory = t.vs_memory /\ z.vs_data_section = t.vs_data_section
Proof
  simp[venom_state_component_equality]
QED

Theorem widen_region_lookup[local]:
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t) ==>
  !ce' scopes id b n. ce'.ce_vars = ce.ce_vars ==>
    (local_region ce' scopes z id b n <=> local_region ce' scopes t id b n)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> simp[local_region_def] >>
  eq_tac >> rpt strip_tac >>
  `not_fresh_at sm p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`entry`,`p`,`w`] >> simp[] >> metis_tac[]
QED

Theorem widen_immutable_frame[local]:
  immutable_frame_mods func ce cx mid t /\
  z.vs_memory = t.vs_memory /\ z.vs_data_section = t.vs_data_section /\
  t.vs_alloca_next <= z.vs_alloca_next /\
  (!aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,n) \/ t.vs_alloca_next <= b) /\
  (!aid b n. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint (w2n dw) cap b n) /\
  (!name b n. local_region ce mid.scopes z name b n ==>
      regions_disjoint (w2n dw) cap b n) /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n (dw:256 word),cap) /\
  k <= cap /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sm.cs_next_id /\
  z with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t) /\
  q = (mcopy (w2n dw) a k z) with vs_inst_idx := idx ==>
  immutable_frame_mods func ce cx mid q
Proof
  strip_tac >>
  `!ce' scopes id b n. ce'.ce_vars = ce.ce_vars ==>
      (local_region ce' scopes z id b n <=> local_region ce' scopes t id b n)` by
    (drule widen_region_lookup >>
     disch_then (qspecl_then [`z`,`t`] mp_tac) >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  fs[immutable_frame_mods_def] >> conj_tac
  >- suspend "bytes" >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`t`,`mid`] >>
  `q.vs_alloca_next = z.vs_alloca_next /\ q.vs_allocas = z.vs_allocas` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  fs[] >> rpt strip_tac >> disj1_tac >>
  (qexists_tac `id` >>
   qpat_assum `!ce' scopes id b n. _`
     (qspecl_then [`ce with ce_module := src`,`mid.scopes`,`id`,`b`,`sz`] mp_tac) >>
   fs[local_region_def,lookup_var_def,mcopy_def,write_memory_with_expansion_def] >>
   metis_tac[])
QED
Resume widen_immutable_frame[bytes]:
  fs[immutables_rel_mods_def,immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  `(mcopy (w2n dw) a k z with vs_inst_idx := idx).vs_data_section = t.vs_data_section` by
    simp[mcopy_def,write_memory_with_expansion_def] >>
  qpat_x_assum `q = _` kall_tac >>
  `immutables_rel ce cx.txn.target src ce.ce_is_ctor mid t` by simp[] >>
  irule immutables_rel_mem_agree >> qexists_tac `t` >> simp[] >>
  conj_tac >- (qpat_assum `z.vs_memory = t.vs_memory` (SUBST1_TAC o GSYM) >>
               irule placeMemoryTypedPrimitiveTheory.mcopy_memory_length) >>
  rpt strip_tac >>
  `immutable_alloca_sep func (ce with ce_module := src) cx mid t` by simp[] >>
  `off + type_memory_size tv <= t.vs_alloca_next` by
    (qpat_x_assum `immutable_alloca_sep func (ce with ce_module := src) cx mid t` mp_tac >>
     pure_rewrite_tac[immutable_alloca_sep_def,compile_env_accfupds,combinTheory.K_THM] >>
     strip_tac >>
     qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >> simp[]) >>
  `regions_disjoint off (type_memory_size tv) (w2n dw) cap` by
    (Cases_on `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,cap)`
     >- (qpat_assum `immutable_alloca_sep func (ce with ce_module := src) cx mid t` mp_tac >>
         pure_rewrite_tac[immutable_alloca_sep_def,compile_env_accfupds,combinTheory.K_THM] >>
         strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >> simp[] >>
         disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >> simp[] >>
         disch_then assume_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!inst b sz. _`
           (qspecl_then [`inst`,`w2n dw`,`cap`] mp_tac) >> simp[] >>
         disch_then assume_tac >> first_x_assum drule)
     >- (`FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,cap)` by metis_tac[] >>
         qpat_assum `!aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==> _`
           (qspecl_then [`inst.inst_id`,`w2n dw`,`cap`] mp_tac) >>
         disch_then drule >> simp[] >>
         `t.vs_alloca_next <= w2n dw` by metis_tac[] >>
         fs[regions_disjoint_def] >> decide_tac)) >>
  qpat_assum `z.vs_memory = t.vs_memory` (SUBST1_TAC o GSYM) >>
  irule mcopy_mem_bytes_at_disjoint >> fs[regions_disjoint_def] >> metis_tac[]
QED
Finalise widen_immutable_frame

Theorem widen_protected_prefix[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn t /\
  ghost_inv_at D 0 d ce cx mid Gf tnf q /\ allocas_from lo q /\
  lo <= t.vs_alloca_next /\ t.vs_alloca_next <= q.vs_alloca_next /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
         op_taint tnf (Var x) = op_taint tn (Var x)) /\
  mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t.vs_memory /\
  (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem) ==>
  ghost_inv_at_mods D lo d ce cx mid Gf tnf q
Proof
  strip_tac >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    metis_tac[local_ptrs_reserved_imm_base] >>
  `lo <= q.vs_alloca_next` by decide_tac >>
  fs[ghost_inv_at_mods_def,ghost_inv_at_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> metis_tac[]))
QED

Theorem widen_mcopy_prefix[local]:
  lookup_var dst z = SOME dw /\ lookup_var src z = SOME a /\ k < dimword (:256) /\
  z.vs_memory = t.vs_memory /\ lo <= t.vs_alloca_next /\ lo <= w2n dw /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
     (t.vs_alloca_next <= i /\ i < w2n dw+cap)) /\
  q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := idx /\
  Gf = step_prov PG Ga (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] [])
          (mcopy (w2n dw) (w2n a) k z) /\
  tnf = step_taint (mk_inst iid MCOPY [Var dst;Var src;Lit (n2w k)] []) z
          (mcopy (w2n dw) (w2n a) k z) tna ==>
  mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t.vs_memory /\
  Gf = Ga /\ tnf.t_var = tna.t_var /\
  (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (simp[] >> qpat_assum `z.vs_memory = t.vs_memory` (SUBST1_TAC o GSYM) >>
      irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  Q.SUBGOAL_THEN
    `eval_operand (Var dst) z = SOME dw /\ eval_operand (Var src) z = SOME a /\
     eval_operand (Lit (n2w k)) z = SOME (n2w k)`
    (mp_tac o MATCH_MP mcopy_operand_ghost_frame)
  >- simp[eval_operand_def] >>
  disch_then (qspecl_then [`PG`,`Ga`,`tna`,`iid`] mp_tac) >>
  simp[wordsTheory.w2n_n2w] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >>
    `~(w2n dw <= i)` by decide_tac >> gvs[] >> decide_tac))
QED

Theorem widen_vv_post[local]:
  expr_post H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid vout op q /\
  storage_well_formed_on cx mid (FST H) /\ ~is_word_type dst /\
  immutable_frame_mods func ce cx mid q ==>
  vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid (Value vout) (LocatedValue dst (mk_ptr op LocMemory)) q
Proof
  strip_tac >> drule_all dynamic_word_vv_post >> strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) vv_post_stack_as_memory >>
  simp[post_value_type_def,expr_type_def] >>
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Theorem bytes_convert_widen_post_mods:
  expr_post_mods H ctx func ce cx e es sa sm s0 mid v (Var src) t /\
  ghost_inv_at_mods D lo d ce cx mid G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel H ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  is_bytestring_type dst /\ evaluate_type (get_tenv cx) dst = SOME rt /\
  val_wf rt vout /\ val_footprint rt vout <= k /\
  type_memory_bytes ce dst = cap /\ type_memory_size rt = cap /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt vout (w2n a) m) /\
  compile_bytestring_widen_copy cap (Var src) k sm = (Var dstvar,sb) /\
  0 < k /\ k < cap /\ cap < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  not_fresh_at sm src /\ lookup_var src t = SOME a /\
  w2n a+k <= t.vs_alloca_next /\
  run_inst_seq (emitted_insts sm sb) t = OK u /\
  q = u with vs_inst_idx := LENGTH sb.cs_current_insts /\
  q.vs_current_bb = sb.cs_current_bb /\ alloca_history func q /\ allocas_from lo q /\
  stmt_state_rel H ctx func ce cx mid z /\
  z with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
  t.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,cap) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
  (!aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,n) \/ t.vs_alloca_next <= b) /\
  (!aid b n. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint (w2n dw) cap b n) /\
  (!name b n. local_region ce mid.scopes z name b n ==>
      regions_disjoint (w2n dw) cap b n) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
     FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
      (t.vs_alloca_next <= i /\ i < w2n dw+cap)) /\
  lookup_var dstvar z = SOME dw /\ ptr_covers Ga tna dstvar z cap /\
  w2n dw+cap <= z.vs_alloca_next /\
  q = (mcopy (w2n dw) (w2n a) k z) with vs_inst_idx := LENGTH sb.cs_current_insts /\
  Gf = step_prov PG Ga (mk_inst iid MCOPY [Var dstvar;Var src;Lit (n2w k)] [])
         (mcopy (w2n dw) (w2n a) k z) /\
  tnf = step_taint (mk_inst iid MCOPY [Var dstvar;Var src;Lit (n2w k)] []) z
         (mcopy (w2n dw) (w2n a) k z) tna ==>
  (\H res ee G tn t. ?tv. res = INL tv /\
    vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 ee tv
      (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) t /\
    vv_store_bound cx dst dst ee tv (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods D lo d ce cx ee G tn t /\
    ptr_vv_ok cx dst tv (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type dst /\ ~is_bytestring_type dst ==>
      vv_own ce cx dst sa sb ee tv (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) t /\
      (!t' p. LocatedValue dst (mk_ptr (Var dstvar) LocMemory) = LocatedValue t' p ==>
              p.ptr_location = LocMemory)) /\
    (ce.ce_is_ctor /\ vv_location (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val, ee) /\
            !ty w. evaluate_type (get_tenv cx) dst = SOME ty /\
              eval_operand (vv_operand (LocatedValue dst (mk_ptr (Var dstvar) LocMemory))) t = SOME w ==>
              w2n w + type_memory_size ty <= lo /\
              (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                val_in_memory ty val (w2n w) mem)) /\
    (!t' op. LocatedValue dst (mk_ptr (Var dstvar) LocMemory) = StackValue t' op /\
             ~is_word_type dst ==> ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) op G t) /\
    (!t' p. LocatedValue dst (mk_ptr (Var dstvar) LocMemory) = LocatedValue t' p /\
             p.ptr_location = LocMemory ==> ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) p.ptr_operand G t) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn) H (INL (Value vout)) mid Gf tnf q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >>
  `expr_post H ctx func ce cx e es sa sm s0 mid v (Var src) t /\
   immutable_frame_mods func ce cx mid t` by fs[expr_post_mods_def] >>
  `wb_frame ce es mid sa s0 t /\ stmt_state_rel H ctx func ce cx mid t` by
    metis_tac[expr_post_frame,expr_post_state] >>
  `storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
  `~is_word_type dst` by fs[is_bytestring_word_type] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `z.vs_memory = t.vs_memory /\ z.vs_data_section = t.vs_data_section` by
    (drule widen_alloc_fields >> simp[]) >>
  `t.vs_alloca_next <= z.vs_alloca_next /\ lo <= t.vs_alloca_next /\
   k <= cap /\ k < dimword (:256)` by
    (conj_tac >- decide_tac >> conj_tac >- fs[ghost_inv_at_mods_def] >> decide_tac) >>
  `immutable_frame_mods func ce cx mid q` by suspend "immutable" >>
  `expr_post H ctx func ce cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 mid vout (Var dstvar) q` by
    suspend "plain_post" >>
  `ghost_inv_at_mods D lo d ce cx mid Gf tnf q /\
   ptr_val_ok cx dst vout (Var dstvar) Gf tnf q /\
   ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) (Var dstvar) Gf q /\
   ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf /\
   vv_store_bound cx dst dst mid (Value vout) (StackValue dst (Var dstvar)) q` by
    suspend "ghosts" >>
  suspend "finish"
QED

Resume bytes_convert_widen_post_mods[immutable]:
  irule widen_immutable_frame >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  qexistsl_tac [`w2n a`,`cap`,`dw`,`LENGTH sb.cs_current_insts`,`inst`,`k`,`sm`,`z`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])
QED

Resume bytes_convert_widen_post_mods[plain_post]:
  `val_in_memory rt vout (w2n a) t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `expr_post H ctx func ce cx (TypeBuiltin dst Convert dst [e]) mid sm sb t mid vout (Var dstvar) q` by
    (irule convert_widen_copy_endpoint_post >>
     simp[expr_type_def,post_value_type_def,eval_operand_def] >>
     conj_tac >- (qpat_assum `q = u with vs_inst_idx := _` mp_tac >> simp[]) >>
     qexistsl_tac [`a`,`cap`,`k`,`Var src`] >> simp[eval_operand_def]) >>
  qpat_x_assum `q = (mcopy _ _ _ _) with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `q = u with vs_inst_idx := _` kall_tac >>
  irule convert_expr_post_compose >>
  simp[expr_has_effect_thm] >>
  conj_tac >- fs[wb_frame_def,locals_kept_def] >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ (TypeBuiltin _ _ _ _) _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`e`,`v`,`Var src`] >> simp[]
QED

Resume bytes_convert_widen_post_mods[ghosts]:
  `ghost_inv_at D 0 d ce cx mid G tn t` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp[ghost_inv_at_def,allocas_from_def,NoAsms] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from 0 z` by simp[allocas_from_def] >>
  `ghost_kept_at 0 ce es sa G0 tn0 s0 G tn` by
    (qpat_assum `ghost_kept_at lo _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `lookup_var src z = SOME a` by
    (qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `src` mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ mid t`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id ==>
     b+n <= t.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n` by
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (b,n)` by metis_tac[wb_frame_def] >>
     `b+n <= s0.vs_alloca_next` by
       (qpat_assum `alloca_inv s0` mp_tac >>
        pure_rewrite_tac[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
     `b+n <= t.vs_alloca_next` by
       (qpat_assum `b + n <= s0.vs_alloca_next` (fn th1 =>
        qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` (fn th2 =>
        ACCEPT_TAC (MATCH_MP arithmeticTheory.LESS_EQ_TRANS (CONJ th1 th2))))) >>
     `regions_disjoint (w2n dw) cap b n` by
       (qpat_assum `!aid b n. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==> _`
          irule >> qexists_tac `aid` >> simp[] >> metis_tac[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b n. local_region ce es.scopes s0 name b n ==>
     local_region ce mid.scopes z name b n` by
    (rpt strip_tac >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
       fs[wb_frame_def,locals_kept_def] >>
     `local_region ce es.scopes z name b n` suffices_by
       metis_tac[local_region_scopes_domain] >>
     qpat_x_assum `local_region ce es.scopes s0 name b n` mp_tac >>
     simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
     `lookup_var p t = SOME w` by metis_tac[wb_frame_def] >>
     `lookup_var p z = SOME w` by metis_tac[] >>
     qexistsl_tac [`entry`,`p`,`w`] >> simp[] >> metis_tac[]) >>
  `!name b n. local_region ce es.scopes s0 name b n ==>
     b+n <= t.vs_alloca_next /\ regions_disjoint (w2n dw) cap b n` by
    (rpt strip_tac >>
     `local_region ce mid.scopes z name b n` by metis_tac[] >>
     `b+n <= s0.vs_alloca_next` by (drule_all abi_caller_local_end >> simp[]) >>
     `b+n <= t.vs_alloca_next` by
       (qpat_assum `b + n <= s0.vs_alloca_next` (fn th1 =>
        qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` (fn th2 =>
        ACCEPT_TAC (MATCH_MP arithmeticTheory.LESS_EQ_TRANS (CONJ th1 th2))))) >>
     `regions_disjoint (w2n dw) cap b n` by
       (qpat_assum `!name b n. local_region ce mid.scopes z name b n ==> _`
          irule >> qexists_tac `name` >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `val_store_size rt vout <= cap` by
    (drule val_store_size_le >> simp[]) >>
  suspend "apply_copy_ghosts"
QED

Resume bytes_convert_widen_post_mods[apply_copy_ghosts]:
  `type_memory_bytes ce dst <= cap /\ type_memory_size rt <= cap` by simp[] >>
  `ghost_inv_at D 0 d ce cx mid Gf tnf q /\
   ptr_val_ok cx dst vout (Var dstvar) Gf tnf q /\
   (!ex. lowered_value_type ce ex = dst ==> ptr_buf_ok ce ex (Var dstvar) Gf q) /\
   ghost_kept_at 0 ce es sa G0 tn0 s0 Gf tnf /\
   vv_store_bound cx dst dst mid (Value vout) (StackValue dst (Var dstvar)) q` by
    suspend "ordinary_ghosts" >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t.vs_memory /\
   Gf = Ga /\ tnf.t_var = tna.t_var /\
   (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem)` by
    suspend "prefix" >>
  conj_tac >- suspend "linked_ghost" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (first_x_assum irule >> simp[lowered_value_type_def,expr_type_def]) >>
  conj_tac
  >- (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ Gf tnf` mp_tac >>
      pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume bytes_convert_widen_post_mods[ordinary_ghosts]:
  irule convert_widen_copy_endpoint_ghosts >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `ghost_inv_at _ 0 _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ t`)) >>
  goal_assum (drule_at (Pat `_ = (mcopy _ _ _ _) with vs_inst_idx := _`)) >>
  qexistsl_tac [`cap`,`rt`,`sm`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Resume bytes_convert_widen_post_mods[prefix]:
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo z` mp_tac >>
     fs[allocas_from_def] >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n dw`,`cap`] mp_tac) >>
     simp[]) >>
  irule widen_mcopy_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ = (mcopy _ _ _ _) with vs_inst_idx := _`)) >>
  qexists_tac `cap` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume bytes_convert_widen_post_mods[linked_ghost]:
  `t.vs_alloca_next <= q.vs_alloca_next` by
    (qpat_assum `q = (mcopy _ _ _ _) with vs_inst_idx := _` SUBST1_TAC >>
     simp[mcopy_def,write_memory_with_expansion_def]) >>
  irule widen_protected_prefix >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `sm` >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> fs[op_taint_def] >> metis_tac[]))
QED

Resume bytes_convert_widen_post_mods[finish]:
  `stmt_state_rel H ctx func ce cx mid q` by metis_tac[expr_post_state] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid q`
       (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `t.vs_alloca_next <= q.vs_alloca_next` by
    (qpat_assum `q = (mcopy _ _ _ _) with vs_inst_idx := _` SUBST1_TAC >>
     simp[mcopy_def,write_memory_with_expansion_def]) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 mid
     (Value vout) (LocatedValue dst (mk_ptr (Var dstvar) LocMemory)) q` by
    (irule widen_vv_post >> goal_assum (drule_at (Pat `expr_post _ _ _ _ _ (TypeBuiltin _ _ _ _) _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `q.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `q = u with vs_inst_idx := _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `q = u with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `q = (mcopy _ _ _ _) with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Gf = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tnf = step_taint _ _ _ _` kall_tac >>
  fs[mk_ptr_def,vv_location_def,ptr_vv_ok_def,vv_store_bound_def,
     ptr_val_ok_def,vyperStateTheory.read_result_def,vyperStateTheory.return_def]
QED
Finalise bytes_convert_widen_post_mods
