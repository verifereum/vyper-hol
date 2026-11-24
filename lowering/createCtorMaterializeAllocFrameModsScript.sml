(* Transport the original expression's value posts across the private ALLOCA.
   The interval of the value stays [sa,sm]; [sm,mid] is the destination's. *)
Theory createCtorMaterializeAllocFrameMods
Ancestors
  createCtorMaterializeAllocFrame createExprSizeExitDefsMods
  abiEncodeMaterialize bodyFullAllocaFresh bodyPtrBopRepresentationFrame
  bodyPtrIfExpAllocSource revertReasonPrefixPtr bodyFullHashKeccakFixed
  bodyMemoryDefs stateRelProj allocaSiteResource logValueFramePtr
  exprSimProps exprSimMemDefs loweringPosts stmtSimDefs loweringStateRelDefs
  exprLoweringProps bodyPtrDefs context ptrDiscipline venomState vyperStorageFootprint words finite_map bodyFullPostsMods bodyFullShadowBodyInv

Theorem ctor_materialize_alloc_vv_frame_mods:
  read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\ val_wf rty v /\
  compile_alloc_buffer capacity sm = (buf,mid) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  a with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
  (!(H':(bool # bytes32 # type_value) list # num list).
    stmt_state_rel H' ctx func ce cx ee s ==> stmt_state_rel H' ctx func ce cx ee a) /\
  allocas_from lo a /\ s.vs_alloca_next <= a.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP a.vs_allocas aid = SOME entry) /\
  (!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) /\ FLOOKUP s.vs_allocas aid = NONE ==>
     s.vs_alloca_next <= b) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/
     (s.vs_alloca_next <= i /\ i < w2n w + capacity)) /\
  (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s /\
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv a /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv a /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee Ga ta a /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op Ga a) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w0. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) a = SOME w0 ==>
        w2n w0 + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
          val_in_memory rt val (w2n w0) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\
  return_buf_frame d ce mid a /\ local_ptrs_reserved ce mid /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  ~a.vs_halted /\ s0.vs_alloca_next <= a.vs_alloca_next /\ a.vs_memory = s.vs_memory /\
  eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s /\
  ghost_kept_at lo ce ee sm G tn s Ga ta /\ alloca_frame ce ee sm s ce ee a /\
  (!aid off len i. FLOOKUP s.vs_allocas aid = SOME (off,len) /\
    off <= i /\ i < off + len /\ i IN ta.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  `stmt_state_rel H0 ctx func ce cx ee s /\
   vv_at ce cx (post_value_type ce e) sa sm ee pv vv s` by fs[vv_post_mods_def] >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `~a.vs_halted /\ a.vs_memory = s.vs_memory /\ a.vs_labels = s.vs_labels /\
   a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
   a.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> fs[eval_operand_def]) >>
  `(!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> fs[op_taint_def,op_prov_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> fs[]) >>
  `sm.cs_next_var <= mid.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_rel func ce ee.scopes s /\ alloca_inv s` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!aid off len. FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
        off + len <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all alloca_site_registered_below >> simp[]) >>
  `!i. i < s.vs_alloca_next /\ i IN ta.t_mem ==> i IN tn.t_mem` by
    (simp[] >> rpt strip_tac >> fs[]) >>
  `!name off len. local_region ce ee.scopes s name off len ==>
        off + len <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> simp[]) >>
  conj_tac >- suspend "horizon" >>
  conj_tac >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[]) >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- (rpt strip_tac >> fs[vv_operand_def] >>
    irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> fs[vv_operand_def] >>
    irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]) >>
  conj_tac >- suspend "constructor" >>
  conj_tac >- suspend "entry_kept" >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`sm`] >> simp[]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac
  >- (`stmt_state_rel H0 ctx func ce cx ee a` by simp[] >>
      drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  simp[] >> conj_tac >- suspend "rhs_kept" >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
      (mp_then Any irule alloca_frame_of_mem_frame) >> simp[]) >>
  rpt strip_tac >> `off + len <= s.vs_alloca_next` by metis_tac[] >>
  `i < s.vs_alloca_next` by decide_tac >> fs[]
QED

Resume ctor_materialize_alloc_vv_frame_mods[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  `a.vs_data_section = s.vs_data_section /\ a.vs_immutables = s.vs_immutables` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
                            vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. (z.vs_data_section,z.vs_immutables)``) >> simp[]) >>
  `!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at sm p` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
        (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      `!n b sz. local_region ce ee.scopes a n b sz <=>
                  local_region ce ee.scopes s n b sz` by
        (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
         qexists_tac `sm` >> simp[]) >>
      simp[vv_post_mods_def] >>
      conj_tac
      >- (fs[immutable_frame_mods_def] >> conj_tac
          >- (qpat_x_assum `immutables_rel_mods _ _ _ _ s` mp_tac >>
              simp[bodyInvSplitTheory.immutables_rel_mods_def, immutables_rel_def]) >>
          fs[bodyInvSplitTheory.immutable_alloca_sep_mods_def] >>
          rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_frame >>
          qexistsl_tac [`s`,`ee`] >> simp[] >> conj_tac
          >- (rpt gen_tac >> strip_tac >> disj1_tac >> qexists_tac `id` >>
              `!z. local_region (ce with ce_module := src) ee.scopes z id b sz <=>
                   local_region ce ee.scopes z id b sz` by simp[local_region_def] >>
              qpat_assum `!n b sz. local_region ce ee.scopes a n b sz <=> _`
                (qspecl_then [`id`,`b`,`sz`] mp_tac) >> fs[]) >>
          rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
          >- (disj2_tac >> qpat_assum `!aid b sz. FLOOKUP a.vs_allocas aid = _ /\ _ ==> _`
                (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> simp[]) >>
          disj1_tac >>
          qpat_x_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
            (qspecl_then [`aid`,`x`] mp_tac) >> fs[]) >>
      conj_tac
      >- (Cases_on `vv` >> fs[vv_holds_mods_def, vv_operand_def] >>
          TRY (rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`) >>
          gvs[vv_holds_mods_def] >>
          (irule exprSimVVFrameTheory.vv_holds_vars_frame >>
           qexists_tac `s` >> simp[vv_operand_def,contract_storage_def,contract_transient_def]
           ORELSE
           fs[immutable_holds_mods_def] >>
           qexistsl_tac [`src`,`tops`] >> simp[] >>
           qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
           simp[immutable_holds_def])) >>
      conj_tac
      >- (irule materialize_vv_at_alloc_frame >> qexistsl_tac [`s`,`sm`] >> simp[]) >>
      conj_tac
      >- (Cases_on `vv` >> Cases_on `pv` >> gvs[vv_place_ptr_mods_def,vv_operand_def] >>
          TRY (rename1 `PlaceR place` >> Cases_on `place` >> gvs[vv_place_ptr_mods_def]) >>
          (irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[vv_operand_def] >>
           rpt strip_tac >> `not_fresh_at sm q` by metis_tac[] >> fs[]
           ORELSE
           fs[vv_place_ptr_def])) >>
      conj_tac
      >- (strip_tac >> irule exprSimIfExpWidenedAdapterTheory.vv_own_alloc_mono_frame >>
          qexistsl_tac [`s`,`sm`] >> simp[]) >>
      conj_tac >- (Cases_on `vv` >> gvs[vv_storage_live_def,vv_operand_def]) >>
      conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      conj_tac >- (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
      strip_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> simp[]) >>
  `!p sz. not_fresh_at sm p /\ ptr_covers G tn p s sz ==>
          ptr_covers Ga ta p a sz` by (rpt strip_tac >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
    qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  qpat_x_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  simp[ghost_inv_at_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sm p` by metis_tac[] >>
      `ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
         mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem` by
        (first_x_assum (drule_all_then strip_assume_tac) >> simp[]) >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w'` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       w2n w' + type_memory_size entry.type <= s.vs_alloca_next` by
        (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
         simp[local_ptrs_rel_def] >> strip_tac >>
         first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
         simp[] >> strip_tac >> gvs[]) >>
      irule robust_val_in_memory_footprint_frame >> simp[] >>
      qexistsl_tac [`s.vs_memory`,`s.vs_memory`,`tn.t_mem`,`ta.t_mem`] >> simp[] >>
      `val_footprint entry.type entry.value <= type_memory_size entry.type` by
        simp[val_footprint_le] >>
      rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> fs[]) >>
  conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  conj_tac >- fs[stor_taint_ok_at_def] >>
  conj_tac >- (rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> fs[]) >>
  rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Resume ctor_materialize_alloc_vv_frame_mods[pointer]:
  `(!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
   ptr_mem_ok cx (post_value_type ce e) v (vv_operand vv) G tn s ==>
   ptr_mem_ok cx (post_value_type ce e) v (vv_operand vv) Ga ta a` by
    (strip_tac >> irule bop_ptr_mem_ok_frame >>
     qexistsl_tac [`G`,`s`,`tn`,`rty`] >> simp[] >> rpt strip_tac >>
     drule_all vv_at_memory_footprint >> strip_tac >>
     `i < s.vs_alloca_next` by simp[] >> fs[]) >>
  Cases_on `vv` >> fs[vv_operand_def]
  >- (gvs[ptr_vv_ok_def,ptr_val_ok_def] >> simp[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[ptr_vv_ok_def] >> simp[]) >>
  irule ptr_vv_ok_nonmemory_frame >> simp[] >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]
QED

Resume ctor_materialize_alloc_vv_frame_mods[constructor]:
  disch_then (fn guard =>
    qpat_x_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`
      (strip_assume_tac o C MATCH_MP guard)) >>
  gvs[] >> qx_gen_tac `src` >> strip_tac >>
  `type_memory_size rty + w2n src <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rty v (w2n src) mem)` by
    (qpat_assum `!src. eval_operand _ _ = SOME src ==> _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  qx_gen_tac `mem` >> strip_tac >>
  irule robust_val_in_memory_footprint_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`,`s.vs_memory`,`tn.t_mem`,`ta.t_mem`] >> simp[] >>
  `val_footprint rty v <= type_memory_size rty` by simp[val_footprint_le] >>
  rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> fs[]
QED

Resume ctor_materialize_alloc_vv_frame_mods[entry_kept]:
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`w2n w + capacity`,`s`,`tn`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes s name b sz` by
        (irule local_region_frame_fwd >>
         qexistsl_tac [`s0`,`sa`,`es.scopes`] >> fs[vv_post_mods_def]) >>
      metis_tac[]) >>
  fs[vv_post_mods_def] >> rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
  qpat_assum `!aid off len. FLOOKUP s.vs_allocas aid = SOME (off,len) ==> _`
    (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >> decide_tac
QED

Resume ctor_materialize_alloc_vv_frame_mods[rhs_kept]:
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`w2n w + capacity`,`s`,`tn`] >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Finalise ctor_materialize_alloc_vv_frame_mods
