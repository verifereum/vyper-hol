(* Resource transport across the reason encoder's allocation prefix. *)
Theory reasonPrefixResourcesPtr
Ancestors
  wordLoadStorePtr reasonAllocationFramePtr reasonBufferPtr allocationPtr normalizationAllocPtr robustCopyTransportPtr typedCopyPtr
  bodyPtrDefs ptrDiscipline venomState venomInst pred_set arithmetic
  loweringPosts compileEnv loweringStateRelDefs exprLoweringProps exprSimProps exprSimAlloc emitHelperProps exprSimHash loweringHalt venomExecSemantics

Theorem reason_encoder_store_robust_preserved:
  !tn s id dst value a w tv v p.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory m ==>
      val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (cj 5 mstore_ghost_frame) >> pure_rewrite_tac[FORALL_SIMP] >>
  disch_then (qspec_then `id` assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) w s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`,
    `{i | w2n a <= i /\ i < w2n a + 32}`] >> simp[] >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`s`, `w2n (a:bytes32)`, `w`] mstore_memory_frame) >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

(* Stores change the representation, but not its allocation/local location. *)
Theorem reason_encoder_store_value_location:
  !cenv cx ty sa sb es v op s a w.
    expr_val_at cenv cx ty sa sb es v op (mstore a w s) <=>
    expr_val_at cenv cx ty sa sb es v op s
Proof
  simp[expr_val_at_def, local_region_def, eval_operand_def,
       lookup_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem reason_encoder_original_local_region:
  !ctx func cenv cx e es sa sb s0 es' v op s n b sz.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    local_region cenv es.scopes s0 n b sz ==>
    local_region cenv es'.scopes s n b sz
Proof
  rpt gen_tac >> strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
  gvs[expr_post_def] >> metis_tac[]
QED

(* A read-only allocation preserves placement without moving the expression's
   ownership interval.  Local-region equivalence is supplied by fresh outputs. *)
Theorem reason_encoder_value_location_frame:
  !cenv cx ty sa sb es v op s t.
    expr_val_at cenv cx ty sa sb es v op s /\
    eval_operand op t = eval_operand op s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!n b sz. local_region cenv es.scopes t n b sz <=>
      local_region cenv es.scopes s n b sz) ==>
    expr_val_at cenv cx ty sa sb es v op t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[] >> metis_tac[]
QED

Theorem reason_encoder_readonly_post:
  !ctx func cenv cx e es sa sb s0 es' v op s t cc.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    stmt_state_rel ctx func cenv cx es' t /\
    sa.cs_next_var <= cc.cs_next_var /\
    eval_operand op t = eval_operand op s /\
    t.vs_memory = s.vs_memory /\
    (!x w. not_fresh_at cc x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!n b sz. local_region cenv es'.scopes t n b sz <=>
      local_region cenv es'.scopes s n b sz) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op t
Proof
  rpt gen_tac >> strip_tac >>
  `expr_val_at cenv cx (post_value_type cenv e) sa sb es' v op t` by
    (irule reason_encoder_value_location_frame >>
     qexists_tac `s` >> gvs[expr_post_def]) >>
  `post_value_type cenv e <> expr_type e ==>
   expr_val_own cenv cx (post_value_type cenv e) sa sb es' v op t` by
    (strip_tac >> gvs[expr_post_def, expr_val_own_def] >> rpt strip_tac >>
     qpat_x_assum `!tv. _ ==> _` drule_all >> strip_tac >>
     qexists_tac `w` >> simp[] >> metis_tac[]) >>
  gvs[expr_post_def, expr_val_rel_def, locals_kept_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at cc x` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!x w. not_fresh_at cc x /\ _ ==> _` irule >>
      simp[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` irule >> simp[]) >>
  metis_tac[]
QED

Theorem reason_encoder_alloc_buffer_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc cd buf n.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    (!p. op = Var p ==> not_fresh_at cc p) /\ local_ptrs_reserved cenv cc /\
    fn_inst_ids_distinct func /\ n < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var ==>
    ?t w. run_inst_seq (emitted_insts cc cd) s = OK t /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString cc.cs_next_var)]) s = OK t /\
      local_ptrs_reserved cenv cd /\
      eval_operand op t = eval_operand op s /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas cc.cs_next_id = SOME (w2n w,n) /\
      w2n w + n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!aid b len. aid < cc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) n b len) /\
      (!name b len. local_region cenv es'.scopes t name b len ==>
        regions_disjoint (w2n w) n b len)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by gvs[expr_post_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand op t = eval_operand op s` by suspend "operand" >>
  `!name b len. local_region cenv es'.scopes t name b len <=>
     local_region cenv es'.scopes s name b len` by suspend "locals" >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op t` by
    (irule reason_encoder_readonly_post >>
     simp[] >> qexistsl_tac [`cc`, `s`] >> simp[]) >>
  `step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString cc.cs_next_var)]) s = OK t` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
         run_inst_seq_def, AllCaseEqs()]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> asm_rewrite_tac[]
QED

Resume reason_encoder_alloc_buffer_post[operand]:
  Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]
QED

Resume reason_encoder_alloc_buffer_post[locals]:
  rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >> conj_tac
      >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`cc`, `es'.scopes`, `t`] >> simp[]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `cc`, `es'.scopes`] >> simp[]
QED

Finalise reason_encoder_alloc_buffer_post

(* The store is confined to an allocated buffer, separated from the old
   allocations and current locals by the allocation-run boundary. *)
Theorem reason_encoder_allocated_store_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc inst b sz a w.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_id <= cc.cs_next_id /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= a /\ a + 32 <= b + sz /\
    (!aid off len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      regions_disjoint b sz off len) /\
    (!name off len. local_region cenv es'.scopes s name off len ==>
      regions_disjoint b sz off len) /\
    expr_val_rel cx (expr_type e) v op (mstore a w s) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op (mstore a w s)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' (mstore a w s)` by
    (irule literal_mstore_state_rel >> reverse conj_tac
     >- gvs[expr_post_def] >>
     qexistsl_tac [`b`, `inst`, `sz`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!name off len. _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `locals_kept cenv es s0 (mstore a w s)` by suspend "locals" >>
  gvs[expr_post_def, reason_encoder_store_value_location] >>
  rpt strip_tac >>
  `regions_disjoint b sz off sz'` by
    (qpat_x_assum `!aid off len. aid < cc.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `mem_bytes_at off sz' (mstore a w s).vs_memory =
   mem_bytes_at off sz' s.vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >> simp[]) >>
  simp[] >> qpat_x_assum `!aid off sz. _` irule >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  qexists_tac `aid` >> simp[]
QED

Resume reason_encoder_allocated_store_post[locals]:
  `!name off len. local_region cenv es.scopes s0 name off len ==>
     regions_disjoint b sz off len` by
    (rpt strip_tac >>
     `local_region cenv es'.scopes s name off len` by
       (drule_all reason_encoder_original_local_region >> simp[]) >> metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >>
  gvs[expr_post_def] >> rpt strip_tac >>
  irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >> simp[] >>
  metis_tac[]
QED

Finalise reason_encoder_allocated_store_post

(* Unlike normalizationAllocPtr's endpoint-specific wrapper, this boundary
   keeps the original expression interval while compilation advances at cc. *)
Theorem reason_encoder_alloc_buffer_resources:
  !ctx func cenv cx e es sa sb s0 es' v op s cc cd buf n tv ow PG G tn.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    (!p. op = Var p ==> not_fresh_at cc p) /\ local_ptrs_reserved cenv cc /\
    fn_inst_ids_distinct func /\ n < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var /\ sb.cs_next_id <= cc.cs_next_id /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\
    eval_operand op s = SOME ow /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n ow) m) ==>
    ?t out i b G1 tn1.
      buf.buf_operand = Var out /\
      i = mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out] /\
      step_inst_base i s = OK t /\
      G1 = step_prov PG G i t /\ tn1 = step_taint i s t tn /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      local_ptrs_reserved cenv cd /\
      eval_operand op t = SOME ow /\
      eval_operand (Var out) t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas cc.cs_next_id = SOME (b,n) /\
      b + n < dimword (:256) /\ ptr_covers G1 tn1 out t n /\
      (!aid off len. aid < cc.cs_next_id /\
        FLOOKUP t.vs_allocas aid = SOME (off,len) ==>
        regions_disjoint b n off len) /\
      (!name off len. local_region cenv es'.scopes t name off len ==>
        regions_disjoint b n off len) /\
      (!j. w2n ow <= j /\ j < w2n ow + val_footprint tv v ==>
        ~(b <= j /\ j < b+n)) /\
      (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n ow) m) /\
      (!p k. p <> out /\ ptr_covers G tn p s k ==> ptr_covers G1 tn1 p t k) /\
      MEM i (fn_insts func) /\ not_local_ptr cenv es'.scopes out /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 t) /\
      (!p. p <> out ==> FLOOKUP G1 p = FLOOKUP G p /\
        op_taint tn1 (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reason_encoder_alloc_buffer_post >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by gvs[expr_post_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `expr_val_at cenv cx (expr_type e) sa sb es' v op s` by gvs[expr_post_def] >>
  `not_local_ptr cenv es'.scopes (STRING #"%" (toString cc.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `cc` >> simp[]) >>
  qexistsl_tac [`t`, `STRING #"%" (toString cc.cs_next_var)`,
    `mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString cc.cs_next_var)]`, `w2n w`,
    `step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString cc.cs_next_var)]) t`,
    `step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString cc.cs_next_var)]) s t tn`] >>
  asm_rewrite_tac[wordsTheory.n2w_w2n] >>
  rpt conj_tac
  >- metis_tac[]
  >- (drule_all alloca_step_ptr_covers >> simp[])
  >- suspend "sites"
  >- suspend "separation"
  >- suspend "robust"
  >- suspend "oldptr"
  >- (strip_tac >> drule_all alloca_step_stor_taint_ok >> simp[expr_post_def]) >>
  gen_tac >> disch_tac >> drule_all reason_alloca_old_metadata >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]
QED

Resume reason_encoder_alloc_buffer_resources[sites]:
  rpt gen_tac >> strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
     gvs[AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  qpat_x_assum `!aid b len. aid < cc.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `aid` >> simp[]
QED

Resume reason_encoder_alloc_buffer_resources[separation]:
  rpt gen_tac >> strip_tac >> irule alloca_step_expr_disjoint >>
  metis_tac[]
QED

Resume reason_encoder_alloc_buffer_resources[robust]:
  drule_at (Pat `step_inst_base _ _ = _`) alloca_step_expr_robust_preserved >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspec_then `tn` mp_tac) >> simp[]
QED

Resume reason_encoder_alloc_buffer_resources[oldptr]:
  rpt strip_tac >> irule alloca_step_old_ptr_covers >>
  simp[] >> qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >> simp[]
QED

Finalise reason_encoder_alloc_buffer_resources

(* Rebuild the ordinary expression value from the stronger robust memory
   resource after a separated encoder store. *)
Theorem reason_encoder_store_value:
  !cx ty tv v op ow s tn dst value a w.
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME ow /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} /\
    val_wf tv v /\
    (!i. w2n ow <= i /\ i < w2n ow + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n ow) m) ==>
    expr_val_rel cx ty v op (mstore (w2n a) w s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lookup_var _ _ = _`) reason_encoder_store_robust_preserved >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (qspecl_then
    [`0`, `w2n ow`, `(mstore (w2n a) w s).vs_memory`] mp_tac) >>
  simp[mem_agree_outside_def] >> strip_tac >>
  simp[expr_val_rel_def, eval_operand_def, lookup_var_def,
       mstore_def, write_memory_with_expansion_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def,
    mstore_def, write_memory_with_expansion_def]
QED

Theorem reason_encoder_allocated_store_resources:
  !ctx func cenv cx e es sa sb s0 es' v op s cc inst b sz
    dst value a addr u w tv ow tn id.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_id <= cc.cs_next_id /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    w2n a = addr /\ u = mstore addr w s /\
    b <= addr /\ addr + 32 <= b + sz /\
    (!aid off len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      regions_disjoint b sz off len) /\
    (!name off len. local_region cenv es'.scopes s name off len ==>
      regions_disjoint b sz off len) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\
    eval_operand op s = SOME ow /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} /\
    (!i. w2n ow <= i /\ i < w2n ow + val_footprint tv v ==>
      ~(b <= i /\ i < b + sz)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n ow) m) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
    (!m. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s u tn).t_mem
      u.vs_memory m ==>
      val_in_memory tv v (w2n ow) m)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `w2n a = addr` (assume_tac o GSYM) >>
  qpat_x_assum `addr = _` SUBST_ALL_TAC >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  `!i. w2n ow <= i /\ i < w2n ow + val_footprint tv v ==>
     ~(w2n a <= i /\ i < w2n a + 32)` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `expr_val_rel cx (expr_type e) v op (mstore (w2n a) w s)` by
    (irule reason_encoder_store_value >> metis_tac[]) >>
  conj_tac
  >- (irule reason_encoder_allocated_store_post >> simp[] >>
      qexistsl_tac [`b`, `cc`, `inst`, `sz`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule reason_encoder_store_robust_preserved >> metis_tac[]
QED

(* First compiler consumer of the allocation and store resource boundaries. *)
Theorem reason_encoder_selector_resources:
  !ctx func cenv cx e es sa sb s0 es' v op s cc c1 c2 buf n tv ow PG G tn.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,c1) /\ fn_has_code cc c1 func /\
    emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
    (!p. op = Var p ==> not_fresh_at cc p) /\ local_ptrs_reserved cenv cc /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    fn_inst_ids_distinct func /\ 32 <= n /\ n < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var /\
    sa.cs_next_id <= cc.cs_next_id /\ sb.cs_next_id <= cc.cs_next_id /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\
    eval_operand op s = SOME ow /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n ow) m) ==>
    ?t out b G1 tn1 u tn2.
      buf.buf_operand = Var out /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
      G1 = step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t /\
      tn1 = step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn /\
      eval_operand (Var out) t = SOME (n2w b) /\ b + n < dimword (:256) /\
      u = mstore b 0x08c379a0w t /\
      run_inst_seq (emitted_insts c1 c2) t = OK u /\
      step_inst_base (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) t = OK u /\
      tn2 = step_taint (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) t u tn1 /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
      local_ptrs_reserved cenv c2 /\
      eval_operand op u = SOME ow /\
      step_prov PG G1 (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) u = G1 /\
      ptr_covers G1 tn2 out u n /\
      (!p k. p <> out /\ ptr_covers G tn p s k ==> ptr_covers G1 tn2 p u k) /\
      (!m. mem_agree_outside tn2.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n ow) m) /\
      (!p. p <> out ==> FLOOKUP G1 p = FLOOKUP G p /\
        op_taint tn2 (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reason_encoder_alloc_buffer_resources >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `lookup_var out t = SOME (n2w b)` by gvs[eval_operand_def] >>
  `eval_operand buf.buf_operand t = SOME (n2w b)` by simp[] >>
  `run_inst_seq (emitted_insts c1 c2) t = OK (mstore b 0x08c379a0w t)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     `step_inst_base (mk_inst c1.cs_next_id MSTORE
        [Var out; Lit 0x08c379a0w] []) t = OK (mstore b 0x08c379a0w t)` by
       (qpat_assum `w2n (n2w b : bytes32) = b`
          (fn th => once_rewrite_tac[GSYM th]) >>
        irule step_MSTORE >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op (mstore b 0x08c379a0w t) /\
   (!m. mem_agree_outside
     (step_taint (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
       t (mstore b 0x08c379a0w t) tn1).t_mem
     (mstore b 0x08c379a0w t).vs_memory m ==>
     val_in_memory tv v (w2n ow) m)` by suspend "post" >>
  suspend "finish"
QED

Resume reason_encoder_selector_resources[finish]:
  `local_ptrs_reserved cenv c2` by suspend "reserved" >>
  `eval_operand (Lit 0x08c379a0w) t = SOME 0x08c379a0w /\
   op_taint tn1 (Lit 0x08c379a0w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G1`, `c1.cs_next_id`] mp_tac) >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  `!p k. ptr_covers G1 tn1 p t k ==>
    ptr_covers G1
      (step_taint (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
        t (mstore b 0x08c379a0w t) tn1) p (mstore b 0x08c379a0w t) k` by
    (rpt strip_tac >> gvs[ptr_covers_def, op_taint_def, lookup_var_def,
      mstore_def, write_memory_with_expansion_def]) >>
  qexistsl_tac [`t`, `out`, `b`, `G1`, `tn1`, `mstore b 0x08c379a0w t`,
    `step_taint (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [])
      t (mstore b 0x08c379a0w t) tn1`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[]
  >- (qpat_assum `w2n (n2w b : bytes32) = b`
        (fn th => once_rewrite_tac[GSYM th]) >>
      irule step_MSTORE >> simp[eval_operand_def])
  >- simp[eval_operand_mstore]
  >- metis_tac[] >>
  gvs[op_taint_def] >> metis_tac[]
QED

Resume reason_encoder_selector_resources[post]:
  `MEM i (fn_insts func)` by
    (drule_all buffer_alloc_code >> strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  irule reason_encoder_allocated_store_resources >>
  simp[op_taint_def, eval_operand_def] >>
  qexistsl_tac [`b`, `cc`, `i`, `n`] >>
  simp[mk_inst_def] >> metis_tac[]
QED

Resume reason_encoder_selector_resources[reserved]:
  irule local_ptrs_reserved_next_var >> qexists_tac `c1` >> simp[] >>
  drule emitted_insts_emit_void >> simp[]
QED

Finalise reason_encoder_selector_resources

(* Read-only encoder arithmetic writes a fresh compiler temporary. *)
Theorem reason_encoder_fresh_update_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc x w.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv cc /\ sa.cs_next_var <= cc.cs_next_var /\
    ~not_fresh_at cc x /\
    eval_operand op (update_var x w s) = eval_operand op s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op (update_var x w s)
Proof
  rpt gen_tac >> strip_tac >>
  `not_local_ptr cenv es'.scopes x` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  irule reason_encoder_readonly_post >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> gvs[expr_post_def]) >>
  qexistsl_tac [`cc`, `s`] >> simp[update_var_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> `x <> x'` by metis_tac[] >>
      gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  simp[local_region_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[not_local_ptr_def] >> metis_tac[]
QED

Theorem reason_encoder_add_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc cd src result a d.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv cc /\ sa.cs_next_var <= cc.cs_next_var /\
    emit_op ADD [src; Lit d] cc = (result,cd) /\
    eval_operand src s = SOME a /\
    (!z. op = Var z ==> not_fresh_at cc z) ==>
    ?t x. result = Var x /\ ~not_fresh_at cc x /\
      t = update_var x (a + d) s /\
      step_inst_base (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s = OK t /\
      run_inst_seq (emitted_insts cc cd) s = OK t /\
      eval_operand result t = SOME (a + d) /\
      local_ptrs_reserved cenv cd /\
      eval_operand op t = eval_operand op s /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      (!PG G tn.
        (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s t tn).t_mem = tn.t_mem /\
        (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s t tn).t_stor = tn.t_stor /\
        (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s t tn).t_trans = tn.t_trans /\
        (!p. p <> x ==>
          FLOOKUP (step_prov PG G (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) t) p = FLOOKUP G p /\
          op_taint (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s t tn) (Var p) = op_taint tn (Var p)) /\
        (!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
          ptr_covers
            (step_prov PG G (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) t)
            (step_taint (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s t tn) p t k))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `result = Var x` >>
  `~not_fresh_at cc x` by simp[Abbr `x`, not_fresh_at_def] >>
  `step_inst_base (mk_inst cc.cs_next_id ADD [src; Lit d] [x]) s =
    OK (update_var x (a + d) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts cc cd) s = OK (update_var x (a + d) s)` by
    simp[run_inst_seq_def] >>
  `eval_operand (Lit d) s = SOME d` by simp[eval_operand_def] >>
  `eval_operand op (update_var x (a + d) s) = eval_operand op s` by
    (Cases_on `op` >> simp[eval_operand_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >> simp[]) >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op
     (update_var x (a + d) s)` by
    (irule reason_encoder_fresh_update_post >> simp[] >>
     qexists_tac `cc` >> simp[]) >>
  qexistsl_tac [`update_var x (a + d) s`, `x`] >>
  simp[copy_len_binop_ghost_frame, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> suspend "ghost"
QED

Resume reason_encoder_add_post[ghost]:
  rpt gen_tac >> rpt conj_tac >>
  rpt strip_tac >> `p <> x` by metis_tac[] >>
  gvs[ptr_covers_def, SRULE [update_var_def] copy_len_binop_ghost_frame,
      lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Finalise reason_encoder_add_post

(* Offset arithmetic inherits the input allocation site, including at zero. *)
Theorem reason_encoder_offset_covers:
  !PG G tn s id root out a total off k.
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    off + k <= total /\ w2n a + off < dimword (:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
        (update_var out (a + n2w off) s))
      (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
        (update_var out (a + n2w off) s) tn)
      out (update_var out (a + n2w off) s) k
Proof
  rpt gen_tac >> strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  gvs[ptr_covers_def] >>
  simp[copy_len_binop_ghost_frame, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, wordsTheory.w2n_add_2,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

(* The original source interval survives all four prefix operations. *)
Theorem reason_encoder_prefix_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc c1 c2 c3 c4 buf payload tuple n m tv ow PG G tn.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,c1) /\ fn_has_code cc c1 func /\
    emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
    emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
    compile_alloc_buffer m c3 = (tuple,c4) /\ fn_has_code c3 c4 func /\
    local_ptrs_reserved cenv cc /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    fn_inst_ids_distinct func /\ 32 <= n /\ n < dimword (:256) /\
    m < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var /\
    sa.cs_next_id <= cc.cs_next_id /\ sb.cs_next_id <= cc.cs_next_id /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\
    eval_operand op s = SOME ow /\
    (!z. op = Var z ==> not_fresh_at cc z) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n ow) mem) ==>
    ?t out b G1 tn1 u tn2 r x z out2 b2 G2 tn3 G3 tn4.
      buf.buf_operand = Var out /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
      G1 = step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t /\
      tn1 = step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn /\
      u = mstore b 0x08c379a0w t /\
      run_inst_seq (emitted_insts c1 c2) t = OK u /\
      tn2 = step_taint (mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] []) t u tn1 /\
      payload = Var x /\
      r = update_var x (n2w b + 32w) u /\
      run_inst_seq (emitted_insts c2 c3) u = OK r /\
      tuple.buf_operand = Var out2 /\
      eval_operand buf.buf_operand z = SOME (n2w b) /\
      eval_operand payload z = SOME (n2w b + 32w) /\
      b + n < dimword (:256) /\
      step_inst_base (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) r = OK z /\
      eval_operand tuple.buf_operand z = SOME (n2w b2) /\
      FLOOKUP z.vs_allocas c3.cs_next_id = SOME (b2,m) /\
      b2 + m < dimword (:256) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op z /\
      local_ptrs_reserved cenv c4 /\
      eval_operand op z = SOME ow /\
      G2 = step_prov PG G1 (mk_inst c2.cs_next_id ADD [buf.buf_operand; Lit 32w] [x]) r /\
      tn3 = step_taint (mk_inst c2.cs_next_id ADD [buf.buf_operand; Lit 32w] [x]) u r tn2 /\
      G3 = step_prov PG G2 (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) z /\
      tn4 = step_taint (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) r z tn3 /\
      ptr_covers G3 tn4 out2 z m /\
      ptr_covers G3 tn4 out z n /\ ptr_covers G3 tn4 x z (n - 32) /\
      (!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
        ptr_covers G3 tn4 p z k) /\
      (!mem. mem_agree_outside tn4.t_mem z.vs_memory mem ==>
        val_in_memory tv v (w2n ow) mem) /\
      MEM (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) (fn_insts func) /\
      not_local_ptr cenv es'.scopes out2 /\
      (!p. not_fresh_at cc p ==> FLOOKUP G3 p = FLOOKUP G p /\
        op_taint tn4 (Var p) = op_taint tn (Var p)) /\
      op_prov G3 op = op_prov G op /\ op_taint tn4 op = op_taint tn op
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reason_encoder_selector_resources >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `cc.cs_next_var <= c2.cs_next_var /\ cc.cs_next_id <= c2.cs_next_id` by
    suspend "counters" >>
  `eval_operand buf.buf_operand u = SOME (n2w b)` by
    simp[eval_operand_mstore] >>
  `!z. op = Var z ==> not_fresh_at c2 z` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `sa.cs_next_var <= c2.cs_next_var` by decide_tac >>
  drule_all reason_encoder_add_post >> strip_tac >>
  suspend "allocate"
QED

Resume reason_encoder_prefix_post[counters]:
  qpat_assum `compile_alloc_buffer n cc = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  drule emitted_insts_emit_void >> strip_tac >> simp[]
QED

Resume reason_encoder_prefix_post[allocate]:
  qexistsl_tac [`t`, `out`, `b`, `G1`, `tn1`, `u`, `tn2`, `t'`, `x`] >>
  pure_asm_rewrite_tac[] >>
  `sa.cs_next_var <= c3.cs_next_var` by
    (drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  `sb.cs_next_id <= c3.cs_next_id` by
    (drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  qabbrev_tac `ai = mk_inst c2.cs_next_id ADD [buf.buf_operand; Lit 32w] [x]` >>
  qabbrev_tac `G2 = step_prov PG G1 ai t'` >>
  qabbrev_tac `tn3 = step_taint ai u t' tn2` >>
  `eval_operand op t' = SOME ow` by simp[] >>
  `!mem. mem_agree_outside tn3.t_mem t'.vs_memory mem ==>
     val_in_memory tv v (w2n ow) mem` by
    (simp[Abbr `tn3`, Abbr `ai`] >> metis_tac[]) >>
  `not_fresh_at c2 out` by suspend "out_fresh" >>
  `ptr_covers G2 tn3 out t' n` by suspend "buffer" >>
  `ptr_covers G2 tn3 x t' (n - 32)` by suspend "payload" >>
  `!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
     ptr_covers G2 tn3 p t' k` by suspend "oldptr" >>
  `!p. op = Var p ==> not_fresh_at c3 p` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (mp_then Any mp_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
      reason_encoder_alloc_buffer_resources)) >>
  rpt (disch_then drule) >>
  disch_then (qspecl_then [`PG`, `G2`] strip_assume_tac) >>
  `out <> out' /\ x <> out' /\
   (!p. not_fresh_at cc p ==> p <> out')` by suspend "distinct" >>
  `ptr_covers G1' tn1' out t'' n /\
   ptr_covers G1' tn1' x t'' (n - 32) /\
   (!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
     ptr_covers G1' tn1' p t'' k)` by metis_tac[] >>
  `eval_operand (Var out) t'' = SOME (n2w b) /\
   eval_operand (Var x) t'' = SOME (n2w b + 32w)` by suspend "addresses" >>
  `!p. not_fresh_at cc p ==> FLOOKUP G1' p = FLOOKUP G p /\
    op_taint tn1' (Var p) = op_taint tn (Var p)` by suspend "metadata" >>
  `op_prov G1' op = op_prov G op /\ op_taint tn1' op = op_taint tn op` by
    (Cases_on `op` >> simp[op_prov_def, op_taint_def] >> metis_tac[]) >>
  qexistsl_tac [`t''`, `out'`, `b'`, `G2`, `tn3`, `G1'`, `tn1'`] >>
  pure_asm_rewrite_tac[] >>
  qpat_x_assum `t' = update_var _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `u = mstore _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `i = mk_inst _ _ _ _` SUBST_ALL_TAC >>
  simp[Abbr `G2`, Abbr `tn3`, Abbr `ai`]
QED

Resume reason_encoder_prefix_post[distinct]:
  qpat_assum `compile_alloc_buffer n cc = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Resume reason_encoder_prefix_post[out_fresh]:
  qpat_assum `compile_alloc_buffer n cc = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[not_fresh_at_def]
QED

Resume reason_encoder_prefix_post[buffer]:
  simp[Abbr `G2`, Abbr `tn3`] >>
  qpat_x_assum `!PG G tn. _` (qspecl_then [`PG`, `G1`, `tn2`] mp_tac) >>
  simp[]
QED

Resume reason_encoder_prefix_post[payload]:
  `lookup_var out u = SOME (n2w b)` by
    (qpat_x_assum `eval_operand buf.buf_operand u = _` mp_tac >>
     simp[eval_operand_def]) >>
  `w2n (n2w b : bytes32) + 32 < dimword (:256)` by simp[] >>
  simp[Abbr `G2`, Abbr `tn3`, Abbr `ai`] >>
  qpat_x_assum `t' = update_var _ _ _` SUBST_ALL_TAC >>
  pure_asm_rewrite_tac[] >>
  irule reason_encoder_offset_covers >> simp[] >>
  conj_tac >- metis_tac[eval_operand_def] >>
  qexists_tac `n` >> simp[] >> metis_tac[]
QED

Resume reason_encoder_prefix_post[oldptr]:
  rpt strip_tac >>
  `not_fresh_at c2 p` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `p <> out` by
    (qpat_assum `compile_alloc_buffer n cc = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
     gvs[not_fresh_at_def] >> metis_tac[]) >>
  `ptr_covers G1 tn2 p u k` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `tn3`] >>
  qpat_x_assum `!PG G tn. _` (qspecl_then [`PG`, `G1`, `tn2`] mp_tac) >>
  simp[]
QED

Resume reason_encoder_prefix_post[addresses]:
  `out <> x` by metis_tac[] >>
  `eval_operand (Var out) t' = SOME (n2w b)` by
    (qpat_x_assum `t' = update_var _ _ _` SUBST1_TAC >>
     simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     qpat_x_assum `eval_operand buf.buf_operand u = _` mp_tac >>
     simp[eval_operand_def, lookup_var_def]) >>
  `eval_operand (Var x) t' = SOME (n2w b + 32w)` by metis_tac[] >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  `out' = STRING #"%" (toString c3.cs_next_var)` by gvs[] >>
  `!operand. (!p. operand = Var p ==> p <> out') ==>
     eval_operand operand t'' = eval_operand operand t'` by
    (rpt strip_tac >> irule alloca_step_operand_preserved >>
     qexistsl_tac [`c3.cs_next_id`, `m`, `out'`] >> gvs[]) >>
  simp[]
QED

Resume reason_encoder_prefix_post[metadata]:
  gen_tac >> disch_tac >>
  qpat_assum `compile_alloc_buffer n cc = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  `not_fresh_at c2 p /\ not_fresh_at c3 p` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `p <> out /\ p <> x /\ p <> out'` by (gvs[] >> metis_tac[]) >>
  `FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `FLOOKUP G2 p = FLOOKUP G1 p /\ op_taint tn3 (Var p) = op_taint tn2 (Var p)` by
    (simp[Abbr `G2`, Abbr `tn3`, Abbr `ai`] >>
     qpat_x_assum `!PG G tn. _` (qspecl_then [`PG`, `G1`, `tn2`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

Finalise reason_encoder_prefix_post
