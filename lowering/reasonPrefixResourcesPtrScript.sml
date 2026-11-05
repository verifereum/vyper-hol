(* Resource transport across the reason encoder's allocation prefix. *)
Theory reasonPrefixResourcesPtr
Ancestors
  reasonBufferPtr allocationPtr normalizationAllocPtr robustCopyTransportPtr typedCopyPtr
  bodyPtrDefs ptrDiscipline venomState venomInst pred_set arithmetic
  loweringPosts compileEnv exprLoweringProps exprSimProps exprSimAlloc emitHelperProps exprSimHash loweringHalt venomExecSemantics

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
  `expr_val_at cenv cx (expr_type e) sa sb es' v op t` by
    (irule reason_encoder_value_location_frame >>
     qexists_tac `s` >> gvs[expr_post_def]) >>
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
    fresh_vars_wrt cc s /\ local_ptrs_reserved cenv cc /\
    fn_inst_ids_distinct func /\ n < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var ==>
    ?t w. run_inst_seq (emitted_insts cc cd) s = OK t /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString cc.cs_next_var)]) s = OK t /\
      fresh_vars_wrt cd t /\ local_ptrs_reserved cenv cd /\
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
  `fresh_vars_wrt cd t` by suspend "fresh" >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> asm_rewrite_tac[]
QED

Resume reason_encoder_alloc_buffer_post[operand]:
  `?ow. eval_operand op s = SOME ow` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[eval_operand_def] >>
  rename1 `lookup_var x s = SOME ow` >>
  `not_fresh_at cc x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     gvs[fresh_vars_wrt_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     metis_tac[]) >>
  metis_tac[]
QED

Resume reason_encoder_alloc_buffer_post[locals]:
  rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >> conj_tac
      >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`cc`, `es'.scopes`, `t`] >> simp[]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `cc`, `es'.scopes`] >> simp[]
QED

Resume reason_encoder_alloc_buffer_post[fresh]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[fresh_vars_wrt_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Finalise reason_encoder_alloc_buffer_post

(* The store is confined to an allocated buffer, separated from the old
   allocations and current locals by the allocation-run boundary. *)
Theorem reason_encoder_allocated_store_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc inst b sz a w.
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
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    fresh_vars_wrt cc s /\ local_ptrs_reserved cenv cc /\
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
      fresh_vars_wrt cd t /\ local_ptrs_reserved cenv cd /\
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
      (!p k. ptr_covers G tn p s k ==> ptr_covers G1 tn1 p t k) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 t)
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
  >- suspend "oldptr" >>
  strip_tac >> drule_all alloca_step_stor_taint_ok >> simp[expr_post_def]
QED

Resume reason_encoder_alloc_buffer_resources[sites]:
  rpt gen_tac >> strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
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
  `lookup_var (STRING #"%" (toString cc.cs_next_var)) s = NONE` by
    gvs[fresh_vars_wrt_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
  conj_tac
  >- (strip_tac >> gvs[ptr_covers_def]) >>
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
    dst value a w tv ow tn id.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_id <= cc.cs_next_id /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n a /\ w2n a + 32 <= b + sz /\
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
    expr_post ctx func cenv cx e es sa sb s0 es' v op
      (mstore (w2n a) w s) /\
    (!m. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory m ==>
      val_in_memory tv v (w2n ow) m)
Proof
  rpt gen_tac >> strip_tac >>
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
