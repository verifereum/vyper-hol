(* Transport a physical expression post to a normalized result, retaining
   the original expression-entry frame. *)
Theory exprSimIfExpWidenedPosts
Ancestors
  loweringPosts placeMemoryProtectedFrame exprLoweringProps

Theorem normalized_expr_post_frame:
  expr_post ctx func ce cx e es sa sm s0 ee v src s /\
  post_value_type ce out = expr_type out /\
  stmt_state_rel ctx func ce cx ee q /\
  expr_val_rel cx (expr_type out) v dst q /\
  expr_val_at ce cx (expr_type out) sa sb ee v dst q /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP q.vs_allocas aid = SOME entry) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id /\
    (!n b sz. local_region ce es.scopes s0 n b sz ==>
      off+len <= b \/ b+sz <= off) ==>
    mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (~expr_has_effect out ==> pure_frame ce func es sa s0 q) /\
  locals_kept ce es ee s0 q ==>
  expr_post ctx func ce cx out es sa sb s0 ee v dst q
Proof
  rewrite_tac[expr_post_def] >> strip_tac >> asm_rewrite_tac[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  qpat_x_assum `!aid off len. _ ==> mem_bytes_at _ _ q.vs_memory = _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then SUBST1_TAC >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `aid` >> asm_rewrite_tac[]
QED

(* Validate the reused-allocation alternative at the allocation endpoint.
   No pre-allocation freshness claim is needed for constructor separation. *)
Theorem allocated_result_immutable_disjoint[local]:
  compile_alloc_buffer N sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx ee u /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,N) ==>
  off + type_memory_size tv <= w2n w \/ w2n w + N <= off
Proof
  strip_tac >>
  `immutable_alloca_sep func ce cx ee u` by fs[stmt_state_rel_def] >>
  irule compile_alloc_buffer_immutable_disjoint >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
  asm_rewrite_tac[] >> goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Theorem allocated_result_expr_post_frame:
  expr_post ctx func ce cx e es origin sm s0 ee v src s /\
  post_value_type ce out = expr_type out /\
  stmt_state_rel ctx func ce cx ee q /\
  expr_val_rel cx (expr_type out) v dst q /\
  eval_operand dst q = SOME w /\
  FLOOKUP q.vs_allocas aid = SOME (b,N) /\
  (~expr_has_effect out ==> ~expr_has_effect e) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\
  (!tv. evaluate_type (get_tenv cx) (expr_type out) = SOME tv /\
    ~is_word_type (expr_type out) ==>
    val_wf tv v /\ w2n w + val_footprint tv v <= b + N) /\
  (!n lb len. local_region ce ee.scopes s n lb len ==>
    b + N <= lb \/ lb + len <= b) /\
  (!n lb len. local_region ce ee.scopes q n lb len ==>
    local_region ce ee.scopes s n lb len) /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
    local_region ce ee.scopes s n lb len) /\
  (!old off len. FLOOKUP s0.vs_allocas old = SOME (off,len) /\
    old < origin.cs_next_id ==> b + N <= off \/ off + len <= b) /\
  (!x. not_fresh_at origin x ==> lookup_var x q = lookup_var x s) /\
  (!old entry. FLOOKUP s.vs_allocas old = SOME entry ==>
    FLOOKUP q.vs_allocas old = SOME entry) /\
  (!off len. b + N <= off \/ off + len <= b ==>
    mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  expr_post ctx func ce cx out es origin sb s0 ee v dst q
Proof
  strip_tac >>
  `expr_val_at ce cx (expr_type out) origin sb ee v dst q` by
    (simp[expr_val_at_def] >> rpt strip_tac >>
     disj1_tac >>
     qexistsl_tac [`aid`, `b`, `N`] >> simp[] >>
     rpt strip_tac >>
     `local_region ce ee.scopes s n lb lsz` by metis_tac[] >>
     qpat_x_assum `!n lb len. local_region _ _ s _ _ _ ==> _` drule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule normalized_expr_post_frame >> disch_then irule >> simp[] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid' = SOME (off,len)` by metis_tac[] >>
      `b + N <= off \/ off + len <= b` by metis_tac[] >>
      metis_tac[]) >>
  conj_tac
  >- (strip_tac >>
      irule exprSimPropsTheory.pure_frame_buffer_tail >>
      qexistsl_tac [`b`, `N`, `inst`, `s`] >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
      conj_tac
      >- (rpt strip_tac >>
          `local_region ce ee.scopes s n lb lsz` by metis_tac[] >>
          qpat_x_assum `!n lb len. local_region _ _ s _ _ _ ==> _` drule >>
          simp[arithmeticTheory.ADD_COMM]) >>
      rpt strip_tac >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at off len q.vs_memory = _` irule >>
      decide_tac) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists_tac `s` >> asm_rewrite_tac[] >> rpt strip_tac >>
  `local_region ce ee.scopes s n b' sz` by metis_tac[] >>
  `b + N <= b' \/ b' + sz <= b` by metis_tac[] >>
  metis_tac[]
QED
