(* Default expressions can allocate scratch without overwriting argument owners. *)
Theory groupedKeywordOwners
Ancestors
  loweringPosts bodyPtrDefs
  appendStorageGhostPtr robustCopyTransportPtr exprLoweringProps loweringStateRelDefs
  compileEnv venomState finite_map arithmetic

Theorem grouped_keyword_expr_owner_frame:
  expr_post H ctx fn (ce with ce_vars := FEMPTY) cx e es sa sb s ee v op t /\
  ghost_kept_at lo (ce with ce_vars := FEMPTY) es sa G tn s G1 tn1 /\
  ci_mono sa sb /\ not_fresh_at sa p /\
  oid < sa.cs_next_id /\ FLOOKUP s.vs_allocas oid = SOME (b,n) /\
  lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s n /\
  val_wf tv x /\ val_footprint tv x <= n /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv x b mem) ==>
  oid < sb.cs_next_id /\ FLOOKUP t.vs_allocas oid = SOME (b,n) /\
  lookup_var p t = SOME (n2w b) /\ ptr_covers G1 tn1 p t n /\
  (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
    val_in_memory tv x b mem)
Proof
  strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_post_def]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
  `!id b z. ~local_region (ce with ce_vars := FEMPTY) es.scopes s id b z` by
    simp[local_region_def, FLOOKUP_EMPTY] >>
  `oid < sb.cs_next_id` by fs[ci_mono_def] >>
  `FLOOKUP t.vs_allocas oid = SOME (b,n)` by metis_tac[] >>
  `lookup_var p t = SOME (n2w b)` by metis_tac[] >>
  `FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p)` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `lookup_var p t = lookup_var p s` by asm_rewrite_tac[] >>
  `ptr_covers G1 tn1 p t n` by
    (pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var p t = lookup_var p s` (pure_rewrite_tac o single) >>
     qpat_assum `FLOOKUP G1 p = FLOOKUP G p` (pure_rewrite_tac o single) >>
     qpat_assum `op_taint tn1 (Var p) = op_taint tn (Var p)` (pure_rewrite_tac o single) >>
     qpat_assum `ptr_covers G tn p s n` (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
  `mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by
    (qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`oid`,`b`,`n`] mp_tac) >> simp[]) >>
  `!i. i < n /\ b+i IN tn1.t_mem ==> b+i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`oid`,`b`,`n`,`b+i`] mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`tv`,`x`,`b`,`b`,`n`,`tn.t_mem`,`tn1.t_mem`,
                  `s.vs_memory`,`t.vs_memory`] robust_val_in_memory_decreasing_taint_transport) >>
  impl_tac >- asm_rewrite_tac[] >> disch_then (qspec_then `mem` mp_tac) >>
  asm_rewrite_tac[]
QED
