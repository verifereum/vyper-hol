(* Frame-only composition: digest operands are not memory-value posts. *)
Theory bodyMemBopHeldPost
Ancestors
  exprBopSimProps exprLoweringProps compileEnv loweringPosts vyperAST
  exprSimProps valueEncoding localPtrsProps emitHelperProps
  loweringSlice freshWrites venomExecSemantics exprSimWordArgs

Theorem held_digest_compare_post:
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
               off + sz <= b \/ b + sz' <= off) ==>
    mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es s0 t /\
  (!x w. not_fresh_at s1 x /\ lookup_var x t = SOME w ==>
         lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  (!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\
    aid < s1.cs_next_id /\
    (!n b sz'. local_region cenv es1.scopes t n b sz' ==>
               off + sz <= b \/ b + sz' <= off) ==>
    mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory) /\
  locals_kept cenv es1 t u /\
  stmt_state_rel ctx func cenv cx ee ss /\
  eval_operand op ss = SOME (bool_to_word b) /\
  (!z. not_fresh_at s2 z ==> lookup_var z ss = lookup_var z u) /\
  ss.vs_memory = u.vs_memory /\ ss.vs_allocas = u.vs_allocas /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id ==>
  expr_post ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee (BoolV b) op ss
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es1 s1 t u` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es sa s0 u` by
    (mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`,
       `es1`, `s1`, `t`, `u`, `ctx`] wb_frame_trans) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `wb_frame cenv es sa s0 ss` by
    (mp_tac (Q.SPECL [`cenv`, `es`, `sa`, `s0`, `u`, `s2`, `ss`]
       wb_frame_readonly_tail) >>
     impl_tac >- (simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  irule expr_post_word_intro >>
  simp[expr_type_def, is_word_type_def, word_value_def, val_to_w256_def,
       bool_to_word_def] >> Cases_on `b` >> simp[bool_to_word_def]
QED
