(* Frame-only composition: digest operands are not memory-value posts. *)
Theory bodyMemBopHeldPost
Ancestors
  exprBopSimProps exprLoweringProps compileEnv loweringPosts vyperAST
  exprSimProps valueEncoding localPtrsProps emitHelperProps
  loweringSlice freshWrites venomExecSemantics

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
  `bool_to_word b = if b then 1w else 0w` by
    (Cases_on `b` >> simp[bool_to_word_def]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
    expr_type_def, is_word_type_def, typed_val_to_w256_word_value,
    word_value_def, val_to_w256_def, bool_to_word_def] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      `not_fresh_at s2 z` by
        (irule not_fresh_at_mono >> qexists_tac `s1` >> asm_rewrite_tac[]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      disch_then irule >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
          qexists_tac `n` >> irule local_region_frame >>
          conj_tac >- (qexists_tac `func` >>
            gvs[stmt_state_rel_def, state_rel_def]) >>
          qexistsl_tac [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[])
      >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
          qexists_tac `sa.cs_next_id` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  irule locals_kept_mem_tail >> qexists_tac `u` >> simp[] >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
