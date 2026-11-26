(* Linked value-post endpoint for the Len word result. *)
Theory bodyLenVvPostMods
Ancestors
  bodyFullPostsMods exprSimLen
  loweringPosts loweringStateRelDefs exprLoweringProps
  bodySimFull bodyPtrDefs compileEnv exprSimProps
  freshWrites loweringShapeDefs
  vyperInterpreter vyperState vyperAST vyperContext vyperValue valueEncoding
  finite_map list pair option

Theorem len_vv_post_load_mods:
  !func cenv cx e es sa sm sb s0 es' tv vv s1 op s n ctx.
    vv_post_mods H ctx func cenv cx e es sa sm s0 es' tv vv s1 /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel H ctx func cenv cx es' s /\
    eval_operand op s = SOME (n2w n) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    vv_post H ctx func cenv cx
      (Builtin (BaseT (UintT 256)) Len [e]) es sa sb s0 es'
      (Value (IntV (&n))) (StackValue (BaseT (UintT 256)) op) s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  rw[vv_post_def]
  >~ [`vv_holds`] >- simp[vv_holds_def, read_result_def, return_def,
       expr_val_rel_def, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def]
  >~ [`vv_at`] >- simp[vv_at_def, expr_val_at_def, expr_type_def,
       is_word_type_def]
  >~ [`lookup_var x s`] >- (fs[] >> metis_tac[freshWritesTheory.not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- (fs[] >> metis_tac[])
  >~ [`locals_kept`] >- (fs[] >> metis_tac[exprSimPropsTheory.locals_kept_mem_tail])
  >~ [`pure_frame`] >-
    (match_mp_tac exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `s1` >>
     fs[expr_has_effect_thm])
  >> fs[]
QED
