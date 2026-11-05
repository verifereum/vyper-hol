(* Post framing for the raw value/place length suffix. *)
Theory bodyPtrEnvBuiltinsLenSuffix
Ancestors
  bodyPtrEnvBuiltinsLen bodyPtrEnvBuiltinsLenSource bodyPtrEnvBuiltinsOperandFrame
  context loweringPosts exprSimDefs exprSimProps exprLoweringProps compileEnv
  exprSimLen vyperState vyperAST vyperTyping vyperValue valueEncoding integer_word freshWrites

Theorem len_builtin_post_frame:
  !func cenv cx e es sa sm sb s0 es' tv vv s1 op s n ctx.
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s1 /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' s /\ eval_operand op s = SOME (n2w n) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\ s.vs_memory = s1.vs_memory ==>
    vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
      sa sb s0 es' (Value (IntV (&n))) (StackValue (BaseT (UintT 256)) op) s
Proof
  rw[vv_post_def]
  >~ [`vv_holds`]
  >- simp[vv_holds_def, read_result_def, return_def, expr_val_rel_def, expr_type_def, is_word_type_def,
          evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
          integer_wordTheory.i2w_def]
  >~ [`vv_at`]
  >- simp[vv_at_def, expr_val_at_def, expr_type_def, is_word_type_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- (fs[vv_post_def] >> metis_tac[])
  >~ [`locals_kept`]
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem len_operand_header:
  !env ctx fn cenv cx ty r vv es s tv.
    stmt_state_rel ctx fn cenv cx es s /\
    vv_holds cenv cx ty r vv es s /\ is_sized_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,es) r (Type ty) /\
    (!v. read_result cx r es = (INL v,es) ==> value_has_type tv v) ==>
    ?n w. result_array_length cx r es = (INL n,es) /\
      eval_operand (vv_operand vv) s = SOME w /\
      ptr_load_val cenv.ce_is_ctor
        (case vv_location vv of SOME l => l | NONE => LocMemory) w s = n2w n /\
      (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata
Proof
  rpt gen_tac >> strip_tac >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  qexistsl_tac [`n`, `w`] >> simp[] >>
  Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> gvs[]
QED
