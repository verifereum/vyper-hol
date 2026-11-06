(* Full semantic continuation pieces for bytes-to-uint, retaining ghost posts. *)
Theory bodyPtrTypeBuiltinsUintContinue
Ancestors bodyPtrTypeBuiltinsSourceTyping bodyPtrTypeBuiltinsFrameProbe
  bodyPtrTypeBuiltinsUnsignedValue bodyPtrTypeBuiltinsLiteralPost
  exprSimConvert fragGasPathPtr gasSummaryComposePtr
  loweringPosts exprLoweringProps compileEnv vyperAST venomState bodyPtrDefs
  exprSimProps loweringShapeDefs
Libs monadsyntax

Theorem zero_convert_child_post:
  expr_post ctx func cenv cx e es sa s1 s0 ee v1 x s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  typed_val_to_w256 tv v = 0w ==>
  expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa s1 s0
    ee v (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def] >> metis_tac[]
QED

Theorem zero_uint_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT (UintT b)) /\
  well_formed_type tenv (BaseT (UintT b)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  value_has_type stv v1 /\ v1 = BytesV [] /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT (UintT b)) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT (UintT b)) Convert (BaseT (UintT b)) [e])
        es sa s1 s0 fin v (Lit 0w) ss /\
      ss.vs_current_bb = s1.cs_current_bb /\
      ss.vs_inst_idx = LENGTH s1.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (UintT b)) v (Lit 0w) H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> gvs[] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def,
       listTheory.PAD_LEFT, byteTheory.word_of_bytes_be_def,
       GSYM rich_listTheory.REPLICATE_GENLIST,
       valueEncodingProofsTheory.word_of_bytes_replicate_zero,
       vyperValueTheory.within_int_bound_def] >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (IntV 0)`,`ee`,`G`,`tn`,`OK t0`] >>
  simp[gas_path_ptr_rules, ptr_val_ok_word_literal, is_word_type_def] >>
  irule zero_convert_child_post >>
  gvs[is_word_type_def, vyperValueTheory.evaluate_type_def,
       vyperTypeSystemTheory.well_formed_type_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def] >>
  goal_assum (drule_at Any)
QED

(* Semantic post transport for a memory-preserving scalar suffix. *)
Theorem scalar_suffix_expr_post:
  expr_post ctx func cenv cx e es sa s1 s0 ee v1 x t0 /\
  stmt_state_rel ctx func cenv cx ee s /\
  evaluate_type (get_tenv cx) (expr_type eout) = SOME tv /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
         lookup_var z s = SOME w) /\
  s.vs_allocas = t0.vs_allocas /\ s.vs_memory = t0.vs_memory /\
  is_word_type (expr_type eout) /\ sa.cs_next_var <= s1.cs_next_var ==>
  expr_post ctx func cenv cx eout es sa sb s0 ee v op s
Proof
  simp[expr_post_def] >> strip_tac >>
  `locals_kept cenv es s0 s` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  simp[expr_val_rel_def, expr_val_at_def] >> conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s1 z /\ lookup_var z t0 = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem bytes_uint_read_length:
  expr_body_pre cenv cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  valid_conversion (expr_type e) (BaseT (UintT b)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  ?bs. v = BytesV bs /\ LENGTH bs <= 32
Proof
  strip_tac >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  drule_all source_read_bytestring_view >>
  gvs[is_bytestring_type_def, vyperTypeSystemTheory.valid_conversion_def] >>
  strip_tac >> gvs[] >> decide_tac
QED
