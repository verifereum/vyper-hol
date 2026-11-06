(* Full semantic continuation pieces for bytes-to-uint, retaining ghost posts. *)
Theory bodyPtrTypeBuiltinsUintContinue
Ancestors bodyPtrTypeBuiltinsSourceTyping bodyPtrTypeBuiltinsFrameProbe
  bodyPtrTypeBuiltinsUnsignedValue bodyPtrTypeBuiltinsLiteralPost
  exprSimConvert fragGasPathPtr gasSummaryComposePtr
  loweringPosts exprLoweringProps compileEnv vyperAST venomState bodyPtrDefs
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
