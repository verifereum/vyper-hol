(* Typed source boundaries exclude unreachable compiler alternatives.
   Lowering decompositions already live in exprSimWordBuiltins:
   lower_value_floor, lower_value_ceil, lower_value_as_wei_value,
   lower_value_ternary_modular and lower_value_pow_mod256; reuse them. *)
Theory bodyPtrWordBuiltinsTypedShapes
Ancestors exprSimHypsDefs exprSimSource exprSimWordBuiltins
  vyperTyping vyperTypeSystem vyperAST compileEnv list

Theorem word_scaling_operand_pre:
  expr_body_pre cenv cx env (Builtin ann (AsWeiValue d) [e]) es ==>
  (?k. expr_type e = BaseT (UintT k)) /\ ann = BaseT (UintT 256) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `is_uint_type (expr_type e) /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  conj_tac
  >- (Cases_on `expr_type e` >> gvs[is_uint_type_def] >>
      rename1 `is_uint_type (BaseT bt)` >> Cases_on `bt` >> gvs[is_uint_type_def]) >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_rounding_operand_pre:
  (bt = Ceil \/ bt = Floor) /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es ==>
  expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_modular_types:
  (bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
  expr_body_pre cenv cx env (Builtin ann bt args) es ==>
  ann = BaseT (UintT 256) /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) args /\
  LENGTH args = (if bt = PowMod256 then 2 else 3)
Proof
  strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      EVERY_MAP, EVERY_MEM, MAP_EQ_CONS, MAP_EQ_NIL] >>
  metis_tac[]
QED
