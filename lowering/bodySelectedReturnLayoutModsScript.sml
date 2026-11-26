(* Physical source and post layouts for a linked returned expression. *)
Theory bodySelectedReturnLayoutMods
Ancestors
  bodyAnnNonwordReadTypesMods bodyCopyReadPhysicalTypeMods
  exprBodyPreProps exprSimHypsDefs loweringPosts
  vyperTypeSystem vyperAST valueTypingMemoryProps

Theorem selected_return_value_layout_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) ret /\
  ~is_word_type ret /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee) ==>
  ?stv ptv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
    value_has_type stv v /\ value_has_type ptv v /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret /\
    (post_value_type cenv e = lowered_value_type cenv e \/
     (is_bytestring_type (post_value_type cenv e) /\
      is_bytestring_type (lowered_value_type cenv e)))
Proof
  strip_tac >>
  drule_all ann_copy_nonword_layout_mods >> strip_tac >>
  drule_all copy_read_physical_type_gas_obs_mods >> strip_tac >>
  qexistsl_tac [`rt`,`pt`] >> simp[]
QED
