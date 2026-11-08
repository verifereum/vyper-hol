(* Mapping keys have no aggregate layout widening.  The hash input
   cleanliness/coverage interfaces are hash_dynamic_bytes_operand and
   hash_string_operand (bodyPtrHashBuiltinsCases); scalar cleanliness is
   the first conjunct of ptr_val_ok. *)
Theory bodyPtrSubscriptSeamMapInterface
Ancestors
  bodyPtrHashBuiltinsCases bodyPtrPrecompileBuiltinsGhost exprBopSimProps
  exprSimMapKey vyperTypeSystem loweringPosts compileEnv vyperValue

Theorem mapping_key_post_type:
  !cenv e tv. hashmap_key_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    post_value_type cenv e = expr_type e
Proof
  rpt strip_tac >>
  `is_word_type (expr_type e) \/ is_bytestring_type (expr_type e)` by
    (Cases_on `expr_type e` >>
     gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
     Cases_on `b` >> gvs[hashmap_key_type_def, is_word_type_def,
                            is_bytestring_type_def] >>
     Cases_on `b'` >> gvs[is_word_type_def, is_bytestring_type_def,
                              evaluate_type_def, AllCaseEqs()]) >>
  simp[]
QED

Theorem mapping_slot_index_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!l. op <> Label l) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  eval_operand op s0 = SOME slot /\ op_taint tn0 op = {} ==>
  eval_operand op s = SOME slot /\ op_taint tn op = {}
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> metis_tac[]) >>
  drule_all ghost_kept_operand_taint >> simp[]
QED
