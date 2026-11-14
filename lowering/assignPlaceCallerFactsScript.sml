Theory assignPlaceCallerFacts
Ancestors
  assignPlacePureCode exprSimHyps exprSimHypsDefs loweringPosts
  allocLimits allocLimitsProps valueEncodingProps vyperTypeArgFits vyperTypeSystem
  exprLowering compileEnv vyperAST

(* The frozen root excludes zero-sized destination representations.  This
   does not follow from expr_post alone: retain RHS assignability. *)
Theorem assign_place_caller_store_types:
  expr_sim_inv cenv cx env es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  assignable_type env.type_defs (expr_type e) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
  post_value_type cenv e = expr_type e /\
  assignable_type (get_tenv cx) dty /\
  0 < type_slot_size dtv /\ 0 < type_memory_size dtv
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `assignable_type (get_tenv cx) dty` by
    metis_tac[type_widens_to_assignable_type] >>
  `0 < type_slot_size dtv` by
    metis_tac[assignable_type_slot_size_pos] >>
  simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  metis_tac[post_value_type_lowered, post_value_type_bytestring]
QED

(* Normalization is guarded by the compiler's actual lowered source type. *)
Theorem assign_place_caller_normalization_alloc:
  assign_alloc_ok cenv bt e /\
  compile_get_target_ptr cfn cenv bt sa =
    ((dst,SOME loc,SOME (ValPT dty)),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  (~is_word_type dty /\ dty <> lowered_value_type cenv e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
   type_alloc_ok cenv dty)
Proof
  strip_tac >>
  `target_store_place cenv bt = SOME (SOME (ValPT dty))` by
    (drule compile_get_target_ptr_store_place >> simp[] >> metis_tac[]) >>
  gvs[assign_alloc_ok_def, type_alloc_ok_def] >> gvs[]
QED
