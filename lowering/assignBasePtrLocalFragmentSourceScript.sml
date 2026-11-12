(* Layout boundary used by the counted local-assignment continuation. *)
Theory assignBasePtrLocalFragmentSource
Ancestors assignBasePtrLocalAssign annAssignPtrMemorySource valueCopyBytes
  exprSimProps loweringPosts bodyPtrDefs valueTypingMemoryProps
  vyperTypeValues valueEncoding exprSimDefs

Theorem assign_base_local_rhs_val_at:
  (src = dst \/ is_bytestring_type src /\ is_bytestring_type dst) /\
  evaluate_type (get_tenv cx) src = SOME stv /\
  evaluate_type (get_tenv cx) dst = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  expr_val_at cenv cx src sa sb es v op s ==>
  expr_val_at cenv cx dst sa sb es v op s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `src = dst` >- gvs[] >>
  `is_bytestring_type src /\ is_bytestring_type dst` by metis_tac[] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  `val_footprint dtv v = val_footprint stv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf dtv v` by metis_tac[value_has_type_memory_wf] >>
  gvs[expr_val_at_def, is_bytestring_word_type] >>
  `(?bt. stv = BaseTV bt) /\ (?bt. dtv = BaseTV bt)` by
    metis_tac[bytestring_type_value] >> gvs[] >>
  simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
  `local_val_at cenv cx n (w2n w - b) (BaseTV bt') v` by
    (irule local_val_at_base >> qexistsl_tac [`bt`, `v`] >> simp[]) >>
  metis_tac[]
QED

