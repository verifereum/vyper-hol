(* Runtime bytes coverage is independent of the lowered buffer's bound. *)
Theory bodyPtrStructLitBytesCoverage
Ancestors bodyPtrMakeArrayConsLayout exprPtrUnwrapFacts bodyPtrDefs
  venomState compileEnv

Theorem structlit_bytes_source_coverage:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ ptr_mem_ok cx ty v op G tn s /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?src. op = Var src /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s (val_store_size tv v)
Proof
  strip_tac >>
  `val_footprint tv v <> 0` by
    (drule_all literal_bytes_runtime_slot >> strip_tac >> simp[]) >>
  `?p. op = Var p /\ ptr_covers G tn p s (val_store_size tv v)` by
    (irule ptr_mem_ok_read_covers >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  gvs[eval_operand_def]
QED
