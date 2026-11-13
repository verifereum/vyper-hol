(* The actual singleton aggregate store after its target evaluator cut. *)
Theory assignTupleStoreCutPtr
Ancestors stmtLowering compileEnv context

Theorem tuple_aggregate_singleton_store_cut:
  ~is_word_type sty /\ ~is_word_type dty /\
  compile_get_target_ptr compile_expr cenv bt sa =
    ((dst,SOME loc,SOME (ValPT dty)),sm) /\
  compile_tuple_store_all cenv [sty] [BaseTarget bt] [op] sa = ((),sb) ==>
  compile_assign_value cenv dst loc op F NONE dty sty
    (case dty of
       ArrayT et (Dynamic cap) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
     | _ => NONE)
    (type_memory_bytes cenv dty) sm = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_store_all_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,LET_THM] >> strip_tac >> pairarg_tac >> gvs[]
QED
