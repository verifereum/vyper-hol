(* The generic forward typed-copy path needs only the allocation end bound,
   unlike the more restrictive child-forward interface. *)
Theory annassignRelayoutBounds
Ancestors
  placeTypedCopyRecursivePath placeMemoryCopyEffect loweringPosts context
  typedMemoryCopy venomState

Theorem compile_store_memory_relayout_effect:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    compile_store_memory cenv src dst dty sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `compile_store_memory_typed cenv dst dty src sty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  drule_all compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >>
  gnvs[typed_copy_state_frame_def, typed_copy_frame_def, typed_copy_effect_def] >>
  RULE_L_ASSUM_TAC CONJUNCTS >> simp[] >> conj_tac
  >- (qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  first_assum ACCEPT_TAC
QED
