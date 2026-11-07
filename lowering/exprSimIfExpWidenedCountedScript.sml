Theory exprSimIfExpWidenedCounted
Ancestors
  placeTypedCopyRecursivePath exprSimCopy exprSimStorageCopy typedMemoryCopy
  valueEncoding valueEncodingTyping vyperTypeSystem venomState

Theorem typed_copy_semantic_frame:
  typed_copy_state_frame sa b sz s t /\
  stmt_state_rel ctx semantic_func ce cx ee s /\
  local_ptrs_reserved ce sa /\
  MEM inst (fn_insts semantic_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region ce ee.scopes s name lb len ==>
    b + sz <= lb \/ lb + len <= b) ==>
  stmt_state_rel ctx semantic_func ce cx ee t
Proof
  strip_tac >> irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  gvs[venom_state_component_equality, copy_static_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem typed_store_counted_semantic_frame:
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb execution_func /\ fn_inst_ids_distinct execution_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx semantic_func ce cx ee s /\ local_ptrs_reserved ce sa /\
  MEM inst (fn_insts semantic_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size dtv) /\
  (!name lb len. local_region ce ee.scopes s name lb len ==>
    w2n dw + type_memory_size dtv <= lb \/ lb + len <= w2n dw) ==>
  ?t. gas_marked_path F ctx execution_func s 0 (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    stmt_state_rel ctx semantic_func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[value_has_type_val_wf] >>
  drule_all compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  irule typed_copy_semantic_frame >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  metis_tac[]
QED
