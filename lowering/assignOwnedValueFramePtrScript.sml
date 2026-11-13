(* A local overwrite leaves every value in a disjoint owned buffer intact. *)
Theory assignOwnedValueFramePtr
Ancestors assignTuplePtrBoundary bodyPtrDefs loweringPosts venomState
  ptrDiscipline finite_map arithmetic pred_set valueEncoding valueEncodingDefs
  exprLoweringProps loweringStateRelDefs compileEnv words

Theorem owned_value_local_write_frame_ptr:
  ptr_val_ok cx ty v op G tn s /\
  eval_operand op t = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op /\
  (!p. op = Var p ==> FLOOKUP G' p = FLOOKUP G p) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  (!tv w. ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    own_base <= w2n w /\ w2n w+val_footprint tv v <= own_base+own_size) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    own_base+own_size <= b \/ b+sz <= own_base) /\
  local_region cenv es.scopes s id dst dsz /\ written <= dsz /\
  (!i. ~(dst <= i /\ i < dst+written) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- gvs[ptr_val_ok_def] >>
  `!tv w i. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\ w2n w <= i /\
    i < w2n w+val_footprint tv v ==> ~(dst <= i /\ i < dst+written)` by
    (rpt gen_tac >> strip_tac >>
     `own_base <= w2n w /\ w2n w+val_footprint tv v <= own_base+own_size` by
       metis_tac[] >>
     `own_base+own_size <= dst \/ dst+dsz <= own_base` by metis_tac[] >> decide_tac) >>
  irule ptr_val_ok_exterior_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`tn`,`{i | dst <= i /\ i < dst+written}`] >>
  simp[] >> metis_tac[]
QED
