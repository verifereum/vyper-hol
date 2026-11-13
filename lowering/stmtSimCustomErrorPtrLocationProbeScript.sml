Theory stmtSimCustomErrorPtrLocationProbe
Ancestors
  bodyPtrDefs exprSimPtrTopLevelForce accountsRelProps ptrDiscipline
  valueEncodingProps loweringPosts words pred_set exprSimUnwrap
  exprSimProps representationCleanPtr

(* The expression pointer contract itself, rather than a global liveness
   assumption, suffices to make a forced word storage load clean. *)
Theorem custom_error_word_source_taint[local]:
  ptr_vv_ok cx t raw (LocatedValue ann p) es G tn s /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  key_taint (if p.ptr_location = LocTransient then tn.t_trans else tn.t_stor) w = {}
Proof
  strip_tac >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  gvs[ptr_vv_ok_def, key_taint_def, EXTENSION] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`w`, `x`] mp_tac) >>
  simp[] >> metis_tac[toplevel_word_dead_bytes]
QED

Theorem custom_error_word_memory_clean[local]:
  ptr_mem_ok cx t v op G tn s /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n w) mem = typed_val_to_w256 tv v` by
    metis_tac[ptr_mem_ok_def, exprSimPropsTheory.val_in_memory_word] >>
  drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]
QED
