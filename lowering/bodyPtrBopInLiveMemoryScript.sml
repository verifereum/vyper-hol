(* Project the robust representation carried by a memory value/place post.
   Coverage of an emitted address remains a separate load-check premise. *)
Theory bodyPtrBopInLiveMemory
Ancestors bodyPtrDefs bodyPtrBopInMemoryContents exprSimProps
  representationCleanPtr ptrDiscipline pred_set typedCopyLayoutPtr

Theorem memory_dynamic_header_clean:
  ptr_mem_ok cx ty (ArrayV (DynArrayV vs)) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand op s = SOME w ==>
  mem_word_taint tn.t_mem (w2n w) = {}
Proof
  strip_tac >> gvs[ptr_mem_ok_def] >>
  metis_tac[dynarray_memory_header_clean]
QED

Theorem memory_dynamic_element_clean:
  ptr_mem_ok cx ty (ArrayV (DynArrayV vs)) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand op s = SOME w /\ i < LENGTH vs /\
  ((?b. EL i vs = BoolV b) \/ (?n. EL i vs = IntV n) \/
   (?k. EL i vs = FlagV k) \/ (?n. EL i vs = DecimalV n) \/
   (?bs. EL i vs = BytesV bs)) ==>
  mem_word_taint tn.t_mem (w2n w + 32 + i * type_memory_size tv) = {}
Proof
  strip_tac >> irule dynarray_memory_element_clean >>
  qexistsl_tac [`cap`, `s.vs_memory`, `vs`] >>
  simp[] >> gvs[ptr_mem_ok_def]
QED

Theorem memory_fixed_element_clean:
  ptr_mem_ok cx ty (ArrayV (SArrayV kvs)) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV tv (Fixed cap)) /\
  eval_operand op s = SOME w /\ i < cap /\
  v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
  ((?b. v = BoolV b) \/ (?n. v = IntV n) \/ (?k. v = FlagV k) \/
   (?n. v = DecimalV n) \/ (?bs. v = BytesV bs)) ==>
  mem_word_taint tn.t_mem (w2n w + i * type_memory_size tv) = {}
Proof
  strip_tac >> gvs[ptr_mem_ok_def] >>
  metis_tac[sarray_memory_element_clean]
QED

Theorem robust_typed_word_memory_clean:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v a m) ==>
  mem_word_taint tn.t_mem a = {}
Proof
  strip_tac >>
  `!m. mem_agree_outside tn.t_mem mem m ==>
       mem_word_at a m = typed_val_to_w256 tv v` by
    (rpt strip_tac >> irule val_in_memory_word_type >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_then assume_tac robust_mem_word_at_clean >>
  simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
  first_x_assum (qspec_then `a + x` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem memory_dynamic_typed_element_clean:
  ptr_mem_ok cx aty (ArrayV (DynArrayV vs)) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand baseop s = SOME bw /\ i < LENGTH vs /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv (EL i vs) ==>
  mem_word_taint tn.t_mem (w2n bw + 32 + i * type_memory_size tv) = {}
Proof
  strip_tac >> irule robust_typed_word_memory_clean >>
  qpat_assum `value_has_type tv (EL i vs)` (irule_at Any) >>
  qpat_assum `evaluate_type _ ety = SOME tv` (irule_at Any) >>
  qexists_tac `s.vs_memory` >> reverse conj_tac >- simp[] >>
  rpt strip_tac >> irule dynarray_in_memory_robust_element >>
  conj_tac >- simp[] >>
  qexistsl_tac [`cap`, `s.vs_memory`, `tn`] >>
  gvs[ptr_mem_ok_def]
QED

Theorem memory_fixed_typed_element_clean:
  ptr_mem_ok cx aty (ArrayV (SArrayV kvs)) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Fixed cap)) /\
  eval_operand baseop s = SOME bw /\ i < cap /\
  v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv v ==>
  mem_word_taint tn.t_mem (w2n bw + i * type_memory_size tv) = {}
Proof
  strip_tac >> irule robust_typed_word_memory_clean >>
  qpat_assum `value_has_type tv v` (irule_at Any) >>
  qpat_assum `evaluate_type _ ety = SOME tv` (irule_at Any) >>
  qexists_tac `s.vs_memory` >> reverse conj_tac >- simp[] >>
  rpt strip_tac >> irule sarray_in_memory_robust_element >>
  qexistsl_tac [`cap`, `kvs`, `s.vs_memory`, `tn`] >>
  gvs[ptr_mem_ok_def]
QED

Theorem memory_dynamic_typed_element_mload:
  ptr_mem_ok cx aty (ArrayV (DynArrayV vs)) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand baseop s = SOME bw /\ i < LENGTH vs /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv (EL i vs) ==>
  mload (w2n bw + 32 + i * type_memory_size tv) s =
    typed_val_to_w256 tv (EL i vs)
Proof
  strip_tac >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  irule val_in_memory_word_type >>
  qpat_assum `value_has_type tv (EL i vs)` (irule_at Any) >>
  qpat_assum `evaluate_type _ ety = SOME tv` (irule_at Any) >>
  conj_tac >- simp[] >>
  irule dynarray_in_memory_robust_element >>
  conj_tac >- simp[] >> qexistsl_tac [`cap`, `s.vs_memory`, `tn`] >>
  gvs[ptr_mem_ok_def, mem_agree_outside_def]
QED

Theorem memory_fixed_typed_element_mload:
  ptr_mem_ok cx aty (ArrayV (SArrayV kvs)) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Fixed cap)) /\
  eval_operand baseop s = SOME bw /\ i < cap /\
  v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv v ==>
  mload (w2n bw + i * type_memory_size tv) s = typed_val_to_w256 tv v
Proof
  strip_tac >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  irule val_in_memory_word_type >>
  qpat_assum `value_has_type tv v` (irule_at Any) >>
  qpat_assum `evaluate_type _ ety = SOME tv` (irule_at Any) >> simp[] >>
  irule sarray_in_memory_robust_element >>
  qexistsl_tac [`cap`, `kvs`, `s.vs_memory`, `tn`] >>
  gvs[ptr_mem_ok_def, mem_agree_outside_def]
QED

(* A single consumer interface for the two concrete array layouts. *)
Theorem memory_array_typed_element_read:
  ptr_mem_ok cx aty (ArrayV av) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  eval_operand baseop s = SOME bw /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv v /\
  ((?vs cap. av = DynArrayV vs /\ bd = Dynamic cap /\
       prefix = 32 /\ i < LENGTH vs /\ v = EL i vs) \/
   (?kvs cap. av = SArrayV kvs /\ bd = Fixed cap /\
       prefix = 0 /\ i < cap /\
       v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv))) ==>
  mem_word_taint tn.t_mem (w2n bw + prefix + i * type_memory_size tv) = {} /\
  mload (w2n bw + prefix + i * type_memory_size tv) s = typed_val_to_w256 tv v
Proof
  strip_tac
  >- (gvs[] >> conj_tac
      >- (drule_all memory_dynamic_typed_element_clean >> simp[]) >>
      drule_all memory_dynamic_typed_element_mload >> simp[]) >>
  gvs[] >> conj_tac
  >- (drule_all (SRULE [] (GEN_ALL memory_fixed_typed_element_clean)) >> simp[]) >>
  drule_all (SRULE [] (GEN_ALL memory_fixed_typed_element_mload)) >> simp[]
QED
