Theory bodyPtrPopReachableHistoryProbe
Ancestors bodyPtrPopPathStore bodyPtrPopHistoryStore bodyPtrPopSpatialSplit
  vyperPlaceResultTyping vyperState vyperValueOperation valueEncoding
  robustCopyTransportPtr pred_set

(* A concrete operational trace, with an entirely opaque pre-capture suffix. *)
Theorem pop_probe_inner_live:
  entry.type = ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [ArrayV (DynArrayV [ArrayV (DynArrayV [x;y])])]) ==>
  entry_pop_step entry [ValueSubscript (IntV 0);ValueSubscript (IntV 0)]
    (entry with <|value := ArrayV (DynArrayV [ArrayV (DynArrayV [ArrayV (DynArrayV [x])])]);
      popped := ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)],y)::entry.popped|>)
Proof
  strip_tac >> simp[entry_pop_step_def, read_memory_path_def,
    evaluate_subscripts_def, assign_subscripts_def, subscript_type_def,
    subscripts_type_def, array_index_def,
    popped_value_def, pop_element_def, record_pop_def] >> EVAL_TAC >>
  simp[popped_value_def, pop_element_def, record_pop_def]
QED

Theorem pop_probe_middle_live:
  entry.type = ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [ArrayV (DynArrayV [ArrayV (DynArrayV [x])])]) ==>
  entry_pop_step entry [ValueSubscript (IntV 0)]
    (entry with <|value := ArrayV (DynArrayV [ArrayV (DynArrayV [])]);
      popped := ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],ArrayV (DynArrayV [x]))::entry.popped|>)
Proof
  strip_tac >> simp[entry_pop_step_def, read_memory_path_def,
    evaluate_subscripts_def, assign_subscripts_def, subscript_type_def,
    subscripts_type_def, array_index_def,
    popped_value_def, pop_element_def, record_pop_def] >> EVAL_TAC >>
  simp[popped_value_def, pop_element_def, record_pop_def]
QED

Theorem pop_probe_outer_live:
  entry.value = ArrayV (DynArrayV [ArrayV (DynArrayV [])]) ==>
  entry_pop_step entry []
    (entry with <|value := ArrayV (DynArrayV []);
      popped := ([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::entry.popped|>)
Proof
  strip_tac >> simp[entry_pop_step_def, read_memory_path_def,
    evaluate_subscripts_def, assign_subscripts_def,
    popped_value_def, pop_element_def, record_pop_def] >> EVAL_TAC >>
  simp[popped_value_def, pop_element_def, record_pop_def]
QED

Theorem pop_probe_fallback_read:
  read_popped
    (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0);ValueSubscript (IntV 0)]
    (([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
     ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],ArrayV (DynArrayV [x]))::
     ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)],y)::old)
  = SOME (ArrayV (DynArrayV [x]))
Proof
  simp[read_popped_def, subscripts_type_def, subscript_type_def,
    evaluate_subscripts_def, array_index_def] >> EVAL_TAC
QED

Theorem pop_probe_fallback_step:
  entry.type = ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV []) /\
  entry.popped =
    ([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
    ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],ArrayV (DynArrayV [x]))::
    ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)],y)::old ==>
  entry_pop_step entry [ValueSubscript (IntV 0);ValueSubscript (IntV 0)]
    (entry with popped :=
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 0)],x)::
      ([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)],y)::old)
Proof
  strip_tac >> simp[entry_pop_step_def, read_memory_path_def, pop_probe_fallback_read,
    evaluate_subscripts_def, assign_subscripts_def, subscript_type_def,
    subscripts_type_def, array_index_def, replace_popped_def,
    popped_value_def, pop_element_def, record_pop_def] >> EVAL_TAC >>
  simp[popped_value_def, pop_element_def, record_pop_def, replace_popped_def,
    subscripts_type_def, subscript_type_def, evaluate_subscripts_def,
    assign_subscripts_def, array_index_def] >> EVAL_TAC >>
  simp[vyperStateTheory.scope_entry_component_equality]
QED

Theorem pop_probe_layout:
  mem_path_offset (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] =
    SOME (64,ArrayTV tv (Dynamic 2)) /\
  mem_path_offset (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 0)] = SOME (96,tv) /\
  mem_path_offset (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)] =
    SOME (96 + type_memory_size tv,tv)
Proof
  simp[loweringPostsTheory.mem_path_offset_def, loweringPostsTheory.mem_step_offset_def]
QED

(* Empty owners use only their header, although val_footprint reserves capacity.
   Thus exterior_frame over the capacity window is deliberately not used. *)
Theorem pop_probe_empty_owner_frame[local]:
  (p + 32 <= off \/ off + 32 <= p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV [])) p m) /\
  t = ((mstore off w s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV [])) p m
Proof
  strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at p m = 0w` by
    gvs[valueEncodingTheory.val_in_memory_def] >>
  `!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem` by
    (drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]) >>
  `mem_agree_outside {i | off <= i /\ i < off+32} t.vs_memory s.vs_memory` by
    (gvs[] >> irule typedCopyPtrTheory.mstore_memory_frame) >>
  rpt strip_tac >>
  `mem_word_at p m = mem_word_at p t.vs_memory` by
    (irule pop_clean_word_agreement >> goal_assum (drule_at Any) >> simp[]) >>
  `mem_word_at p t.vs_memory = mem_word_at p s.vs_memory` by
    (irule pop_clean_word_agreement >>
     qexists_tac `{i | off <= i /\ i < off+32}` >>
     conj_tac
     >- (rpt strip_tac >> fs[pred_setTheory.IN_GSPEC_IFF] >> decide_tac) >>
     gvs[bodyPtrDefsTheory.mem_agree_outside_def] >> metis_tac[]) >>
  gvs[valueEncodingTheory.val_in_memory_def] >>
  first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
  simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Theorem pop_probe_y_frame[local]:
  val_wf tv y /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv y (a+96+type_memory_size tv) m) /\
  t = ((mstore (a+64) 0w s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory tv y (a+96+type_memory_size tv) m
Proof
  strip_tac >> rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn.t_mem`,
    `{i | a+64 <= i /\ i < a+96}`] >>
  conj_tac >- (simp[] >> decide_tac) >>
  conj_tac >- (gvs[] >> mp_tac (Q.SPECL [`s`,`a+64`,`0w`] typedCopyPtrTheory.mstore_memory_frame) >>
    simp[bodyPtrDefsTheory.mem_agree_outside_def, arithmeticTheory.ADD_ASSOC] >>
    metis_tac[]) >>
  simp[] >> gvs[] >>
  mp_tac (Q.SPECL [`s`,`a+64`,`0w`] typedCopyPtrTheory.mstore_memory_frame) >>
  simp[bodyPtrDefsTheory.mem_agree_outside_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem pop_probe_simultaneous_store:
  val_wf tv x /\ val_wf tv y /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
      (ArrayV (DynArrayV [])) a m /\
    val_in_memory (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1))
      (ArrayV (DynArrayV [])) (a+32) m /\
    val_in_memory (ArrayTV tv (Dynamic 2)) (ArrayV (DynArrayV [x])) (a+64) m /\
    val_in_memory tv y (a+96+type_memory_size tv) m) /\
  t = ((mstore (a+64) 0w s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1))
      (ArrayV (DynArrayV [])) a m /\
    val_in_memory (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1))
      (ArrayV (DynArrayV [])) (a+32) m /\
    val_in_memory (ArrayTV tv (Dynamic 2)) (ArrayV (DynArrayV [])) (a+64) m /\
    val_in_memory tv x (a+96) m /\
    val_in_memory tv y (a+96+type_memory_size tv) m
Proof
  strip_tac >> rpt gen_tac >> disch_tac >> conj_tac
  >- (irule pop_probe_empty_owner_frame >> simp[] >>
      qexistsl_tac [`a+64`,`s`,`tn`,`0w`] >> gvs[] >> metis_tac[])
  >> conj_tac
  >- (irule pop_probe_empty_owner_frame >> simp[] >>
      qexistsl_tac [`a+64`,`s`,`tn`,`0w`] >> gvs[] >> metis_tac[])
  >> conj_tac
  >- (mp_tac (Q.INST [`vs` |-> `[x]`, `p` |-> `a+64`, `cap` |-> `2`] pop_shortened_owner_robust_store_nat) >>
      simp[valueEncodingTheory.val_wf_def] >>
      gvs[] >> metis_tac[])
  >> conj_tac
  >- (mp_tac (Q.INST [`vs` |-> `[x]`, `a` |-> `a+64`, `cap` |-> `2`] pop_removed_child_robust_header_store) >>
      simp[valueEncodingTheory.val_wf_def, arithmeticTheory.ADD_ASSOC] >>
      disch_then irule >> gvs[] >>
      mp_tac (Q.SPECL [`s`,`a+64`,`0w`] typedCopyPtrTheory.mstore_memory_frame) >>
      simp[arithmeticTheory.ADD_ASSOC])
  >> irule pop_probe_y_frame >> simp[] >> qexistsl_tac [`s`,`tn`] >>
  gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem pop_probe_four_steps:
  entry.type = ArrayTV (ArrayTV (ArrayTV tv (Dynamic 2)) (Dynamic 1)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [ArrayV (DynArrayV [ArrayV (DynArrayV [x;y])])]) /\
  entry.popped = old ==>
  ?e1 e2 e3 e4.
    entry_pop_step entry [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] e1 /\
    entry_pop_step e1 [ValueSubscript (IntV 0)] e2 /\
    entry_pop_step e2 [] e3 /\
    entry_pop_step e3 [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] e4 /\
    e4.value = ArrayV (DynArrayV []) /\
    e4.popped =
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 0)],x)::
      ([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],ArrayV (DynArrayV []))::
      ([ValueSubscript (IntV 0);ValueSubscript (IntV 0);ValueSubscript (IntV 1)],y)::old
Proof
  strip_tac >> drule_all pop_probe_inner_live >> disch_then (irule_at Any) >>
  simp[] >> irule_at Any pop_probe_middle_live >> simp[] >>
  irule_at Any pop_probe_outer_live >> simp[] >>
  irule_at Any pop_probe_fallback_step >> simp[]
QED
