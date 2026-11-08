Theory bodyPtrPopOwnerStore
Ancestors bodyPtrPopPathStore bodyPtrPopHistoryStore bodyPtrPopPathStep
  bodyPtrPopLiveSupport bodyPtrPopLivePath valueTypingMemoryProps valueEncoding
  vyperLookup vyperValueOperation bodyPtrDefs typedCopyPtr

Theorem pop_selected_array_elems_wf:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\
  mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) ==>
  elems_val_wf vs et
Proof
  strip_tac >> drule_all pop_path_support_extract >> strip_tac >>
  drule pop_live_support_typed >> strip_tac >>
  drule value_has_type_memory_wf >> simp[val_wf_def]
QED

Theorem pop_selected_owner_robust_store:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts rt root path (Replace short) = INL updated /\
  mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt root addr m) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt updated addr m) /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory et child (addr+k+32+(LENGTH vs-1)*type_memory_size et) m)
Proof
  strip_tac >> drule pop_live_support_typed >> strip_tac >>
  drule_all pop_selected_array_elems_wf >> strip_tac >>
  drule_all assign_subscripts_pop_replace >>
  disch_then (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  conj_tac
  >- (rpt strip_tac >> irule pop_path_robust_header_store >> simp[] >>
      qpat_assum `assign_subscripts _ _ _ PopOp = _` (irule_at Any) >> simp[] >>
      qexistsl_tac [`tn`, `s`] >> gvs[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) (addr+k) m` by
    (rpt strip_tac >> irule pop_path_memory_extract >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `mem_agree_outside {i | addr+k <= i /\ i < addr+k+32}
    t.vs_memory s.vs_memory` by
    (gvs[] >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> irule mstore_memory_frame) >>
  `child = LAST vs` by gvs[popped_value_def] >>
  mp_tac (Q.INST [`a` |-> `addr+k`, `tv` |-> `et`] (SPEC_ALL pop_removed_child_robust_header_store)) >>
  FULL_SIMP_TAC bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
