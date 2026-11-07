Theory bodyPtrPopPathStore
Ancestors bodyPtrPopPathLift bodyPtrPopPathStep bodyPtrPopSpatialSplit
  bodyPtrDefs typedCopyPtr valueEncoding vyperValueOperation pred_set

Theorem pop_path_robust_header_store:
  !rt root path vs updated k tv cap addr tn s t.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\
  assign_subscripts rt root path PopOp = INL updated /\
  mem_path_offset rt path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  vs <> [] /\ elems_val_wf vs tv /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory rt root addr m) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs - 1)) s)
    with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory rt updated addr m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (addr+k) m` by
    (rpt strip_tac >> drule_all pop_path_robust_memory_extract >> simp[]) >>
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (FRONT vs))) (addr+k) m` by
    (rpt strip_tac >> irule pop_shortened_owner_robust_store_nat >> simp[] >>
     goal_assum (drule_at Any) >> gvs[]) >>
  `mem_agree_outside {i | addr+k <= i /\ i < addr+k+32}
    t.vs_memory s.vs_memory` by
    (gvs[] >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
     irule mstore_memory_frame) >>
  rpt strip_tac >> irule pop_path_robust_memory_pop >> simp[] >>
  qpat_assum `assign_subscripts rt root path PopOp = _` (irule_at Any) >> simp[] >>
  simp[pop_element_def] >>
  qexistsl_tac [`{i | addr+k <= i /\ i < addr+k+32}`,
    `t.vs_memory`, `s.vs_memory`, `tn.t_mem`] >>
  fs[type_memory_size_def, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> irule mstore_memory_frame
QED
