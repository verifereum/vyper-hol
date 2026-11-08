Theory bodyPtrPopInventoryStore
Ancestors bodyPtrPopOwnerStore bodyPtrPopReachableSupport
  bodyPtrPopRepresentationSupport bodyPtrPopLiveSupport bodyPtrDefs typedCopyPtr
  bodyPtrPopOwnerPartition vyperState vyperValueOperation
  list arithmetic pred_set

Theorem pop_live_support_robust_mstore_frame:
  pop_live_support tv v a supp /\
  DISJOINT {i | off <= i /\ i < off+32} supp /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory tv v a m) /\
  t.vs_memory = (mstore off w s).vs_memory ==>
  !m. mem_agree_outside dirty t.vs_memory m ==> val_in_memory tv v a m
Proof
  strip_tac >> drule pop_live_support_sound >> strip_tac >>
  `mem_agree_outside {i | off <= i /\ i < off+32} s.vs_memory t.vs_memory` by
    (gvs[] >> mp_tac mstore_memory_frame >>
     simp[mem_agree_outside_def] >> metis_tac[]) >>
  rpt strip_tac >> irule pop_rep_support_robust_frame >>
  qexistsl_tac [`t.vs_memory`, `s.vs_memory`, `dirty`, `supp`,
    `{i | off <= i /\ i < off+32}`] >>
  simp[] >> metis_tac[DISJOINT_SYM]
QED

Theorem pop_live_inventory_robust_store:
  pop_live_support rt root addr (supps 0) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      pop_live_support ptv v (addr+kp) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) /\
  evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts rt root q (Replace short) = INL root' /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt root addr m) /\
  (!p v. MEM (p,v) fresh ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt root' addr m) /\
  (!p v. MEM (p,v) (record_pop q (ArrayV (DynArrayV vs)) child fresh) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ptv v (addr+kp) m))
Proof
  strip_tac >> drule_all pop_selected_owner_robust_store >> strip_tac >>
  drule_all pop_recorded_child_offset >> strip_tac >>
  conj_tac >- simp[] >>
  simp[record_pop_def] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> FULL_SIMP_TAC bool_ss [ADD_ASSOC] >> metis_tac[]) >>
  `?j. j < LENGTH fresh /\ EL j fresh = (p,v)` by metis_tac[MEM_EL] >>
  `?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    pop_live_support ptv v (addr+kp) (supps (SUC j))` by metis_tac[] >>
  `?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)` by metis_tac[] >>
  gvs[] >>
  `DISJOINT {x | addr+k <= x /\ x < addr+k+32} (supps (SUC j))` by
    (irule pop_inventory_live_header_exclusion >> simp[] >> conj_tac
     >- (qexists_tac `SUC (LENGTH fresh)` >> simp[]) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule pop_live_support_robust_mstore_frame >>
  qpat_assum `pop_live_support ptv v _ _` (irule_at Any) >>
  qpat_assum `mem_agree_outside _ _ m` (irule_at Any) >> simp[] >>
  qexistsl_tac [`n2w (LENGTH vs-1)`, `s`, `addr+k`] >> simp[]
QED
