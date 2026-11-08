Theory bodyPtrPopInventoryStore
Ancestors bodyPtrPopOwnerStore bodyPtrPopReachableSupport bodyPtrPopOwnerReachability
  bodyPtrPopRepresentationSupport bodyPtrPopLiveSupport bodyPtrDefs typedCopyPtr
  bodyPtrPopOwnerPartition bodyPtrPopLivePath vyperState vyperValueOperation
  exprSimProps list arithmetic pred_set

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
  qpat_assum `pop_rep_support _ _ _ _` (irule_at Any) >>
  qpat_assum `mem_agree_outside dirty t.vs_memory m` (irule_at Any) >>
  qexistsl_tac [`{i | off <= i /\ i < off+32}`, `s.vs_memory`] >>
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

Theorem pop_relative_owner_robust_store:
  IS_PREFIX q p /\ mem_path_offset rt p = SOME (kp,ptv) /\
  pop_live_support ptv old (addr+kp) supp /\
  evaluate_subscripts ptv old (DROP (LENGTH p) q) = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts ptv old (DROP (LENGTH p) q) (Replace short) = INL updated /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv old (addr+kp) m) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ptv updated (addr+kp) m) /\
  (?kc. mem_path_offset rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) = SOME (kc,et) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory et child (addr+kc) m)) /\
  {x | addr+k <= x /\ x < addr+k+32} SUBSET supp
Proof
  strip_tac >> drule_all pop_supported_array_offset >> strip_tac >>
  drule_all pop_prefix_drop_offset >> strip_tac >> gs[] >>
  `t = ((mstore ((addr+kp)+k') (n2w (LENGTH vs-1)) s)
    with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gvs[] >> FULL_SIMP_TAC bool_ss [ADD_ASSOC]) >>
  drule_all pop_selected_owner_robust_store >> strip_tac >>
  drule_all pop_recorded_child_offset >> strip_tac >>
  drule_all pop_path_support_header >> strip_tac >>
  `q = p ++ DROP (LENGTH p) q` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >> metis_tac[TAKE_DROP]) >>
  `mem_path_offset rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) =
    SOME (kp+(k'+32+(LENGTH vs-1)*type_memory_size et),et)` by
    (once_asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule pop_path_offset_append >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> FULL_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Theorem pop_history_robust_frame_except:
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      pop_live_support ptv v (addr+kp) (supps (SUC j))) /\
  (!p v. MEM (p,v) fresh ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)) /\
  (!j. j < LENGTH fresh /\ j <> selected ==>
    DISJOINT {x | off <= x /\ x < off+32} (supps (SUC j))) /\
  t.vs_memory = (mstore off w s).vs_memory ==>
  !j p v. j < LENGTH fresh /\ j <> selected /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      (!m. mem_agree_outside dirty t.vs_memory m ==> val_in_memory ptv v (addr+kp) m)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM (p,v) fresh` by metis_tac[MEM_EL] >>
  `?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    pop_live_support ptv v (addr+kp) (supps (SUC j))` by metis_tac[] >>
  `?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)` by metis_tac[] >>
  gvs[] >> rpt strip_tac >> irule pop_live_support_robust_mstore_frame >>
  qpat_assum `pop_live_support ptv v _ _` (irule_at Any) >>
  qpat_assum `mem_agree_outside _ _ m` (irule_at Any) >> simp[] >>
  qexistsl_tac [`w`, `s`, `off`] >> simp[]
QED

Theorem pop_historical_inventory_robust_store:
  pop_live_support rt root addr (supps 0) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      pop_live_support ptv v (addr+kp) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) /\
  read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  popped_value (ArrayV (DynArrayV vs)) = INL child /\
  pop_element (ArrayV (DynArrayV vs)) = INL short /\
  replace_popped rt q short fresh = SOME fresh' /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt root addr m) /\
  (!p v. MEM (p,v) fresh ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt root addr m) /\
  (!p v. MEM (p,v) (record_pop q (ArrayV (DynArrayV vs)) child fresh') ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ptv v (addr+kp) m))
Proof
  strip_tac >> drule_all pop_historical_update_zipper >> strip_tac >>
  `?kp ot. mem_path_offset rt p = SOME (kp,ot) /\
    pop_live_support ot old (addr+kp) (supps (SUC (LENGTH pre)))` by
    (first_x_assum (qspecl_then [`LENGTH pre`, `p`, `old`] mp_tac) >> simp[EL_APPEND_EQN]) >>
  `?kp ot. mem_path_offset rt p = SOME (kp,ot) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ot old (addr+kp) m)` by
    (qpat_x_assum `!p v. MEM (p,v) fresh ==> _` (qspecl_then [`p`, `old`] mp_tac) >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >> gs[] >>
  drule_all pop_relative_owner_robust_store >> strip_tac >>
  `!j. j < SUC (LENGTH fresh) /\ j <> SUC (LENGTH pre) ==>
    DISJOINT {x | addr+k <= x /\ x < addr+k+32} (supps j)` by
    (rpt strip_tac >> irule bodyPtrPopSupportTransferTheory.pop_family_selected_exclusion >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `SUC (LENGTH fresh)` >> simp[]) >>
  `!j p v. j < LENGTH fresh /\ j <> LENGTH pre /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ptv v (addr+kp) m)` by
    (rpt gen_tac >> strip_tac >> irule pop_history_robust_frame_except >>
     qpat_assum `EL j fresh = _` (irule_at Any) >>
     qpat_assum `j <> LENGTH pre` (irule_at Any) >> simp[] >>
     qexistsl_tac [`n2w (LENGTH vs-1)`, `supps`, `s`, `addr+k`] >> simp[] >>
     FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND, ADD1, AC ADD_ASSOC ADD_COMM] >>
     metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule pop_live_support_robust_mstore_frame >>
      qpat_assum `pop_live_support rt root _ _` (irule_at Any) >>
      qpat_assum `mem_agree_outside _ _ m` (irule_at Any) >> simp[] >>
      qexistsl_tac [`n2w (LENGTH vs-1)`, `s`, `addr+k`] >> simp[]) >>
  simp_tac pure_ss [record_pop_def, TypeBase.case_def_of ``:value``,
    TypeBase.case_def_of ``:array_value``, MEM] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  `?j. j < LENGTH fresh' /\ EL j fresh' = (p',v)` by metis_tac[MEM_EL] >>
  Cases_on `j = LENGTH pre`
  >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  `EL j fresh = (p',v)` by
    (gs[] >> FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND] >>
     `j < LENGTH pre + SUC (LENGTH post)` by decide_tac >>
     metis_tac[pop_history_replace_other]) >>
  gs[] >> metis_tac[]
QED

Theorem pop_owner_step_robust_store:
  pop_owner_reachable rt initial root fresh /\
  well_formed_type_value rt /\ value_has_type rt initial /\
  pop_owner_step rt root fresh q root' next /\
  (evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) \/
   ?err. evaluate_subscripts rt root q = INR err /\
     read_popped rt q fresh = SOME (ArrayV (DynArrayV vs))) /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt root addr m) /\
  (!p v. MEM (p,v) fresh ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt root' addr m) /\
  (!p v. MEM (p,v) next ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ptv v (addr+kp) m))
Proof
  strip_tac >> drule_all pop_owner_reachable_support >>
  disch_then (qspec_then `addr` strip_assume_tac) >>
  drule pop_owner_step_invert >> strip_tac >> gs[]
  >- (drule_all pop_live_inventory_robust_store >> simp[]) >>
  drule_all pop_historical_inventory_robust_store >> simp[]
QED
