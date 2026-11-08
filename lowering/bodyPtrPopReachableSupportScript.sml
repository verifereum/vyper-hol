Theory bodyPtrPopReachableSupport
Ancestors bodyPtrPopOwnerPartition bodyPtrPopSupportTransfer bodyPtrPopOwnerReachability
  bodyPtrPopLiveSupport bodyPtrPopLivePath bodyPtrPopOwnerSelection exprSimProps loweringPosts vyperState
  vyperTyping list arithmetic pred_set

Theorem pop_live_inventory_step:
  pop_live_support rt root addr (supps 0) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?k tv. mem_path_offset rt p = SOME (k,tv) /\
      pop_live_support tv v (addr+k) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) /\
  evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  vyperValueOperation$popped_value (ArrayV (DynArrayV vs)) = INL child /\
  vyperValueOperation$pop_element (ArrayV (DynArrayV vs)) = INL short /\
  assign_subscripts rt root q (Replace short) = INL root' ==>
  ?next. pop_live_support rt root' addr (next 0) /\
    (!j p v. j < LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh) /\
      EL j (record_pop q (ArrayV (DynArrayV vs)) child fresh) = (p,v) ==>
      ?k tv. mem_path_offset rt p = SOME (k,tv) /\
        pop_live_support tv v (addr+k) (next (SUC j))) /\
    (!j k. j < SUC (LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh)) /\
      k < SUC (LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh)) /\ j <> k ==>
      DISJOINT (next j) (next k))
Proof
  strip_tac >> drule_all pop_source_support_split >> strip_tac >>
  drule_all pop_recorded_child_offset >> strip_tac >>
  `?next. next 0 = left /\ next 1 = right /\
    (!j. 0 < j /\ j < SUC (LENGTH fresh) ==> next (SUC j) = supps j) /\
    (!j k. j < SUC (LENGTH fresh)+1 /\ k < SUC (LENGTH fresh)+1 /\ j <> k ==>
      DISJOINT (next j) (next k))` by
    (mp_tac (Q.INST [`i` |-> `0`, `n` |-> `SUC (LENGTH (fresh : (subscript list # value) list))`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:num``] pop_family_transfer))) >> simp[]) >>
  qexists_tac `next` >> simp[record_pop_def] >>
  rpt gen_tac >> Cases_on `j` >> simp[] >> strip_tac >> gvs[]
QED

Theorem pop_history_replace_other:
  j < LENGTH pre + SUC (LENGTH post) /\ j <> LENGTH pre ==>
  EL j (pre ++ (p,new)::post) = EL j (pre ++ (p,old)::post)
Proof
  strip_tac >> simp[EL_APPEND_EQN] >> Cases_on `j < LENGTH pre` >> simp[] >>
  `0 < j - LENGTH pre` by decide_tac >> Cases_on `j - LENGTH pre` >> gvs[]
QED

Theorem pop_historical_inventory_step:
  pop_live_support rt root addr (supps 0) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?k tv. mem_path_offset rt p = SOME (k,tv) /\
      pop_live_support tv v (addr+k) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) /\
  read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  vyperValueOperation$popped_value (ArrayV (DynArrayV vs)) = INL child /\
  vyperValueOperation$pop_element (ArrayV (DynArrayV vs)) = INL short /\
  replace_popped rt q short fresh = SOME fresh' ==>
  ?next. pop_live_support rt root addr (next 0) /\
    (!j p v. j < LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh') /\
      EL j (record_pop q (ArrayV (DynArrayV vs)) child fresh') = (p,v) ==>
      ?k tv. mem_path_offset rt p = SOME (k,tv) /\
        pop_live_support tv v (addr+k) (next (SUC j))) /\
    (!j k. j < SUC (LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh')) /\
      k < SUC (LENGTH (record_pop q (ArrayV (DynArrayV vs)) child fresh')) /\ j <> k ==>
      DISJOINT (next j) (next k))
Proof
  strip_tac >> drule_all pop_historical_support_split >> strip_tac >>
  `?next. next 0 = supps 0 /\ next 1 = right /\
    (!j. 0 < j /\ j < SUC (LENGTH fresh) ==>
      next (SUC j) = if j = SUC (LENGTH pre) then left else supps j) /\
    (!j k. j < SUC (LENGTH fresh)+1 /\ k < SUC (LENGTH fresh)+1 /\ j <> k ==>
      DISJOINT (next j) (next k))` by
    (mp_tac (Q.INST [`i` |-> `SUC (LENGTH (pre : (subscript list # value) list))`,
       `n` |-> `SUC (LENGTH (fresh : (subscript list # value) list))`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:num``] pop_family_transfer))) >> simp[]) >>
  qexists_tac `next` >> gvs[record_pop_def] >>
  rpt gen_tac >> Cases_on `j` >> simp[] >> strip_tac >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  Cases_on `n = LENGTH pre`
  >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  simp[] >>
  `EL n (pre ++ (p,old)::post) = (p',v)` by
    (`n < LENGTH pre + SUC (LENGTH post)` by decide_tac >>
     metis_tac[pop_history_replace_other]) >>
  qpat_x_assum `!j p' v. _` irule >> simp[]
QED

Theorem pop_owner_inventory_step:
  pop_owner_step rt root fresh q root' fresh' /\
  pop_live_support rt root addr (supps 0) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?k tv. mem_path_offset rt p = SOME (k,tv) /\
      pop_live_support tv v (addr+k) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) ==>
  ?next. pop_live_support rt root' addr (next 0) /\
    (!j p v. j < LENGTH fresh' /\ EL j fresh' = (p,v) ==>
      ?k tv. mem_path_offset rt p = SOME (k,tv) /\
        pop_live_support tv v (addr+k) (next (SUC j))) /\
    (!j k. j < SUC (LENGTH fresh') /\ k < SUC (LENGTH fresh') /\ j <> k ==>
      DISJOINT (next j) (next k))
Proof
  strip_tac >> drule pop_owner_step_invert >> strip_tac
  >- (drule_all pop_live_inventory_step >> simp[]) >>
  drule_all pop_historical_inventory_step >> simp[]
QED

Theorem pop_owner_reachable_support:
  !rt initial root fresh. pop_owner_reachable rt initial root fresh ==>
  well_formed_type_value rt /\ value_has_type rt initial ==>
  !addr. ?supps. pop_live_support rt root addr (supps 0) /\
    (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
      ?k tv. mem_path_offset rt p = SOME (k,tv) /\
        pop_live_support tv v (addr+k) (supps (SUC j))) /\
    (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
      DISJOINT (supps j) (supps k))
Proof
  ho_match_mp_tac pop_owner_reachable_ind >> rpt strip_tac
  >- (drule_all pop_live_support_exists >> disch_then (qspec_then `addr` mp_tac) >>
      strip_tac >> qexists_tac `\j. supp` >> simp[]) >>
  first_x_assum drule_all >> disch_then (qspec_then `addr` mp_tac) >> strip_tac >>
  drule_all pop_owner_inventory_step >> simp[]
QED

Theorem pop_inventory_live_header_exclusion:
  pop_live_support rt root addr (supps 0) /\
  evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  (!j k. j < n /\ k < n /\ j <> k ==> DISJOINT (supps j) (supps k)) /\
  0 < n ==>
  !j. 0 < j /\ j < n ==>
    DISJOINT {x | addr+k <= x /\ x < addr+k+32} (supps j)
Proof
  strip_tac >> drule_all pop_path_support_header >> strip_tac >>
  rpt strip_tac >> metis_tac[pop_family_selected_exclusion, NOT_ZERO_LT_ZERO]
QED

Theorem pop_inventory_historical_header_exclusion:
  read_popped rt q fresh = SOME (ArrayV (DynArrayV vs)) /\
  (!j p v. j < LENGTH fresh /\ EL j fresh = (p,v) ==>
    ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
      pop_live_support ptv v (addr+kp) (supps (SUC j))) /\
  (!j k. j < SUC (LENGTH fresh) /\ k < SUC (LENGTH fresh) /\ j <> k ==>
    DISJOINT (supps j) (supps k)) ==>
  ?pre p old post k et cap.
    fresh = pre ++ (p,old)::post /\ read_popped rt q pre = NONE /\
    mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
    {x | addr+k <= x /\ x < addr+k+32} SUBSET supps (SUC (LENGTH pre)) /\
    (!j. j < SUC (LENGTH fresh) /\ j <> SUC (LENGTH pre) ==>
      DISJOINT {x | addr+k <= x /\ x < addr+k+32} (supps j))
Proof
  strip_tac >> drule pop_owner_read_decompose >> strip_tac >>
  `?kp ot. mem_path_offset rt p = SOME (kp,ot) /\
    pop_live_support ot old (addr+kp) (supps (SUC (LENGTH pre)))` by
    (first_x_assum (qspecl_then [`LENGTH pre`, `p`, `old`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  drule mem_path_offset_sound >> strip_tac >> gvs[] >>
  drule_all pop_supported_array_offset >> strip_tac >>
  drule_all pop_path_support_header >> strip_tac >>
  `mem_path_offset rt q = SOME (kp+k,ArrayTV et (Dynamic cap))` by
    (irule pop_prefix_drop_offset >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`pre`, `p`, `old`, `post`, `kp+k`, `et`, `cap`] >>
  FULL_SIMP_TAC bool_ss [GSYM ADD_ASSOC] >> simp[] >>
  rpt strip_tac >>
  `SUC (LENGTH pre) < SUC (LENGTH pre + SUC (LENGTH post)) /\
   j < SUC (LENGTH pre + SUC (LENGTH post))` by decide_tac >>
  FULL_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >>
  metis_tac[pop_family_selected_exclusion]
QED
