(* The owned base buffer survives the forced key at the reached cut. *)
Theory bodyArrayOwnedMemoryAtKeyMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayOwnedSelectViewMods
  bodyFullSubscriptCapturedPlace exprSimSubscriptArraySuffix
  exprSimSubscriptArrayCompose exprSimIfExpWidenedOwnedProvenance
  bodyPtrBopHashFootprint bodyPtrBopInMemoryContents typedCopyLayoutPtr
  typedMemoryCopy instMemFrontier stateRelProj venomMemDefs valueTypingMemoryProps
  loweringPosts exprSimProps bodyFullPostsMods exprSimMemDefs bodyPtrDefs
  bodyFullShadowBodyInv ptrDiscipline vyperState vyperStorageFootprint
  vyperTyping valueEncodingProps compileEnv context words finite_map
Libs
  monadsyntax

Theorem owned_array_normalize_own[local]:
  vv_own ce cx ty sa sm ee (Value v) vv u /\
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  ~is_word_type ty /\ sm.cs_next_id <= sn.cs_next_id ==>
  vv_own ce cx ty sa sn ee (Value v)
    (LocatedValue ann (mk_ptr (vv_operand vv) LocMemory)) u
Proof
  Cases_on `vv` >>
  simp[vv_own_def, expr_val_own_def, vv_operand_def, mk_ptr_def,
       read_result_def, return_def] >>
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> disj1_tac >>
  rename1 `FLOOKUP u.vs_allocas aid = SOME (b,sz)` >>
  qexistsl [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem owned_array_normalize_ptr[local]:
  ptr_vv_ok cx ty (Value v) vv ee G tn u /\
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  ~is_word_type ty ==>
  ptr_vv_ok cx ty (Value v) (LocatedValue ty (mk_ptr (vv_operand vv) LocMemory)) ee G tn u
Proof
  Cases_on `vv` >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, vv_operand_def, mk_ptr_def,
       read_result_def, return_def] >> strip_tac >> gvs[]
QED

Theorem owned_array_normalize_post[local]:
  vv_post_mods H ctx func ce cx obj es sa sm s0 mid (Value v) vv s /\
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  ~is_word_type (post_value_type ce obj) /\
  vv_at ce cx (post_value_type ce obj) sa sm mid (Value v)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand vv) LocMemory)) s /\
  vv_own ce cx (post_value_type ce obj) sa sm mid (Value v)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand vv) LocMemory)) s ==>
  vv_post H ctx func ce cx obj es sa sm s0 mid (Value v)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand vv) LocMemory)) s
Proof
  Cases_on `vv` >>
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, vv_operand_def, mk_ptr_def] >>
  strip_tac
  >- (fs[vv_holds_def, expr_val_rel_def, read_result_def, return_def] >>
      first_assum ACCEPT_TAC) >>
  fs[vv_holds_def] >> first_assum ACCEPT_TAC
QED

Theorem owned_array_positive_extent[local]:
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  ptr_mem_ok cx (ArrayT et bd) (ArrayV av) bop Gi tni it /\
  vv_own ce cx (ArrayT et bd) sa sn fin (Value (ArrayV av))
    (LocatedValue (ArrayT et bd) (mk_ptr bop LocMemory)) it /\
  eval_operand bop it = SOME a /\ alloca_next_valid it /\
  type_memory_size (ArrayTV etv bd) <> 0 ==>
  w2n a + type_memory_size (ArrayTV etv bd) <= it.vs_alloca_next /\
  ?base len. op_prov Gi bop = SOME (base,len) /\ base <= w2n a /\
    w2n a + type_memory_size (ArrayTV etv bd) <= base + len
Proof
  strip_tac >>
  `val_footprint (ArrayTV etv bd) (ArrayV av) <> 0` by simp[val_footprint_def] >>
  drule_all_then strip_assume_tac ptr_mem_ok_bounds >>
  conj_tac
  >- (qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_own_def, mk_ptr_def, read_result_def, return_def, val_footprint_def] >>
      strip_tac >>
      `w2n a + type_memory_size (ArrayTV etv bd) <= it.vs_alloca_next` by
        (irule alloca_region_below_frontier >> simp[] >>
         qexistsl [`aid`,`b'`,`sz'`] >> gvs[]) >>
      decide_tac) >>
  qexistsl [`b`,`sz`] >> fs[op_prov_def, val_store_size_def]
QED

Theorem owned_array_live_header[local]:
  value_has_type (ArrayTV etv (Dynamic cap)) v /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV etv (Dynamic cap)) v (w2n a) m) ==>
  ?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\
       mem_word_taint tn.t_mem (w2n a) = {} /\
       mload (w2n a) u = n2w (LENGTH vs)
Proof
  strip_tac >> drule_then strip_assume_tac typed_copy_dynarray_typed_value >>
  gvs[] >> conj_tac
  >- (irule dynarray_memory_header_clean >> goal_assum (drule_at Any)) >>
  drule dynarray_in_memory_robust_length >>
  disch_then (qspec_then `u.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def, mem_word_at_eq_mload]
QED

Theorem owned_array_packet[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) v /\ val_wf (ArrayTV etv bd) v /\
  vv_own ce cx (ArrayT et bd) sa sn fin (Value v)
    (LocatedValue (ArrayT et bd) (mk_ptr bop LocMemory)) it /\
  ptr_vv_ok cx (ArrayT et bd) (Value v)
    (LocatedValue (ArrayT et bd) (mk_ptr bop LocMemory)) fin Gi tni it /\
  eval_operand bop it = SOME a /\ alloca_next_valid it /\
  w2n a + type_memory_size (ArrayTV etv bd) < dimword (:256) ==>
  array_owned_memory_view_mods ce cx (et,bd,etv) (sa,sn) (fin,v) (bop,it,Gi,tni,a)
Proof
  strip_tac >>
  `op_taint tni bop = {} /\ ptr_mem_ok cx (ArrayT et bd) v bop Gi tni it` by
    fs[ptr_vv_ok_def, mk_ptr_def, read_result_def, return_def] >>
  `!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
       val_in_memory (ArrayTV etv bd) v (w2n a) m` by
    (gen_tac >> strip_tac >> irule ptr_mem_ok_robust >>
     goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >> simp[]) >>
  `vv_at ce cx (ArrayT et bd) sa sn fin (Value v)
    (LocatedValue (ArrayT et bd) (mk_ptr bop LocMemory)) it` by
    (irule vv_own_memory_transport >>
     qexistsl [`ArrayTV etv bd`,`ArrayTV etv bd`,`ArrayT et bd`,`ArrayT et bd`,`v`] >>
     simp[read_result_def, return_def]) >>
  simp[array_owned_memory_view_mods_def] >> conj_tac
  >- (strip_tac >>
      `?av. v = ArrayV av` by
        (qpat_assum `value_has_type (ArrayTV _ _) v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `v` >> simp[value_has_type_def]) >>
      gvs[] >> drule_all owned_array_positive_extent >> simp[]) >>
  rpt strip_tac >> gvs[] >> irule owned_array_live_header >> qexists `etv` >> simp[]
QED

Theorem array_owned_memory_at_key_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,Value v,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) v /\
  (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand bvv <> Label l) ==>
  loc = LocMemory /\ ?a. array_owned_memory_view_mods ce cx (et,bd,etv) (sa,st2)
    (fin,v) (vv_operand bvv,it,Gi,tni,a)
Proof
  rewrite_tac[array_nocopy_cut_mods_def] >> strip_tac >>
  `~is_word_type (post_value_type ce obj) /\ ~is_bytestring_type (post_value_type ce obj)` by
    simp[is_word_type_def, is_bytestring_type_def] >>
  qpat_x_assum `!w. Value v = Value w /\ _ ==> _`
    (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  conj_tac >- (Cases_on `bvv` >> gvs[vv_location_def]) >>
  qabbrev_tac `H = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H fin.storage_trace` by fs[Abbr `H`, storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  drule_all_then assume_tac owned_array_normalize_ptr >>
  `vv_own ce cx (post_value_type ce obj) sa sm mid (Value v)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand bvv) LocMemory)) s` by
    (irule owned_array_normalize_own >> simp[] >> qexists `sm` >> simp[]) >>
  `vv_at ce cx (post_value_type ce obj) sa sm mid (Value v)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand bvv) LocMemory)) s` by
    (irule vv_own_memory_transport >>
     goal_assum (drule_at (Pat `vv_own _ _ _ _ _ _ _ _ _`)) >>
     qexistsl [`ArrayTV etv bd`,`ArrayTV etv bd`,`v`] >>
     simp[read_result_def, return_def, value_has_type_memory_wf]) >>
  drule_all_then assume_tac owned_array_normalize_post >>
  suspend "carry"
QED

Resume array_owned_memory_at_key_mods[carry]:
  qabbrev_tac `bop = vv_operand bvv` >>
  qabbrev_tac `p = mk_ptr bop LocMemory` >>
  `p.ptr_location = LocMemory /\ p.ptr_operand = bop` by simp[Abbr `p`, mk_ptr_def] >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME (ArrayTV etv bd)` by simp[] >>
  `expr_post H ctx func ce cx idx (mid with gas_obs := gs2) sm st2 s fin key iop it` by
    fs[expr_post_mods_def, expr_post_initial_gas] >>
  `ghost_kept_at lo ce (mid with gas_obs := gs2) sm G1 tn1 s Gi tni` by
    (qpat_x_assum `ghost_kept_at lo ce mid sm _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_kept_at_def, vyperStateTheory.evaluation_state_accfupds]) >>
  `(!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l)` by simp[] >>
  drule_all_then strip_assume_tac subscript_owned_value_transport >>
  rename1 `eval_operand p.ptr_operand it = SOME a` >> qexists `a` >>
  `read_result cx (Value v) mid = (INL v,mid)` by simp[read_result_def, return_def] >>
  `evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv bd)` by simp[] >>
  `w2n a + val_footprint (ArrayTV etv bd) v < dimword (:256)` by
    (drule_all vv_post_memory_footprint_bound >> simp[]) >>
  `?av. v = ArrayV av` by
        (qpat_assum `value_has_type (ArrayTV _ _) v` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `v` >> simp[value_has_type_def]) >>
  `alloca_next_valid it` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ it` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     drule_then (strip_assume_tac) stmt_state_rel_local_ptrs_alloca >> fs[alloca_inv_def]) >>
  irule owned_array_packet >> simp[] >> conj_tac
  >- (qpat_x_assum `v = ArrayV av` SUBST_ALL_TAC >>
      qpat_x_assum `_ + val_footprint _ _ < _` mp_tac >> simp[val_footprint_def]) >>
  qpat_x_assum `expr_type obj = ArrayT et bd`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_x_assum `post_value_type ce obj = ArrayT et bd`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  conj_tac >- (qpat_assum `p.ptr_operand = bop` (fn th => once_rewrite_tac[SYM th]) >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- (gvs[]) >>
  qpat_assum `vv_own _ _ _ sa sm fin _ _ it`
    (mp_then Any mp_tac owned_array_normalize_own) >>
  disch_then (qspecl_then [`st2`,`ArrayT et bd`] mp_tac) >>
  simp[vv_operand_def, Abbr `p`, is_word_type_def]
QED

Finalise array_owned_memory_at_key_mods
