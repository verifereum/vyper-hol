(* Reassemble the success post at the single tuple ADD endpoint. *)
Theory bodySubscriptTuplePostMods
Ancestors
  bodySubscriptTupleGeometryMods bodySubscriptTuplePlacePtrMods
  bodySubscriptTupleMemoryPostMods bodySubscriptTupleSlotsPostMods
  bodySubscriptTupleCodePostMods bodyFullPostsMods
  typedMemoryCopy exprSimHypsDefs exprSimCopy exprSimVVFrame exprSimMemDefs
  exprSimProps exprSimAttributeProps exprLoweringProps vyperAST exprLowering ptrDiscipline valueEncoding vyperValue
  vyperPlaceResultTyping supportedExprTraverse loweringPosts compileEnv context
  vyperInterpreter vyperState venomState finite_map words

Theorem tuple_linked_sizes[local]:
  expr_sim_inv_mods mods cenv cx env ee ==>
  !ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
          type_memory_bytes cenv ty = type_memory_size rt
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
  qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
    drule >> simp[]
QED

Theorem tuple_loc_cases[local]:
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t ==>
  vv_loc bvv = LocMemory \/ vv_loc bvv = LocCode \/ ?tr. vv_loc bvv = slot_loc tr
Proof
  Cases_on `bvv` >> simp[vv_loc_def, vv_location_def, vv_holds_mods_def] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[vv_holds_def] >> metis_tac[slot_loc_def]
QED

Theorem selected_nonmemory_at[local]:
  vv_loc bvv <> LocMemory /\ vv_at cenv cx (TupleT tys) sa sb ee raw bvv t /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL raw',ee) ==>
  vv_at cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >> drule_then assume_tac select_result_memory_place >>
  simp[vv_at_def,mk_ptr_def] >> rpt strip_tac >>
  `?p. raw = PlaceR (MemoryPlace id p)` by metis_tac[] >>
  Cases_on `bvv` >> fs[vv_at_def,vv_loc_def,vv_location_def,is_word_type_def]
QED

Theorem tuple_selected_value_base[local]:
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL (Value v),ee) ==>
  ?u. raw = Value u
Proof
  Cases_on `raw` >> simp[select_result_def,raise_def] >> strip_tac >>
  drule_then strip_assume_tac extend_place_result_shape >> gvs[]
QED

Theorem tuple_subscript_selected_post_mods:
  expr_sim_inv_mods mods cenv cx env ee /\
  eval_result_typed (env,cx,ee) raw (Type (TupleT tys)) /\
  post_value_type cenv obj = TupleT tys /\ k < LENGTH tys /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  values_have_types tvs vs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL raw',ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\
  vv_post_mods H ctx func cenv cx obj es sa sb s0 ee raw bvv t /\
  vv_store_bound cx (TupleT tys) (lowered_value_type cenv obj) ee raw bvv s /\
  ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  (!v. raw = Value v ==> vv_own cenv cx (TupleT tys) sa sm ee raw bvv s /\
                         vv_loc bvv = LocMemory) /\
  (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt a. evaluate_type (get_tenv cx) (TupleT tys) = SOME rt /\
              eval_operand (vv_operand bvv) s = SOME a ==>
              w2n a + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n a) mem)) /\
  eval_operand (vv_operand bvv) s = SOME w /\ eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  dst = Var out /\ FLOOKUP G' out = op_prov G (vv_operand bvv) /\ op_taint tn' dst = {} /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  local_ptrs_reserved cenv sm /\ sm.cs_next_id <= sb.cs_next_id /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' ==>
  let ann = EL k tys;
      e = Subscript ann obj (Literal ity (IntL (&k)));
      vv = LocatedValue ann (mk_ptr dst (vv_loc bvv)) in
    vv_post_mods H ctx func cenv cx e es sa sb s0 ee raw' vv t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw' vv t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
    ptr_vv_ok cx (post_value_type cenv e) raw' vv ee G' tn' t /\
    (!v. raw' = Value v /\ ~is_word_type (post_value_type cenv e) /\
         ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee raw' vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx raw' ee = (INL v,ee) /\
         !rt a. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) t = SOME a ==>
                w2n a + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n a) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
             ptr_buf_ok cenv e op G' t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand G' t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => rpt conj_tac >> simp[SimpLHS,Once th])) >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  drule_then assume_tac tuple_linked_sizes >>
  drule_all_then strip_assume_tac tuple_subscript_geometry_mods >>
  qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `post_value_type cenv obj = TupleT tys`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `!tag op. bvv = StackValue tag op ==> !pl. raw <> PlaceR pl` by
    (rpt strip_tac >> fs[vv_at_def,is_word_type_def]) >>
  `vv_place_ptr_mods cenv cx ee t raw' (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv)))` by
    (irule tuple_subscript_place_ptr_mods >>
     conj_tac >- (qexists_tac `w` >> simp[]) >>
     conj_tac >- (qexists_tac `tvs` >> simp[] >> metis_tac[]) >>
     qexistsl_tac [`env`,`ee`,`mods`,`raw`] >> simp[]) >>
  `!v. raw' = Value v ==> vv_loc bvv = LocMemory` by
    (rpt strip_tac >> qpat_assum `raw' = Value v` (fn eq =>
       qpat_assum `select_result _ _ _ _ _ = _`
         (strip_assume_tac o MATCH_MP tuple_selected_value_base o REWRITE_RULE [eq])) >>
     qpat_assum `!v. raw = Value v ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  simp[LET_THM, expr_type_def, lowered_value_type_def] >>
  drule_then strip_assume_tac tuple_loc_cases
  >- suspend "memory"
  >- suspend "code" >>
  suspend "slots"
QED

Resume tuple_subscript_selected_post_mods[memory]:
  `!v. raw = Value v ==> vv_own cenv cx (TupleT tys) sa sb ee raw bvv t` by
    (rpt strip_tac >> qpat_assum `!v. raw = Value v ==> _` (drule_then strip_assume_tac) >>
     irule vv_own_vars_frame >> goal_assum (drule_at (Pat `vv_own _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> drule_all copy_buffer_local_region_frame >>
     disch_then (qspecl_then [`ee.scopes`,`n`,`b`,`sz`] mp_tac) >> simp[]) >>
  `!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. dst = Var y /\ FLOOKUP G' y = SOME (b,sz)` by simp[op_prov_def] >>
  `eval_operand dst t = SOME (w + n2w (SUM (MAP type_memory_size (TAKE k tvs))))` by simp[] >>
  `type_memory_bytes cenv (lowered_value_type cenv (Subscript (EL k tys) obj (Literal ity (IntL (&k))))) =
     type_memory_size (EL k tvs)` by simp[lowered_value_type_def,expr_type_def] >>
  qabbrev_tac `vv = LocatedValue (EL k tys) (mk_ptr dst LocMemory)` >>
  `vv_holds_mods cenv cx (EL k tys) raw' vv ee t /\
   vv_at cenv cx (EL k tys) sa sb ee raw' vv t /\
   vv_store_bound cx (EL k tys) (EL k tys) ee raw' vv t /\
   ptr_vv_ok cx (EL k tys) raw' vv ee G' tn' t /\
   ptr_buf_ok cenv (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) dst G' t /\
   (!v. raw' = Value v /\ ~is_word_type (EL k tys) /\ ~is_bytestring_type (EL k tys) ==>
     vv_own cenv cx (EL k tys) sa sb ee raw' vv t)` by
    (unabbrev_all_tac >> irule (PURE_REWRITE_RULE [LET_THM] tuple_subscript_memory_post_mods |> BETA_RULE) >>
     simp[] >> conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `read_result cx raw ee = _`)) >>
     qexists_tac `lowered_value_type cenv obj` >> simp[op_prov_def] >>
     rpt strip_tac >> qpat_assum `raw = Value v` (SUBST1_TAC o SYM) >>
     qpat_assum `!v. raw = Value v ==> vv_own _ _ _ _ sb _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  fs[Abbr `vv`,mk_ptr_def,vv_location_def,vv_post_mods_def,expr_type_def] >>
  rpt conj_tac >> rpt strip_tac >>
  first_assum (drule_all_then ACCEPT_TAC)
QED

Resume tuple_subscript_selected_post_mods[code]:
  `eval_operand dst t = SOME (w + n2w (SUM (MAP type_memory_size (TAKE k tvs))))` by simp[] >>
  `vv_at cenv cx (EL k tys) sa sb ee raw' (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) t` by
    (irule selected_nonmemory_at >> simp[] >> qexistsl_tac [`k`,`raw`,`tys`] >> simp[]) >>
  qabbrev_tac `vv = LocatedValue (EL k tys) (mk_ptr dst LocCode)` >>
  `vv_holds_mods cenv cx (EL k tys) raw' vv ee t /\
   ptr_vv_ok cx (EL k tys) raw' vv ee G' tn' t /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw' ee = (INL v,ee) /\
        !rt a. evaluate_type (get_tenv cx) (EL k tys) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME a ==>
               w2n a + type_memory_size rt <= lo /\
               (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                      val_in_memory rt v (w2n a) mem))` by
    (unabbrev_all_tac >> irule (PURE_REWRITE_RULE [LET_THM] tuple_subscript_code_post_mods |> BETA_RULE) >>
     simp[] >> goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `read_result cx raw ee = _`)) >>
     simp[] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor /\ vv_location bvv = _ ==> _` mp_tac >> simp[]) >>
  `!v. raw' <> Value v` by (rpt strip_tac >> qpat_assum `!v. raw' = Value v ==> _` drule >> simp[]) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  qpat_assum `vv_loc bvv = LocCode` SUBST_ALL_TAC >>
  fs[Abbr `vv`,mk_ptr_def,vv_location_def,vv_operand_def,vv_post_mods_def,
     expr_type_def,vv_store_bound_nonmem] >>
  qpat_x_assum `cenv.ce_is_ctor ==> ?v. read_result cx raw' ee = _ /\ _` mp_tac >>
  simp[] >> rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC)
QED

Resume tuple_subscript_selected_post_mods[slots]:
  `eval_operand dst t = SOME (w + n2w (tuple_prefix_slot_size k tvs))` by simp[] >>
  `slot_loc tr <> LocMemory /\ slot_loc tr <> LocCode` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  `vv_at cenv cx (EL k tys) sa sb ee raw' (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) t` by
    (irule selected_nonmemory_at >> simp[] >> qexistsl_tac [`k`,`raw`,`tys`] >> simp[]) >>
  drule_all_then (qspecl_then [`H`,`G'`] strip_assume_tac) tuple_subscript_slots_post_mods >>
  `!v. raw' <> Value v` by (rpt strip_tac >> qpat_assum `!v. raw' = Value v ==> _` drule >> simp[]) >>
  `~expr_has_effect obj ==> vv_storage_live H cx
     (LocatedValue (EL k tys) (mk_ptr dst (slot_loc tr))) ee t` by
    (strip_tac >> qpat_assum `vv_storage_live _ _ bvv _ _ ==> _` irule >> simp[]) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  qpat_assum `vv_loc bvv = slot_loc tr` SUBST_ALL_TAC >>
  fs[mk_ptr_def,vv_location_def,vv_post_mods_def,expr_type_def,vv_store_bound_nonmem] >>
  rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC)
QED

Finalise tuple_subscript_selected_post_mods
