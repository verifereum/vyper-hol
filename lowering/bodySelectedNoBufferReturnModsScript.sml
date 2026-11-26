(* Interpret the selected no-buffer result at the advanced caller cursor. *)
Theory bodySelectedNoBufferReturnMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprSimHypsDefs typedMemoryCopy
  exprSimProps exprLoweringProps exprSimMemDefs valueEncodingProofs
  valueEncodingTyping vyperTypeArgFits
  bodyPtrDefs ptrDiscipline loweringStateRelDefs venomState
  exprLowering loweringPosts compileEnv context vyperInterpreter
  vyperValue valueEncoding vyperTypeSystem vyperTypeValues vyperState bodyInvSplit
  vyperMisc

Theorem no_buffer_immutable_cursor[local]:
  immutable_frame_mods func cenv cx es (s with vs_inst_idx := pc) <=>
  immutable_frame_mods func cenv cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       local_region_def, lookup_var_def]
QED

Theorem no_buffer_ghost_cursor[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn (s with vs_inst_idx := pc) <=>
  ghost_inv_at_mods D lo d cenv cx es G tn s
Proof
  Cases_on `d` >>
  simp[ghost_inv_at_mods_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_at_def, allocas_from_def, lookup_var_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem no_buffer_type_layout[local]:
  expr_sim_inv_mods mods cenv cx tenv es /\
  evaluate_type (get_tenv cx) ret = SOME rtv ==>
  type_memory_bytes cenv ret = type_memory_size rtv
Proof
  strip_tac >> irule typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >> fs[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem zero_layout_not_word_or_bytes[local]:
  type_memory_bytes cenv ty = 0 ==> ~is_word_type ty /\ ~is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def] >>
  Cases_on `b` >> gvs[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def]
QED

Theorem selected_no_buffer_return_post_mods:
  !ann src name es dflt u i mods cenv cx tenv es0 ret rtv v vv H ctx
   func ee DF lo d J N sa G0 tn0 s0 sm.
  let e = Call ann (IntCall (src,name)) es dflt in
  let a = u with vs_inst_idx := i in
    expr_sim_inv_mods mods cenv cx tenv es0 /\
    cenv.ce_func_return_type (nsid_to_string (src,name)) = ret /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    value_has_type rtv v /\ type_widens_to (get_tenv cx) ret ann /\
    (ret = NoneT \/ type_memory_bytes cenv ret = 0) /\
    vv = StackValue ret (Lit 0w) /\
    stmt_state_rel H ctx func cenv cx ee u /\
    immutable_frame_mods func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee J N u /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 J N /\
    locals_kept cenv es0 ee s0 u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
            lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
       aid < sa.cs_next_id /\
       (!n lb lsz. local_region cenv es0.scopes s0 n lb lsz ==>
                   b + sz <= lb \/ lb + lsz <= b) ==>
       mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    u.vs_current_bb = sm.cs_current_bb /\ i = LENGTH sm.cs_current_insts /\
    alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    s0.vs_alloca_next <= u.vs_alloca_next ==>
    vv_post_mods H ctx func cenv cx e es0 sa sm s0 ee (Value v) vv a /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
      ee (Value v) vv a /\
    a.vs_current_bb = sm.cs_current_bb /\
    a.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    s0.vs_alloca_next <= a.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee J N a /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) vv ee J N a /\
    (!w. Value v = Value w /\ ~is_word_type (post_value_type cenv e) /\
         ~is_bytestring_type (post_value_type cenv e) ==>
         vv_own cenv cx (post_value_type cenv e) sa sm ee (Value v) vv a /\
         (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx (Value v) ee = (INL val,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) a = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside N.t_mem a.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
             ptr_buf_ok cenv e op J a) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand J a) /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 J N
Proof
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes cenv ret = 0 /\ type_memory_size rtv = 0` by
    (Cases_on `ret = NoneT`
     >- fs[type_memory_bytes_def, evaluate_type_def, type_memory_size_def] >>
     drule_all no_buffer_type_layout >> fs[]) >>
  drule zero_layout_not_word_or_bytes >> strip_tac >>
  `~is_word_type ann /\ ~is_bytestring_type ann` by
    metis_tac[type_widens_to_word, type_widens_to_def, arg_type_fits_bytestring_source] >>
  drule_then assume_tac (CONJUNCT1 value_has_type_val_wf) >>
  drule_all_then assume_tac return_zero_wf_memory >>
  `val_footprint rtv v = 0` by (drule_then mp_tac val_footprint_le >> simp[]) >>
  `val_store_size rtv v = 0` by (drule_then mp_tac val_store_size_le >> simp[]) >>
  simp[lowered_value_type_def, vv_location_def, no_buffer_ghost_cursor,
       vv_store_bound_def, ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
       ptr_buf_ok_def, op_taint_def, eval_operand_def, read_result_def,
       return_def, vv_own_def, expr_val_own_def] >>
  simp[vv_post_mods_def, lowered_value_type_def, stmt_state_rel_inst_idx,
       no_buffer_immutable_cursor, lookup_var_def, vv_holds_mods_def, vv_holds_def,
       vv_at_def, vv_place_ptr_mods_def, vv_place_ptr_def, vv_own_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def,
       eval_operand_def, read_result_def, return_def] >>
  conj_tac
  >- (qpat_assum `!x w. not_fresh_at sa x /\ _ ==> lookup_var x u = SOME w`
        (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
  first_assum ACCEPT_TAC
QED
