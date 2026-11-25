(* Extend one reached target by the checked offset of its field. *)
Theory bodyWriteFieldStageMods
Ancestors
  bodyWriteTargetStageMods placeMemoryTypedBase exprSimFieldLayout
  targetPtrFacts stmtSimAssignAttrStorage bodyFullTargetRoots
  exprSimAttributeFields exprSimWordArgs vyperTypeExprSoundness
  vyperTypeEnv vyperTypeInvariants vyperValue vyperState vyperInterpreter
  exprSimHypsDefs loweringPosts loweringStateRelDefs finite_map list alist pair
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyFullAttributeAdd bodyFullPathHistory bodyFullShared
  allocasBelowFmpUpdatesProps bodyInvSplit bodyFullShadowBodyInv
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompile
  exprLoweringProps emitHelperProps words vyperTypeSystem compileEnv
  bodyFullTargetDefs targetPlaceSimCasesBase vyperPlaceTyping exprLowering
  bodyFullPostsMods bodyPtrDefs ptrDiscipline fragGasOriginPtr venomState venomInst
  emitHelper decoderGhostFramePtr vyperAST targetPlaceSimDefs exprSimDefs
  gasContext vyperStorageFootprint vyperStorageTrace gasShadow gasShadowState
  exprBodyPreProps stmtLoweringMono fragExec gasShadowCompileBase
  targetPlaceSim allocLimits arithmetic

Theorem field_layout_zip[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
                            sz = type_memory_size tv) fields ==>
    fields_layout fields (ZIP (MAP FST fields,tvs))
Proof
  Induct >> simp[fields_layout_def] >> PairCases >> rpt strip_tac >> gvs[fields_layout_def]
QED

Theorem field_layout_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME tv /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
  ?fs ftv fsz.
    tv = StructTV fs /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) fty = SOME ftv
Proof
  strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def] >>
  drule_all_then strip_assume_tac typed_memory_struct_evaluation >>
  `ALOOKUP args fld = SOME fty` by fs[attribute_type_def] >>
  `?fsz. ALOOKUP fields fld = SOME (fty,fsz)` by
    (qabbrev_tac `g : (string # type # num) -> (string # type) = \(k,v). (k,FST v)` >>
     `MAP FST (MAP g fields) = MAP FST args /\
      MAP SND (MAP g fields) = MAP SND args` by
       (simp[Abbr `g`, MAP_MAP_o, combinTheory.o_DEF, pairTheory.UNCURRY_VAR] >>
        asm_simp_tac bool_ss [ETA_THM, GSYM combinTheory.o_DEF]) >>
     `MAP g fields = args` by metis_tac[ZIP_UNZIP, UNZIP_MAP] >>
     qpat_x_assum `ALOOKUP args fld = _` mp_tac >>
     pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
     Cases_on `ALOOKUP fields fld` >> simp[Abbr `g`, ALOOKUP_MAP, combinTheory.o_THM] >>
     PairCases_on `x` >> simp[]) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP SND args) = SOME tvs` by
    (fs[vyperValueTheory.evaluate_types_OPT_MMAP] >> metis_tac[]) >>
  drule_all_then strip_assume_tac OPT_MMAP_ALOOKUP_ZIP >>
  rename1 `evaluate_type (get_tenv cx) fty = SOME ftv` >>
  `fields_layout fields (ZIP (MAP FST fields,tvs))` by
    (irule field_layout_zip >> qexists_tac `get_tenv cx` >>
     simp[] >> fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qexistsl_tac [`ZIP (MAP FST fields,tvs)`, `ftv`, `fsz`] >>
  fs[get_struct_fields_def] >>
  qpat_x_assum `MAP FST fields = MAP FST args` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

(* The field of an ordinary place uses byte offsets in memory and slot
   offsets in either storage backend. *)
Theorem ordinary_field_source[local]:
  expr_sim_inv_mods mods cenv cx env es /\ popped_keys_indexed mid.scopes /\
  place_ptr_rel cenv cx t pv w loc (Type (StructT sid)) /\
  place_readable cx mid pv /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
  (!m. FST (extend_place cx pv (AttrSubscript fld) mid) <>
       INR (Error (TypeError m))) ==>
  ?pv'.
    extend_place cx pv (AttrSubscript fld) mid = (INL pv',mid) /\
    place_readable cx mid pv' /\
    target_field_type cenv (SOME (ValPT (StructT sid))) fld = SOME (ValPT fty) /\
    place_ptr_rel cenv cx t pv'
      (w + n2w (target_field_offset cenv loc (SOME (ValPT (StructT sid))) fld))
      loc (Type fty) /\
    (!rb G tn. target_ptr_ok cenv pv rb G tn t ==> target_ptr_ok cenv pv' rb G tn t) /\
    (!rb G u. write_target_location_mods cenv cx (AttributeTarget bt fld) mid
       pv' (Type fty) rb G u <=>
       place_readable cx mid pv' /\ (?q. eval_operand (FST rb) u = SOME q /\
         place_ptr_rel cenv cx u pv' q (FST (SND rb)) (Type fty)))
Proof
  strip_tac >> Cases_on `pv` >> fs[place_ptr_rel_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >> gvs[place_ptr_rel_def]
  >- suspend "slot" >>
  suspend "memory"
QED

Resume ordinary_field_source[slot]:
  rename1 `StoragePlace tr slot tv` >>
  drule_all_then strip_assume_tac field_layout_mods >> gvs[] >>
  Cases_on `extend_storage_place cx tr slot (StructTV fs) (AttrSubscript fld) mid` >>
  rename1 `(res,es')` >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[extend_place_def, bind_def, raise_def]) >>
  drule_all_then strip_assume_tac extend_storage_place_attr >> gvs[] >>
  drule_then assume_tac struct_field_slot_type >> gvs[] >>
  drule_all_then assume_tac struct_field_offset_slots_eq >> gvs[] >>
  Cases_on `tr` >>
  simp[extend_place_def, bind_def, return_def, place_readable_def,
       place_ptr_rel_def, target_ptr_ok_def, target_field_type_def,
       target_field_offset_def, slot_loc_def, write_target_location_mods_def]
QED

Resume ordinary_field_source[memory]:
  rename1 `MemoryPlace id path` >>
  drule_all_then strip_assume_tac field_layout_mods >> gvs[] >>
  Cases_on `extend_place cx (PlaceR (MemoryPlace id path)) (AttrSubscript fld) mid` >>
  rename1 `(res,es')` >> fs[] >>
  drule_all_then strip_assume_tac extend_place_memory_attr >> gvs[] >>
  drule_all_then assume_tac mem_field_offset_layout >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld,ftv)` by simp[mem_step_offset_def] >>
  drule_all_then strip_assume_tac exprSimPropsTheory.mem_path_offset_snoc >>
  simp[place_ptr_rel_def, target_ptr_ok_def, target_field_type_def,
       target_field_offset_def, GSYM word_add_n2w, WORD_ADD_ASSOC,
       write_target_location_mods_def] >> metis_tac[]
QED

Finalise ordinary_field_source

(* Immutable paths keep the original qualified owner; the additional
   offset is relative to the reached value, not to the active module. *)
Theorem immutable_field_source[local]:
  expr_sim_inv_mods mods cenv cx env es /\ state_well_typed mid /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
  ALOOKUP mid.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME ptv /\
  evaluate_subscripts itv iv path = INL v ==>
  ?ftv fv fsz.
    extend_place cx (PlaceR (ImmutablePlace owner id path)) (AttrSubscript fld) mid =
      (INL (PlaceR (ImmutablePlace owner id (path ++ [AttrSubscript fld]))),mid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\
    mem_path_offset itv (path ++ [AttrSubscript fld]) =
      SOME (k + struct_field_offset (get_struct_fields cenv.ce_struct_fields
               (nsid_to_string sid)) fld,ftv) /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    evaluate_subscripts itv iv (path ++ [AttrSubscript fld]) = INL fv /\
    (fixed_shape_path itv path ==> fixed_shape_path itv (path ++ [AttrSubscript fld]))
Proof
  strip_tac >> drule_all_then strip_assume_tac field_layout_mods >> gvs[] >>
  drule_all_then assume_tac mem_field_offset_layout >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld,ftv)` by simp[mem_step_offset_def] >>
  drule_all_then strip_assume_tac exprSimPropsTheory.mem_path_offset_snoc >>
  drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
  drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >>
  qpat_assum `mem_path_offset itv path = _`
    (mp_then Any strip_assume_tac exprSimPropsTheory.mem_path_offset_sound) >>
  `value_has_type (StructTV fs) v` by
    (irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
     goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >> simp[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `struct_has_type fs vals` >>
  `?fv. ALOOKUP vals fld = SOME fv` by
    (Cases_on `ALOOKUP vals fld` >> simp[] >>
     drule_all_then mp_tac vyperTypeStatePreservationTheory.struct_has_type_alookup_none >> simp[]) >>
  drule_all_then assume_tac evaluate_subscripts_snoc_attr >>
  qexists_tac `fv` >> simp[] >>
  conj_tac
  >- simp[extend_place_def, place_type_value_def, read_place_def, get_immutables_def,
          get_address_immutables_def, extend_memory_place_def, bind_def,
          ignore_bind_def, lift_option_type_def, lift_sum_def, return_def,
          evaluate_subscripts_def] >>
  strip_tac >> irule immutable_target_fixed_snoc >>
  simp[] >> qexistsl_tac [`k`,`StructTV fs`] >> simp[]
QED

(* This suffix changes a fresh SSA variable and the cursor, not the
   linked immutable section or any of the preexisting allocations. *)
Theorem field_add_immutable_frame[local]:
  immutable_frame_mods func cenv cx mid t /\
  u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section /\
  u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
  (!x sz id. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz) ==>
              lookup_var x u = lookup_var x t) ==>
  immutable_frame_mods func cenv cx mid u
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
        (drule_then assume_tac) >>
      fs[immutables_rel_def, LET_THM] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`t`,`mid`] >> simp[local_region_def] >> metis_tac[]
QED

Theorem field_add_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx mid G tn t /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\ u.vs_call_ctx = t.vs_call_ctx /\
  u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
  u.vs_immutables = t.vs_immutables /\ tn'.t_mem = tn.t_mem /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d cenv cx mid G' tn' u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p t sz ==>
          ptr_covers G' tn' p u sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME db) _ _ _ _` >> PairCases_on `db` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem field_add_suffix[local]:
  emit_op ADD [FST rb; Lit (n2w fieldoff)] sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  eval_operand (FST rb) t = SOME w /\ op_taint tn (FST rb) = {} /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt
         es sa sm s0 mid pv vt rb G0 tn0 G tn t) /\
  target_ptr_ok cenv pv' rb G tn t /\
  (!u G'. eval_operand dst u = SOME (w + n2w fieldoff) /\
          op_prov G' dst = op_prov G (FST rb) /\
          (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t) ==>
       write_target_location_mods cenv cx (AttributeTarget bt fld) mid pv' vt'
         (dst,FST (SND rb),SOME (value_type_place vt')) G' u) ==>
  ?u G' tn'. !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G',tn') /\
    write_target_post_mods H (DF H) lo d ctx func cenv cx (AttributeTarget bt fld)
      es sa sb s0 mid pv' vt' (dst,FST (SND rb),SOME (value_type_place vt')) G0 tn0 G' tn' u
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  drule_then strip_assume_tac loweringShapeRulesTheory.emit_op_facts >>
  qpat_x_assum `dst = _` SUBST_ALL_TAC >>
  `out = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [FST rb;Lit (n2w fieldoff)] [out]` >>
  qabbrev_tac `v = update_var out (w + n2w fieldoff) t` >>
  qabbrev_tac `u = v with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i v` >>
  qabbrev_tac `tn' = step_taint i t v tn` >>
  mp_tac (Q.INST [`left` |-> `FST (rb : operand # data_location option # place_ty option)`,
                  `off` |-> `n2w fieldoff`, `sn` |-> `sb`, `dst` |-> `Var out`,
                  `s` |-> `t`, `u` |-> `v`, `t` |-> `u`] attribute_add_full_frame) >>
  (impl_tac >- simp[Abbr `i`, Abbr `v`, Abbr `u`, Abbr `G'`, Abbr `tn'`]) >>
  strip_tac >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G',tn')` by simp[] >>
  simp[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     qpat_assum `!n. _ <= n ==> _` (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  qpat_x_assum `out = STRING _ _` kall_tac >>
  qpat_x_assum `Var out = Var (STRING _ _)` kall_tac >>
  `!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> x <> out` drule >> strip_tac >>
     qpat_assum `!p. p <> out ==> _` drule >> strip_tac >>
     simp[Abbr `u`, Abbr `v`, update_var_def, lookup_var_def, FLOOKUP_UPDATE, EQ_SYM_EQ]) >>
  suspend "post"
QED

Resume field_add_suffix[post]:
  `not_local_ptr cenv mid.scopes out` by
    (rw[not_local_ptr_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (simp[Abbr `u`, Abbr `v`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `wb_frame cenv es mid sa s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`,`t`] >>
     reverse conj_tac >- simp[Abbr `u`, Abbr `v`, update_var_def] >>
     rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  `immutable_frame_mods func cenv cx mid u` by
    (irule field_add_immutable_frame >> qexists_tac `t` >>
     simp[Abbr `u`, Abbr `v`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' u` by
    (irule field_add_ghost_frame >>
     qexistsl_tac [`G`,`sa`,`t`,`tn`] >>
     simp[] >> simp[Abbr `u`, Abbr `v`, update_var_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >> simp[]) >>
  `target_ptr_ok cenv pv' (Var out,FST (SND rb),SOME (value_type_place vt')) G' tn' u` by
    (irule target_ptr_ok_operand_transport >>
     simp[] >> qexistsl_tac [`G`,`rb`,`t`,`tn`] >> simp[op_prov_def] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `eval_operand (Var out) u = SOME (w + n2w fieldoff)` by
    simp[Abbr `u`, Abbr `v`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ s0.vs_alloca_next <= u.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    simp[Abbr `u`, Abbr `v`, update_var_def, allocas_below_fmp_updates] >>
  `write_target_location_mods cenv cx (AttributeTarget bt fld) mid pv' vt'
     (Var out,FST (SND rb),SOME (value_type_place vt')) G' u` by
    (first_x_assum irule >> simp[op_prov_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `out = STRING #"%" (toString sm.cs_next_var)` by
    (drule emitted_insts_emit_op >> simp[]) >>
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  simp[write_target_post_mods_def]
QED

Finalise field_add_suffix

Theorem write_field_stage_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  (!gs pv mid. eval_base_place cx bt (es with gas_obs := gs) = (INL pv,mid) ==>
      state_well_typed mid /\ popped_keys_indexed mid.scopes) ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[write_base_sim_mods_def] >> rpt gen_tac >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  fs[type_place_target_AttributeTarget] >>
  rename1 `type_place_target env bt = SOME (Type bty)` >>
  `?sid. bty = StructT sid` by (Cases_on `bty` >> fs[attribute_type_def]) >>
  gvs[] >>
  qpat_x_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  drule_then strip_assume_tac compile_get_target_ptr_attr >> gvs[] >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = (srb,shadow_sm)` >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target bt))` by
    irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by metis_tac[ci_mono_emit_op,SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))` by
    simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (rewrite_tac[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >- simp[target_res_ok_def] >>
     qpat_assum `gas_admissible (bind _ _) _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[bind_def]) >>
  qpat_x_assum `write_base_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_base_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`Type (StructT sid)`,`sa`,`sm`,`shadow_sa`,
    `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[write_target_entry_mods_def] >>
     conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[])) >> strip_tac >>
  suspend "bind"
QED

Resume write_field_stage_mods[bind]:
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]
QED

Resume write_field_stage_mods[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `pv` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL pv,mid)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _`
       (qspec_then `[]` mp_tac) >> REWRITE_TAC[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => REWRITE_TAC[th])) >>
  qpat_assum `!gs pv mid. eval_base_place _ _ _ = _ ==> _` (drule_then strip_assume_tac) >>
  `!m. FST (extend_place cx pv (AttrSubscript fld) mid) <> INR (Error (TypeError m))` by
    (qpat_assum `gas_admissible (bind _ _) _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     Cases_on `extend_place cx pv (AttrSubscript fld) mid` >>
     simp[bind_def,target_res_ok_def] >> rpt strip_tac >> gvs[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0 mid pv
        (Type (StructT sid)) rb G0 tn0 G1 tn1 t` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[]) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_x_assum `SND (SND rb) = SOME (value_type_place _)`
    (assume_tac o REWRITE_RULE [value_type_place_def]) >>
  `op_taint tn1 (FST rb) = {}` by fs[target_ptr_ok_def] >>
  qpat_x_assum `target_field_type cenv _ _ = target_field_type (gas_shadow_env T cenv) _ _`
    (assume_tac o SYM) >>
  `?pv' w.
       extend_place cx pv (AttrSubscript fld) mid = (INL pv',mid) /\
       target_field_type cenv (SND (SND rb)) fld = SOME (ValPT ty) /\
       eval_operand (FST rb) t = SOME w /\ target_ptr_ok cenv pv' rb G1 tn1 t /\
       (!u G'. eval_operand dst u = SOME (w + n2w (target_field_offset cenv
                      (FST (SND rb)) (SND (SND rb)) fld)) /\
               op_prov G' dst = op_prov G1 (FST rb) /\
               (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t) ==>
         write_target_location_mods cenv cx (AttributeTarget bt fld) mid pv'
           (Type ty) (dst,FST (SND rb),SOME (ValPT ty)) G' u)` by suspend "location" >>
  suspend "pure"
QED

Resume write_field_stage_mods[location]:
  Cases_on `?owner id path. pv = PlaceR (ImmutablePlace owner id path)`
  >- suspend "immutable" >>
  `place_readable cx mid pv /\
    (?w. eval_operand (FST rb) t = SOME w /\
         place_ptr_rel cenv cx t pv w (FST (SND rb)) (Type (StructT sid)))` by
    (Cases_on `pv` >> fs[write_target_location_mods_def] >> Cases_on `p` >>
     fs[write_target_location_mods_def]) >>
  drule_all_then (qspec_then `bt` strip_assume_tac) ordinary_field_source >>
  rename1 `extend_place _ _ _ _ = (INL pv',_)` >>
  qexistsl_tac [`pv'`,`w`] >> simp[] >> rpt strip_tac >>
  irule place_ptr_rel_vars_frame >> qexistsl_tac [`t`,`sa`] >> simp[]
QED

Resume write_field_stage_mods[immutable]:
  gvs[] >>
  qpat_assum `write_target_location_mods _ _ _ _ (PlaceR (ImmutablePlace _ _ _)) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [write_target_location_mods_def]) >>
  drule_all_then strip_assume_tac immutable_field_source >>
  qexistsl_tac [`PlaceR (ImmutablePlace owner id (path ++ [AttrSubscript fld]))`,
                `n2w (off + k)`] >>
  simp[target_ptr_ok_def,value_type_place_def,target_field_type_def,target_field_offset_def] >>
  rpt strip_tac >>
  simp[write_target_location_mods_def,target_root_def,target_through_dynarray_def,
       GSYM word_add_n2w, ADD_ASSOC] >>
  pure_rewrite_tac[WORD_ADD_ASSOC] >> AP_THM_TAC >> AP_TERM_TAC >>
  irule WORD_ADD_COMM
QED

Resume write_field_stage_mods[pure]:
  drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac)
    (SIMP_RULE std_ss [value_type_place_def] (Q.INST [`vt'` |-> `Type ty`] field_add_suffix)) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL pv'`,`u`,`tn'`] >>
  conj_tac >- simp[extend_place_attr_gas_obs] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[] >> qexists_tac `pv'` >> simp[]
QED

Finalise write_field_stage_mods
