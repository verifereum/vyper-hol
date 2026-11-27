(* Restore the ghost invariant after a write to one live immutable path. *)
Theory immutableDeployAssignPathGhost
Ancestors
  immutableDeployAssignMemoryFrame immutableDeployAssignRestore immutablePrefixDead
  immutableDeployAssignFacts bodyPtrDefs bodySim bodyInvSplit gasContext
  immutableRelation bodyStorageMetadata vyperContext immutableDeployAssignSourceFrame
  stateRelProj valueTypingMemoryProps abiCanonicalHeadSize
  valueMemoryTransport valueEncodingDefs loweringSlice vyperState words
  ctorDeployDeadSection ctorDeployDeadSectionFrame immSectionDead
  bodyPtrBytestringBuiltinsWindowGhost exprSimSubscriptArrayLiveImmutableView
  exprLoweringProps exprSimProps immutableDeployAssignAdmissible loweringPosts loweringStateRelDefs
  valueEncodingProps valueEncodingProofs vyperTypeInvariants vyperPlaceFrames
  compileVyper compileEnv list finite_map alist venomState
  bodySimLogArgs abiCallerTypeEnv immutableRegionDeadProps vyperTypeConstantFold valueCopyBytes
  exprSimHypsDefs vyperValue pair

Theorem immutable_section_replace_exact:
  (!t u. evaluate_type (type_env tops) t = SOME u ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) t =
    type_memory_size u) /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len
          (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec1 = lo /\ LENGTH sec2 = lo /\
  off + type_memory_size tv <= lo /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead tops sec1 j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < lo /\ j IN M2 ==> imm_section_dead tops sec2 j
Proof
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `off <= j /\ j < off + type_memory_size tv`
  >- (rewrite_tac[imm_section_dead_def] >>
      qexistsl_tac [`pre`,`vis`,`name`,`ty`,`slot`,`post`,`tv`] >>
      gvs[]) >>
  `imm_section_dead tops sec1 j` by metis_tac[] >>
  qpat_x_assum `imm_section_dead tops sec1 j` mp_tac >>
  rewrite_tac[imm_section_dead_def] >> strip_tac >>
  rename1 `evaluate_type (type_env tops) ty' = SOME tv'` >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
     type_memory_size tv` by
    (qpat_assum `!t u. evaluate_type _ t = SOME u ==> _`
       (qspecl_then [`ty`,`tv`] mp_tac) >> simp[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
     type_memory_size tv'` by
    (qpat_assum `!t u. evaluate_type _ t = SOME u ==> _`
       (qspecl_then [`ty'`,`tv'`] mp_tac) >> simp[]) >>
  drule (CONJUNCT1 mem_dead_bytes_range) >> strip_tac >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
     pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'`
    by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  qpat_assum `type_mem_bytes _ ty = type_memory_size tv` (fn width =>
    qpat_assum `type_mem_bytes _ ty' = type_memory_size tv'` (fn width' =>
      pure_rewrite_tac[width,width'])) >>
  strip_tac
  >- (fs[] >> gvs[]) >>
  `mem_dead_bytes sec2
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv' =
    mem_dead_bytes sec1
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv'`
    by (irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
        ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
        qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >>
        rpt strip_tac >>
        qpat_x_assum `!j. _ ==> EL j sec2 = EL j sec1` irule >>
        gvs[] >> decide_tac) >>
  rewrite_tac[imm_section_dead_def] >>
  qexistsl_tac [`pre'`, `vis'`, `name'`, `ty'`, `slot'`, `post'`, `tv'`] >>
  gvs[]
QED

Theorem immutable_section_replace:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len
          (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec1 = lo /\ LENGTH sec2 = lo /\
  off + type_memory_size tv <= lo /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead tops sec1 j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < lo /\ j IN M2 ==> imm_section_dead tops sec2 j
Proof
  strip_tac >>
  MATCH_MP_TAC (Q.INST [`tops` |-> `tops`,`lo` |-> `lo`,`pre` |-> `pre`,
    `vis` |-> `vis`,`name` |-> `name`,`ty` |-> `ty`,`slot` |-> `slot`,
    `post` |-> `post`,`tv` |-> `tv`,`off` |-> `off`,`sec1` |-> `sec1`,
    `sec2` |-> `sec2`,`M1` |-> `M1`,`M2` |-> `M2`]
    immutable_section_replace_exact) >>
  conj_tac
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC imm_frame_size) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem immutable_layout_type_env_submap[local]:
  bare_globals_layout ctor module_var_type module_vars mods cx globals assignable ==>
  type_env_all_modules mods SUBMAP get_tenv cx
Proof
  strip_tac >>
  fs[bare_globals_layout_def, SUBMAP_FLOOKUP_EQN, FORALL_PROD] >>
  qx_genl_tac [`src`, `name`] >>
  simp[FLOOKUP_type_env_all_modules] >>
  Cases_on `ALOOKUP mods src` >> gvs[] >>
  rename1 `get_module_code cx src = SOME tops` >>
  gvs[get_module_code_def, get_tenv_def, AllCaseEqs()] >>
  rename1 `ALOOKUP cx.sources cx.txn.target = SOME unit` >>
  `type_env_for_module src tops SUBMAP type_env_all_modules unit` by
    (irule module_type_env_submap >> metis_tac[]) >>
  pop_assum mp_tac >> simp[SUBMAP_FLOOKUP_EQN] >> metis_tac[]
QED

Theorem immutable_bytes_section_replace:
  expr_sim_inv ce cx env es /\
  immutable_section_layout_mods ce.ce_modules ce /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  is_bytestring_type dty /\ evaluate_type (get_tenv cx) dty = SOME tv /\
  tops = cx_tops cx /\ struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable id dty slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec1 = lo /\ LENGTH sec2 = lo /\ off + type_memory_size tv <= lo /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead_mods ce sec1 j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < lo /\ j IN M2 ==> imm_section_dead_mods ce sec2 j
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     ce.ce_modules cx env.bare_globals env.bare_global_assignable` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  Cases_on `?ts. ce.ce_modules = [(NONE,ts)]`
  >- (qpat_x_assum `?ts. ce.ce_modules = [(NONE,ts)]`
        (qx_choose_then `ts` assume_tac) >>
      `get_module_code cx NONE = SOME ts` by
        (qpat_assum `bare_globals_layout _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [bare_globals_layout_def]) >>
         qpat_assum `ce.ce_modules = [(NONE,ts)]` (fn modules =>
           qpat_assum `!src. ALOOKUP ce.ce_modules src = get_module_code cx src`
             (qspec_then `NONE:num option`
               (ACCEPT_TAC o SYM o SIMP_RULE (srw_ss()) [modules, ALOOKUP_def])))) >>
      `tops = ts` by metis_tac[cx_tops_module] >>
      `evaluate_type (type_env tops) dty = SOME tv` by
        (Cases_on `dty` >> fs[is_bytestring_type_def, evaluate_type_def] >>
         Cases_on `b` >> fs[is_bytestring_type_def, evaluate_type_def] >>
         Cases_on `d` >> fs[is_bytestring_type_def, evaluate_type_def]) >>
      qpat_x_assum `tops = ts` (SUBST_ALL_TAC o SYM) >>
      qpat_assum `ce.ce_modules = [(NONE,tops)]` (fn modules =>
        let val singleton = MATCH_MP immSectionDeadTheory.imm_section_dead_mods_singleton modules
        in RULE_ASSUM_TAC (REWRITE_RULE [singleton]) >> PURE_REWRITE_TAC [singleton] end) >>
      MATCH_MP_TAC (Q.INST [`tops` |-> `tops`, `lo` |-> `lo`,
        `pre` |-> `pre`, `post` |-> `post`, `vis` |-> `vis`, `slot` |-> `slot`,
        `name` |-> `id`, `ty` |-> `dty`, `tv` |-> `tv`, `off` |-> `off`,
        `sec1` |-> `sec1`, `sec2` |-> `sec2`,
        `M1` |-> `M1`, `M2` |-> `M2`] immutable_section_replace) >>
      asm_rewrite_tac[]) >>
  `!sec j. imm_section_dead_mods ce sec j <=>
     ?src ts vis id ty slot off tv.
       ALOOKUP ce.ce_modules src = SOME ts /\
       MEM (VariableDecl vis Immutable id ty slot) ts /\
       FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
       evaluate_type (type_env_all_modules ce.ce_modules) ty = SOME tv /\
       mem_dead_bytes sec off tv j` by
    metis_tac[imm_section_dead_mods_other] >>
  `!src name ty ts vis slot. ALOOKUP ce.ce_modules src = SOME ts /\
     MEM (VariableDecl vis Immutable name ty slot) ts ==>
     FLOOKUP env.bare_globals (src,name) = SOME ty` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        exprSimHypsDefsTheory.bare_globals_layout_def,
        env_consistent_def, env_context_consistent_def, bare_globals_complete_def] >>
     metis_tac[]) >>
  `?ts vis slot.
     ALOOKUP ce.ce_modules ce.ce_module = SOME ts /\
     MEM (VariableDecl vis Immutable id dty slot) ts` by
    (qpat_assum `immutable_section_layout_mods _ _`
       (mp_tac o Q.SPECL [`ce.ce_module`, `id`, `off`] o CONJUNCT1 o
        REWRITE_RULE [immutable_section_layout_mods_def]) >>
     qpat_assum `FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off)`
       (fn loc => PURE_REWRITE_TAC [loc]) >>
     simp[immutable_region_mods_def, MEM_APPEND] >>
     disch_then (qx_choosel_then [`p`, `q`, `v`, `ty`, `ann`]
       (assume_tac o CONJUNCT1)) >>
     `MEM (VariableDecl v Immutable id ty ann)
           (p ++ VariableDecl v Immutable id ty ann :: q)` by simp[MEM_APPEND] >>
     `FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty` by metis_tac[] >>
     `ty = dty` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `ty = dty` SUBST_ALL_TAC >>
     qexistsl_tac [`p ++ VariableDecl v Immutable id dty ann :: q`, `v`, `ann`] >>
     simp[MEM_APPEND, IgnAsm `off = _`, IgnAsm `tops = _`]) >>
  `evaluate_type (type_env_all_modules ce.ce_modules) dty = SOME tv` by
    (Cases_on `dty` >> fs[is_bytestring_type_def, evaluate_type_def] >>
     Cases_on `b` >> fs[is_bytestring_type_def, evaluate_type_def] >>
     Cases_on `d` >> fs[is_bytestring_type_def, evaluate_type_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `off <= j /\ j < off + type_memory_size tv`
  >- metis_tac[] >>
  `imm_section_dead_mods ce sec1 j` by metis_tac[] >>
  qpat_assum `!sec j. imm_section_dead_mods ce sec j <=> _` (fn dead =>
    qpat_assum `imm_section_dead_mods ce sec1 j`
      (strip_assume_tac o REWRITE_RULE [dead])) >>
  rename1 `FLOOKUP ce.ce_module_vars (src',id') = SOME (ImmutableLoc off')` >>
  `src' = ce.ce_module` by metis_tac[immutable_store_layout_active] >>
  `evaluate_type (get_tenv cx) ty = SOME tv'` by
    metis_tac[abi_caller_type_submap, immutable_layout_type_env_submap] >>
  `FLOOKUP env.bare_globals (src',id') = SOME ty` by metis_tac[] >>
  Cases_on `id' = id`
  >- (`off' = off /\ tv' = tv` by
        metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
      qpat_assum `mem_dead_bytes sec1 off' tv' j`
        (mp_tac o MATCH_MP (cj 1 mem_dead_bytes_range)) >>
      qpat_assum `off' = off` (fn offset =>
        qpat_assum `tv' = tv` (fn tyval => PURE_REWRITE_TAC [offset,tyval])) >>
      qpat_assum `~(off <= j /\ j < off + type_memory_size tv)`
        (fn outside => REWRITE_TAC [EQF_INTRO outside])) >>
  qpat_x_assum `src' = ce.ce_module` SUBST_ALL_TAC >>
  `regions_disjoint off (type_memory_size tv) off' (type_memory_size tv')` by
    (qpat_assum `bare_globals_layout _ _ _ _ _ _ _`
       (mp_tac o Q.SPECL [`ce.ce_module`,`id`,`id'`,`dty`,`ty`,`off`,`off'`,`tv`,`tv'`] o
        el 4 o CONJUNCTS o REWRITE_RULE [bare_globals_layout_def]) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `mem_dead_bytes sec2 off' tv' = mem_dead_bytes sec1 off' tv'` by
    (irule mem_dead_bytes_frame >>
     qpat_assum `LENGTH sec1 = lo` (fn len1 =>
       qpat_assum `LENGTH sec2 = lo` (fn len2 => REWRITE_TAC [len1,len2])) >>
     rpt strip_tac >>
     qpat_assum `!j. _ ==> EL j sec2 = EL j sec1` irule >>
     qpat_assum `regions_disjoint off _ off' _`
       (mp_tac o REWRITE_RULE [regions_disjoint_def]) >>
     decide_tac) >>
  qpat_assum `!sec j. imm_section_dead_mods ce sec j <=> _`
    (fn dead => PURE_REWRITE_TAC [dead]) >>
  qexistsl_tac [`ce.ce_module`,`ts'`,`vis''`,`id'`,`ty`,`slot''`,`off'`,`tv'`] >>
  asm_rewrite_tac[]
QED

Theorem immutable_assign_section_root:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  ce.ce_is_ctor /\ dead_lo_ok H D lo ce cx /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME itv ==>
  tops = cx_tops cx /\ get_tenv cx = type_env tops /\
  ce.ce_module = NONE /\ lo = imm_len tops /\ off + type_memory_size itv <= lo /\
  ?pre post vis slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre
Proof
  strip_tac >>
  `ce.ce_module = NONE /\ ce.ce_modules = [(NONE,tops)] /\
   cx_tops cx = tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   ce.ce_module_var_type = build_var_type_map tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    gvs[body_inv_def,cenv_module_pins_def,cx_tops_module] >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def,type_env_all_modules_def,type_env_def] >>
  `lo = imm_len tops` by fs[dead_lo_ok_def,immSectionDeadTheory.imm_len_mods_singleton] >>
  `?pre post vis ity slot.
    tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre` by
    (drule body_inv_immutable_section_layout >>
     simp[immutable_section_layout_def] >> metis_tac[]) >>
  `ity = ty` by
    (`MEM (VariableDecl vis Immutable id ity slot) tops` by simp[] >>
     drule_all build_maps_variable >> strip_tac >>
     qpat_x_assum `build_var_type_map tops _ = SOME ity` mp_tac >>
     simp[] >> gvs[build_maps_variable]) >>
  qpat_x_assum `ity = ty` SUBST_ALL_TAC >>
  `evaluate_type (type_env tops) ty = SOME itv` by fs[] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size itv` by drule_all_then ACCEPT_TAC immutable_exact_slot_size >>
  `off + type_memory_size itv <= lo` by
    (qpat_assum `off = _` (fn offset =>
       qpat_assum `type_mem_bytes _ ty = _` (fn width =>
         qpat_assum `lo = _` (fn len =>
           PURE_REWRITE_TAC [offset, GSYM width, len, imm_len_def]))) >>
     qpat_assum `tops = _` (PURE_ONCE_REWRITE_TAC o single) >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`off` |-> `0`] immutable_declaration_interval_bound))) >>
  simp[] >> metis_tac[]
QED

Theorem immutable_path_section_dead:
  body_inv tops ctx ce cx /\
  stmt_state_rel H ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  ghost_inv_at D lo d ce cx ee G tn s /\ dead_lo_ok H D lo ce cx /\
  ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME itv /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace ce.ce_module id path) v ee = (INL (),fin) /\
  value_has_type ptv v /\
  (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory ptv v (off+k) m) /\
  (!b n. regions_disjoint b n (off+k) (type_memory_size ptv) ==>
      mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (!i. ~(off+k <= i /\ i < off+k+type_memory_size ptv) /\ i IN tf.t_mem ==>
       i IN tn.t_mem) ==>
  !i. i < lo /\ i IN tf.t_mem ==>
      imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo q.vs_memory) i
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_assign_section_root >>
  `ce.ce_modules = [(NONE,tops)]` by
    gvs[body_inv_split_def,cenv_module_pins_def] >>
  `!t u. evaluate_type (type_env tops) t = SOME u ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) t =
    type_memory_size u` by (rpt strip_tac >> drule_all_then ACCEPT_TAC immutable_exact_slot_size) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `?imms old. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (itv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  drule_all_then strip_assume_tac immutable_path_write_source >>
  `FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,old)` by metis_tac[] >>
  drule_then (assume_tac o MATCH_MP state_rel_immutables_rel)
    stmt_state_rel_state_rel >>
  `immutable_value_admissible itv old /\ val_in_memory itv old off s.vs_memory` by
    (qpat_assum `immutables_rel _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [immutables_rel_def,LET_THM]) >>
     CONV_TAC (LAND_CONV BETA_CONV) >>
     disch_then (mp_tac o Q.SPECL [`id`,`itv`,`old`,`off`]) >> simp[]) >>
  `value_has_type itv old /\ well_formed_type_value itv` by
    (qspecl_then [`ce`,`cx`,`env`,`ee`,`ce.ce_module`,`id`,`[]`,`itv`,
                 `old`,`0`,`itv`,`old`] mp_tac
       exprSimSubscriptArrayLiveImmutableViewTheory.imm_place_at_value_type >>
     simp[mem_path_offset_def,evaluate_subscripts_def]) >>
  qabbrev_tac `sec = mem_bytes_at 0 lo s.vs_memory` >>
  qabbrev_tac `sec' = mem_bytes_at 0 lo q.vs_memory` >>
  `LENGTH sec = lo /\ LENGTH sec' = lo` by
    simp[Abbr `sec`,Abbr `sec'`,LENGTH_mem_bytes_at_proof] >>
  `!j. j < lo /\ ~(off+k <= j /\ j < off+k+type_memory_size ptv) ==>
         EL j sec' = EL j sec` by
    (rpt strip_tac >>
     `mem_bytes_at j 1 q.vs_memory = mem_bytes_at j 1 s.vs_memory` by
       (first_x_assum irule >> simp[NoAsms,regions_disjoint_def] >> decide_tac) >>
     pop_assum (mp_tac o AP_TERM ``EL 0:byte list -> byte``) >>
     simp[Abbr `sec`,Abbr `sec'`,EL_mem_bytes_at]) >>
  `mem_bytes_at off (type_memory_size itv) sec =
     mem_bytes_at off (type_memory_size itv) s.vs_memory` by
    (simp[NoAsms,Abbr `sec`] >>
     irule immutable_section_byte_window >> first_assum ACCEPT_TAC) >>
  `val_in_memory itv old off sec` by
    (irule val_in_memory_transport >> conj_tac
     >- metis_tac[immutable_admissible_val_wf] >>
     qexistsl [`s.vs_memory`,`off`] >> metis_tac[]) >>
  `off+k+type_memory_size ptv <= lo` by decide_tac >>
  `mem_bytes_at (off+k) (type_memory_size ptv) sec' =
    mem_bytes_at (off+k) (type_memory_size ptv) q.vs_memory` by
    (simp[NoAsms,Abbr `sec'`] >>
     irule immutable_section_byte_window >> decide_tac) >>
  `!m. mem_agree_outside tf.t_mem sec' m ==> val_in_memory ptv v (off+k) m` by
    (rpt strip_tac >> irule robust_val_in_memory_window_transport >>
     conj_tac >- metis_tac[value_has_type_memory_wf] >>
     qexistsl_tac [`tf.t_mem`,`tf.t_mem`,`type_memory_size ptv`,`q.vs_memory`,`sec'`] >>
     simp[val_footprint_le,value_has_type_memory_wf]) >>
  `!j. j < lo /\ j IN tn.t_mem ==> imm_section_dead tops sec j` by
    (qpat_assum `ce.ce_modules = [(NONE,tops)]`
       (fn mods => pure_rewrite_tac [GSYM (MATCH_MP imm_section_dead_mods_singleton mods)]) >>
     qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     simp[Abbr `sec`]) >>
  `evaluate_type (type_env tops) ty = SOME itv` by metis_tac[] >>
  `!j. off <= j /\ j < off + type_memory_size itv /\
       (j < off+k \/ off+k+type_memory_size ptv <= j) ==>
       EL j sec' = EL j sec /\ (j IN tf.t_mem ==> mem_dead_bytes sec off itv j)` by
    (gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- (first_x_assum irule >> decide_tac) >>
     strip_tac >>
     `j IN tn.t_mem /\ j < lo` by
       (conj_tac >- (first_x_assum irule >> conj_tac
                      >- decide_tac >> first_assum ACCEPT_TAC) >> decide_tac) >>
     drule_all imm_frame_restrict_exact >> metis_tac[]) >>
  `off + type_memory_size itv <= LENGTH sec /\ LENGTH sec' = LENGTH sec` by
    metis_tac[] >>
  `!j. off <= j /\ j < off+type_memory_size itv /\ j IN tf.t_mem ==>
     mem_dead_bytes sec' off itv j` by
    (rpt strip_tac >> irule immutable_replace_path_dirty_dead >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tf.t_mem`,`k`,`new`,`old`,`path`,`ptv`,`sec`,`v`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!j. j < lo /\ ~(off <= j /\ j < off+type_memory_size itv) ==>
    EL j sec' = EL j sec` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!j. j < lo /\ ~(off <= j /\ j < off+type_memory_size itv) /\ j IN tf.t_mem ==>
    j IN tn.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> conj_tac
     >- decide_tac >> first_assum ACCEPT_TAC) >>
  qsuff_tac `!i. i < lo /\ i IN tf.t_mem ==> imm_section_dead tops sec' i`
  >- (qpat_assum `tops = cx_tops cx` (fn th =>
         pure_rewrite_tac[GSYM th]) >> disch_then ACCEPT_TAC) >>
  rpt strip_tac >> irule immutable_section_replace_exact >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`lo`,`id`,`off`,`post`,`pre`,`sec`,
                `slot`,`itv`,`ty`,`vis`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem immutable_path_store_ghost_inv:
  body_inv tops ctx ce cx /\
  stmt_state_rel H ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  ghost_inv_at D lo d ce cx ee G tn s /\ dead_lo_ok H D lo ce cx /\
  ce.ce_is_ctor /\ local_ptrs_reserved ce sa /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME itv /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace ce.ce_module id path) v ee = (INL (),fin) /\
  value_has_type ptv v /\
  (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory ptv v (off+k) m) /\
  (!b n. regions_disjoint b n (off+k) (type_memory_size ptv) ==>
      mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (!i. ~(off+k <= i /\ i < off+k+type_memory_size ptv) /\ i IN tf.t_mem ==>
       i IN tn.t_mem) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
  q.vs_transient = s.vs_transient /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  allocas_from lo q /\ s.vs_alloca_next <= q.vs_alloca_next ==>
  ghost_inv_at D lo d ce cx fin Gf tf q
Proof
  strip_tac >>
  drule_then (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules)
    body_inv_contract >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  `!i. i < lo /\ i IN tf.t_mem ==>
      imm_section_dead_mods ce (mem_bytes_at 0 lo q.vs_memory) i` by
    (drule_then (fn th => PURE_REWRITE_TAC [th])
       immSectionDeadTheory.imm_section_dead_mods_singleton >>
     qpat_assum `cx_tops cx = tops` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     rpt strip_tac >> irule immutable_path_section_dead >> metis_tac[]) >>
  drule_all_then strip_assume_tac immutable_assign_declared_region >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `fin.scopes = ee.scopes` by metis_tac[write_immutable_place_scopes] >>
  `local_ptrs_rel func ce ee.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!n b len. local_region ce ee.scopes s n b len ==>
    mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `regions_disjoint b len (off+k) (type_memory_size ptv)` by
       (qpat_assum `!nm a n. local_region ce ee.scopes s nm a n ==> _`
          (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >>
        simp[regions_disjoint_def] >> decide_tac) >>
     conj_tac
     >- (qpat_assum `!b n. regions_disjoint b n _ _ ==> _` (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >>
     qpat_assum `!i. _ ==> i IN tn.t_mem` (qspec_then `i` match_mp_tac) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  qpat_assum `ghost_inv_at D lo d ce cx ee G tn s`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  `stor_taint_ok_at D tf q` by
    (`!i. D.d_imm i = UNIV` by fs[dead_lo_ok_def] >>
     fs[stor_taint_ok_at_def]) >>
  `ghost_inv_at D 0 d ce cx ee G tn s` by
    (simp[ghost_inv_at_def,ptrDisciplineTheory.allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 0 q.vs_memory = mem_bytes_at 0 0 s.vs_memory` by
    simp[mem_bytes_at_def] >>
  `ghost_inv_at D 0 d ce cx fin Gf tf q` by
    (irule ghost_inv_at_local_window_transport >>
     simp[ptrDisciplineTheory.allocas_from_def] >>
     qexistsl_tac [`G`,`ee`,`func`,`s`,`sa`,`tn`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_assum `fin.scopes = ee.scopes` (fn eq =>
    qpat_x_assum `ghost_inv_at D 0 d ce cx fin Gf tf q`
      (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def,eq])) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
      FLOOKUP Gf x = NONE /\ op_taint tf (Var x) = {}` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by drule_all_then ACCEPT_TAC local_ptrs_reserved_imm_base >>
     simp[]) >>
  `lo <= q.vs_alloca_next` by decide_tac >>
  simp[ghost_inv_at_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
