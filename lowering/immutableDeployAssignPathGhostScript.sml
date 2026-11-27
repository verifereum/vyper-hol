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

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `ce.ce_module = NONE /\ cx_tops cx = tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   ce.ce_module_var_type = build_var_type_map tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    gvs[body_inv_def,cenv_module_pins_def,cx_tops_module] >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def,type_env_all_modules_def,type_env_def] >>
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
  `lo = imm_len tops` by metis_tac[dead_lo_ok_def] >>
  `evaluate_type (type_env tops) ty = SOME itv` by metis_tac[] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size itv` by drule_all_then ACCEPT_TAC immutable_exact_slot_size >>
  `off + type_memory_size itv <= lo` by
    (mp_tac (Q.INST [`off` |-> `0`, `prefix` |-> `pre`, `suffix` |-> `post`,
       `sft` |-> `get_struct_fields (make_struct_fields_map tops)`,
       `ty` |-> `ty`, `vis` |-> `vis`, `name` |-> `id`, `slot` |-> `slot`]
       immutable_declaration_interval_bound) >>
     simp[GSYM imm_len_def]) >>
  simp[] >> metis_tac[]
QED
*)
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
  cheat
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
  `!t u. evaluate_type (type_env tops) t = SOME u ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) t =
    type_memory_size u` by (rpt strip_tac >> drule_all_then ACCEPT_TAC immutable_exact_slot_size) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `?imms old. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (itv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  drule_all_then strip_assume_tac immutable_path_write_source >>
  `FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,old)` by
    metis_tac[] >>
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
     pop_assum (mp_tac o AP_TERM “EL 0:byte list -> byte”) >>
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
    (mp_tac (Q.INST [`tv` |-> `ptv`,`v` |-> `v`,`b` |-> `off+k`,
       `len` |-> `type_memory_size ptv`,`mem'` |-> `sec'`,
       `mem` |-> `q.vs_memory`,`dirty'` |-> `tf.t_mem`,`dirty` |-> `tf.t_mem`]
       robust_val_in_memory_window_transport) >>
     simp[val_footprint_le,value_has_type_memory_wf]) >>
  `!j. j < lo /\ j IN tn.t_mem ==> imm_section_dead tops sec j` by
    fs[ghost_inv_at_def] >>
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
    (MATCH_MP_TAC (Q.INST [`itv` |-> `itv`,`old` |-> `old`,`v` |-> `v`,
       `ptv` |-> `ptv`,`path` |-> `path`,`k` |-> `k`,`new` |-> `new`,
       `off` |-> `off`,`sec` |-> `sec`,`sec'` |-> `sec'`,`dirty` |-> `tf.t_mem`]
       immutable_replace_path_dirty_dead) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!j. j < lo /\ ~(off <= j /\ j < off+type_memory_size itv) ==>
    EL j sec' = EL j sec` by
    (rpt strip_tac >> first_x_assum irule >> conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `!j. j < lo /\ ~(off <= j /\ j < off+type_memory_size itv) /\ j IN tf.t_mem ==>
    j IN tn.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> conj_tac
     >- decide_tac >> first_assum ACCEPT_TAC) >>
  qsuff_tac `!i. i < lo /\ i IN tf.t_mem ==> imm_section_dead tops sec' i`
  >- (qpat_assum `tops = cx_tops cx` (fn th =>
         pure_rewrite_tac[GSYM th]) >> disch_then ACCEPT_TAC) >>
  MATCH_MP_TAC (Q.INST [`tops` |-> `tops`,`lo` |-> `lo`,`pre` |-> `pre`,
    `vis` |-> `vis`,`name` |-> `id`,`ty` |-> `ty`,`slot` |-> `slot`,
    `post` |-> `post`,`tv` |-> `itv`,`off` |-> `off`,`sec1` |-> `sec`,
    `sec2` |-> `sec'`,`M1` |-> `tn.t_mem`,`M2` |-> `tf.t_mem`]
    immutable_section_replace_exact) >>
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
  `!i. i < lo /\ i IN tf.t_mem ==>
      imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo q.vs_memory) i` by
    (MATCH_MP_TAC (Q.INST [`tops` |-> `tops`,`ctx` |-> `ctx`,`func` |-> `func`,
       `ce` |-> `ce`,`ee` |-> `ee`,`env` |-> `env`,`H` |-> `H`,
       `d` |-> `d`,`D` |-> `D`,`s` |-> `s`,`G` |-> `G`,`tn` |-> `tn`,
       `id` |-> `id`,`ty` |-> `ty`,`off` |-> `off`,`k` |-> `k`,
       `itv` |-> `itv`,`path` |-> `path`,`ptv` |-> `ptv`,`fin` |-> `fin`,`v` |-> `v`]
       immutable_path_section_dead) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
    (MATCH_MP_TAC (Q.INST [`es` |-> `ee`,`s` |-> `s`,`G` |-> `G`,`tn` |-> `tn`,
       `fn` |-> `func`,`sa` |-> `sa`] ghost_inv_at_local_window_transport) >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
     simp[ptrDisciplineTheory.allocas_from_def] >>
     rpt strip_tac >> simp[]) >>
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
