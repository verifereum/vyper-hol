Theory bodyFullToplevelCtorSourceFrame
Ancestors
  bodyFullToplevelCtorSourceLayout ctorDeployDeadSectionRel abiCallerTypeEnv
  loweringSlice abiCanonicalHeadSize valueEncodingProofs valueEncodingProps
  bodySim vyperContext bodyPtrDefs typedMemoryCopy structFieldsProps exprSimHypsDefs

Theorem toplevel_ctor_source_type_transport[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es ==>
  type_env tops SUBMAP get_tenv cx
Proof
  strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   (!src ts. get_module_code cx src = SOME ts ==> src = NONE)` by
    fs[body_inv_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target`
  >- gvs[get_module_code_def] >>
  rename1 `ALOOKUP cx.sources cx.txn.target = SOME mods` >>
  Cases_on `mods` >- gvs[get_module_code_def] >>
  PairCases_on `h` >>
  `get_module_code cx h0 = SOME h1` by
    simp[get_module_code_def] >>
  `h0 = NONE` by metis_tac[] >>
  gvs[get_module_code_def, get_tenv_def, type_env_all_modules_def,
      type_env_def, finite_mapTheory.SUBMAP_FUNION]
QED

Theorem toplevel_ctor_source_frame:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
  evaluate_type (get_tenv cx) ann = SOME rt /\
  cx_tops cx = tops /\ off + type_memory_size rt <= lo /\
  tops = pre ++ VariableDecl vis Immutable id ann slot :: post /\
  off = compute_immutables_len
    (get_struct_fields (make_struct_fields_map tops)) pre /\
  type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ann =
    type_memory_size rt ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v off mem
Proof
  strip_tac >>
  `immutable_value_admissible rt v /\ val_in_memory rt v off s.vs_memory` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def,
        loweringStateRelDefsTheory.immutables_rel_def] >> metis_tac[]) >>
  `val_wf rt v` by metis_tac[immutable_admissible_val_wf] >>
  `well_formed_type_value rt` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `!m. mem_bytes_at off (type_memory_size rt) (mem_bytes_at 0 lo m) =
       mem_bytes_at off (type_memory_size rt) m` by
    (gen_tac >> qpat_x_assum `off = _` kall_tac >>
     qpat_x_assum `tops = _` kall_tac >>
     simp[valueEncodingDefsTheory.mem_bytes_at_bounded,
          abiCanonicalHeadSizeTheory.mem_bytes_at_window]) >>
  `val_in_memory rt v off (mem_bytes_at 0 lo s.vs_memory)` by
    (irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
     conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `s.vs_memory`] >> simp[]) >>
  gen_tac >> strip_tac >>
  `val_in_memory rt v off (mem_bytes_at 0 lo mem)` suffices_by
    (strip_tac >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
     conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `mem_bytes_at 0 lo mem`] >> simp[]) >>
  irule section_value_memory_frame >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexists_tac `mem_bytes_at 0 lo s.vs_memory` >>
  simp[IgnAsm `off = _`, IgnAsm `tops = _`] >>
  gen_tac >> strip_tac >> suspend "live_byte"
QED

Resume toplevel_ctor_source_frame[live_byte]:
  `j NOTIN tn.t_mem` suffices_by
    (strip_tac >>
     `mem_bytes_at j 1 s.vs_memory = mem_bytes_at j 1 mem` by
       fs[mem_agree_outside_def] >>
     `j < lo` by decide_tac >>
     qpat_x_assum `mem_bytes_at j 1 _ = _`
       (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at,
          IgnAsm `off = _`, IgnAsm `tops = _`]) >>
  strip_tac >>
  `imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) j` by
    (`j < lo` by decide_tac >>
     qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def, IgnAsm `off = _`, IgnAsm `tops = _`] >>
     metis_tac[]) >>
  pop_assum mp_tac >> pure_rewrite_tac[immSectionDeadTheory.imm_section_dead_def] >>
  disch_then (qx_choosel_then [`pre2`,`vis2`,`name2`,`ty2`,`slot2`,`post2`,`tv2`]
    strip_assume_tac) >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule toplevel_ctor_source_type_transport >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) ty2 = SOME tv2` by
    metis_tac[abi_caller_type_submap] >>
  `type_memory_bytes cenv ty2 = type_memory_size tv2` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty2 =
     type_memory_size tv2` by
    (fs[body_inv_def] >> metis_tac[type_mem_bytes_type_memory_bytes]) >>
  drule (cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >>
  strip_tac >>
  `pre ++ [VariableDecl vis Immutable id ann slot] ++ post =
   pre2 ++ (VariableDecl vis2 Immutable name2 ty2 slot2 :: post2)` by
    (pure_rewrite_tac[listTheory.APPEND, listTheory.APPEND_ASSOC] >>
     (gvs[])) >>
  pop_assum mp_tac >> pure_rewrite_tac[listTheory.APPEND_EQ_APPEND_MID] >>
  disch_then (DISJ_CASES_THEN (qx_choose_then `mid` strip_assume_tac))
  >- (qpat_x_assum `pre2 = _` SUBST_ALL_TAC >>
      qpat_x_assum `off = _` SUBST_ALL_TAC >>
      fs[compileVyperTheory.compute_immutables_len_append,
         compileVyperTheory.compute_immutables_len_def] >> gvs[]) >>
  Cases_on `mid`
  >- (gvs[] >>
      rule_assum_tac (PURE_REWRITE_RULE
        [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >> fs[]) >>
  qpat_x_assum `pre = _` SUBST_ALL_TAC >>
  gvs[listTheory.APPEND] >>
  fs[compileVyperTheory.compute_immutables_len_append,
     compileVyperTheory.compute_immutables_len_def] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >> gvs[]
QED
Finalise toplevel_ctor_source_frame
