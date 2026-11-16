Theory bodyFullToplevelCtorSourceLayout
Ancestors
  bodySim bodyPtrDefs exprSimHypsDefs gasContext immutableRelation
  typedMemoryCopy structFieldsProps vyperTypeInvariants exprLoweringProps
  vyperTypeGlobalLookupSoundness immSectionDead

Theorem toplevel_ctor_source_layout:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  cx_tops cx = tops /\ off + type_memory_size rt <= lo /\
  ?pre post vis ty slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) pre /\
    ty = ann /\
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size rt
Proof
  strip_tac >>
  `cenv.ce_module = NONE /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_struct_fields = make_struct_fields_map tops` by
    fs[body_inv_def, cenv_module_pins_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `env_consistent env cx es /\ well_typed_expr env
     (TopLevelName ann (cenv.ce_module,id))` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_all TopLevelName_toplevel_vtypes_Type >> strip_tac >>
  drule body_inv_immutable_section_layout >>
  simp[immutable_section_layout_def] >>
  `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)` by metis_tac[] >>
  disch_then (drule_then strip_assume_tac) >>
  `FLOOKUP env.bare_globals (NONE,id) = SOME ty` by
    (fs[env_consistent_def, env_context_consistent_def,
        bare_globals_complete_def] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `ty = ann` by
    (`env_context_consistent env cx` by fs[env_consistent_def] >>
     drule_all env_context_consistent_bare_global_find_NONE >>
     strip_tac >> gvs[]) >>
  `type_memory_bytes cenv ann = type_memory_size rt` by
    (irule typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ann =
     type_memory_size rt` by
    metis_tac[type_mem_bytes_type_memory_bytes] >>
  `lo = imm_len tops` by fs[dead_lo_ok_def] >>
  conj_tac
  >- (qpat_x_assum `lo = _` SUBST1_TAC >>
      simp[imm_len_def] >>
      qpat_assum `tops = _` (fn th => once_rewrite_tac[th]) >>
      simp[compileVyperTheory.compute_immutables_len_append,
           compileVyperTheory.compute_immutables_len_def] >> gvs[]) >>
  qexistsl_tac [`pre`, `post`, `vis`, `slot`] >> simp[]
QED
