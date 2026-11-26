(* The linked StructLit compiler uses the same order as its typed source fields. *)
Theory bodyStructFieldsLayoutMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimAggregateLayout structFieldsProps
  loweringStateRelDefs typedMemoryCopy compileEnv allocLimits exprSimHyps
  vyperTypeSystem vyperTypeEvalCaseProofs vyperTypeABI vyperValue vyperContext
  vyperAST valueEncoding list pair finite_map option words

Theorem layout_field_sizes[local]:
  EVERY (\(name,ty,sz). !rt. evaluate_type tenv ty = SOME rt ==>
                              sz = type_memory_size rt) fields /\
  i < LENGTH fields /\ evaluate_type tenv (FST (SND (EL i fields))) = SOME tv ==>
  SND (SND (EL i fields)) = type_memory_size tv
Proof
  simp[EVERY_EL] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  Cases_on `EL i fields` >> rename1 `(_, info)` >> Cases_on `info` >> gvs[]
QED

Theorem layout_ordered_fields[local]:
  MAP FST fields = MAP FST kes /\ ALL_DISTINCT (MAP FST fields) /\
  LIST_REL arg_type_fits (MAP (expr_type o SND) kes) (MAP (FST o SND) fields) /\
  EVERY (\(name,ty,sz). !rt. evaluate_type tenv ty = SOME rt ==>
                              sz = type_memory_size rt) fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name flds. FLOOKUP ce.ce_struct_fields name = SOME flds ==>
    EVERY (\(name,ty,sz). !rt. evaluate_type tenv ty = SOME rt ==>
                                sz = type_memory_size rt) flds) /\
  OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs ==>
  LIST_REL (\t (name,e). ALOOKUP fields name = SOME (t,type_memory_bytes ce t))
    (MAP (FST o SND) fields) kes /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t)
    (MAP (FST o SND) fields) (MAP SND kes)
Proof
  strip_tac >>
  `LENGTH fields = LENGTH kes` by metis_tac[LENGTH_MAP] >>
  reverse conj_tac
  >- (fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >> simp[]) >>
  drule_then assume_tac OPT_MMAP_LIST_REL >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  `ALOOKUP fields (FST (EL n kes)) = SOME (SND (EL n fields))` by
    (irule struct_layout_lookup >> simp[]) >>
  `evaluate_type tenv (FST (SND (EL n fields))) = SOME (EL n tvs)` by
    fs[LIST_REL_EL_EQN, EL_MAP] >>
  `n < LENGTH fields` by simp[] >>
  drule_all_then assume_tac layout_field_sizes >>
  drule_all_then assume_tac typed_copy_memory_size >>
  Cases_on `EL n kes` >> gvs[pairTheory.PAIR_FST_SND_EQ]
QED

Theorem struct_fields_layout_mods:
  expr_body_pre_mods mods ce cx env (StructLit ann nsid kes) es ==>
  ann = StructT nsid /\
  LIST_REL (\t (name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME (t,type_memory_bytes ce t))
    (MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) kes /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t)
    (MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))
    (MAP SND kes) /\
  ?tvs.
    OPT_MMAP (evaluate_type (get_tenv cx))
      (MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) = SOME tvs /\
    type_memory_size_list tvs =
      SUM (MAP (SND o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
    evaluate_type (get_tenv cx) (StructT nsid) = SOME (StructTV (ZIP (MAP FST kes,tvs))) /\
    type_memory_size_list tvs < dimword(:256)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(name,ty,sz). !rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
                                  sz = type_memory_size rt) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     asm_rewrite_tac[]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by simp[] >>
  drule_all_then strip_assume_tac struct_literal_layout_types >>
  `?tv. evaluate_type (get_tenv cx) (StructT nsid) = SOME tv` by
    gvs[well_typed_expr_def, well_formed_type_def, IS_SOME_EXISTS] >>
  drule_then strip_assume_tac evaluated_struct_layout >>
  `MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (qpat_assum `sfields_tenv_consistent _ (get_tenv cx)`
       (strip_assume_tac o PURE_REWRITE_RULE [sfields_tenv_consistent_def]) >>
     qpat_assum `!nsid args. FLOOKUP _ nsid = SOME (StructArgs args) ==> _`
       (drule_then strip_assume_tac) >>
     gvs[]) >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     EVERY (\(name,ty,sz). !rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
                                 sz = type_memory_size rt) fields` by
    (rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> ALL_DISTINCT _ /\ _`
       drule >> simp[]) >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (drule OPT_MMAP_LENGTH >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs` by
    (drule_all typed_copy_memory_size >> simp[type_memory_size_def, struct_layout_size_zip]) >>
  `type_memory_bytes ce (StructT nsid) < 2 ** 64` by
    fs[expr_body_pre_mods_def, alloc_limits_expr_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    gvs[wordsTheory.dimword_def] >>
  `LIST_REL (\t (name,e). ALOOKUP fields name = SOME (t,type_memory_bytes ce t))
      (MAP (FST o SND) fields) kes /\
   LIST_REL (\t e. arg_type_fits (expr_type e) t)
      (MAP (FST o SND) fields) (MAP SND kes)` by
    (qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> ALL_DISTINCT _ /\ _`
       (drule_then strip_assume_tac) >>
     irule layout_ordered_fields >> simp[] >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`get_tenv cx`, `tvs`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `get_struct_fields ce.ce_struct_fields (nsid_to_string nsid) = fields` by
    simp[get_struct_fields_def] >>
  `type_memory_size_list tvs = SUM (MAP (SND o SND) fields)` by
    (qpat_assum `type_memory_bytes ce (StructT nsid) = type_memory_size_list _`
       (mp_tac o SYM) >>
     pure_rewrite_tac[compileEnvTheory.type_memory_bytes_def] >> asm_rewrite_tac[]) >>
  fs[] >> conj_tac >>
  qpat_assum `MAP (FST o SND) fields = MAP SND args` (PURE_REWRITE_TAC o single o SYM) >>
  first_assum ACCEPT_TAC
QED
