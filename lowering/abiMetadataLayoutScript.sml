(* Compiler ABI layout for successfully evaluated types in any namespace. *)
Theory abiMetadataLayout
Ancestors
  abiMetadataErasure abiLayoutSource abiEncoderProps structFieldsProps vyperTyping
  vyperTypeABI vyperValue compileEnv vyperABI finite_map list rich_list pair option vyperMisc

Theorem abi_layout_list_assemble[local]:
  !ts. EVERY (\t.
    is_abi_dynamic sf t = vyper_is_dynamic env t /\
    abi_size_bound sf t = vyper_abi_size_bound env t /\
    (~vyper_is_dynamic env t ==>
     abi_static_size sf t = vyper_abi_size_bound env t)) ts ==>
    EXISTS (is_abi_dynamic sf) ts = vyper_any_dynamic env ts /\
    SUM (MAP (\t. (if is_abi_dynamic sf t then 32
                   else abi_static_size sf t) +
                  (if is_abi_dynamic sf t then abi_size_bound sf t
                   else 0)) ts) = vyper_abi_size_bound_list env ts /\
    (~vyper_any_dynamic env ts ==>
     SUM (MAP (\t. if is_abi_dynamic sf t then 32
                   else abi_static_size sf t) ts) =
       vyper_abi_size_bound_list env ts)
Proof
  Induct >> simp[vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
  rpt strip_tac >> Cases_on `vyper_is_dynamic env h` >> gvs[]
QED

val abi_size_defs =
  [is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
   vyper_is_dynamic_def, vyper_abi_size_bound_def,
   abi_embedded_static_size_def];

Theorem abi_layout_evaluated_size[local]:
  !n env ty tv sf.
    type_value_size tv = n /\ evaluate_type env ty = SOME tv /\
    sfields_tenv_consistent sf env ==>
    is_abi_dynamic sf ty = vyper_is_dynamic env ty /\
    abi_size_bound sf ty = vyper_abi_size_bound env ty /\
    (~vyper_is_dynamic env ty ==>
     abi_static_size sf ty = vyper_abi_size_bound env ty)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >> Cases_on `ty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
      gvs[evaluate_type_def] >> simp (contractABITheory.ceil32_def::abi_size_defs))
  >~ [`NoneT`]
  >- simp abi_size_defs
  >~ [`FlagT nsid`]
  >- simp abi_size_defs
  >~ [`ArrayT t bd`]
  >- (gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum (qspec_then `type_value_size tv'` mp_tac) >>
      simp[type_value_size_def] >>
      disch_then (qspecl_then [`env`, `t`, `tv'`, `sf`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `bd` >> simp abi_size_defs >>
      Cases_on `vyper_is_dynamic env t` >> gvs[])
  >~ [`TupleT ts`]
  >- (gvs[evaluate_type_def, AllCaseEqs()] >>
      drule evaluate_types_LIST_REL >> strip_tac >>
      `EVERY (\t. is_abi_dynamic sf t = vyper_is_dynamic env t /\
         abi_size_bound sf t = vyper_abi_size_bound env t /\
         (~vyper_is_dynamic env t ==>
          abi_static_size sf t = vyper_abi_size_bound env t)) ts` by
        (simp[EVERY_MEM] >> rpt strip_tac >>
         drule_all LIST_REL_MEM_IMP >> strip_tac >>
         drule_all MEM_type_value_size_TupleTV >> strip_tac >>
         fs[type_value_size_def] >>
         first_x_assum (qspec_then `type_value_size y` mp_tac) >>
         simp[] >>
         disch_then (qspecl_then [`env`, `t`, `y`, `sf`] mp_tac) >> simp[]) >>
      drule abi_layout_list_assemble >> strip_tac >>
      simp abi_size_defs >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])
  >> suspend "struct"
QED

Resume abi_layout_evaluated_size[struct]:
  rename1 `StructT a` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  drule_all evaluate_types_erase_struct_aliases >>
  qmatch_goalsub_abbrev_tac `evaluate_types erased _ _` >> strip_tac >>
  `sfields_tenv_consistent (sf \\ nsid_to_string a) erased` by
    (drule sfields_tenv_consistent_erase_aliases >>
     disch_then (qspec_then `a` mp_tac) >> simp[Abbr `erased`]) >>
  `erased SUBMAP env` by simp[Abbr `erased`] >>
  `?fields. FLOOKUP sf (nsid_to_string a) = SOME fields /\
            MAP (FST o SND) fields = MAP SND args` by
    (qpat_assum `sfields_tenv_consistent sf env` mp_tac >>
     pure_rewrite_tac[sfields_tenv_consistent_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> simp[]) >>
  `LENGTH tvs = LENGTH args` by
    (drule evaluate_types_LIST_REL >>
     disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  `!y. MEM y tvs ==> type_value_size y <
      type_value_size (StructTV (ZIP(MAP FST args,tvs)))` by
    (rpt strip_tac >>
     `MEM y (MAP SND (ZIP(MAP FST args,tvs)))` by simp[MAP_ZIP] >>
     gvs[MEM_MAP, EXISTS_PROD] >> drule_all MEM_type_value_size_StructTV >> simp[]) >>
  drule_at (Pat `evaluate_types erased _ _`) evaluate_types_LIST_REL >> strip_tac >>
  `EVERY (\t. is_abi_dynamic (sf \\ nsid_to_string a) t =
                  vyper_is_dynamic erased t /\
     abi_size_bound (sf \\ nsid_to_string a) t = vyper_abi_size_bound erased t /\
     (~vyper_is_dynamic erased t ==>
      abi_static_size (sf \\ nsid_to_string a) t = vyper_abi_size_bound erased t))
     (MAP SND args)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >> strip_tac >>
     first_assum drule >> strip_tac >>
     fs[type_value_size_def] >>
     qpat_x_assum `!m. _` (qspec_then `type_value_size y` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`erased`, `t`, `y`, `sf \\ nsid_to_string a`] mp_tac) >>
     simp[]) >>
  drule abi_layout_list_assemble >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `vyper_any_dynamic erased (MAP SND args) =
     vyper_any_dynamic (env \\ a) (MAP SND args) /\
   vyper_abi_size_bound_list erased (MAP SND args) =
     vyper_abi_size_bound_list (env \\ a) (MAP SND args)` by
    (qpat_assum `evaluate_types erased _ _ = _`
       (mp_then Any mp_tac (cj 2 vyper_abi_layout_submap)) >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `evaluate_types (env \\ a) _ _ = _`
       (mp_then Any mp_tac (cj 2 vyper_abi_layout_submap)) >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  simp abi_size_defs >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  gvs[]
QED

Finalise abi_layout_evaluated_size

Theorem abi_layout_vyper_type:
  evaluate_type env ty = SOME tv /\ sfields_tenv_consistent sf env ==>
  is_abi_dynamic sf ty = vyper_is_dynamic env ty /\
  abi_size_bound sf ty = vyper_abi_size_bound env ty /\
  (~vyper_is_dynamic env ty ==>
   abi_static_size sf ty = vyper_abi_size_bound env ty)
Proof
  metis_tac[abi_layout_evaluated_size]
QED

Theorem abi_layout_vyper_list:
  evaluate_types env ts acc = SOME tvs /\ sfields_tenv_consistent sf env ==>
  EXISTS (is_abi_dynamic sf) ts = vyper_any_dynamic env ts /\
  SUM (MAP (\t. (if is_abi_dynamic sf t then 32
                 else abi_static_size sf t) +
                (if is_abi_dynamic sf t then abi_size_bound sf t
                 else 0)) ts) = vyper_abi_size_bound_list env ts /\
  (~vyper_any_dynamic env ts ==>
   SUM (MAP (\t. if is_abi_dynamic sf t then 32
                 else abi_static_size sf t) ts) =
     vyper_abi_size_bound_list env ts)
Proof
  strip_tac >> irule abi_layout_list_assemble >>
  gvs[evaluate_types_OPT_MMAP, AllCaseEqs(), OPT_MMAP_SOME_IFF] >>
  gvs[EVERY_MAP, EVERY_MEM, IS_SOME_EXISTS] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all abi_layout_vyper_type >> simp[]
QED
