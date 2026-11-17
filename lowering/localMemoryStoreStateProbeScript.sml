(* Source-state reconstruction for a joint subpath store. *)
Theory localMemoryStoreStateProbe
Ancestors
  localMemoryStoreProbe placeMemoryPathRebuild typedMemoryCopy
  exprLoweringProps localPtrsProps loweringStateRelDefs loweringSlice
  loweringPosts compileEnv vyperState vyperLookup venomState
  valueEncoding valueEncodingProps memoryValueEncoding valueTypingMemoryProps
  exprSimProps vyperAssignPreservesType vyperTypeValues
  finite_map list words arithmetic

Theorem memory_subpath_state_post:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  lookup_scopes id ff.scopes = SOME entry' /\
  (!name. name <> id ==>
    lookup_scopes name ff.scopes = lookup_scopes name es.scopes) /\
  ff = es with scopes := ff.scopes /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME bw /\
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ value_has_type tv v /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  replace_memory_entry entry path v = INL entry' /\
  val_in_memory tv v (w2n bw+k) t.vs_memory /\
  typed_copy_state_frame sa (w2n bw+k) (type_memory_size tv) s t ==>
  stmt_state_rel H ctx func cenv cx ff t
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `local_region cenv es.scopes s id (w2n bw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_backed func p s (w2n bw) cap /\
   w2n bw+cap <= s.vs_alloca_next /\ type_memory_size entry.type <= cap /\
   val_in_memory entry.type entry.value (w2n bw) s.vs_memory` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
     metis_tac[memory_value_rel_val_in_memory]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `entry'.type = entry.type /\ value_has_type entry'.type entry'.value` by
    (gvs[replace_memory_entry_def,AllCaseEqs()] >>
     irule assign_subscripts_type_path_preserves_type >> metis_tac[]) >>
  `val_wf entry'.type entry'.value` by
    metis_tac[value_has_type_memory_wf] >>
  `val_in_memory entry'.type entry'.value (w2n bw) t.vs_memory` by
    (irule typed_memory_replace_entry_frame >>
     goal_assum (drule_at (Pat `replace_memory_entry _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     qexists_tac `s.vs_memory` >> simp[] >> rpt strip_tac >>
     fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
     first_x_assum irule >> decide_tac) >>
  `!name q sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) ==>
    lookup_var q t = lookup_var q s` by
    (fs[typed_copy_state_frame_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p t = SOME bw` by metis_tac[] >>
  `!name b sz. local_region cenv ff.scopes t name b sz <=>
    local_region cenv es.scopes s name b sz` by
    (rpt gen_tac >> simp[local_region_def] >>
     Cases_on `name = id` >> gvs[] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_labels = s.vs_labels /\ t.vs_data_section = s.vs_data_section /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    fs[typed_copy_state_frame_def,typed_copy_frame_def,venom_state_component_equality] >>
  `!name b len. name <> id /\ local_region cenv es.scopes s name b len ==>
    regions_disjoint (w2n bw) cap b len` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ff.scopes t` by suspend "locals" >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    suspend "immutables" >>
  `state_rel H func cenv cx ff t` by
    (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`,`s`] >>
     simp[] >> fs[stmt_state_rel_def,typed_copy_state_frame_def,
       venom_state_component_equality] >> metis_tac[]) >>
  `ff.immutables = es.immutables` by
    (fs[evaluation_state_component_equality]) >>
  `immutable_alloca_sep func cenv cx ff t` by
    (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >>
     simp[] >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
     fs[stmt_state_rel_def,local_ptrs_reserved_def,typed_copy_state_frame_def] >>
     metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >>
  simp[] >> qexistsl_tac [`es`,`s`] >> simp[]
QED

Resume memory_subpath_state_post[locals]:
  `!n b len. n <> id /\ local_region cenv es.scopes s n b len ==>
    mem_bytes_at b len s.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt strip_tac >>
      qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE
          [typed_copy_state_frame_def,typed_copy_frame_def]) >>
      sym_tac >> first_x_assum irule >>
      `regions_disjoint (w2n bw) cap b len` by metis_tac[] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  `memory_value_rel entry'.type entry'.value (w2n bw) t.vs_memory` by
    (irule val_in_memory_memory_value_rel >> simp[]) >>
  irule local_ptrs_rel_write_local >>
  qexistsl_tac [`entry'`,`id`,`p`,`es.scopes`,`s`,`cap`,`bw`] >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Resume memory_subpath_state_post[immutables]:
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  rename1 `mem_bytes_at off (type_memory_size itv) t.vs_memory = _` >>
  `regions_disjoint off (type_memory_size itv) (w2n bw) cap` by
    (fs[stmt_state_rel_def,immutable_alloca_sep_def] >> metis_tac[]) >>
  fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
  first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac
QED

Finalise memory_subpath_state_post
