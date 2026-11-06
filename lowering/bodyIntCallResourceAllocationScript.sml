Theory bodyIntCallResourceAllocation
Ancestors
  entryStateRel compileVyper compileEnv supportedProgram supportedDecls vyperTypeContract vyperAST
  vyperContext vyperState list finite_map option

(* Distinct flattened namespaces separate keys of different declarations. *)
Theorem distinct_flat_keys_members:
  !keys xs x y k.
    ALL_DISTINCT (FLAT (MAP keys xs)) /\ MEM x xs /\ MEM y xs /\
    MEM k (keys x) /\ MEM k (keys y) ==> x = y
Proof
  gen_tac >> Induct >> simp[] >> rpt gen_tac >>
  simp[ALL_DISTINCT_APPEND] >> strip_tac >> gvs[] >>
  fs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem nonimmutable_declaration_locations:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  MEM top tops /\ toplevel_vtype_keys_toplevel (NONE:num option) top = [(NONE,name)] /\
  (!vis ty slot. top <> VariableDecl vis Immutable name ty slot) ==>
  FLOOKUP (add_immutable_locations sft tops off
    (add_module_var_locations tops FEMPTY)) (NONE,name) =
  FLOOKUP (add_module_var_locations [top] FEMPTY) (NONE,name)
Proof
  strip_tac >>
  `!vis nm ty slot. MEM (VariableDecl vis Immutable nm ty slot) tops ==>
     ((NONE:num option),nm) <> (NONE,name)` by
    (rpt strip_tac >> gvs[] >>
     `MEM ((NONE:num option),name) (toplevel_vtype_keys_toplevel NONE top)` by simp[] >>
     `MEM ((NONE:num option),name) (toplevel_vtype_keys_toplevel NONE
        (VariableDecl vis Immutable name ty slot))` by
       simp[toplevel_vtype_keys_toplevel_def] >>
     drule (Q.ISPEC `toplevel_vtype_keys_toplevel (NONE:num option)`
       distinct_flat_keys_members) >> metis_tac[]) >>
  drule add_immutable_locations_lookup_unchanged >>
  disch_then (qspecl_then [`sft`, `off`, `add_module_var_locations tops FEMPTY`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  irule add_module_var_locations_mem >> simp[]
QED

Theorem pinned_module_allocated:
  supported_program tops /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  ce.ce_module = NONE /\
  ce.ce_module_vars = add_immutable_locations sft tops 0
    (add_module_var_locations tops FEMPTY) /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx ==>
  module_allocated cx.layouts cx.txn.target NONE tops
Proof
  strip_tac >> fs[supported_program_def] >>
  simp[module_allocated_def, EVERY_MEM] >> gen_tac >> strip_tac >>
  rename1 `MEM top tops` >> Cases_on `top` >>
  simp[toplevel_allocated_def]
  >~ [`MEM (VariableDecl vis mut nm ty slot) tops`]
  >- (Cases_on `mut` >> simp[toplevel_allocated_def] >>
      `?n. slot = SOME n` by metis_tac[supported_storage_decl_slot] >> gvs[] >>
      drule_at (Pat `MEM _ _`) nonimmutable_declaration_locations >>
      simp[toplevel_vtype_keys_toplevel_def, add_module_var_locations_def] >>
      disch_then (qspecl_then [`sft`, `0`] assume_tac) >>
      gvs[FLOOKUP_UPDATE, storage_vars_rel_def, transient_vars_rel_def,
         lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def] >> metis_tac[IS_SOME_EXISTS]) >>
  rename1 `MEM (HashMapDecl vis tr nm kt vt slot) tops` >>
  `?n. slot = SOME n` by metis_tac[supported_hashmap_decl_slot] >> gvs[] >>
  drule_at (Pat `MEM _ _`) nonimmutable_declaration_locations >>
  simp[toplevel_vtype_keys_toplevel_def, add_module_var_locations_def] >>
  disch_then (qspecl_then [`sft`, `0`] assume_tac) >>
  Cases_on `tr` >>
  gvs[FLOOKUP_UPDATE, storage_vars_rel_def, transient_vars_rel_def,
     lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def] >> metis_tac[IS_SOME_EXISTS]
QED
