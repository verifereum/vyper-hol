Theory entryModuleLocations
Ancestors
  e2eModsDefs bodyInvSplit bodySimModsProps[qualified]
  compileUnit compileVyper compileEnv immutableLocationProps entryStateRel
  loweringStateRelDefs vyperInterpreter vyperContext vyperState vyperTypeContract
  vyperTypeContractStaticMaps[qualified] vyperTypeConstantCells vyperAST
  venomFnInstsProofs finite_map alist list pair

Theorem slot_lookup_src_other[local]:
  !tops m vars k.
    ~MEM k (FLAT (MAP (toplevel_vtype_keys_toplevel m) tops)) ==>
    FLOOKUP (add_module_var_locations_src m tops vars) k = FLOOKUP vars k
Proof
  Induct >- simp[add_module_var_locations_src_def] >>
  rpt gen_tac >> simp[add_module_var_locations_src_def] >> strip_tac >>
  BasicProvers.every_case_tac >>
  gvs[toplevel_vtype_keys_toplevel_def,FLOOKUP_UPDATE]
QED

Theorem slot_lookup_src_mem[local]:
  !tops m vars top k.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel m) tops)) /\
    MEM top tops /\ MEM k (toplevel_vtype_keys_toplevel m top) ==>
    FLOOKUP (add_module_var_locations_src m tops vars) k =
    FLOOKUP (add_module_var_locations_src m [top] vars) k
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[ALL_DISTINCT_APPEND] >> strip_tac
  >- (gvs[] >> simp[Once add_module_var_locations_src_def] >>
      simp[add_module_var_locations_src_def,slot_lookup_src_other]) >>
  `~MEM k (toplevel_vtype_keys_toplevel m h)` by
    (fs[MEM_FLAT,MEM_MAP] >> metis_tac[]) >>
  simp[Once add_module_var_locations_src_def] >>
  first_x_assum (drule_at Any) >> simp[] >> disch_then (K all_tac) >>
  Cases_on `h` >> BasicProvers.every_case_tac >>
  gvs[add_module_var_locations_src_def,toplevel_vtype_keys_toplevel_def,
      FLOOKUP_UPDATE] >>
  Cases_on `top` >> BasicProvers.every_case_tac >>
  gvs[toplevel_vtype_keys_toplevel_def,FLOOKUP_UPDATE]
QED

Theorem slot_lookup_src_cases[local]:
  !tops m vars k loc.
    FLOOKUP (add_module_var_locations_src m tops vars) k = SOME loc ==>
    FLOOKUP vars k = SOME loc \/
    (?vis id ty n. MEM (VariableDecl vis Storage id ty (SOME n)) tops /\
      k = (m,id) /\ loc = StorageLoc (n2w n)) \/
    (?vis id ty n. MEM (VariableDecl vis Transient id ty (SOME n)) tops /\
      k = (m,id) /\ loc = TransientLoc (n2w n)) \/
    (?vis tr id kt vt n. MEM (HashMapDecl vis tr id kt vt (SOME n)) tops /\
      k = (m,id) /\
      loc = (if tr then TransientLoc (n2w n) else StorageLoc (n2w n)))
Proof
  Induct >- simp[add_module_var_locations_src_def] >>
  rpt gen_tac >> simp[add_module_var_locations_src_def] >> strip_tac >>
  first_x_assum drule >> reverse strip_tac
  >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  pop_assum mp_tac >> BasicProvers.every_case_tac >> simp[FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

Theorem slot_lookup_mods_other[local]:
  !mods vars k.
    ~MEM k (contract_keys toplevel_vtype_keys_toplevel mods) ==>
    FLOOKUP (add_module_var_locations_mods mods vars) k = FLOOKUP vars k
Proof
  Induct >- simp[add_module_var_locations_mods_def] >>
  Cases_on `h` >>
  gvs[contract_keys_def,add_module_var_locations_mods_def,
      slot_lookup_src_other]
QED

Theorem slot_lookup_mods_cases[local]:
  !mods vars src id loc.
    FLOOKUP (add_module_var_locations_mods mods vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    ?tops. MEM (src,tops) mods /\
      ((?vis ty n. MEM (VariableDecl vis Storage id ty (SOME n)) tops /\
        loc = StorageLoc (n2w n)) \/
       (?vis ty n. MEM (VariableDecl vis Transient id ty (SOME n)) tops /\
        loc = TransientLoc (n2w n)) \/
       (?vis tr kt vt n. MEM (HashMapDecl vis tr id kt vt (SOME n)) tops /\
        loc = (if tr then TransientLoc (n2w n) else StorageLoc (n2w n))))
Proof
  Induct >- simp[add_module_var_locations_mods_def] >>
  Cases_on `h` >> rpt gen_tac >> simp[add_module_var_locations_mods_def] >>
  strip_tac >> first_x_assum drule >> reverse strip_tac
  >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  drule slot_lookup_src_cases >> simp[] >> metis_tac[]
QED

Theorem slot_lookup_mods_mem[local]:
  !mods vars m tops top k loc.
    ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
    MEM (m,tops) mods /\ MEM top tops /\
    MEM k (toplevel_vtype_keys_toplevel m top) /\
    (!fm. FLOOKUP (add_module_var_locations_src m [top] fm) k = SOME loc) ==>
    FLOOKUP (add_module_var_locations_mods mods vars) k = SOME loc
Proof
  Induct >- simp[] >>
  Cases_on `h` >> rpt gen_tac >> simp[Once contract_keys_def, ALL_DISTINCT_APPEND] >>
  strip_tac >> simp[Once add_module_var_locations_mods_def]
  >- (gvs[GSYM contract_keys_def] >>
      `~MEM k (contract_keys toplevel_vtype_keys_toplevel mods)` by
        (fs[MEM_FLAT,MEM_MAP,contract_keys_def] >> metis_tac[]) >>
      simp[slot_lookup_mods_other] >>
      drule_all slot_lookup_src_mem >> simp[]) >>
  first_x_assum irule >> gvs[contract_keys_def] >> metis_tac[]
QED

Theorem unit_slot_map_lookup[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) ==>
  (FLOOKUP (add_module_var_locations_mods mods FEMPTY) (src,id) = SOME loc <=>
   ?tops. MEM (src,tops) mods /\
     ((?vis ty n. MEM (VariableDecl vis Storage id ty (SOME n)) tops /\
       loc = StorageLoc (n2w n)) \/
      (?vis ty n. MEM (VariableDecl vis Transient id ty (SOME n)) tops /\
       loc = TransientLoc (n2w n)) \/
      (?vis tr kt vt n. MEM (HashMapDecl vis tr id kt vt (SOME n)) tops /\
       loc = (if tr then TransientLoc (n2w n) else StorageLoc (n2w n)))))
Proof
  strip_tac >> iff_tac
  >- (strip_tac >> drule slot_lookup_mods_cases >> simp[]) >>
  rpt strip_tac >> irule slot_lookup_mods_mem >> simp[] >>
  qexists_tac `src` >>
  qpat_assum `MEM _ tops` (EXISTS_TAC o rand o rator o concl) >>
  qexists_tac `tops` >>
  simp[toplevel_vtype_keys_toplevel_def,add_module_var_locations_src_def,
       FLOOKUP_UPDATE]
QED

Theorem annotated_imm_src_lookup[local]:
  !tops owner base src id loc.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel owner) tops)) ==>
    (FLOOKUP (add_annotated_immutables_src owner tops base) (src,id) = SOME loc <=>
     (?off vis ty. src = owner /\
        MEM (VariableDecl vis Immutable id ty (SOME off)) tops /\
        loc = ImmutableLoc off) \/
     (~(?off vis ty. src = owner /\
         MEM (VariableDecl vis Immutable id ty (SOME off)) tops) /\
      FLOOKUP base (src,id) = SOME loc))
Proof
  Induct >- simp[add_annotated_immutables_src_def] >>
  qx_gen_tac `top` >> Cases_on `top` >>
  simp[toplevel_vtype_keys_toplevel_def, add_annotated_immutables_src_def] >>
  rename1 `mut = Immutable` >> Cases_on `mut` >> simp[] >>
  rename1 `SOME _ = slot` >> Cases_on `slot` >> simp[] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >>
  rename1 `if owner = src /\ name = id then _ else _` >>
  Cases_on `owner = src /\ name = id` >> gvs[] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED

Theorem annotated_imm_map_lookup[local]:
  !mods base src id loc.
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) ==>
    (FLOOKUP (add_annotated_immutables_mods mods base) (src,id) = SOME loc <=>
     (?off. (?tops vis ty. MEM (src,tops) mods /\
                MEM (VariableDecl vis Immutable id ty (SOME off)) tops) /\
            loc = ImmutableLoc off) \/
     (~(?off tops vis ty. MEM (src,tops) mods /\
                         MEM (VariableDecl vis Immutable id ty (SOME off)) tops) /\
      FLOOKUP base (src,id) = SOME loc))
Proof
  Induct >- simp[add_annotated_immutables_mods_def] >>
  Cases >>
  simp[contract_keys_def, ALL_DISTINCT_APPEND, add_annotated_immutables_mods_def] >>
  rpt strip_tac >>
  rename1 `~MEM owner (MAP FST mods)` >>
  Cases_on `src = owner`
  >- (gvs[] >>
      `!ts. ~MEM (owner,ts) mods` by metis_tac[MEM_MAP_f, FST] >>
      gvs[annotated_imm_src_lookup] >> metis_tac[]) >>
  gvs[annotated_imm_src_lookup]
QED

Theorem nonsingleton_add_immutable_locations_unit[local]:
  (!tops. mods <> [(NONE,tops)]) ==>
  add_immutable_locations_unit sft mods fm = add_annotated_immutables_mods mods fm
Proof
  Cases_on `mods` >- simp[add_immutable_locations_unit_def] >>
  Cases_on `h` >> Cases_on `t` >> Cases_on `q` >>
  simp[add_immutable_locations_unit_def]
QED

(* The two kinds of declarations that provide slots cannot share a key
   with an immutable declaration. *)
Theorem unit_slot_key_not_immutable[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  FLOOKUP (add_module_var_locations_mods mods FEMPTY) (src,id) = SOME loc ==>
  ~(?off tops vis ty. MEM (src,tops) mods /\
                     MEM (VariableDecl vis Immutable id ty (SOME off)) tops)
Proof
  rpt strip_tac >> gvs[unit_slot_map_lookup] >>
  `tops' = tops` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11] >>
  gvs[] >>
  drule_all contract_keys_module_distinct >> strip_tac >>
  drule all_distinct_flat_map_unique
  >- (rename1 `MEM (VariableDecl sv Storage id sty (SOME sn)) tops` >>
      rename1 `MEM (VariableDecl iv Immutable id ity (SOME off)) tops` >>
      disch_then (qspecl_then
        [`VariableDecl sv Storage id sty (SOME sn)`,
         `VariableDecl iv Immutable id ity (SOME off)`, `(src,id)`] mp_tac) >>
      simp[toplevel_vtype_keys_toplevel_def])
  >- (rename1 `MEM (VariableDecl sv Transient id sty (SOME sn)) tops` >>
      rename1 `MEM (VariableDecl iv Immutable id ity (SOME off)) tops` >>
      disch_then (qspecl_then
        [`VariableDecl sv Transient id sty (SOME sn)`,
         `VariableDecl iv Immutable id ity (SOME off)`, `(src,id)`] mp_tac) >>
      simp[toplevel_vtype_keys_toplevel_def]) >>
  rename1 `MEM (HashMapDecl hv is_transient id kt vt (SOME sn)) tops` >>
  rename1 `MEM (VariableDecl iv Immutable id ity (SOME off)) tops` >>
  disch_then (qspecl_then
    [`HashMapDecl hv is_transient id kt vt (SOME sn)`,
     `VariableDecl iv Immutable id ity (SOME off)`, `(src,id)`] mp_tac) >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

Theorem unit_slot_lookup_frame[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  (!off. loc <> ImmutableLoc off) ==>
  (FLOOKUP (add_immutable_locations_unit sft mods
      (add_module_var_locations_mods mods FEMPTY)) (src,id) = SOME loc <=>
   FLOOKUP (add_module_var_locations_mods mods FEMPTY) (src,id) = SOME loc)
Proof
  strip_tac >> Cases_on `?tops. mods = [(NONE,tops)]`
  >- (gvs[add_immutable_locations_unit_singleton,
          add_module_var_locations_mods_singleton, contract_keys_def] >>
      iff_tac >> strip_tac >>
      metis_tac[add_immutable_locations_FLOOKUP, entry_module_lookup_immutable_frame]) >>
  gvs[nonsingleton_add_immutable_locations_unit, annotated_imm_map_lookup] >>
  metis_tac[unit_slot_key_not_immutable]
QED

(* Compare the full options: uses-only declarations need not carry slots. *)
Theorem unit_slot_layout_lookup[local]:
  layouts_agree_mods mods exps am tx /\
  cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  MEM (src,tops) mods ==>
  (!vis id ty a. MEM (VariableDecl vis Storage id ty a) tops ==>
                 lookup_var_slot_from_layout cx F src id = a) /\
  (!vis id ty a. MEM (VariableDecl vis Transient id ty a) tops ==>
                 lookup_var_slot_from_layout cx T src id = a) /\
  (!vis tr id kt vt a. MEM (HashMapDecl vis tr id kt vt a) tops ==>
                      lookup_var_slot_from_layout cx tr src id = a)
Proof
  simp[layouts_agree_mods_def, lookup_var_slot_from_layout_def] >>
  Cases_on `ALOOKUP am.layouts tx.target` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `ALOOKUP am.layouts tx.target = SOME p` >>
  PairCases_on `p` >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem singleton_unit_immutable_lookup[local]:
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel [(NONE:num option,tops)]) ==>
  (FLOOKUP
     (add_immutable_locations_unit
       (get_struct_fields (make_struct_fields_map_mods [(NONE,tops)]))
       [(NONE,tops)] (add_module_var_locations_mods [(NONE,tops)] FEMPTY))
     (src,name) = SOME (ImmutableLoc off) <=>
   ?size. immutable_region_mods [(NONE,tops)] src name off size)
Proof
  simp[contract_keys_def, make_struct_fields_map_mods_singleton,
       add_immutable_locations_unit_singleton, add_module_var_locations_mods_singleton,
       bodySimModsPropsTheory.singleton_immutable_region] >>
  strip_tac >> iff_tac
  >- (strip_tac >> drule immutable_locations_origin >> strip_tac
      >- (drule immutable_module_vars_origin >> simp[]) >>
      gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  irule (add_immutable_locations_declaration_lookup |> Q.INST [`off` |-> `0`] |> SRULE []) >>
  rpt strip_tac >> gvs[] >>
  drule vyperTypeContractStaticMapsTheory.module_toplevel_vtype_key_MEM_Variable >>
  disch_then (qspec_then `NONE` assume_tac) >>
  metis_tac[]
QED

Theorem linked_unit_immutable_lookup[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  (!tops. mods <> [(NONE,tops)]) ==>
  (FLOOKUP
     (add_immutable_locations_unit
       (get_struct_fields (make_struct_fields_map_mods mods)) mods
       (add_module_var_locations_mods mods FEMPTY))
     (src,name) = SOME (ImmutableLoc off) <=>
   ?size. immutable_region_mods mods src name off size)
Proof
  strip_tac >> simp[nonsingleton_add_immutable_locations_unit,
       annotated_imm_map_lookup, unit_slot_map_lookup, immutable_region_mods_def] >>
  `!tr n. ImmutableLoc off <> (if tr then TransientLoc (n2w n) else StorageLoc (n2w n))`
    by (Cases >> simp[]) >>
  simp[] >> iff_tac
  >- (rpt strip_tac >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> strip_tac >> metis_tac[MEM_SPLIT]) >>
  rpt strip_tac >> drule_then assume_tac ALOOKUP_MEM >>
  qexistsl [`pre ++ VariableDecl vis Immutable name ty (SOME off) :: post`, `vis`, `ty`] >> simp[]
QED

Theorem unit_immutable_region_lookup[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) ==>
  (FLOOKUP
     (add_immutable_locations_unit
       (get_struct_fields (make_struct_fields_map_mods mods)) mods
       (add_module_var_locations_mods mods FEMPTY))
     (src,name) = SOME (ImmutableLoc off) <=>
   ?size. immutable_region_mods mods src name off size)
Proof
  strip_tac >> Cases_on `?tops. mods = [(NONE,tops)]`
  >- gvs[singleton_unit_immutable_lookup] >>
  gvs[linked_unit_immutable_lookup]
QED

Theorem unit_module_locations_immutable_layout:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  layouts_agree_mods mods exps am tx /\
  ce.ce_module_vars =
    add_immutable_locations_unit
      (get_struct_fields (make_struct_fields_map_mods mods)) mods
      (add_module_var_locations_mods mods FEMPTY) ==>
  immutable_section_layout_mods mods ce
Proof
  strip_tac >> fs[layouts_agree_mods_def, immutable_section_layout_mods_def,
                  unit_immutable_region_lookup] >>
  metis_tac[]
QED

Theorem unit_module_locations_slot_relations:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  source_deployment_rel_mods mods exps am tx /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target /\
  ce.ce_module_vars =
    add_immutable_locations_unit
      (get_struct_fields (make_struct_fields_map_mods mods)) mods
      (add_module_var_locations_mods mods FEMPTY) ==>
  storage_vars_rel ce cx /\ transient_vars_rel ce cx
Proof
  strip_tac >>
  `layouts_agree_mods mods exps am tx /\
   ALOOKUP cx.sources cx.txn.target = SOME mods` by
    gvs[source_deployment_rel_mods_def] >>
  `!src ts. get_module_code cx src = SOME ts ==> MEM (src,ts) mods` by
    (simp[get_module_code_def] >> metis_tac[ALOOKUP_MEM]) >>
  simp[storage_vars_rel_def, transient_vars_rel_def,
       unit_slot_lookup_frame, unit_slot_map_lookup] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (drule find_var_decl_by_name_mem >> strip_tac) >>
  gvs[AllCaseEqs(), var_decl_transient_def] >>
  TRY (qpat_x_assum `!src ts. get_module_code _ src = SOME ts ==> _`
         drule >> strip_tac) >>
  drule_all unit_slot_layout_lookup >> strip_tac >>
  metis_tac[]
QED
