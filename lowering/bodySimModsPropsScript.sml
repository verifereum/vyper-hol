Theory bodySimModsProps
Ancestors
  bodyInvSplit bodyInvModuleProps compileEnv compileUnit compileVyper
  exprLowering exprSimHypsDefs immutableRelation loweringStateRelDefs moduleLowering
  supportedDecls supportedExprForms supportedNameRoot vyperAST vyperContext
  vyperInterpreter finite_map arithmetic alist list

Theorem contract_inv_nonreentrant_slot[local]:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\ nr /\
  (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
  cx.nonreentrant_slot = SOME global_nonreentrant_slot
Proof
  rw[contract_inv_def] >> res_tac >> fs[]
QED

Theorem body_inv_nonreentrant_slot_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\ nr /\
  (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
  cx.nonreentrant_slot = SOME global_nonreentrant_slot
Proof
  metis_tac[module_body_inv_lookup, contract_inv_nonreentrant_slot]
QED

Theorem contract_inv_source_modules[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALOOKUP cx.sources cx.txn.target = SOME mods
Proof
  simp[contract_inv_def]
QED

Theorem contract_inv_cenv_module_pins[local]:
  contract_inv mods exps ctx cenv cx ==> cenv_module_pins_mods mods cenv
Proof
  simp[contract_inv_def]
QED

Theorem body_inv_copies_subscript_base_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  copies_subscript_base cenv obj idx = subscript_reads_base cx obj idx
Proof
  strip_tac >> drule contract_inv_source_modules >>
  drule contract_inv_cenv_module_pins >>
  simp[cenv_module_pins_mods_def,
       exprLoweringTheory.copies_subscript_base_def,
       vyperInterpreterTheory.subscript_reads_base_def] >>
  rw[]
QED

Theorem contract_inv_module_tables[local]:
  contract_inv mods exps ctx cenv cx ==>
  (!src. ALOOKUP cenv.ce_modules src = get_module_code cx src) /\
  (!src ts. get_module_code cx src = SOME ts ==>
     ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))) /\
  ALL_DISTINCT (MAP FST cenv.ce_modules)
Proof
  rw[contract_inv_def, cenv_module_pins_mods_def, get_module_code_def] >>
  res_tac
QED

Theorem body_inv_modules_aligned_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  (!src. ALOOKUP cenv.ce_modules src = get_module_code cx src) /\
  (!src ts. get_module_code cx src = SOME ts ==>
     ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))) /\
  ALL_DISTINCT (MAP FST cenv.ce_modules)
Proof
  metis_tac[contract_inv_module_tables]
QED

(* Existing support predicates resolve names in the main namespace. *)
Theorem contract_inv_module_keys[local]:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))
Proof
  rw[contract_inv_def] >> res_tac
QED

Theorem body_inv_const_name_decl_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  cx_const_name_mods mods (NONE,id) ==>
  ?vis c ty slot.
    supported_variable_decl (main_module mods) (NONE,id) =
      SOME (vis,Constant c,ty,slot)
Proof
  rw[cx_const_name_mods_def, main_module_def] >>
  irule distinct_module_consts_env_names_constant >>
  simp[] >> metis_tac[contract_inv_module_keys]
QED

Theorem body_inv_const_name_not_root_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  cx_const_name_mods mods (NONE,id) ==>
  (!ty. ~supported_storage_value (main_module mods) (NONE,id) ty) /\
  supported_immutable_type (main_module mods) (NONE,id) = NONE
Proof
  metis_tac[body_inv_const_name_decl_mods, supported_constant_decl_not_root]
QED

Theorem body_inv_immutable_section_layout_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  immutable_section_layout_mods mods cenv
Proof
  metis_tac[contract_inv_immutable_section_layout]
QED

Theorem immutable_region_mods_linked[local]:
  1 < LENGTH mods ==>
  (immutable_region_mods mods src name off bytes <=>
   ?tops vis ty.
     ALOOKUP mods src = SOME tops /\
     MEM (VariableDecl vis Immutable name ty (SOME off)) tops /\
     bytes = type_mem_bytes
       (get_struct_fields (make_struct_fields_map_mods mods)) ty)
Proof
  strip_tac >>
  `!tops. mods <> [(NONE,tops)]` by (rpt strip_tac >> gvs[]) >>
  simp[immutable_region_mods_def] >> eq_tac >> strip_tac
  >- (qexistsl_tac [`pre ++ VariableDecl vis Immutable name ty (SOME off)::post`,
                    `vis`, `ty`] >> simp[]) >>
  qpat_x_assum `MEM _ tops` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qexistsl_tac [`l1`, `l2`, `vis`, `ty`] >>
  gvs[APPEND_ASSOC]
QED

(* Layout-bearing declarations from the linked-unit twin_names fixture. *)
Theorem twin_names_immutable_layout:
  mods =
    [(NONE, [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 1);
             VariableDecl Private Immutable "IMM" (BaseT (UintT 256)) (SOME 32)]);
     (SOME 2, [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0);
               VariableDecl Private Immutable "IMM" (BaseT (UintT 256)) (SOME 0)])] /\
  cenv_module_pins_mods mods cenv ==>
  immutable_section_layout_mods mods cenv /\ imm_len_mods mods = 64
Proof
  strip_tac >> gvs[] >>
  `!src name off size.
      immutable_region_mods
        [(NONE, [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 1);
                 VariableDecl Private Immutable "IMM" (BaseT (UintT 256)) (SOME 32)]);
         (SOME 2, [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0);
                   VariableDecl Private Immutable "IMM" (BaseT (UintT 256)) (SOME 0)])]
        src name off size <=>
      name = "IMM" /\ size = 32 /\
      (src = NONE /\ off = 32 \/ src = SOME 2 /\ off = 0)` by
    (simp[immutable_region_mods_linked, ALOOKUP_def, type_mem_bytes_def,
          AllCaseEqs()] >>
     rpt gen_tac >> Cases_on `src` >> simp[AllCaseEqs()] >>
     EVAL_TAC >> simp[] >> metis_tac[]) >>
  `!src name off.
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) <=>
      name = "IMM" /\ (src = NONE /\ off = 32 \/ src = SOME 2 /\ off = 0)` by
    (qpat_x_assum `cenv_module_pins_mods _ _` mp_tac >>
     simp[cenv_module_pins_mods_def, add_immutable_locations_unit_def,
          add_annotated_immutables_mods_def, add_annotated_immutables_src_def,
          add_module_var_locations_mods_def, add_module_var_locations_src_def,
          FLOOKUP_UPDATE, AllCaseEqs()] >>
     strip_tac >> rpt gen_tac >> Cases_on `src` >- simp[] >>
     rename1 `SOME src_id = SOME 2` >> simp[] >>
     Cases_on `src_id = 2` >> simp[] >> metis_tac[]) >>
  simp[immutable_section_layout_mods_def, loweringStateRelDefsTheory.regions_disjoint_def,
       imm_len_mods_def, compute_immutables_len_unit_def,
       annotated_immutables_len_def, type_mem_bytes_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `i < 32`
  >- (qexistsl_tac [`SOME 2`, `0`] >> simp[]) >>
  qexistsl_tac [`NONE`, `32`] >> simp[]
QED

Theorem singleton_immutable_region:
  immutable_region_mods [(NONE,tops)] src name off width <=>
    src = NONE /\
    ?pre post vis ty slot.
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
      off = compute_immutables_len
        (get_struct_fields (make_struct_fields_map tops)) pre /\
      width = type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  Cases_on `src` >>
  simp[immutable_region_mods_def, make_struct_fields_map_mods_singleton, ALOOKUP_def] >>
  eq_tac >> rpt strip_tac >>
  qexistsl [`pre`, `post`, `vis`, `ty`, `slot`] >> gvs[]
QED

Theorem immutable_section_layout_mods_singleton:
  immutable_section_layout_mods [(NONE,tops)] cenv ==>
  immutable_section_layout cenv tops
Proof
  simp[immutable_section_layout_mods_def, immutable_section_layout_def,
       singleton_immutable_region] >> metis_tac[]
QED
