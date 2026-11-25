Theory bodyInvSplit
Ancestors
  bodyCallSupport compileUnit compileEnv compileVyper immSectionDead
  exprLoweringProps loweringStateRelDefs immutableLocationProps
  supportedProgram vyperTypeContract vyperTypeSystem vyperTypeConstantFold
  vyperAST vyperContext vyperABI moduleLowering venomInst
  alist finite_map list words combin

(* The fixed memory prefix shared by all modules of a deploy unit. *)
Definition imm_len_mods_def[nocompute]:
  imm_len_mods mods =
    compute_immutables_len_unit
      (get_struct_fields (make_struct_fields_map_mods mods)) mods
End

Theorem imm_len_mods_singleton:
  imm_len_mods [(NONE,tops)] = imm_len tops
Proof
  simp[imm_len_mods_def, imm_len_def, make_struct_fields_map_mods_singleton,
       compute_immutables_len_unit_singleton]
QED

(* A uses-only module has no allocated region for an unannotated
   immutable. The singleton allocator uses declaration order. *)
Definition immutable_region_mods_def[nocompute]:
  immutable_region_mods mods src name off size <=>
    ?tops pre post vis ty slot.
      ALOOKUP mods src = SOME tops /\
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
      (if mods = [(NONE,tops)] then
         off = compute_immutables_len
           (get_struct_fields (make_struct_fields_map_mods mods)) pre
       else slot = SOME off) /\
      size = type_mem_bytes
        (get_struct_fields (make_struct_fields_map_mods mods)) ty
End

(* Allocated immutables partition the fixed prefix at their builder offsets. *)
Definition immutable_section_layout_mods_def[nocompute]:
  immutable_section_layout_mods mods cenv <=>
    (!src name off.
       FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) <=>
       ?size. immutable_region_mods mods src name off size) /\
    (!src name off size.
       immutable_region_mods mods src name off size ==>
       off + size <= imm_len_mods mods) /\
    (!src name off size src' name' off' size'.
       (src,name) <> (src',name') /\
       immutable_region_mods mods src name off size /\
       immutable_region_mods mods src' name' off' size' ==>
       loweringStateRelDefs$regions_disjoint off size off' size') /\
    (!i. i < imm_len_mods mods ==>
       ?src name off size.
         immutable_region_mods mods src name off size /\
         off <= i /\ i < off + size)
End

(* The singleton equation also holds before the caller has established
   that cenv's immutable locations agree with its declarations. *)
Definition imm_section_dead_mods_def[nocompute]:
  imm_section_dead_mods cenv sec j <=>
    case cenv.ce_modules of
      [(NONE,tops)] => imm_section_dead tops sec j
    | mods =>
      ?src tops vis name ty slot off tv.
        ALOOKUP mods src = SOME tops /\
        MEM (VariableDecl vis Immutable name ty slot) tops /\
        FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        evaluate_type (type_env_all_modules mods) ty = SOME tv /\
        mem_dead_bytes sec off tv j
End

Theorem imm_section_dead_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] ==>
  (imm_section_dead_mods cenv sec j <=> imm_section_dead tops sec j)
Proof
  simp[imm_section_dead_mods_def]
QED

(* These relations cover the shared immutable section even when a call
   changes the active module. *)
Definition immutables_rel_mods_def[nocompute]:
  immutables_rel_mods cenv addr ctor vs ss <=>
    !src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
      immutables_rel cenv addr src ctor vs ss
End

Definition immutable_decl_sep_mods_def[nocompute]:
  immutable_decl_sep_mods cenv cx scopes vars allocas next <=>
    !src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
      immutable_decl_sep (cenv with ce_module := src) cx scopes vars allocas next
End

Definition immutable_alloca_sep_mods_def[nocompute]:
  immutable_alloca_sep_mods func cenv cx vs ss <=>
    !src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
      immutable_alloca_sep func (cenv with ce_module := src) cx vs ss
End

(* Compile-env tables that the single-module cenv_module_pins checks. *)
Definition cenv_module_pins_mods_def[nocompute]:
  cenv_module_pins_mods mods cenv <=>
    cenv.ce_modules = mods /\
    cenv.ce_func_mutability = build_func_mutability_mods mods /\
    cenv.ce_module_var_type = build_var_type_map_mods mods /\
    cenv.ce_module_vars =
      add_immutable_locations_unit
        (get_struct_fields (make_struct_fields_map_mods mods)) mods
        (add_module_var_locations_mods mods FEMPTY) /\
    cenv.ce_flag_member_id = FST (build_flag_info_mods mods (K (K 0)) (K 0)) /\
    cenv.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0)) /\
    cenv.ce_error_info = (\name. lookup_custom_error_args_mods mods name) /\
    cenv.ce_method_id =
      (\s tys. w2n (calldata_method_id
                     (function_selector s
                       (vyper_to_abi_types (type_env_all_modules mods) tys))))
End

(* Facts shared by all function bodies of a linked unit. The relations
   on individual runtime states are carried by the body judgments. *)
Definition contract_inv_def[nocompute]:
  contract_inv mods exps ctx cenv cx <=>
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    IS_SOME (ALOOKUP mods NONE) /\
    ALL_DISTINCT (MAP FST mods) /\
    (!src tops. ALOOKUP mods src = SOME tops ==>
       supported_module_headers tops /\
       (src = NONE ==>
          supported_program tops /\
          (cx.in_deploy ==> supported_program_deploy tops)) /\
       ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))) /\
    ALL_DISTINCT (FLAT (MAP (\(src,tops).
       FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) mods)) /\
    (?rpolicy unit.
       (if cx.in_deploy then
          ?rbc. lower_vyper_deploy_unit_mods mods exps rpolicy rbc = SOME unit
        else lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit) /\
       ctx = unit.cu_context /\ cenv.ce_target = rpolicy.rpol_target) /\
    (cx.in_deploy ==>
       IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps)))))) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env_all_modules mods) target)) /\
    linked_body_calls_resolved mods cx /\
    cenv_module_pins_mods mods cenv /\
    cenv.ce_func_ids = build_func_ids_mods 0 mods /\
    cenv.ce_func_param_types = build_func_param_types_mods mods /\
    cenv.ce_func_info =
      build_func_info_mods (get_struct_fields (make_struct_fields_map_mods mods))
        mods /\
    cenv.ce_func_return_type = build_func_return_type_mods mods /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    cenv.ce_event_info = build_event_info_mods (type_env_all_modules mods) mods (K NONE) /\
    cenv.ce_struct_fields = make_struct_fields_map_mods mods /\
    (cenv.ce_is_ctor <=> cx.in_deploy) /\ cenv.ce_alloca_locals /\
    cenv.ce_hashmap_info = build_hashmap_info_mods mods /\
    cenv.ce_module_dynarray_capacity =
      build_dynarray_capacity (collect_module_vars_mods mods) /\
    (!src name. IS_SOME (ALOOKUP mods src) /\ ~MEM (src,name) cx.stk ==>
       ALOOKUP cenv.ce_func_defaults (nsid_to_string (src,name)) =
       ALOOKUP (build_func_defaults_mods mods) (nsid_to_string (src,name))) /\
    (!src tops vis mut nr rr name args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
       (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
       function_mutability_ok mods vis mut nr dflts ss /\
       (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
       (cx.in_deploy /\ vis = Deploy ==> EVERY (supported_value_type tops o SND) args)) /\
    (!src tops vis mut nr rr name args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
       (src = NONE \/ context_function_live cx (src,name)) ==>
       supported_declaration_body tops
         (FunctionDecl vis mut nr rr name args dflts ret ss) /\
       (cx.in_deploy ==> supported_deploy_declaration tops
         (FunctionDecl vis mut nr rr name args dflts ret ss))) /\
    immutable_section_layout_mods mods cenv
End

(* The body currently runs in src while using the unit's shared tables. *)
Definition module_body_inv_def[nocompute]:
  module_body_inv mods src tops cenv (cx : evaluation_context) <=>
    ALOOKUP mods src = SOME tops /\ cenv.ce_module = src
End

Theorem contract_inv_module_gate:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods NONE tops cenv cx ==>
  supported_program tops /\ (cx.in_deploy ==> supported_program_deploy tops)
Proof
  rw[contract_inv_def, module_body_inv_def] >>
  res_tac
QED

Theorem contract_inv_module_distinct_keys:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))
Proof
  rw[contract_inv_def, module_body_inv_def] >>
  res_tac
QED

Theorem contract_inv_module_code:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  get_module_code cx src = SOME tops
Proof
  rw[contract_inv_def, module_body_inv_def, get_module_code_def]
QED

Theorem contract_inv_module_type_env:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx ==>
  type_env_for_module src tops SUBMAP get_tenv cx
Proof
  rw[contract_inv_def, module_body_inv_def, get_tenv_def,
     SUBMAP_FLOOKUP_EQN, pairTheory.FORALL_PROD] >>
  rename1 `FLOOKUP (type_env_for_module src tops) (sid,id) = SOME a` >>
  `sid = src` by
    (qpat_x_assum `FLOOKUP (type_env_for_module _ _) _ = _` mp_tac >>
     qid_spec_tac `tops` >>
     Induct >> simp[type_env_for_module_def] >>
     Cases >> simp[type_env_for_module_def, FLOOKUP_UPDATE] >>
     rw[] >> gvs[AllCaseEqs()]) >>
  gvs[FLOOKUP_type_env_all_modules]
QED

Theorem contract_inv_immutable_section_layout:
  contract_inv mods exps ctx cenv cx ==>
  immutable_section_layout_mods mods cenv
Proof
  simp[contract_inv_def]
QED
