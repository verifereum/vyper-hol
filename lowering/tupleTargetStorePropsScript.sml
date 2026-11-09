(* Static interfaces for sequential tuple-target stores. *)
Theory tupleTargetStoreProps
Ancestors
  list rich_list finite_map
  stmtSimAssignStorage stmtSimAssignAttrStorage tupleLocalStoreRun
  stmtSimAssignTuple stmtSim exprSim vyperExprNoControl
  vyperTypeSystem vyperInterpreter vyperState vyperValue vyperTyping vyperLookup
  stmtLowering exprLowering emitHelper compileEnv

Theorem tuple_targets_typing:
  !env ret_ty gs e env'.
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' ==>
    ?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
          assignable_type env.type_defs (TupleT tys) /\
          LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\ env' = env
Proof
  rpt strip_tac >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
      AllCaseEqs(), ETA_THM]
QED

(* Locals and module words reuse the existing zero-instruction pointer
   interface; struct fields emit exactly one ADD, in either storage space. *)
Theorem tuple_target_local_pointer:
  !cfn cenv id ptr sz ty st.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar ptr sz) /\
    cenv.ce_var_type id = SOME ty ==>
    compile_get_target_ptr cfn cenv (NameTarget id) st =
      ((ptr, SOME LocMemory, SOME (ValPT ty)), st)
Proof
  simp[compile_get_target_ptr_def, comp_return_def]
QED

Theorem tuple_target_field_pointer:
  !cenv nsid tr slot sid fld fty fsz st ptr st'.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    emit_op ADD [Lit slot; Lit (n2w (struct_field_offset_slots
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
      st = (ptr, st') ==>
    compile_get_target_ptr compile_expr cenv
      (AttributeTarget (TopLevelNameTarget nsid) fld) st =
      ((ptr, SOME (if tr then LocTransient else LocStorage),
        SOME (ValPT fty)), st')
Proof
  rpt strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [Once compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM]
QED

Theorem tuple_target_base_type:
  !env bt ty.
    well_typed_atarget env (BaseTarget bt) ty <=>
    type_place_target env bt = SOME (Type ty)
Proof
  simp[well_typed_atarget_def, well_typed_target_def]
QED

(* Expose the source's sequential order without imposing distinct targets. *)
Theorem assign_tuple_target_list_cons:
  !cx g gs v vs es res es'.
    assign_tuple_target_list cx (g :: gs) (v :: vs) es = (res, es') <=>
    ?r es1. assign_tuple_targets cx g v es = (r, es1) /\
      case r of
        INL u => assign_tuple_target_list cx gs vs es1 = (res, es')
      | INR ex => res = INR ex /\ es' = es1
Proof
  rpt gen_tac >> simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  Cases_on `assign_tuple_targets cx g v es` >>
  rename1 `assign_tuple_targets _ _ _ _ = (head_res, head_es)` >>
  Cases_on `head_res` >> simp[EQ_SYM_EQ]
QED

Theorem tuple_target_storage_write_safe:
  !cx tr slot ty tv v es.
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v ==>
    ?es'. write_place cx (StoragePlace tr slot tv) v es = (INL (), es') /\
          es'.scopes = es.scopes
Proof
  rpt strip_tac >> drule_all encode_value_word_typed >> strip_tac >>
  Cases_on `tr` >>
  simp[write_place_def, write_storage_slot_def, get_storage_backend_def,
       set_storage_backend_def, get_transient_storage_def, get_accounts_def,
       update_transient_def, update_accounts_def, bind_def,
       lift_option_type_def, return_def]
QED

Theorem tuple_target_local_write_safe:
  !cx id v es pre sc entry rest.
    find_containing_scope id es.scopes = SOME (pre, sc, entry, rest) /\
    entry.assignable ==>
    write_place cx (MemoryPlace id []) v es =
      (INL (), es with scopes :=
        pre ++ (sc |+ (id, entry with <|value := v; popped := []|>)) :: rest)
Proof
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, return_def]
QED

Theorem tuple_target_toplevel_place:
  !cx src id ts tr typ id_str slot tv es.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tv ==>
    eval_target_place cx (TopLevelNameTarget (src, id)) es =
      (INL (StoragePlace tr (n2w slot) tv), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, get_place_def]
QED

Theorem tuple_target_field_place:
  !cx src id ts tr typ id_str slot fs fld off tv es.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, tv) ==>
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (INL (StoragePlace tr (n2w slot + n2w off) tv), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, get_place_def, extend_place_def, extend_storage_place_def]
QED

Theorem tuple_target_local_preserves_layout:
  !id es pre sc entry rest v n.
    find_containing_scope id es.scopes = SOME (pre, sc, entry, rest) ==>
    OPTION_MAP (\e. (e.type, e.assignable))
      (lookup_scopes n
        (pre ++ (sc |+ (id, entry with <|value := v; popped := []|>)) :: rest)) =
    OPTION_MAP (\e. (e.type, e.assignable)) (lookup_scopes n es.scopes)
Proof
  rpt strip_tac >> Cases_on `n = id`
  >- (gvs[] >> drule find_containing_scope_lookup >> strip_tac >>
      drule find_containing_scope_pre_none >> strip_tac >>
      simp[lookup_scopes_update]) >>
  drule find_containing_scope_structure >> strip_tac >>
  simp[lookup_scopes_update_other]
QED

Theorem tuple_target_write_safe:
  !cx bt v es.
    ((?id pre sc entry rest.
       eval_target_place cx bt es = (INL (MemoryPlace id []), es) /\
       find_containing_scope id es.scopes = SOME (pre, sc, entry, rest) /\
       entry.assignable) \/
     (?tr slot ty tv.
       eval_target_place cx bt es = (INL (StoragePlace tr slot tv), es) /\
       is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
       value_has_type tv v)) ==>
    ?es'. assign_tuple_targets cx (BaseTarget bt) v es = (INL (), es') /\
      !n. OPTION_MAP (\e. (e.type, e.assignable)) (lookup_scopes n es'.scopes) =
          OPTION_MAP (\e. (e.type, e.assignable)) (lookup_scopes n es.scopes)
Proof
  rpt gen_tac >> strip_tac
  >- (drule_all tuple_target_local_write_safe >> strip_tac >>
      simp[Once evaluate_def, bind_def] >>
      metis_tac[tuple_target_local_preserves_layout]) >>
  drule_all tuple_target_storage_write_safe >> strip_tac >>
  simp[Once evaluate_def, bind_def] >> metis_tac[]
QED

(* Pure declaration information; deliberately no execution or compiler facts. *)
Definition tuple_source_target_def:
  tuple_source_target cx scopes g tv <=>
    (?id entry. g = BaseTarget (NameTarget id) /\
      lookup_scopes id scopes = SOME entry /\ entry.assignable) \/
    (?src id ts tr typ id_str slot.
      g = BaseTarget (TopLevelNameTarget (src,id)) /\
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
      is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv) \/
    (?src id ts tr typ id_str slot fs fld off fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld) /\
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
      evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off,tv) /\
      is_word_type fty /\ evaluate_type (get_tenv cx) fty = SOME tv)
End

Theorem tuple_source_target_layout:
  !cx scopes scopes' g tv.
    (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
         OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) ==>
    (tuple_source_target cx scopes' g tv <=> tuple_source_target cx scopes g tv)
Proof
  rpt strip_tac >> simp[tuple_source_target_def] >>
  `!id. (?entry. lookup_scopes id scopes' = SOME entry /\ entry.assignable) <=>
         (?entry. lookup_scopes id scopes = SOME entry /\ entry.assignable)` by
    (gen_tac >> first_x_assum (qspec_then `id` mp_tac) >>
     Cases_on `lookup_scopes id scopes'` >>
     Cases_on `lookup_scopes id scopes` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem tuple_source_target_safe:
  !cx es g tv v.
    tuple_source_target cx es.scopes g tv /\ value_has_type tv v ==>
    ?es'. assign_tuple_targets cx g v es = (INL (),es') /\
      !n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
          OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)
Proof
  rpt gen_tac >> simp[tuple_source_target_def] >> strip_tac >> gvs[]
  >- (drule lookup_scopes_find_containing_scope >> strip_tac >>
      irule tuple_target_write_safe >> disj1_tac >>
      first_assum (irule_at Any) >> simp[] >>
      simp[Once evaluate_def, bind_def] >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
           return_def, get_place_def, get_scopes_def])
  >- (drule_all tuple_target_toplevel_place >> strip_tac >>
      irule tuple_target_write_safe >> disj2_tac >> metis_tac[]) >>
  drule_all tuple_target_field_place >> strip_tac >>
  irule tuple_target_write_safe >> disj2_tac >> metis_tac[]
QED

Theorem assign_tuple_target_list_safe:
  !gs cx es tvs vs.
    LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?es'. assign_tuple_target_list cx gs vs es = (INL (),es') /\
      !n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
          OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)
Proof
  Induct
  >- (simp[Once evaluate_def, return_def] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `tvs` >> simp[] >> Cases_on `vs` >> simp[] >>
  strip_tac >> rename1 `LIST_REL value_has_type tail_tvs tail_vs` >>
  drule_all tuple_source_target_safe >> strip_tac >>
  `LIST_REL (tuple_source_target cx es'.scopes) gs tail_tvs` by
    (irule LIST_REL_mono >> first_assum (irule_at Any) >>
     metis_tac[tuple_source_target_layout]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[assign_tuple_target_list_cons] >>
  first_assum (irule_at Any) >> simp[] >> metis_tac[]
QED

Theorem assign_tuple_targets_safe:
  !cx es gs tvs vs.
    LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?es'. assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) es =
      (INL (),es')
Proof
  rpt strip_tac >> drule_all assign_tuple_target_list_safe >>
  simp[Once evaluate_def] >> metis_tac[]
QED

Theorem eval_assign_tuple_targets_error:
  !cx gs e es ex es' lctx.
    eval_stmt cx (Assign (TupleTarget gs) e) es = (INR ex,es') /\
    stmt_res_ok lctx (INR ex) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,es1) ==>
       ?vs tvs. v = ArrayV (TupleV vs) /\
         LIST_REL (tuple_source_target cx es1.scopes) gs tvs /\
         LIST_REL value_has_type tvs vs) ==>
    (do result <- eval_expr cx e; read_result cx result od) es = (INR ex,es') /\
    expr_res_ok (INR ex : value + exception)
Proof
  rpt gen_tac >> strip_tac >> drule eval_assign_tuple >> strip_tac >>
  Cases_on `r` >> gvs[]
  >- (drule_all assign_tuple_targets_safe >> gvs[]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

(* Exact destination types and compiler mappings, independent of source state. *)
Definition tuple_compiler_target_def:
  tuple_compiler_target cenv g ty <=>
    (?id p sz. g = BaseTarget (NameTarget id) /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty) \/
    (?nsid tr slot. g = BaseTarget (TopLevelNameTarget nsid) /\
      FLOOKUP cenv.ce_module_vars nsid =
        SOME (if tr then TransientLoc slot else StorageLoc slot) /\
      cenv.ce_hashmap_info nsid = NONE /\
      cenv.ce_module_var_type nsid = SOME ty /\ is_word_type ty) \/
    (?nsid tr slot sid fld fsz.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      FLOOKUP cenv.ce_module_vars nsid =
        SOME (if tr then TransientLoc slot else StorageLoc slot) /\
      cenv.ce_hashmap_info nsid = NONE /\
      cenv.ce_module_var_type nsid = SOME (StructT sid) /\
      ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        fld = SOME (ty,fsz) /\ is_word_type ty)
End

Theorem tuple_compiler_target_local:
  !cenv id ty.
    tuple_compiler_target cenv (BaseTarget (NameTarget id)) ty <=>
    ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty
Proof
  simp[tuple_compiler_target_def]
QED

Theorem tuple_compiler_target_toplevel:
  !cenv nsid ty.
    tuple_compiler_target cenv (BaseTarget (TopLevelNameTarget nsid)) ty <=>
    ?tr slot. FLOOKUP cenv.ce_module_vars nsid =
        SOME (if tr then TransientLoc slot else StorageLoc slot) /\
      cenv.ce_hashmap_info nsid = NONE /\
      cenv.ce_module_var_type nsid = SOME ty /\ is_word_type ty
Proof
  simp[tuple_compiler_target_def]
QED

Theorem tuple_compiler_target_field:
  !cenv nsid fld ty.
    tuple_compiler_target cenv
      (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty <=>
    ?tr slot sid fsz. FLOOKUP cenv.ce_module_vars nsid =
        SOME (if tr then TransientLoc slot else StorageLoc slot) /\
      cenv.ce_hashmap_info nsid = NONE /\
      cenv.ce_module_var_type nsid = SOME (StructT sid) /\
      ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        fld = SOME (ty,fsz) /\ is_word_type ty
Proof
  simp[tuple_compiler_target_def]
QED

Theorem tuple_compiler_target_base:
  !cenv g ty. tuple_compiler_target cenv g ty ==> ?bt. g = BaseTarget bt
Proof
  simp[tuple_compiler_target_def] >> metis_tac[]
QED

(* Shared source/compiler locations; no execution assumptions. *)
Definition tuple_target_aligned_def:
  tuple_target_aligned cenv cx g ty tv <=>
    (?id p sz. g = BaseTarget (NameTarget id) /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv) \/
    (?src id ts tr id_str k. g = BaseTarget (TopLevelNameTarget (src,id)) /\
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME k /\
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w k) else StorageLoc (n2w k)) /\
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME ty /\ is_word_type ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      (!u mem. storage_dead cx tr (update_storage (n2w k) u mem) =
               storage_dead cx tr mem)) \/
    (?src id ts tr id_str k sid fs fld off fsz.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld) /\
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME k /\
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w k) else StorageLoc (n2w k)) /\
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
      ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        fld = SOME (ty,fsz) /\
      struct_field_slot fs fld = SOME (off,tv) /\
      off = struct_field_offset_slots
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld /\
      is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      (!u mem. storage_dead cx tr (update_storage (n2w k + n2w off) u mem) =
               storage_dead cx tr mem))
End

Definition tuple_target_layout_def:
  tuple_target_layout scopes g ty tv v <=>
    !id. g = BaseTarget (NameTarget id) ==>
      ?entry. lookup_scopes id scopes = SOME entry /\ entry.assignable /\
        entry.type = tv /\ (is_word_type ty ==> store_lays_out tv entry.type v)
End

Theorem tuple_target_aligned_compiler:
  !cenv cx g ty tv.
    tuple_target_aligned cenv cx g ty tv ==> tuple_compiler_target cenv g ty
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def, tuple_compiler_target_def] >>
  strip_tac >> metis_tac[]
QED

Theorem tuple_target_aligned_source:
  !cenv cx scopes g ty tv v.
    tuple_target_aligned cenv cx g ty tv /\ tuple_target_layout scopes g ty tv v ==>
    tuple_source_target cx scopes g tv
Proof
  rpt gen_tac >>
  simp[tuple_target_aligned_def, tuple_target_layout_def, tuple_source_target_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem tuple_target_aligned_nonlocal_word:
  !cenv cx g ty tv.
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) ==> is_word_type ty
Proof
  simp[tuple_target_aligned_def] >> metis_tac[]
QED

Theorem tuple_target_layout_transport:
  !scopes scopes' g ty tv v.
    (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
         OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) ==>
    (tuple_target_layout scopes' g ty tv v <=> tuple_target_layout scopes g ty tv v)
Proof
  rpt strip_tac >> simp[tuple_target_layout_def] >>
  `!id. (?entry. lookup_scopes id scopes' = SOME entry /\ entry.assignable /\
           entry.type = tv /\ (is_word_type ty ==> store_lays_out tv entry.type v)) <=>
         (?entry. lookup_scopes id scopes = SOME entry /\ entry.assignable /\
           entry.type = tv /\ (is_word_type ty ==> store_lays_out tv entry.type v))` by
    (gen_tac >> first_x_assum (qspec_then `id` mp_tac) >>
     Cases_on `lookup_scopes id scopes'` >> Cases_on `lookup_scopes id scopes` >>
     simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem tuple_target_aligned_local:
  !cenv cx id ty tv.
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv <=>
    ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv
Proof
  simp[tuple_target_aligned_def]
QED

Theorem tuple_target_layout_local:
  !scopes id ty tv v.
    tuple_target_layout scopes (BaseTarget (NameTarget id)) ty tv v <=>
    ?entry. lookup_scopes id scopes = SOME entry /\ entry.assignable /\
      entry.type = tv /\ (is_word_type ty ==> store_lays_out tv entry.type v)
Proof
  simp[tuple_target_layout_def]
QED

Theorem tuple_target_aligned_toplevel:
  !cenv cx src id ty tv.
    tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget (src,id))) ty tv <=>
    ?ts tr id_str k.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME k /\
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w k) else StorageLoc (n2w k)) /\
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME ty /\ is_word_type ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      (!u mem. storage_dead cx tr (update_storage (n2w k) u mem) =
               storage_dead cx tr mem)
Proof
  simp[tuple_target_aligned_def]
QED

Theorem tuple_target_aligned_field:
  !cenv cx src id fld ty tv.
    tuple_target_aligned cenv cx
      (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) ty tv <=>
    ?ts tr id_str k sid fs off fsz.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME k /\
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      FLOOKUP cenv.ce_module_vars (src,id) =
        SOME (if tr then TransientLoc (n2w k) else StorageLoc (n2w k)) /\
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
      ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        fld = SOME (ty,fsz) /\
      struct_field_slot fs fld = SOME (off,tv) /\
      off = struct_field_offset_slots
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld /\
      is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      (!u mem. storage_dead cx tr (update_storage (n2w k + n2w off) u mem) =
               storage_dead cx tr mem)
Proof
  simp[tuple_target_aligned_def]
QED

Theorem tuple_target_local_assignment:
  !cx id v es es' entry.
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') ==>
    ?pre sc rest.
      find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
      es' = es with scopes :=
        pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest
Proof
  rpt strip_tac >> drule lookup_scopes_find_containing_scope >> strip_tac >>
  drule_all tuple_target_local_write_safe >> strip_tac >>
  gvs[Once evaluate_def, bind_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, get_place_def, get_scopes_def] >>
  gvs[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
      return_def, get_place_def, ignore_bind_def, type_check_def, assert_def] >>
  metis_tac[]
QED

Theorem tuple_target_storage_assignment:
  !cx bt tr slot tv v es es'.
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),es) /\
    assign_tuple_targets cx (BaseTarget bt) v es = (INL (),es') ==>
    write_storage_slot cx tr slot tv v es = (INL (),es')
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, write_place_def]
QED

Theorem tuple_target_local_domain_frame:
  !id scopes pre sc entry rest v.
    find_containing_scope id scopes = SOME (pre,sc,entry,rest) ==>
    MAP FDOM scopes =
      MAP FDOM (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
Proof
  rpt strip_tac >> drule find_containing_scope_structure >>
  simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem tuple_target_storage_scope_frame:
  !cx tr slot tv v es es'.
    write_storage_slot cx tr slot tv v es = (INL (),es') ==>
    es'.scopes = es.scopes
Proof
  rpt gen_tac >> Cases_on `encode_value tv v` >>
  Cases_on `tr` >>
  simp[raise_def, write_storage_slot_def, get_storage_backend_def, set_storage_backend_def,
       get_transient_storage_def, get_accounts_def, update_transient_def,
       update_accounts_def, bind_def, lift_option_type_def, return_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem tuple_target_assignment_scope_frame:
  !cenv cx g ty tv v es es'.
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\
    assign_tuple_targets cx g v es = (INL (),es') ==>
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
         OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes))
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (gvs[tuple_target_layout_local] >>
      drule_all tuple_target_local_assignment >> strip_tac >> gvs[] >>
      conj_tac
      >- (drule tuple_target_local_domain_frame >> simp[]) >>
      irule tuple_target_local_preserves_layout >> simp[])
  >- (drule_all tuple_target_toplevel_place >>
      disch_then (qspec_then `es` assume_tac) >>
      drule_all tuple_target_storage_assignment >> strip_tac >>
      drule tuple_target_storage_scope_frame >> simp[]) >>
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >> strip_tac >>
  drule tuple_target_storage_scope_frame >> simp[]
QED

Theorem tuple_target_list_cons_success:
  !cenv cx g gs ty tv v vs es es'.
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\ value_has_type tv v /\
    assign_tuple_target_list cx (g::gs) (v::vs) es = (INL (),es') ==>
    ?es1. assign_tuple_targets cx g v es = (INL (),es1) /\
          assign_tuple_target_list cx gs vs es1 = (INL (),es')
Proof
  rpt strip_tac >> drule_all tuple_target_aligned_source >> strip_tac >>
  drule_all tuple_source_target_safe >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ (_::_) _ _ = _` mp_tac >>
  simp[assign_tuple_target_list_cons] >> metis_tac[]
QED
