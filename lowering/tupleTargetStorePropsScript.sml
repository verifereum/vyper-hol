(* Static interfaces for sequential tuple-target stores. *)
Theory tupleTargetStoreProps
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  list rich_list finite_map
  stmtSimAssignStorage stmtSimAssignAttrStorage tupleLocalStoreRun
  stmtSimAssignTuple   vyperExprNoControl
  vyperTypeSystem vyperInterpreter vyperState vyperValue vyperTyping vyperLookup
  stmtLowering exprLowering emitHelper compileEnv

Theorem tuple_targets_typing:
  !env ret_ty gs e env'.
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' ==>
    ?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
          assignable_type env.type_defs (TupleT tys) /\
          LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\ env' = env
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem tuple_target_base_type:
  !env bt ty.
    well_typed_atarget env (BaseTarget bt) ty <=>
    type_place_target env bt = SOME (Type ty)
Proof
  cheat
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
  cheat
QED

Theorem tuple_target_storage_write_safe:
  !cx tr slot ty tv v es.
    ~cx.txn.is_static /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v ==>
    ?es'. write_place cx (StoragePlace tr slot tv) v es = (INL (), es') /\
          es'.scopes = es.scopes
Proof
  cheat
QED

Theorem tuple_target_local_write_safe:
  !cx id v es pre sc entry rest.
    find_containing_scope id es.scopes = SOME (pre, sc, entry, rest) /\
    entry.assignable ==>
    write_place cx (MemoryPlace id []) v es =
      (INL (), es with scopes :=
        pre ++ (sc |+ (id, entry with <|value := v; popped := []|>)) :: rest)
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem tuple_target_local_preserves_layout:
  !id es pre sc entry rest v n.
    find_containing_scope id es.scopes = SOME (pre, sc, entry, rest) ==>
    OPTION_MAP (\e. (e.type, e.assignable))
      (lookup_scopes n
        (pre ++ (sc |+ (id, entry with <|value := v; popped := []|>)) :: rest)) =
    OPTION_MAP (\e. (e.type, e.assignable)) (lookup_scopes n es.scopes)
Proof
  cheat
QED

Theorem tuple_target_write_safe:
  !cx bt v es.
    ~cx.txn.is_static /\
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
  cheat
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
  cheat
QED

Theorem tuple_source_target_safe:
  !cx es g tv v.
    ~cx.txn.is_static /\
    tuple_source_target cx es.scopes g tv /\ value_has_type tv v ==>
    ?es'. assign_tuple_targets cx g v es = (INL (),es') /\
      !n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
          OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)
Proof
  cheat
QED

Theorem assign_tuple_target_list_safe:
  !gs cx es tvs vs.
    ~cx.txn.is_static /\
    LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?es'. assign_tuple_target_list cx gs vs es = (INL (),es') /\
      !n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
          OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)
Proof
  cheat
QED

Theorem assign_tuple_targets_safe:
  !cx es gs tvs vs.
    ~cx.txn.is_static /\
    LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?es'. assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) es =
      (INL (),es')
Proof
  cheat
QED

Theorem eval_assign_tuple_targets_error:
  !cx gs e es ex es' lctx.
    ~cx.txn.is_static ==>
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
  cheat
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
  cheat
QED

Theorem tuple_compiler_target_toplevel:
  !cenv nsid ty.
    tuple_compiler_target cenv (BaseTarget (TopLevelNameTarget nsid)) ty <=>
    ?tr slot. FLOOKUP cenv.ce_module_vars nsid =
        SOME (if tr then TransientLoc slot else StorageLoc slot) /\
      cenv.ce_hashmap_info nsid = NONE /\
      cenv.ce_module_var_type nsid = SOME ty /\ is_word_type ty
Proof
  cheat
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
  cheat
QED

Theorem tuple_compiler_target_base:
  !cenv g ty. tuple_compiler_target cenv g ty ==> ?bt. g = BaseTarget bt
Proof
  cheat
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
  cheat
QED

Theorem tuple_target_aligned_source:
  !cenv cx scopes g ty tv v.
    tuple_target_aligned cenv cx g ty tv /\ tuple_target_layout scopes g ty tv v ==>
    tuple_source_target cx scopes g tv
Proof
  cheat
QED

Theorem tuple_target_aligned_nonlocal_word:
  !cenv cx g ty tv.
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) ==> is_word_type ty
Proof
  cheat
QED

Theorem tuple_target_layout_transport:
  !scopes scopes' g ty tv v.
    (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
         OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) ==>
    (tuple_target_layout scopes' g ty tv v <=> tuple_target_layout scopes g ty tv v)
Proof
  cheat
QED

Theorem tuple_target_aligned_local:
  !cenv cx id ty tv.
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv <=>
    ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv
Proof
  cheat
QED

Theorem tuple_target_layout_local:
  !scopes id ty tv v.
    tuple_target_layout scopes (BaseTarget (NameTarget id)) ty tv v <=>
    ?entry. lookup_scopes id scopes = SOME entry /\ entry.assignable /\
      entry.type = tv /\ (is_word_type ty ==> store_lays_out tv entry.type v)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem tuple_target_storage_assignment:
  !cx bt tr slot tv v es es'.
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),es) /\
    assign_tuple_targets cx (BaseTarget bt) v es = (INL (),es') ==>
    write_storage_slot cx tr slot tv v es = (INL (),es')
Proof
  cheat
QED

Theorem tuple_target_local_domain_frame:
  !id scopes pre sc entry rest v.
    find_containing_scope id scopes = SOME (pre,sc,entry,rest) ==>
    MAP FDOM scopes =
      MAP FDOM (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
Proof
  cheat
QED

Theorem tuple_target_storage_scope_frame:
  !cx tr slot tv v es es'.
    write_storage_slot cx tr slot tv v es = (INL (),es') ==>
    es'.scopes = es.scopes
Proof
  cheat
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
  cheat
QED

Theorem tuple_target_list_cons_success:
  !cenv cx g gs ty tv v vs es es'.
    ~cx.txn.is_static /\ tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\ value_has_type tv v /\
    assign_tuple_target_list cx (g::gs) (v::vs) es = (INL (),es') ==>
    ?es1. assign_tuple_targets cx g v es = (INL (),es1) /\
          assign_tuple_target_list cx gs vs es1 = (INL (),es')
Proof
  cheat
QED
