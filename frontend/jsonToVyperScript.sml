Theory jsonToVyper
Ancestors
  integer alist jsonAST vyperAST jsonToVyperType jsonToVyperTopLevel
Libs
  intLib

Definition collect_consts_and_immutables_def:
  collect_consts_and_immutables [] = [] ∧
  collect_consts_and_immutables (t :: rest) =
    (case t of
       JTL_VariableDecl name _ _ _ T _ _ => name :: collect_consts_and_immutables rest
     | JTL_VariableDecl name _ _ _ _ _ (SOME _) => name :: collect_consts_and_immutables rest
     | _ => collect_consts_and_immutables rest)
End


(* Make Name or BareGlobalName based on constants/immutables list *)
Definition build_import_map_def:
  build_import_map [] = [] ∧
  build_import_map (JImportInfo alias src_id _ :: rest) =
    (alias, Num (src_id + &builtin_source_id_offset)) :: build_import_map rest
End


(* Extract import infos from a toplevel (returns list since JTL_Import has list) *)
Definition get_import_infos_def:
  get_import_infos (JTL_Import infos) = infos ∧
  get_import_infos _ = []
End


(* Collect all import infos from toplevels *)
Definition collect_imports_def:
  collect_imports [] = [] ∧
  collect_imports (t::ts) = get_import_infos t ++ collect_imports ts
End


(* Extract source_ids that a module depends on from its body *)
Definition get_module_deps_def:
  get_module_deps body =
    MAP (λinfo. case info of JImportInfo _ src_id _ => src_id) (collect_imports body)
End


(* Check if imports are topologically sorted (dependencies come before dependents).
   seen: list of source_ids already processed
   Returns T if sorted, F otherwise. *)
Definition imports_topsorted_def:
  imports_topsorted seen [] = T ∧
  imports_topsorted seen (JImportedModule src_id _ body :: rest) =
    let deps = get_module_deps body in
    if EVERY (λd. MEM d seen) deps
    then imports_topsorted (src_id :: seen) rest
    else F
End

(* ===== Storage Layout Key Transformation ===== *)
(* Transform storage layout keys from (alias_opt, var_name) to (source_id_opt, var_name).
   Uses import_map to convert alias to source_id. *)

(* Transform a single storage layout key.
   (NONE, "counter") -> (NONE, "counter")  -- main module
   (SOME "lib1", "counter") -> (SOME 0, "counter")  -- if import_map has ("lib1", 0) *)
Definition transform_layout_key_def:
  transform_layout_key import_map (alias_opt, var_name) =
    case alias_opt of
    | NONE => (NONE, var_name)  (* Main module variable *)
    | SOME alias =>
        case ALOOKUP import_map alias of
        | NONE => (NONE, var_name)  (* Unknown alias, treat as main module *)
        | SOME src_id => (SOME src_id, var_name)
End


(* Transform all keys in a storage layout *)
Definition transform_storage_layout_def:
  transform_storage_layout import_map [] = [] ∧
  transform_storage_layout import_map ((key, slot) :: rest) =
    (transform_layout_key import_map key, slot) ::
    transform_storage_layout import_map rest
End


(* Check if a function decl is external *)
Definition is_external_function_def:
  is_external_function (JTL_FunctionDef _ decs _ _ _ _ _) = MEM "external" decs ∧
  is_external_function _ = F
End

(* Get function name from a function decl *)
Definition get_function_name_def:
  get_function_name (JTL_FunctionDef name _ _ _ _ _ _) = SOME name ∧
  get_function_name _ = NONE
End

(* Get name of a public variable or hashmap (generates an external getter) *)
Definition get_public_var_name_def:
  get_public_var_name (JTL_VariableDecl name _ _ T _ _ _) = SOME name ∧
  get_public_var_name (JTL_HashMapDecl name _ _ T _) = SOME name ∧
  get_public_var_name _ = NONE
End

(* Get all externally-callable names from a module's toplevels:
   external functions + public variable/hashmap getters *)
Definition get_external_func_names_def:
  get_external_func_names [] = [] ∧
  get_external_func_names (t::ts) =
    if is_external_function t then
      case get_function_name t of
        SOME name => name :: get_external_func_names ts
      | NONE => get_external_func_names ts
    else
      case get_public_var_name t of
        SOME name => name :: get_external_func_names ts
      | NONE => get_external_func_names ts
End

(* Find module body by raw source_id in imports list *)
Definition find_module_body_def:
  find_module_body src_id [] = [] ∧
  find_module_body src_id (JImportedModule sid _ body :: rest) =
    if src_id = sid then body else find_module_body src_id rest
End

(* Find module body by offset source_id (num) in imports list *)
Definition find_module_body_nsid_def:
  find_module_body_nsid nsid [] = [] ∧
  find_module_body_nsid nsid (JImportedModule sid _ body :: rest) =
    if nsid = Num (sid + &builtin_source_id_offset) then body
    else find_module_body_nsid nsid rest
End

(* Get export annotation from a toplevel if it's an ExportsDecl *)
Definition get_export_annotation_def:
  get_export_annotation (JTL_ExportsDecl ann) = SOME ann ∧
  get_export_annotation _ = NONE
End

(* ===== Exports Extraction with Transitive Support =====

   When main has `exports: lib2.__interface__`, we need lib2's full exports,
   which includes lib2's external functions PLUS anything lib2 re-exports.

   Design: Build an exports_map by processing imports in topological order.
   When we see `lib.__interface__`, we look up lib's exports in the map.

   The imports list must be topologically sorted (leaf modules first, modules
   depending on them later). This is validated by imports_topsorted in
   translate_annotated_ast, which returns NONE if the ordering is invalid.
*)

(* Build a map from source_id to import_map for all imported modules *)
Definition build_all_import_maps_def:
  build_all_import_maps [] = [] ∧
  build_all_import_maps (JImportedModule src_id _ body :: rest) =
    let nsid = Num (src_id + &builtin_source_id_offset) in
    (nsid, build_import_map (collect_imports body)) ::
    build_all_import_maps rest
End

(* Resolve a module expression (possibly nested) to a source_id.
   e.g. lib1 -> SOME src_id_of_lib1
        lib2.lib1 -> SOME src_id_of_lib1 (via lib2's import_map)
   all_import_maps: source_id -> import_map for each module
   import_map: current module's alias -> source_id map *)
Definition resolve_module_expr_def:
  (resolve_module_expr all_import_maps import_map (JE_Name alias _ _ _) =
     ALOOKUP import_map alias) ∧
  (resolve_module_expr all_import_maps import_map (JE_Attribute inner alias _ _ _ _ _) =
     case resolve_module_expr all_import_maps import_map inner of
     | NONE => NONE
     | SOME parent_src_id =>
         case ALOOKUP all_import_maps parent_src_id of
         | NONE => NONE
         | SOME parent_import_map => ALOOKUP parent_import_map alias) ∧
  (resolve_module_expr _ _ _ = NONE)
Termination
  WF_REL_TAC `measure (λ(_,_,e). json_expr_size e)` >> simp[]
End

(* Get function names from an inline interface definition *)
Definition get_interface_func_names_def:
  get_interface_func_names [] = [] ∧
  get_interface_func_names (JInterfaceFunc name _ _ _ :: rest) =
    name :: get_interface_func_names rest
End

(* Collect inline interface definitions into a compact name -> function-name map. *)
Definition collect_inline_interfaces_def:
  collect_inline_interfaces [] = [] ∧
  collect_inline_interfaces (JTL_InterfaceDef iname funcs :: ts) =
    (iname, get_interface_func_names funcs) :: collect_inline_interfaces ts ∧
  collect_inline_interfaces (_ :: ts) = collect_inline_interfaces ts
End

Definition build_all_inline_interface_maps_def:
  build_all_inline_interface_maps [] = [] ∧
  build_all_inline_interface_maps (JImportedModule src_id _ body :: rest) =
    let nsid = Num (src_id + &builtin_source_id_offset) in
    (nsid, collect_inline_interfaces body) :: build_all_inline_interface_maps rest
End

Definition lookup_inline_interface_def:
  lookup_inline_interface all_inline_maps src_id name =
    case ALOOKUP all_inline_maps src_id of
    | SOME imap => ALOOKUP imap name
    | NONE => NONE
End

(* Look up interface function names for a named export.
   Checks two sources:
   1. Inline JTL_InterfaceDef in the module's toplevels
   2. Imported interface module (whose exported function names define the interface)
   Returns SOME (list of function names) if found, NONE otherwise. *)
Definition find_interface_functions_def:
  find_interface_functions exports_map all_import_maps src_id func_name =
    (* First check if func_name is an imported interface module *)
    case ALOOKUP all_import_maps src_id of
    | NONE => NONE
    | SOME module_import_map =>
        case ALOOKUP module_import_map func_name of
        | SOME iface_src_id =>
            (* func_name is an imported module; its exported function names
               are the interface's function declarations *)
            (case ALOOKUP exports_map iface_src_id of
             | SOME iface_exps => SOME (MAP FST iface_exps)
             | NONE => NONE)
        | NONE => NONE
End

(* Expand a single export expression using only compact indexes.
   exports_map: already-computed source_id -> exported (name, defining source_id)
   all_import_maps: source_id -> alias map
   all_inline_maps: source_id -> inline interface map
   import_map: alias map for the current module *)
Definition expand_single_export_def:
  expand_single_export exports_map all_import_maps all_inline_maps import_map
    (JE_Attribute base func_name _ _ _ _ _) =
    (case resolve_module_expr all_import_maps import_map base of
     | NONE => []
     | SOME src_id =>
         if func_name = "__interface__" then
           case ALOOKUP exports_map src_id of
           | SOME exps => exps
           | NONE => []
         else
           case ALOOKUP exports_map src_id of
           | SOME exps =>
               (case ALOOKUP exps func_name of
                | SOME final_src_id => [(func_name, final_src_id)]
                | NONE =>
                    case find_interface_functions exports_map all_import_maps src_id func_name of
                    | SOME iface_fns => MAP (λn. (n, src_id)) iface_fns
                    | NONE =>
                        case lookup_inline_interface all_inline_maps src_id func_name of
                        | SOME iface_fns => MAP (λn. (n, src_id)) iface_fns
                        | NONE => [(func_name, src_id)])
           | NONE => [(func_name, src_id)]) ∧
  expand_single_export _ _ _ _ _ = []
End

Definition expand_tuple_exports_def:
  expand_tuple_exports exports_map all_import_maps all_inline_maps import_map [] = [] ∧
  expand_tuple_exports exports_map all_import_maps all_inline_maps import_map (e::es) =
    expand_single_export exports_map all_import_maps all_inline_maps import_map e ++
    expand_tuple_exports exports_map all_import_maps all_inline_maps import_map es
End

Definition expand_export_annotation_def:
  expand_export_annotation exports_map all_import_maps all_inline_maps import_map (JE_Tuple exprs) =
    expand_tuple_exports exports_map all_import_maps all_inline_maps import_map exprs ∧
  expand_export_annotation exports_map all_import_maps all_inline_maps import_map (JE_Attribute base attr tc btn btc sid ty) =
    expand_single_export exports_map all_import_maps all_inline_maps import_map (JE_Attribute base attr tc btn btc sid ty) ∧
  expand_export_annotation _ _ _ _ _ = []
End

Definition collect_export_annotations_def:
  collect_export_annotations [] = [] ∧
  collect_export_annotations (JTL_ExportsDecl ann :: ts) = ann :: collect_export_annotations ts ∧
  collect_export_annotations (_ :: ts) = collect_export_annotations ts
End

Definition expand_export_annotations_def:
  expand_export_annotations exports_map all_import_maps all_inline_maps import_map [] = [] ∧
  expand_export_annotations exports_map all_import_maps all_inline_maps import_map (ann::anns) =
    expand_export_annotation exports_map all_import_maps all_inline_maps import_map ann ++
    expand_export_annotations exports_map all_import_maps all_inline_maps import_map anns
End

Definition module_compact_index_def:
  module_compact_index nsid body =
    (nsid,
     build_import_map (collect_imports body),
     get_external_func_names body,
     collect_inline_interfaces body,
     collect_export_annotations body)
End

Definition build_import_compact_indexes_def:
  build_import_compact_indexes [] = [] ∧
  build_import_compact_indexes (JImportedModule src_id _ body :: rest) =
    module_compact_index (Num (src_id + &builtin_source_id_offset)) body ::
    build_import_compact_indexes rest
End

Definition compact_index_import_map_def:
  compact_index_import_map (src_id, import_map, ext_names, inline_map, export_anns) = import_map
End

Definition compact_index_ext_names_def:
  compact_index_ext_names (src_id, import_map, ext_names, inline_map, export_anns) = ext_names
End

Definition compact_index_export_anns_def:
  compact_index_export_anns (src_id, import_map, ext_names, inline_map, export_anns) = export_anns
End

Definition build_import_maps_from_indexes_def:
  build_import_maps_from_indexes [] = [] ∧
  build_import_maps_from_indexes ((src_id, import_map, ext_names, inline_map, export_anns)::rest) =
    (src_id, import_map) :: build_import_maps_from_indexes rest
End

Definition build_inline_maps_from_indexes_def:
  build_inline_maps_from_indexes [] = [] ∧
  build_inline_maps_from_indexes ((src_id, import_map, ext_names, inline_map, export_anns)::rest) =
    (src_id, inline_map) :: build_inline_maps_from_indexes rest
End

Definition compute_index_exports_def:
  compute_index_exports exports_map all_import_maps all_inline_maps
    (src_id, import_map, ext_names, inline_map, export_anns) =
    let ext_funcs = MAP (λn. (n, src_id)) ext_names in
    let reexports = expand_export_annotations exports_map all_import_maps all_inline_maps import_map export_anns in
    ext_funcs ++ reexports
End

Definition build_exports_map_from_indexes_def:
  build_exports_map_from_indexes all_import_maps all_inline_maps acc [] = acc ∧
  build_exports_map_from_indexes all_import_maps all_inline_maps acc (idx::rest) =
    let src_id = FST idx in
    let exps = compute_index_exports acc all_import_maps all_inline_maps idx in
    build_exports_map_from_indexes all_import_maps all_inline_maps ((src_id, exps) :: acc) rest
End

Definition extract_exports_with_indexes_def:
  extract_exports_with_indexes all_import_maps all_inline_maps exports_map main_index =
    expand_export_annotations exports_map all_import_maps all_inline_maps
      (compact_index_import_map main_index)
      (compact_index_export_anns main_index)
End

Definition extract_exports_with_import_maps_def:
  extract_exports_with_import_maps all_import_maps (JModule main_src_id toplevels) imports =
    let import_indexes = build_import_compact_indexes imports in
    let all_inline_maps = build_inline_maps_from_indexes import_indexes in
    let exports_map = build_exports_map_from_indexes all_import_maps all_inline_maps [] import_indexes in
    let main_index = module_compact_index 0 toplevels in
    extract_exports_with_indexes all_import_maps all_inline_maps exports_map main_index
End

Definition extract_exports_def:
  extract_exports main imports =
    extract_exports_with_import_maps (build_all_import_maps imports) main imports
End

(* ===== Module Translation ===== *)

Definition filter_some_def:
  (filter_some [] = []) /\
  (filter_some (NONE :: rest) = filter_some rest) /\
  (filter_some (SOME x :: rest) = x :: filter_some rest)
End


Definition translate_module_def:
  translate_module all_import_maps (JModule main_src_id toplevels) =
    let import_map = build_import_map (collect_imports toplevels) in
    let expr_ctx = (main_src_id, collect_consts_and_immutables toplevels) in
    let type_ctx = (main_src_id, NONE, import_map) in
    filter_some (MAP (translate_toplevel all_import_maps expr_ctx type_ctx) toplevels)
End

Definition translate_imported_module_def:
  translate_imported_module all_import_maps main_src_id (JImportedModule src_id path body) =
    let nsid = Num (src_id + &builtin_source_id_offset) in
    let import_map = build_import_map (collect_imports body) in
    let expr_ctx = (main_src_id, collect_consts_and_immutables body) in
    let type_ctx = (main_src_id, SOME nsid, import_map) in
    (SOME nsid, filter_some (MAP (translate_toplevel all_import_maps expr_ctx type_ctx) body))
End

Definition translate_imported_modules_def:
  translate_imported_modules all_import_maps main_src_id [] = [] ∧
  translate_imported_modules all_import_maps main_src_id (imp::imports) =
    translate_imported_module all_import_maps main_src_id imp ::
    translate_imported_modules all_import_maps main_src_id imports
End

(* Extract toplevels from a JModule (needed to get import infos) *)
Definition main_toplevels_def:
  main_toplevels (JModule _ toplevels) = toplevels
End


(* ===== Annotate Storage Slots ===== *)

(* Look up a variable's slot from the storage layout.
   Keys are (module_alias_opt, var_name). For main module, alias = NONE. *)
Definition lookup_slot_def:
  lookup_slot (layout : json_storage_layout)
              (alias : string option) (name : string) =
    case ALOOKUP layout.storage (alias, name) of
      SOME info => SOME info.slot
    | NONE =>
        case ALOOKUP layout.transient (alias, name) of
          SOME info => SOME info.slot
        | NONE => NONE
End

(* Annotate a toplevel list with storage/transient slots from the layout.
   Only VariableDecl (Storage/Transient) and HashMapDecl get slots.
   Invariant: SOME slot <=> variable is Storage or Transient. *)
Definition annotate_slots_def:
  annotate_slots layout alias ([] : toplevel list) = ([] : toplevel list) ∧
  annotate_slots layout alias (VariableDecl vis mut name ty _ :: rest) =
    VariableDecl vis mut name ty (lookup_slot layout alias name) ::
    annotate_slots layout alias rest ∧
  annotate_slots layout alias (HashMapDecl vis is_trans name kt vt _ :: rest) =
    HashMapDecl vis is_trans name kt vt (lookup_slot layout alias name) ::
    annotate_slots layout alias rest ∧
  annotate_slots layout alias (top :: rest) =
    top :: annotate_slots layout alias rest
End

(* Translate annotated AST, returning:
   - sources: (source_id, toplevels) alist
   - exports: func_name -> source_id
   - import_map: alias -> source_id (for storage layout key transformation)
   Returns NONE if imports are not topologically sorted. *)
Definition translate_annotated_ast_def:
  translate_annotated_ast (JAnnotatedAST (JModule main_src_id toplevels) imports) =
    if ¬imports_topsorted [] imports then NONE else
    let main = JModule main_src_id toplevels in
    let import_indexes = build_import_compact_indexes imports in
    let all_import_maps = build_import_maps_from_indexes import_indexes in
    let all_inline_maps = build_inline_maps_from_indexes import_indexes in
    let exports_map = build_exports_map_from_indexes all_import_maps all_inline_maps [] import_indexes in
    let main_index = module_compact_index 0 toplevels in
    let import_map = compact_index_import_map main_index in
    let sources = (NONE, translate_module all_import_maps main) :: translate_imported_modules all_import_maps main_src_id imports in
    let exports = extract_exports_with_indexes all_import_maps all_inline_maps exports_map main_index in
    SOME (sources, exports, import_map)
End

(* Annotate all sources with storage slots from json_storage_layout.
   Main module (NONE key) uses alias = NONE.
   Imported modules use their alias from import_map (reversed). *)
Definition annotate_sources_slots_def:
  annotate_sources_slots layout [] = [] ∧
  annotate_sources_slots layout ((src_id, tops) :: rest) =
    (* For main module src_id = NONE, alias = NONE.
       For imported modules, alias matching is by variable name
       (the layout keys use the original alias, not source_id). *)
    (src_id, annotate_slots layout NONE tops) ::
    annotate_sources_slots layout rest
End
