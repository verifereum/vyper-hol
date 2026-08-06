Theory jsonToVyperType
Ancestors
  integer alist jsonAST vyperAST
Libs
  intLib

Definition builtin_source_id_offset_def:
  builtin_source_id_offset = 2n
End

(* Convert a JSON source_id (int) to a vyperAST source_id (num option).
   main_src_id maps to NONE (main module), others are offset to be non-negative. *)
Definition source_id_to_module_id_def:
  source_id_to_module_id (src_id:int) =
    Num (src_id + &builtin_source_id_offset)
End

Definition source_id_to_nsid_def:
  source_id_to_nsid (main_src_id:int) (src_id:int) =
    if src_id = main_src_id then NONE
    else SOME (source_id_to_module_id src_id)
End

(* ===== Type Translation ===== *)

(* Nominal kinds come from declarations, not compiler-inferred type metadata. *)
Datatype:
  nominal_kind = StructKind | FlagKind | InterfaceKind
End

Definition nominal_type_def:
  nominal_type StructKind nsid = StructT nsid ∧
  nominal_type FlagKind nsid = FlagT nsid ∧
  nominal_type InterfaceKind nsid = BaseT AddressT
End

Definition tctx_main_src_id_def:
  tctx_main_src_id tctx = FST tctx
End

Definition tctx_current_nsid_def:
  tctx_current_nsid tctx = FST (SND tctx)
End

Definition tctx_import_map_def:
  tctx_import_map tctx = SND (SND tctx)
End

Definition translate_type_def:
  (translate_type ctx (JT_Integer bits T) = BaseT (IntT bits)) ∧
  (translate_type ctx (JT_Integer bits F) = BaseT (UintT bits)) ∧
  (translate_type ctx (JT_BytesM m) = BaseT (BytesT (Fixed m))) ∧
  (translate_type ctx (JT_String n) = BaseT (StringT n)) ∧
  (translate_type ctx (JT_Bytes n) = BaseT (BytesT (Dynamic n))) ∧
  (translate_type ctx (JT_StaticArray vt len) =
    ArrayT (translate_type ctx vt) (Fixed len)) ∧
  (translate_type ctx (JT_DynArray vt len) =
    ArrayT (translate_type ctx vt) (Dynamic len)) ∧
  (translate_type ctx (JT_Tuple tys) = TupleT (MAP (translate_type ctx) tys)) ∧
  (translate_type ctx (JT_Struct NONE name) =
    StructT (tctx_current_nsid ctx, name)) ∧
  (translate_type ctx (JT_Struct (SOME src_id) name) =
    StructT (source_id_to_nsid (tctx_main_src_id ctx) src_id, name)) ∧
  (translate_type ctx (JT_Flag NONE name) =
    FlagT (tctx_current_nsid ctx, name)) ∧
  (translate_type ctx (JT_Flag (SOME src_id) name) =
    FlagT (source_id_to_nsid (tctx_main_src_id ctx) src_id, name)) ∧
  (translate_type ctx (JT_Interface _ _) = BaseT AddressT) ∧
  (translate_type ctx (JT_Named src_id_opt name) =
     if name = "bool" then BaseT BoolT
     else if name = "address" ∨ name = "self" then BaseT AddressT
     else if name = "decimal" then BaseT DecimalT
     else if name = "(void)" then NoneT
     else StructT
       ((case src_id_opt of
           NONE => tctx_current_nsid ctx
         | SOME src_id => source_id_to_nsid (tctx_main_src_id ctx) src_id),
        name)) ∧
  (translate_type ctx (JT_HashMap _ _) = NoneT) ∧
  (translate_type ctx JT_None = NoneT)
Termination
  WF_REL_TAC `measure (λ(_,ty). json_type_size ty)` >> simp[]
End

Definition translate_annotation_def:
  (translate_annotation ctx (JTA_Integer bits T) = BaseT (IntT bits)) ∧
  (translate_annotation ctx (JTA_Integer bits F) = BaseT (UintT bits)) ∧
  (translate_annotation ctx (JTA_BytesM m) = BaseT (BytesT (Fixed m))) ∧
  (translate_annotation ctx (JTA_String n) = BaseT (StringT n)) ∧
  (translate_annotation ctx (JTA_Bytes n) = BaseT (BytesT (Dynamic n))) ∧
  (translate_annotation ctx (JTA_StaticArray ty len) =
    ArrayT (translate_annotation ctx ty) (Fixed len)) ∧
  (translate_annotation ctx (JTA_DynArray ty len) =
    ArrayT (translate_annotation ctx ty) (Dynamic len)) ∧
  (translate_annotation ctx (JTA_Tuple tys) =
    TupleT (MAP (translate_annotation ctx) tys)) ∧
  (translate_annotation ctx (JTA_Named name) =
    if name = "bool" then BaseT BoolT
    else if name = "address" ∨ name = "self" then BaseT AddressT
    else if name = "decimal" then BaseT DecimalT
    else if name = "(void)" then NoneT
    else StructT (tctx_current_nsid ctx, name)) ∧
  (translate_annotation ctx (JTA_Qualified _ name) = StructT (NONE, name)) ∧
  (translate_annotation ctx JTA_None = NoneT)
Termination
  WF_REL_TAC `measure (λ(_,ann). json_type_annotation_size ann)` >> simp[]
End

Definition translate_decl_type_def:
  translate_decl_type ctx inferred ann =
    case inferred of
      JT_None => translate_annotation ctx ann
    | _ => translate_type ctx inferred
End

(* Qualified syntactic annotations are resolved locally using the current
   module import map.  We only use them as namespace hints; the inferred
   type supplies the kind (flag/struct/named). *)
Definition resolve_qualified_type_path_def:
  (resolve_qualified_type_path all_import_maps ctx [] = NONE) ∧
  (resolve_qualified_type_path all_import_maps ctx [alias] =
    ALOOKUP (tctx_import_map ctx) alias) ∧
  (resolve_qualified_type_path all_import_maps ctx (alias::next::rest) =
    case ALOOKUP (tctx_import_map ctx) alias of
    | NONE => NONE
    | SOME parent_src_id =>
        case ALOOKUP all_import_maps parent_src_id of
        | NONE => NONE
        | SOME parent_import_map =>
            resolve_qualified_type_path all_import_maps
              (tctx_main_src_id ctx, SOME parent_src_id, parent_import_map)
              (next::rest))
Termination
  WF_REL_TAC `measure (λ(_,_,path). LENGTH path)` >> simp[]
End

(* Resolve an annotation name to its declaration identity. Unqualified names
   first denote local declarations, then directly imported declarations. *)
Definition resolve_annotation_name_def:
  resolve_annotation_name nominal_index ctx name =
    case ALOOKUP nominal_index (tctx_current_nsid ctx, name) of
    | SOME kind => SOME (kind, (tctx_current_nsid ctx, name))
    | NONE =>
        case ALOOKUP (tctx_import_map ctx) name of
        | NONE => NONE
        | SOME src_id =>
            case ALOOKUP nominal_index (SOME src_id, name) of
            | SOME kind => SOME (kind, (SOME src_id, name))
            | NONE => NONE
End

Definition resolve_qualified_annotation_def:
  resolve_qualified_annotation nominal_index all_import_maps ctx path name =
    case resolve_qualified_type_path all_import_maps ctx path of
    | NONE => NONE
    | SOME src_id =>
        case ALOOKUP nominal_index (SOME src_id, name) of
        | SOME kind => SOME (kind, (SOME src_id, name))
        | NONE => NONE
End

Definition annotation_resolved_def:
  (annotation_resolved nominal_index all_import_maps ctx (JTA_Named name) =
    if name = "bool" ∨ name = "address" ∨ name = "self" ∨
       name = "decimal" ∨ name = "(void)"
    then T
    else IS_SOME (resolve_annotation_name nominal_index ctx name)) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_StaticArray ty _) =
    annotation_resolved nominal_index all_import_maps ctx ty) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_DynArray ty _) =
    annotation_resolved nominal_index all_import_maps ctx ty) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_Tuple tys) =
    EVERY (annotation_resolved nominal_index all_import_maps ctx) tys) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_Qualified path name) =
    IS_SOME (resolve_qualified_annotation nominal_index all_import_maps ctx path name)) ∧
  (annotation_resolved nominal_index all_import_maps ctx _ = T)
Termination
  WF_REL_TAC `measure (λ(_,_,_,ann). json_type_annotation_size ann)` >> simp[]
End

(* Elaborate declaration annotations from syntax and the declaration index.
   This function is used only after annotation_resolved has succeeded. *)
Definition elaborate_annotation_def:
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Integer bits T) = BaseT (IntT bits)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Integer bits F) = BaseT (UintT bits)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_BytesM m) = BaseT (BytesT (Fixed m))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_String n) = BaseT (StringT n)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Bytes n) = BaseT (BytesT (Dynamic n))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_StaticArray ty len) =
    ArrayT (elaborate_annotation nominal_index all_import_maps ctx ty)
      (Fixed len)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_DynArray ty len) =
    ArrayT (elaborate_annotation nominal_index all_import_maps ctx ty)
      (Dynamic len)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Tuple tys) =
    TupleT (MAP (elaborate_annotation nominal_index all_import_maps ctx) tys)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Named name) =
    if name = "bool" then BaseT BoolT
    else if name = "address" ∨ name = "self" then BaseT AddressT
    else if name = "decimal" then BaseT DecimalT
    else if name = "(void)" then NoneT
    else case resolve_annotation_name nominal_index ctx name of
         | SOME (kind, nsid) => nominal_type kind nsid
         | NONE => NoneT) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Qualified path name) =
    case resolve_qualified_annotation nominal_index all_import_maps ctx path name of
    | SOME (kind, nsid) => nominal_type kind nsid
    | NONE => NoneT) ∧
  (elaborate_annotation nominal_index all_import_maps ctx JTA_None = NoneT)
Termination
  WF_REL_TAC `measure (λ(_,_,_,ann). json_type_annotation_size ann)` >> simp[]
End

Definition inferred_source_matches_def:
  inferred_source_matches ctx expected NONE = T ∧
  inferred_source_matches ctx expected (SOME src_id) =
    (expected = source_id_to_nsid (tctx_main_src_id ctx) src_id)
End

(* Check every compiler claim that is present. A missing nominal source is no
   claim; an explicit conflicting source or structural mismatch is rejected. *)
Definition inferred_type_consistent_def:
  (inferred_type_consistent ctx (BaseT (IntT bits))
      (JT_Integer bits' T) = (bits = bits')) ∧
  (inferred_type_consistent ctx (BaseT (UintT bits))
      (JT_Integer bits' F) = (bits = bits')) ∧
  (inferred_type_consistent ctx (BaseT (BytesT (Fixed n)))
      (JT_BytesM n') = (n = n')) ∧
  (inferred_type_consistent ctx (BaseT (StringT n))
      (JT_String n') = (n = n')) ∧
  (inferred_type_consistent ctx (BaseT (BytesT (Dynamic n)))
      (JT_Bytes n') = (n = n')) ∧
  (inferred_type_consistent ctx (ArrayT ty (Fixed n))
      (JT_StaticArray inferred n') =
    (n = n' ∧ inferred_type_consistent ctx ty inferred)) ∧
  (inferred_type_consistent ctx (ArrayT ty (Dynamic n))
      (JT_DynArray inferred n') =
    (n = n' ∧ inferred_type_consistent ctx ty inferred)) ∧
  (inferred_type_consistent ctx (TupleT tys) (JT_Tuple inferred) =
    LIST_REL (inferred_type_consistent ctx) tys inferred) ∧
  (inferred_type_consistent ctx (StructT (ns, name))
      (JT_Struct src name') =
    (name = name' ∧ inferred_source_matches ctx ns src)) ∧
  (inferred_type_consistent ctx (StructT (ns, name))
      (JT_Named src name') =
    (name = name' ∧ inferred_source_matches ctx ns src)) ∧
  (inferred_type_consistent ctx (FlagT (ns, name))
      (JT_Flag src name') =
    (name = name' ∧ inferred_source_matches ctx ns src)) ∧
  (inferred_type_consistent ctx (BaseT AddressT)
      (JT_Interface _ _) = T) ∧
  (inferred_type_consistent ctx ty JT_None = T) ∧
  (inferred_type_consistent ctx _ _ = F)
Termination
  WF_REL_TAC `measure (λ(_,_,inferred). json_type_size inferred)` >> simp[]
End

Definition declaration_type_valid_def:
  declaration_type_valid nominal_index all_import_maps ctx inferred ann =
    annotation_resolved nominal_index all_import_maps ctx ann ∧
    (ann = JTA_None ∨ inferred_type_consistent ctx
      (elaborate_annotation nominal_index all_import_maps ctx ann) inferred)
End

Definition canonical_decl_type_def:
  canonical_decl_type nominal_index all_import_maps ctx inferred ann =
    if ann = JTA_None then translate_type ctx inferred
    else elaborate_annotation nominal_index all_import_maps ctx ann
End

Definition translate_qualified_annotation_def:
  translate_qualified_annotation all_import_maps ctx inferred path attr =
    case inferred of
    | JT_Flag _ name =>
        if attr = name then
          case resolve_qualified_type_path all_import_maps ctx path of
          | SOME src_id => FlagT (SOME src_id, name)
          | NONE => translate_type ctx (JT_Flag NONE name)
        else translate_type ctx inferred
    | JT_Struct _ name =>
        if attr = name then
          case resolve_qualified_type_path all_import_maps ctx path of
          | SOME src_id => StructT (SOME src_id, name)
          | NONE => translate_type ctx (JT_Struct NONE name)
        else translate_type ctx inferred
    | JT_Named _ name =>
        if attr = name then
          case resolve_qualified_type_path all_import_maps ctx path of
          | SOME src_id => StructT (SOME src_id, name)
          | NONE => translate_type ctx (JT_Named NONE name)
        else translate_type ctx inferred
    | _ => translate_type ctx inferred
End

Definition translate_type_with_annotation_def:
  translate_type_with_annotation all_import_maps ctx inferred ann =
    case ann of
    | JTA_Qualified path attr =>
        translate_qualified_annotation all_import_maps ctx inferred path attr
    | _ => translate_type ctx inferred
End
