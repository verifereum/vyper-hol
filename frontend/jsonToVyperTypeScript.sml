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
  (translate_type ctx (JT_Qualified _ name) = StructT (NONE, name)) ∧
  (translate_type ctx (JT_HashMap _ _) = NoneT) ∧
  (translate_type ctx JT_None = NoneT)
Termination
  WF_REL_TAC `measure (λ(_,ty). json_type_size ty)` >> simp[]
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
    | JT_Qualified path attr =>
        translate_qualified_annotation all_import_maps ctx inferred path attr
    | _ => translate_type ctx inferred
End
