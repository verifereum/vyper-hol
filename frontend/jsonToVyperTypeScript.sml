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
Definition source_id_to_nsid_def:
  source_id_to_nsid (main_src_id:int) (src_id:int) =
    if src_id = main_src_id then NONE
    else SOME (Num (src_id + &builtin_source_id_offset))
End

Definition json_nsid_to_nsid_def:
  json_nsid_to_nsid (main_src_id:int) (src_id:int, name:string) =
    (source_id_to_nsid main_src_id src_id, name) : nsid
End
(* ===== Type Translation ===== *)

(* Define mutual recursion to handle lists explicitly *)
Definition source_id_opt_to_nsid_def:
  source_id_opt_to_nsid main_src_id NONE name = (NONE, name) ∧
  source_id_opt_to_nsid main_src_id (SOME src_id) name =
    (source_id_to_nsid main_src_id src_id, name)
End


Definition translate_type_def:
  (translate_type main_src_id (JT_Integer bits T) = BaseT (IntT bits)) /\
  (translate_type main_src_id (JT_Integer bits F) = BaseT (UintT bits)) /\
  (translate_type main_src_id (JT_BytesM m) = BaseT (BytesT (Fixed m))) /\
  (translate_type main_src_id (JT_String n) = BaseT (StringT n)) /\
  (translate_type main_src_id (JT_Bytes n) = BaseT (BytesT (Dynamic n))) /\
  (translate_type main_src_id (JT_StaticArray vt len) = ArrayT (translate_type main_src_id vt) (Fixed len)) /\
  (translate_type main_src_id (JT_DynArray vt len) = ArrayT (translate_type main_src_id vt) (Dynamic len)) /\
  (translate_type main_src_id (JT_Struct src_id_opt name) = StructT (source_id_opt_to_nsid main_src_id src_id_opt name)) /\
  (translate_type main_src_id (JT_Flag src_id_opt name) = FlagT (source_id_opt_to_nsid main_src_id src_id_opt name)) /\
  (translate_type main_src_id (JT_Qualified _ name) = StructT (NONE, name)) /\
  (translate_type main_src_id (JT_Tuple tys) = TupleT (translate_type_list main_src_id tys)) /\
  (translate_type main_src_id (JT_HashMap _ _) = NoneT) /\
  (translate_type main_src_id JT_None = NoneT) /\
  (translate_type main_src_id (JT_Named src_id_opt name) =
     if name = "bool" then BaseT BoolT
     else if name = "address" ∨ name = "self" then BaseT AddressT
     else if name = "decimal" then BaseT DecimalT
     else StructT (source_id_opt_to_nsid main_src_id src_id_opt name)) /\
  (translate_type_list main_src_id [] = []) /\
  (translate_type_list main_src_id (t::ts) = translate_type main_src_id t :: translate_type_list main_src_id ts)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (_,t) => json_type_size t
    | INR (_,ts) => list_size json_type_size ts)` >> simp[]
End


Definition tctx_current_nsid_def:
  tctx_current_nsid tctx = FST (SND tctx)
End

Definition tctx_import_map_def:
  tctx_import_map tctx = SND (SND tctx)
End

Definition translate_type_ctx_def:
  (translate_type_ctx ctx (JT_StaticArray vt len) = ArrayT (translate_type_ctx ctx vt) (Fixed len)) ∧
  (translate_type_ctx ctx (JT_DynArray vt len) = ArrayT (translate_type_ctx ctx vt) (Dynamic len)) ∧
  (translate_type_ctx ctx (JT_Tuple tys) = TupleT (MAP (translate_type_ctx ctx) tys)) ∧
  (translate_type_ctx ctx (JT_Struct NONE name) = StructT (tctx_current_nsid ctx, name)) ∧
  (translate_type_ctx ctx (JT_Flag NONE name) = FlagT (tctx_current_nsid ctx, name)) ∧
  (translate_type_ctx ctx (JT_Named NONE name) =
     if name = "bool" then BaseT BoolT
     else if name = "address" ∨ name = "self" then BaseT AddressT
     else if name = "decimal" then BaseT DecimalT
     else StructT (tctx_current_nsid ctx, name)) ∧
  (translate_type_ctx ctx (JT_Qualified path name) = translate_type (FST ctx) (JT_Qualified path name)) ∧
  (translate_type_ctx ctx ty = translate_type (FST ctx) ty)
Termination
  WF_REL_TAC `measure (λ(_,ty). json_type_size ty)` >> simp[]
End

(* Qualified syntactic annotations are resolved locally using the current
   module import map.  We only use them as namespace hints; the inferred
   type supplies the kind (flag/struct/named). *)
Definition resolve_qualified_type_path_def:
  (resolve_qualified_type_path all_import_maps ctx [] = NONE) ∧
  (resolve_qualified_type_path all_import_maps ctx [alias] = ALOOKUP (tctx_import_map ctx) alias) ∧
  (resolve_qualified_type_path all_import_maps ctx (alias::next::rest) =
    case ALOOKUP (tctx_import_map ctx) alias of
    | NONE => NONE
    | SOME parent_src_id =>
        case ALOOKUP all_import_maps parent_src_id of
        | NONE => NONE
        | SOME parent_import_map =>
            resolve_qualified_type_path all_import_maps (FST ctx, SOME parent_src_id, parent_import_map) (next::rest))
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
          | NONE => translate_type_ctx ctx (JT_Flag NONE name)
        else translate_type_ctx ctx inferred
    | JT_Struct _ name =>
        if attr = name then
          case resolve_qualified_type_path all_import_maps ctx path of
          | SOME src_id => StructT (SOME src_id, name)
          | NONE => translate_type_ctx ctx (JT_Struct NONE name)
        else translate_type_ctx ctx inferred
    | JT_Named _ name =>
        if attr = name then
          case resolve_qualified_type_path all_import_maps ctx path of
          | SOME src_id => StructT (SOME src_id, name)
          | NONE => translate_type_ctx ctx (JT_Named NONE name)
        else translate_type_ctx ctx inferred
    | _ => translate_type_ctx ctx inferred
End

Definition translate_type_with_annotation_def:
  translate_type_with_annotation all_import_maps ctx inferred ann =
    case ann of
    | JT_Qualified path attr => translate_qualified_annotation all_import_maps ctx inferred path attr
    | _ => translate_type_ctx ctx inferred
End

