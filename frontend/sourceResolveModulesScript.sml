Theory sourceResolveModules
Ancestors
  sourceResolve sourceConstAnnotation ASCIInumbers alist list string

(* Registry keys come from the SOURCE loader's module namespace, not compiler
   source_id/path/import_infos metadata. SourceProgram has anonymous modules:
   relating those modules to loader keys is an explicit integration boundary.
   This theory validates unique canonical keys and all source import edges. *)
Definition source_resolve_builtins_def:
  source_resolve_builtins =
    [("method_id",SCB_MethodId); ("len",SCB_Len); ("concat",SCB_Concat);
     ("keccak256",SCB_Keccak256); ("sha256",SCB_Sha256); ("convert",SCB_Convert);
     ("min",SCB_Min); ("max",SCB_Max); ("abs",SCB_Abs);
     ("pow_mod256",SCB_PowMod256); ("uint256_addmod",SCB_Uint256AddMod);
     ("uint256_mulmod",SCB_Uint256MulMod)]
End

Definition source_resolve_primitives_def:
  source_resolve_primitives =
    [("Bytes",SR_Bytes); ("String",SR_Type); ("bool",SR_Type);
     ("address",SR_Type); ("decimal",SR_Type)] ++
    GENLIST (\i. ("bytes" ++ num_to_dec_string (SUC i),SR_FixedBytes (SUC i))) 32 ++
    FLAT (GENLIST (\i.
      [("uint" ++ num_to_dec_string (8 * SUC i),SR_Type);
       ("int" ++ num_to_dec_string (8 * SUC i),SR_Type)]) 32)
End

Definition source_resolve_prelude_def:
  source_resolve_prelude =
    MAP (\(name,b). (["$builtin";name],SR_Builtin b)) source_resolve_builtins ++
    MAP (\(name,kind). (["$builtin";name],kind)) source_resolve_primitives
End

Definition source_resolve_prelude_scope_def:
  source_resolve_prelude_scope =
    MAP (\(path,kind). (LAST path,path)) source_resolve_prelude
End

Definition source_resolve_is_constant_def:
  source_resolve_is_constant (SCA_Qualified q a) =
    (q = SCQ_Constant \/ (q = SCQ_Public /\ source_resolve_is_constant a)) /\
  source_resolve_is_constant _ = F
End

Definition source_resolve_imports_def:
  source_resolve_imports (SourceModule ds) =
    FLAT (MAP (\d. case d of SD_Import imports => imports | _ => []) ds)
End

Definition source_resolve_import_target_def:
  source_resolve_import_target owner (SI_Import name alias) =
    SOME (TOKENS ($= #".") name) /\
  source_resolve_import_target owner (SI_FromImport module_name level name alias) =
    if level = 0 then SOME (TOKENS ($= #".") module_name ++ [name])
    else if level <= LENGTH owner then
      SOME (TAKE (LENGTH owner - level) owner ++
            TOKENS ($= #".") module_name ++ [name])
    else NONE
End

Definition source_resolve_import_alias_def:
  source_resolve_import_alias (SI_Import name alias) =
    (case alias of SOME a => a | NONE => LAST (TOKENS ($= #".") name)) /\
  source_resolve_import_alias (SI_FromImport module_name level name alias) =
    (case alias of SOME a => a | NONE => name)
End

Definition source_resolve_decl_bindings_def:
  source_resolve_decl_bindings owner (SD_Variable name annotation init) =
    [(owner ++ [name],if source_resolve_is_constant annotation
                     then SR_Constant else SR_Dynamic)] /\
  source_resolve_decl_bindings owner (SD_Function name decs args defs ret body) =
    [(owner ++ [name],SR_Function)] /\
  source_resolve_decl_bindings owner (SD_Struct name fields) = [(owner ++ [name],SR_Type)] /\
  source_resolve_decl_bindings owner (SD_Event name fields) = [(owner ++ [name],SR_Type)] /\
  source_resolve_decl_bindings owner (SD_Interface name ds) = [(owner ++ [name],SR_Type)] /\
  source_resolve_decl_bindings owner (SD_Flag name fields) = [(owner ++ [name],SR_Type)] /\
  source_resolve_decl_bindings owner (SD_Import imports) =
    FLAT (MAP (\imp. case source_resolve_import_target owner imp of
      NONE => [] | SOME target =>
        [(owner ++ [source_resolve_import_alias imp],SR_Alias target)]) imports) /\
  source_resolve_decl_bindings owner _ = []
End

Definition source_resolve_module_bindings_def:
  source_resolve_module_bindings owner (SourceModule ds) =
    FLAT (MAP (source_resolve_decl_bindings owner) ds)
End

Definition source_resolve_module_scope_def:
  source_resolve_module_scope owner module_syntax =
    MAP (\(path,kind). (LAST path,path))
      (source_resolve_module_bindings owner module_syntax)
End

Definition source_resolve_table_def:
  source_resolve_table registry = source_resolve_prelude ++
    FLAT (MAP (\(owner,module_syntax).
      (owner,SR_Module)::source_resolve_module_bindings owner module_syntax) registry)
End

Definition source_resolve_initializers_def:
  source_resolve_initializers owner (SourceModule ds) =
    FLAT (MAP (\d. case d of
      SD_Variable name annotation (SOME init) =>
        if source_resolve_is_constant annotation then [(owner ++ [name],init)] else []
    | _ => []) ds)
End

Definition source_resolve_module_ok_def:
  source_resolve_module_ok registry (owner,module_syntax) =
    (EVERY (\imp. source_resolve_import_alias imp <> "" /\
      case source_resolve_import_target owner imp of
        NONE => F | SOME target => IS_SOME (ALOOKUP registry target))
      (source_resolve_imports module_syntax) /\
    EVERY (\d. case d of SD_Variable name annotation init =>
      (source_resolve_is_constant annotation ==> IS_SOME init) | _ => T)
      (source_module_declarations module_syntax))
End

Definition source_resolve_registry_ok_def:
  source_resolve_registry_ok registry =
    (EVERY (\(key,module_syntax). source_const_identity_ok key /\ HD key <> "$builtin") registry /\
    EVERY (source_resolve_module_ok registry) registry /\
    EVERY source_const_identity_ok (MAP FST (source_resolve_table registry)) /\
    ALL_DISTINCT (MAP FST (source_resolve_table registry)))
End

(* Binding locals is explicit and left-biased. Their canonical identities are
   qualified by the function/block owner; the builtin scope remains last. *)
Definition source_resolve_locals_def:
  source_resolve_locals owner names = MAP (\name. (name,owner ++ [name])) names
End

Definition source_resolve_local_bindings_def:
  source_resolve_local_bindings owner names =
    MAP (\name. (owner ++ [name],SR_Dynamic)) names
End

(* Claims are redundant evidence, NEVER an identity map. A claim must match
   actual retained import syntax, its namespace-derived target, and a present
   unique registry entry. Conflicting IDs are rejected, not used to merge two
   different source modules. The ID itself establishes no authenticity. *)
Datatype:
  source_resolve_import_claim = SourceImportClaim (string list) source_import
                                 (string list) num
End

Definition source_resolve_claim_ok_def:
  source_resolve_claim_ok registry (SourceImportClaim owner imp target source_id) =
    case ALOOKUP registry owner of NONE => F | SOME module_syntax =>
      MEM imp (source_resolve_imports module_syntax) /\
      source_resolve_import_target owner imp = SOME target /\
      IS_SOME (ALOOKUP registry target)
End

Definition source_resolve_claim_key_def:
  source_resolve_claim_key (SourceImportClaim owner imp target source_id) = (owner,imp)
End

Definition source_resolve_claim_target_def:
  source_resolve_claim_target (SourceImportClaim owner imp target source_id) = target
End

Definition source_resolve_claim_id_def:
  source_resolve_claim_id (SourceImportClaim owner imp target source_id) = source_id
End

Definition source_resolve_claims_ok_def:
  source_resolve_claims_ok registry claims =
    (source_resolve_registry_ok registry /\
    EVERY (source_resolve_claim_ok registry) claims /\
    ALL_DISTINCT (MAP source_resolve_claim_key claims) /\
    EVERY (\a. EVERY (\b. source_resolve_claim_id a = source_resolve_claim_id b ==>
      source_resolve_claim_target a = source_resolve_claim_target b) claims) claims /\
    EVERY (\(owner,module_syntax). EVERY (\imp.
      MEM (owner,imp) (MAP source_resolve_claim_key claims))
      (source_resolve_imports module_syntax)) registry)
End

(* The registry must enumerate exactly the retained modules in source order.
   Duplicate semantic syntax may have DIFFERENT canonical module identities.
   Equality of module bodies (or source IDs) is not module identity. *)
Definition source_resolve_program_registry_def:
  source_resolve_program_registry (SourceProgram main imports) keys =
    if LENGTH keys = LENGTH (main::imports) then
      let registry = ZIP (keys,main::imports) in
        if source_resolve_registry_ok registry then SOME registry else NONE
    else NONE
End

Definition source_resolve_registry_declarations_def:
  source_resolve_registry_declarations registry =
    OPTION_MAP FLAT (source_resolve_collect (MAP (\(owner,module_syntax).
      source_resolve_declarations
        [source_resolve_module_scope owner module_syntax; source_resolve_prelude_scope]
        (source_resolve_table registry)
        (source_resolve_initializers owner module_syntax)) registry))
End

(* Checked expression API for future source consumers. Local scopes may be
   added using the lower-level lexical API; those entries must be constructed
   from source arguments/bindings, never inferred metadata. *)
Definition source_resolve_module_expr_def:
  source_resolve_module_expr registry owner expr =
    if source_resolve_registry_ok registry then
      case ALOOKUP registry owner of NONE => NONE | SOME module_syntax =>
        source_resolve_expr
          [source_resolve_module_scope owner module_syntax; source_resolve_prelude_scope]
          (source_resolve_table registry) F expr
    else NONE
End

Definition source_resolve_module_candidate_def:
  source_resolve_module_candidate registry owner expr =
    source_resolve_module_expr registry owner (source_constant_candidate expr)
End

Definition source_resolve_registry_constants_def:
  source_resolve_registry_constants registry =
    if source_resolve_registry_ok registry then
      OPTION_MAP (source_const_resolve [])
        (source_resolve_registry_declarations registry)
    else NONE
End

Definition source_resolve_program_constants_def:
  source_resolve_program_constants program keys =
    case source_resolve_program_registry program keys of
      NONE => NONE
    | SOME registry => source_resolve_registry_constants registry
End
