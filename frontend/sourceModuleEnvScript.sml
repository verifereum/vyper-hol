Theory sourceModuleEnv
Ancestors
  sourceModuleDefs sourceExprDefs sourceResolveModules sourceResolve
  sourceTypeDefs sourceSyntax sourceConstAnnotation sourceConstAST
  vyperTypeContract vyperTypeSystem vyperAST ASCIInumbers finite_map alist list
Libs
  intLib

Theorem source_module_funion_empty[compute]:
  (FUNION FEMPTY fm = fm) /\ (FUNION fm FEMPTY = fm)
Proof
  simp[]
QED

Definition source_module_primitive_names_def:
  source_module_primitive_names =
    [(["$builtin";"bool"],STI_Bool); (["$builtin";"address"],STI_Address);
     (["$builtin";"decimal"],STI_Decimal)] ++
    GENLIST (\i. (["$builtin";"bytes" ++ num_to_dec_string (SUC i)],STI_BytesM (SUC i))) 32 ++
    FLAT (GENLIST (\i.
      [(["$builtin";"uint" ++ num_to_dec_string (8 * SUC i)],STI_Integer F (8 * SUC i));
       (["$builtin";"int" ++ num_to_dec_string (8 * SUC i)],STI_Integer T (8 * SUC i))]) 32)
End

Definition source_module_constructors_def:
  source_module_constructors = [STC_String; STC_Bytes; STC_DynArray; STC_HashMap;
    STC_Qualifier SCQ_Constant; STC_Qualifier SCQ_Immutable;
    STC_Qualifier SCQ_Public; STC_Qualifier SCQ_Transient; STC_Qualifier SCQ_Indexed]
End

Definition source_module_intrinsics_def:
  source_module_intrinsics = [("abi_encode",SE_AbiEncode); ("abi_decode",SE_AbiDecode);
    ("raw_call",SE_RawCall); ("raw_revert",SE_RawRevert)]
End

Definition source_module_extra_prelude_def:
  source_module_extra_prelude =
    MAP (\c. (["$builtin"] ++ source_type_constructor_path c,SR_Type)) source_module_constructors ++
    MAP (\(name,b). (["$builtin";name],SR_Function)) source_module_intrinsics ++
    MAP (\name. (["$builtin";name],SR_Function))
      ["range";"slice";"empty";"min_value";"max_value"] ++
    [(["$builtin";"msg"],SR_Module); (["$builtin";"msg";"data"],SR_Dynamic);
     (["$builtin";"msg";"sender"],SR_Dynamic)]
End

Definition source_module_scopes_def:
  source_module_scopes owner syntax =
    [[("self",owner)]; source_resolve_module_scope owner syntax;
     source_resolve_prelude_scope ++
       MAP (\(path,kind). (LAST path,path))
         (FILTER (\(path,kind). LENGTH path = 2) source_module_extra_prelude)]
End

Definition source_module_names_def:
  source_module_names scopes table nominal_names =
    source_module_primitive_names ++ nominal_names ++
    FLAT (MAP (\c.
      let path = source_type_constructor_path c in
      if source_resolve_name scopes table path = SOME (["$builtin"] ++ path,SR_Type) \/
         (c = STC_Bytes /\ source_resolve_name scopes table path = SOME (["$builtin";"Bytes"],SR_Bytes))
      then [(path,STI_Constructor c)] else []) source_module_constructors)
End

Definition source_module_bindings_def:
  source_module_bindings =
    MAP (\(path,id). (path,SE_Type (case source_type_identity id of ST_Ok ty => ty | _ => NoneT)))
      source_module_primitive_names ++
    MAP (\(name,b). (["$builtin";name],SE_Intrinsic b)) source_module_intrinsics ++
    [(["$builtin";"msg";"sender"],SE_Runtime (Builtin (BaseT AddressT) (Env Sender) []))]
End

(* The nominal type environment/identity map, module namespace assignment and
   layout remain explicit inherited frontend inputs. Only those claims are
   trusted. No executable expression can enter through this record. *)
Datatype:
  source_module_trust = <|
    smt_ids : (string list # num option) list;
    smt_nominals : (string list # source_type_identity) list;
    smt_type_defs : (nsid |-> type_args);
    smt_slots : ((num option # string) # num) list
  |>
End

Definition source_module_context_def:
  source_module_context trust registry constants owner syntax =
    let table = source_resolve_table registry ++ source_module_extra_prelude in
    let scopes = source_module_scopes owner syntax in
    let env = (artifact_env empty_contract_type_artifact []
      (case ALOOKUP trust.smt_ids owner of SOME src => src | NONE => NONE))
      with type_defs := trust.smt_type_defs in
    <| sm_env := env; sm_scopes := scopes; sm_table := table;
       sm_constants := constants; sm_bindings := source_module_bindings ++
         FLAT (MAP (\(path,identity). case source_type_identity identity of
           ST_Ok ty => [(path,SE_Type ty)] | ST_Error err => []) trust.smt_nominals);
       sm_names := source_module_names scopes table trust.smt_nominals;
       sm_events := []; sm_owner := owner |>
End

(* Declaration-only module identities are derived from the explicit preserved
   policy registry. They are not additions to inherited nominal trust. *)
Definition source_module_policy_context_def:
  source_module_policy_context trust policies registry constants owner syntax =
    let ctx = source_module_context trust registry constants owner syntax in
    ctx with sm_names := MAP (\(key,p). (key,STI_Interface))
      (FILTER (\(key,p). source_module_declaration_only p) policies) ++ ctx.sm_names
End

Definition source_module_runtime_bindings_def:
  source_module_runtime_bindings ids owner tops =
    FLAT (MAP (\tl. case tl of
      VariableDecl vis mut name ty slot => [(owner ++ [name],SE_Runtime
        (TopLevelName ty ((case ALOOKUP ids owner of SOME src => src | NONE => NONE),name)))]
    | HashMapDecl vis transient name kt vt slot => [(owner ++ [name],SE_Runtime
        (TopLevelName NoneT ((case ALOOKUP ids owner of SOME src => src | NONE => NONE),name)))]
    | FunctionDecl vis mut nr raw name params defaults ret body =>
        if vis = Internal \/ vis = Deploy then
          [(owner ++ [name],SE_Function
            ((case ALOOKUP ids owner of SOME src => src | NONE => NONE),name)
            (MAP SND params) (LENGTH defaults) ret)] else []
    | EventDecl name fields => MAP (\((field,ty),indexed).
        (owner ++ [name;field],SE_Type ty)) fields
    | InterfaceDecl name fs => [(owner ++ [name],SE_Interface fs)]
    | _ => []) tops)
End

Definition source_module_event_bindings_def:
  source_module_event_bindings ids owner tops =
    FLAT (MAP (\tl. case tl of EventDecl name fields =>
      [(owner ++ [name],((case ALOOKUP ids owner of SOME src => src | NONE => NONE),name),
        MAP (SND o FST) fields)] | _ => []) tops)
End

Definition source_module_nominal_names_def:
  source_module_nominal_names ids registry = FLAT (MAP (\(owner,syntax).
    let src = case ALOOKUP ids owner of SOME sid => sid | NONE => NONE in
    FLAT (MAP (\d. case d of
      SD_Struct name fields => [(owner ++ [name],STI_Struct (src,name))]
    | SD_Flag name members => [(owner ++ [name],STI_Flag (src,name))]
    | SD_Interface name fs => [(owner ++ [name],STI_Interface)]
    | _ => []) (source_module_declarations syntax))) registry)
End

Definition source_module_trust_ok_def:
  source_module_trust_ok registry trust =
    (MAP FST trust.smt_ids = MAP FST registry /\ ALL_DISTINCT (MAP SND trust.smt_ids) /\
     (case trust.smt_ids of [] => F | (owner,src)::rest => src = NONE) /\
     ALL_DISTINCT (MAP FST trust.smt_slots) /\
     ALL_DISTINCT (MAP FST trust.smt_nominals) /\
     EVERY (\entry. MEM entry (source_module_nominal_names trust.smt_ids registry)) trust.smt_nominals /\
     EVERY (\entry. MEM entry trust.smt_nominals) (source_module_nominal_names trust.smt_ids registry))
End
