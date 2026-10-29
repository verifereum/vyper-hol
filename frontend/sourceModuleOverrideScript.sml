Theory sourceModuleOverride
Ancestors
  sourceModuleLink sourceModuleDecl sourceModuleDefs sourceModuleEnv sourceExprDefs
  sourceSyntax sourceResolve sourceResolveModules sourceConstAST sourceConstAnnotation
  sourceTypeDefs vyperTypeSystem vyperAST
  alist list
Libs
  intLib

Definition source_module_supertype_def:
  source_module_supertype (BaseT (StringT n)) (BaseT (StringT m)) = (m <= n) /\
  source_module_supertype (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic m))) = (m <= n) /\
  source_module_supertype (ArrayT t (Dynamic n)) (ArrayT u (Dynamic m)) =
    (m <= n /\ source_module_supertype t u) /\
  source_module_supertype (ArrayT t (Fixed n)) (ArrayT u (Fixed m)) =
    (m = n /\ source_module_supertype t u) /\
  source_module_supertype (TupleT ts) (TupleT us) = LIST_REL source_module_supertype ts us /\
  source_module_supertype t u = (t = u)
Termination
  WF_REL_TAC `measure (type_size o FST)` >> simp[] >> rpt strip_tac >> res_tac >> simp[]
End

Definition source_module_override_params_def:
  source_module_override_params ctxa ctxb [] bs = EVERY (IS_SOME o SND o SND) bs /\
  source_module_override_params ctxa ctxb (a::as) [] = F /\
  source_module_override_params ctxa ctxb ((an,at,ad)::as) ((bn,bt,bd)::bs) =
    (an = bn /\ source_module_supertype bt at /\
     source_module_default_override ctxa ctxb ad bd /\
     source_module_override_params ctxa ctxb as bs)
End

Definition source_module_parameters_def:
  source_module_parameters params defaults =
    MAP (\((n,t),d). (n,t,d)) (attach_param_defaults params defaults)
End

Definition source_module_mutability_rank_def:
  source_module_mutability_rank decs = if MEM (SX_Name "pure") decs then 0 else
    if MEM (SX_Name "view") decs then 1 else if MEM (SX_Name "payable") decs then 3 else 2
End

(* Runtime interfaces erase to address. Keep their canonical SOURCE identities
   in compatibility checks rather than identifying unrelated interface types.
   Bounds are compared semantically by supertype, not structurally here. *)
Definition source_module_nominal_shape_def:
  source_module_nominal_shape ctx (SCA_Name names) =
    (case source_resolve_name ctx.sm_scopes ctx.sm_table names of
       SOME (key,SR_Type) => if ALOOKUP ctx.sm_names key = SOME STI_Interface
         then SCA_Name key else SCA_Name ["$value"]
     | SOME (key,SR_Module) => if ALOOKUP ctx.sm_names key = SOME STI_Interface
         then SCA_Name key else SCA_Name ["$value"]
     | _ => SCA_Name ["$value"]) /\
  source_module_nominal_shape ctx (SCA_StaticArray a bound) =
    SCA_StaticArray (source_module_nominal_shape ctx a) (SCE_Literal (SCL_Int 0)) /\
  source_module_nominal_shape ctx (SCA_DynArray a bound) =
    SCA_DynArray (source_module_nominal_shape ctx a) (SCE_Literal (SCL_Int 0)) /\
  source_module_nominal_shape ctx (SCA_Tuple fields) =
    SCA_Tuple (MAP (source_module_nominal_shape ctx) fields) /\
  source_module_nominal_shape ctx (SCA_Qualified q a) = source_module_nominal_shape ctx a /\
  source_module_nominal_shape ctx _ = SCA_Name ["$value"]
Termination
  WF_REL_TAC `measure (source_const_annotation_size o SND)` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
End

Definition source_module_arg_nominals_def:
  source_module_arg_nominals ctx (SourceArg name (SOME a)) = source_module_nominal_shape ctx a /\
  source_module_arg_nominals ctx _ = SCA_Name ["$value"]
End

Definition source_module_return_nominals_def:
  source_module_return_nominals ctx NONE = SCA_Name ["$value"] /\
  source_module_return_nominals ctx (SOME a) = source_module_nominal_shape ctx a
End

Definition source_module_override_compatible_def:
  source_module_override_compatible ctxa
      (SD_Function an ads aa ad ar ab) ctxb (SD_Function bn bds ba bd br bb) =
    (MEM (SX_Name "abstract") ads /\ an = bn /\
     ~MEM (SX_Name "external") ads /\ ~MEM (SX_Name "deploy") ads /\
     ~MEM (SX_Name "external") bds /\ ~MEM (SX_Name "deploy") bds /\
     LENGTH ad <= LENGTH aa /\ LENGTH bd <= LENGTH ba /\
     MAP (source_module_arg_nominals ctxa) aa =
       MAP (source_module_arg_nominals ctxb) (TAKE (LENGTH aa) ba) /\
     source_module_return_nominals ctxa ar = source_module_return_nominals ctxb br /\
     source_module_mutability_rank bds <= source_module_mutability_rank ads /\
     (MEM (SX_Name "nonreentrant") ads = MEM (SX_Name "nonreentrant") bds) /\
     case (source_module_args ctxa aa,source_module_args ctxb ba,
           source_module_return_type ctxa ar,source_module_return_type ctxb br) of
       (SM_Ok ap,SM_Ok bp,SM_Ok at,SM_Ok bt) =>
         source_module_override_params ctxa ctxb
           (source_module_parameters ap ad) (source_module_parameters bp bd) /\
         source_module_supertype at bt
     | _ => F) /\
  source_module_override_compatible ctxa a ctxb b = F
End

Definition source_module_override_targets_def:
  source_module_override_targets (SD_Function name decs args defaults ret body) =
    FLAT (MAP (\d. case d of SX_Call (SX_Name "override") targets [] => targets | _ => []) decs) /\
  source_module_override_targets _ = []
End

Definition source_module_function_entries_def:
  source_module_function_entries registry = FLAT (MAP (\(owner,syntax).
    FLAT (MAP (\d. case d of SD_Function name decs args defaults ret body =>
      [(owner ++ [name],(owner,d))] | _ => []) (source_module_declarations syntax))) registry)
End

Definition source_module_override_links_def:
  source_module_override_links trust registry constants = OPT_MMAP (\(key,owner,d,target).
    case ALOOKUP registry owner of NONE => NONE | SOME syntax =>
    let ctx = source_module_context trust registry constants owner syntax in
    case source_module_module_ref ctx target of NONE => NONE | SOME parent =>
      case d of SD_Function name decs args defaults ret body =>
        SOME (parent ++ [name],key) | _ => NONE)
    (FLAT (MAP (\(key,owner,d).
      MAP (\target. (key,owner,d,target)) (source_module_override_targets d))
      (MAP (\(key,owner,d). (key,owner,d)) (source_module_function_entries registry))))
End

Definition source_module_abstract_def:
  source_module_abstract (SD_Function name decs args defaults ret body) =
    MEM (SX_Name "abstract") decs /\
  source_module_abstract _ = F
End

Definition source_module_initialized_target_def:
  source_module_initialized_target ctx parent (SD_Initializes (SX_Subscript base deps)) =
    (source_module_module_ref ctx base = SOME parent) /\
  source_module_initialized_target ctx parent (SD_Initializes e) =
    (source_module_module_ref ctx e = SOME parent) /\
  source_module_initialized_target ctx parent _ = F
End

Definition source_module_override_link_ok_def:
  source_module_override_link_ok trust registry constants entries (target,key) =
    case (ALOOKUP entries target,ALOOKUP entries key) of
      (SOME (ao,a),SOME (bo,b)) =>
        (case (ALOOKUP registry ao,ALOOKUP registry bo) of
          (SOME am,SOME bm) =>
            let ac = source_module_context trust registry constants ao am in
            let bc = source_module_context trust registry constants bo bm in
            source_module_override_compatible ac a bc b /\
            EXISTS (source_module_initialized_target bc ao) (source_module_declarations bm)
        | _ => F)
    | _ => F
End

Definition source_module_overrides_def:
  source_module_overrides trust registry constants =
    case source_module_override_links trust registry constants of NONE => NONE | SOME links =>
      let entries = source_module_function_entries registry in
      if EVERY (source_module_override_link_ok trust registry constants entries) links /\
         ALL_DISTINCT (MAP FST links) /\
         EVERY (\(key,owner,d). source_module_abstract d ==> MEM key (MAP FST links)) entries
      then SOME links else NONE
End

(* The preserved policy context must also reach source signature compatibility,
   not just body elaboration: imported .vyi annotations denote interfaces here. *)
Definition source_module_policy_override_link_ok_def:
  source_module_policy_override_link_ok trust policies registry constants entries (target,key) =
    case (ALOOKUP entries target,ALOOKUP entries key) of
      (SOME (ao,a),SOME (bo,b)) =>
        (case (ALOOKUP registry ao,ALOOKUP registry bo) of
          (SOME am,SOME bm) =>
            let ac = source_module_policy_context trust policies registry constants ao am in
            let bc = source_module_policy_context trust policies registry constants bo bm in
            source_module_override_compatible ac a bc b /\
            EXISTS (source_module_initialized_target bc ao) (source_module_declarations bm)
        | _ => F)
    | _ => F
End

Definition source_module_policy_overrides_def:
  source_module_policy_overrides trust policies registry constants =
    case source_module_override_links trust registry constants of NONE => NONE | SOME links =>
      let entries = source_module_function_entries registry in
      if EVERY (source_module_policy_override_link_ok trust policies registry constants entries) links /\
         ALL_DISTINCT (MAP FST links) /\
         EVERY (\(key,owner,d). source_module_abstract d ==> MEM key (MAP FST links)) entries
      then SOME links else NONE
End

(* Resolve transitively, rejecting cycles. Rewriting changes CALL TARGETS only;
   it never changes the source used for defaults or compatibility. *)
Definition source_module_override_target_def:
  source_module_override_target 0 links key = NONE /\
  source_module_override_target (SUC fuel) links key =
    case ALOOKUP links key of NONE => SOME key | SOME next =>
      source_module_override_target fuel links next
End

Definition source_module_override_bindings_def:
  source_module_override_bindings trust links bindings = OPT_MMAP (\(key,b).
    case b of SE_Function id params defaults ret =>
      (case source_module_override_target (SUC (LENGTH links)) links key of
        NONE => NONE | SOME final =>
          (case ALOOKUP bindings final of
            SOME (SE_Function fid fp fd fr) => SOME (key,SE_Function fid fp fd fr)
          | _ => NONE))
    | _ => SOME (key,b)) bindings
End

Theorem source_module_nominal_shape_interface:
  source_resolve_name ctx.sm_scopes ctx.sm_table names = SOME (key,SR_Type) /\
  ALOOKUP ctx.sm_names key = SOME STI_Interface ==>
  source_module_nominal_shape ctx (SCA_Name names) = SCA_Name key
Proof
  simp[source_module_nominal_shape_def]
QED

Theorem source_module_overrides_equations:
  source_module_overrides trust registry constants = SOME links ==>
  source_module_override_links trust registry constants = SOME links /\
  ALL_DISTINCT (MAP FST links) /\
  EVERY (source_module_override_link_ok trust registry constants
    (source_module_function_entries registry)) links
Proof
  simp[source_module_overrides_def, AllCaseEqs()] >> rw[] >> gvs[]
QED
