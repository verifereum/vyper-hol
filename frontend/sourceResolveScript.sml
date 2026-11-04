Theory sourceResolve
Ancestors
  sourceSyntax sourceConstEnv option alist list string

(* Lexical scopes map spellings to declaration identities. The declaration
   table, not a spelling, determines the kind. Aliases point to identities;
   only modules permit member lookup. Failed lookup is NEVER dynamic. *)
Datatype:
  source_resolve_kind = SR_Constant | SR_Dynamic | SR_Function | SR_Module
                     | SR_Type | SR_Bytes | SR_FixedBytes num
                     | SR_Builtin source_const_builtin
                     | SR_Alias (string list)
End

Definition source_resolve_lexical_def:
  source_resolve_lexical [] name = NONE /\
  source_resolve_lexical (scope::scopes) name =
    case ALOOKUP scope name of
      NONE => source_resolve_lexical scopes name
    | SOME path => SOME path
End

(* A finite alias chain needs at most LENGTH table edges. Cycles and missing
   targets fail closed; a shadowing alias never falls through to a builtin. *)
Definition source_resolve_alias_def:
  source_resolve_alias 0 table path = NONE /\
  source_resolve_alias (SUC fuel) table path =
    case ALOOKUP table path of
      NONE => NONE
    | SOME (SR_Alias target) => source_resolve_alias fuel table target
    | SOME kind => SOME (path,kind)
End

Definition source_resolve_members_def:
  source_resolve_members fuel table resolved [] = SOME resolved /\
  source_resolve_members fuel table (path,kind) (name::names) =
    if kind = SR_Module then
      case source_resolve_alias fuel table (path ++ [name]) of
        NONE => NONE
      | SOME member => source_resolve_members fuel table member names
    else NONE
End

Definition source_resolve_name_def:
  source_resolve_name scopes table names =
    case names of [] => NONE | name::rest =>
      case source_resolve_lexical scopes name of NONE => NONE | SOME path =>
        case source_resolve_alias (SUC (LENGTH table)) table path of
          NONE => NONE
        | SOME resolved =>
            source_resolve_members (SUC (LENGTH table)) table resolved rest
End

Definition source_resolve_collect_def:
  source_resolve_collect [] = SOME [] /\
  source_resolve_collect (x::xs) =
    case x of NONE => NONE | SOME value =>
      OPTION_MAP (CONS value) (source_resolve_collect xs)
End

Definition source_resolve_two_def:
  source_resolve_two f x y =
    case x of NONE => NONE | SOME a => OPTION_MAP (f a) y
End

Definition source_resolve_atom_def:
  source_resolve_atom type_position (path,kind) =
    case kind of
      SR_Constant => SCE_Name path
    | SR_Dynamic => SCE_Dynamic
    | SR_Function => SCE_Unsupported "function" []
    | SR_Module => SCE_Unsupported "module" []
    | SR_FixedBytes width =>
        if type_position then SCE_BytesType T (SCE_Literal (SCL_Int (&width)))
        else SCE_Unsupported "type" []
    | SR_Type => SCE_Unsupported "type" []
    | SR_Bytes => SCE_Unsupported "type" []
    | SR_Builtin b => SCE_Unsupported "builtin-value" []
    | SR_Alias target => SCE_Unsupported "alias" []
End

Definition source_resolve_callee_def:
  source_resolve_callee scopes table callee args kws =
    case callee of
      SCE_Name names =>
        (case source_resolve_name scopes table names of
           NONE => NONE
         | SOME (path,SR_Builtin b) => SOME (SCE_Builtin b args kws)
         | SOME resolved => SOME (SCE_Call (source_resolve_atom F resolved) args kws))
    | _ => SOME (SCE_Call callee args kws)
End

(* Full unelaborated constant syntax. The flag is used ONLY at output_type
   keyword positions. Already tagged builtins/types are rejected: this entry
   point cannot use a claimed resolved identity as its own evidence. *)
Definition source_resolve_expr_def:
  source_resolve_expr scopes table type_position (SCE_Literal lit) =
    SOME (SCE_Literal lit) /\
  source_resolve_expr scopes table type_position (SCE_Name names) =
    OPTION_MAP (source_resolve_atom type_position)
      (source_resolve_name scopes table names) /\
  source_resolve_expr scopes table type_position SCE_Dynamic = SOME SCE_Dynamic /\
  source_resolve_expr scopes table type_position (SCE_BytesType fixed e) = NONE /\
  source_resolve_expr scopes table type_position (SCE_Unary op e) =
    OPTION_MAP (SCE_Unary op) (source_resolve_expr scopes table F e) /\
  source_resolve_expr scopes table type_position (SCE_Binary op l r) =
    source_resolve_two (SCE_Binary op)
      (source_resolve_expr scopes table F l) (source_resolve_expr scopes table F r) /\
  source_resolve_expr scopes table type_position (SCE_Compare op l r) =
    source_resolve_two (SCE_Compare op)
      (source_resolve_expr scopes table F l) (source_resolve_expr scopes table F r) /\
  source_resolve_expr scopes table type_position (SCE_Boolean op es) =
    OPTION_MAP (SCE_Boolean op)
      (source_resolve_collect (MAP (source_resolve_expr scopes table F) es)) /\
  source_resolve_expr scopes table type_position (SCE_List es) =
    OPTION_MAP SCE_List
      (source_resolve_collect (MAP (source_resolve_expr scopes table F) es)) /\
  source_resolve_expr scopes table type_position (SCE_Tuple es) =
    OPTION_MAP SCE_Tuple
      (source_resolve_collect (MAP (source_resolve_expr scopes table F) es)) /\
  source_resolve_expr scopes table type_position (SCE_Subscript e i) =
    (case e of SCE_Name names =>
       if type_position then
         (case source_resolve_name scopes table names of
            SOME (path,SR_Bytes) => OPTION_MAP (SCE_BytesType F)
              (source_resolve_expr scopes table F i)
          | NONE => NONE
          | SOME resolved => source_resolve_two SCE_Subscript
              (SOME (source_resolve_atom F resolved))
              (source_resolve_expr scopes table F i))
       else source_resolve_two SCE_Subscript
         (source_resolve_expr scopes table F e) (source_resolve_expr scopes table F i)
     | _ => source_resolve_two SCE_Subscript
         (source_resolve_expr scopes table F e) (source_resolve_expr scopes table F i)) /\
  source_resolve_expr scopes table type_position (SCE_Builtin b args kws) = NONE /\
  source_resolve_expr scopes table type_position (SCE_Call callee args kws) =
    (case source_resolve_collect (MAP (source_resolve_expr scopes table F) args) of
       NONE => NONE
     | SOME resolved_args =>
       case source_resolve_collect
         (MAP (\(k,v). OPTION_MAP (\v'. (k,v'))
           (source_resolve_expr scopes table (k = "output_type") v)) kws) of
         NONE => NONE
       | SOME resolved_kws =>
         case callee of
           SCE_Name names =>
             source_resolve_callee scopes table callee resolved_args resolved_kws
         | _ => case source_resolve_expr scopes table F callee of
                  NONE => NONE
                | SOME resolved => SOME (SCE_Call resolved resolved_args resolved_kws)) /\
  source_resolve_expr scopes table type_position (SCE_Unsupported tag es) =
    OPTION_MAP (SCE_Unsupported tag)
      (source_resolve_collect (MAP (source_resolve_expr scopes table F) es))
End

Definition source_resolve_candidate_def:
  source_resolve_candidate scopes table expr =
    source_resolve_expr scopes table F (source_constant_candidate expr)
End

(* Only resolved initializers enter the dependency evaluator. Failure retains
   the declaration's identity in the caller's input; no missing-name seed or
   compiler folded replacement is manufactured. *)
Definition source_resolve_declarations_def:
  source_resolve_declarations scopes table declarations =
    source_resolve_collect (MAP (\(path,expr).
      OPTION_MAP (\resolved. (path,resolved))
        (source_resolve_candidate scopes table expr)) declarations)
End

Definition source_resolve_constants_def:
  source_resolve_constants scopes table seed declarations =
    OPTION_MAP (source_const_resolve seed)
      (source_resolve_declarations scopes table declarations)
End
