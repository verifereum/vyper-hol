Theory sourceSyntax
Ancestors
  sourceConstAST sourceConstAnnotation list string

(* Opt-in source PROGRAM syntax, not the runtime AST or a source acceptance
   predicate. No folded/inferred fields occur in these semantic terms.
   Annotations reuse the independent constant syntax to avoid a type cycle. *)
Datatype:
  source_expr = SX_Literal source_const_literal
              | SX_Name string
              | SX_Attribute source_expr string
              | SX_Subscript source_expr source_expr
              | SX_Unary source_const_unary source_expr
              | SX_Binary source_const_binary source_expr source_expr
              | SX_Compare source_const_compare source_expr source_expr
              | SX_Boolean source_const_boolean (source_expr list)
              | SX_List (source_expr list)
              | SX_Tuple (source_expr list)
              | SX_Dict ((source_expr # source_expr) list)
              | SX_Call source_expr (source_expr list) ((string # source_expr) list)
              | SX_ExtCall source_expr
              | SX_StaticCall source_expr
              | SX_IfExp source_expr source_expr source_expr
              | SX_NamedExpr source_expr source_expr
              | SX_Ellipsis
End

Datatype:
  source_arg = SourceArg string (source_const_annotation option)
End

(* For ranges the ENTIRE iterator Call is retained: arguments, bound keyword,
   order, and dynamic endpoints. No detached numeric bound is imported. *)
Datatype:
  source_stmt = SS_Pass | SS_Break | SS_Continue
              | SS_Expr source_expr
              | SS_Return (source_expr option)
              | SS_Raise (source_expr option)
              | SS_Assert source_expr (source_expr option)
              | SS_Log source_expr
              | SS_Assign source_expr source_expr
              | SS_AnnAssign string source_const_annotation (source_expr option)
              | SS_AugAssign source_expr source_const_binary source_expr
              | SS_If source_expr (source_stmt list) (source_stmt list)
              | SS_For string source_const_annotation source_expr (source_stmt list)
End

(* Import syntax is retained independently of compiler import_infos. Identity
   resolution must validate the separate provenance/import claims later. *)
Datatype:
  source_import = SI_Import string (string option)
                | SI_FromImport string num string (string option)
End

Datatype:
  source_decl = SD_Variable string source_const_annotation (source_expr option)
              | SD_Function string (source_expr list) (source_arg list)
                  (source_expr list) (source_const_annotation option) (source_stmt list)
              | SD_Struct string (source_arg list)
              | SD_Event string (source_arg list)
              | SD_Interface string (source_decl list)
              | SD_Flag string (string list)
              | SD_Import (source_import list)
              | SD_Exports source_expr
              | SD_Initializes source_expr
              | SD_Uses source_expr
              | SD_Implements source_expr
End

Datatype:
  source_module = SourceModule (source_decl list)
End

Datatype:
  source_program = SourceProgram source_module (source_module list)
End

(* Candidate extraction is formal, not an ML evaluator. It does NOT resolve
   builtin identity, accept source typing, or turn unknown syntax into a value.
   General attributes retain their receiver; only actual name paths become
   SCE_Name. Explicit unsupported nodes keep all child candidates. *)
Definition source_constant_candidate_def:
  (source_constant_candidate (SX_Literal lit) = SCE_Literal lit) /\
  (source_constant_candidate (SX_Name n) = SCE_Name [n]) /\
  (source_constant_candidate (SX_Attribute e n) =
     case source_constant_candidate e of
       SCE_Name path => SCE_Name (path ++ [n])
     | child => SCE_Unsupported "attribute" [child]) /\
  (source_constant_candidate (SX_Subscript e i) =
     SCE_Subscript (source_constant_candidate e) (source_constant_candidate i)) /\
  (source_constant_candidate (SX_Unary oper e) =
     SCE_Unary oper (source_constant_candidate e)) /\
  (source_constant_candidate (SX_Binary oper l r) =
     SCE_Binary oper (source_constant_candidate l) (source_constant_candidate r)) /\
  (source_constant_candidate (SX_Compare oper l r) =
     SCE_Compare oper (source_constant_candidate l) (source_constant_candidate r)) /\
  (source_constant_candidate (SX_Boolean oper es) =
     SCE_Boolean oper (MAP source_constant_candidate es)) /\
  (source_constant_candidate (SX_List es) = SCE_List (MAP source_constant_candidate es)) /\
  (source_constant_candidate (SX_Tuple es) = SCE_Tuple (MAP source_constant_candidate es)) /\
  (source_constant_candidate (SX_Dict entries) = SCE_Unsupported "dict"
     (FLAT (MAP (\(k,v). [source_constant_candidate k; source_constant_candidate v]) entries))) /\
  (source_constant_candidate (SX_Call callee args kwargs) =
     SCE_Call (source_constant_candidate callee) (MAP source_constant_candidate args)
       (MAP (\(k,v). (k,source_constant_candidate v)) kwargs)) /\
  (source_constant_candidate (SX_ExtCall e) =
     SCE_Unsupported "extcall" [source_constant_candidate e]) /\
  (source_constant_candidate (SX_StaticCall e) =
     SCE_Unsupported "staticcall" [source_constant_candidate e]) /\
  (source_constant_candidate (SX_IfExp c t e) = SCE_Unsupported "ifexp"
     [source_constant_candidate c; source_constant_candidate t; source_constant_candidate e]) /\
  (source_constant_candidate (SX_NamedExpr target value) = SCE_Unsupported "namedexpr"
     [source_constant_candidate target; source_constant_candidate value]) /\
  (source_constant_candidate SX_Ellipsis = SCE_Unsupported "ellipsis" [])
End

(* Keep immutable originals beside ANY executable payload. Structural consumers
   must use retained_source, never the rewritten executable. Provenance remains
   with the decoding artifact in ML and is not a semantic source identity. *)
Datatype:
  source_retained = SourceRetained source_program 'a
End

Definition retained_source_def:
  retained_source (SourceRetained original executable) = original
End

Definition retained_executable_def:
  retained_executable (SourceRetained original executable) = executable
End

Definition replace_source_executable_def:
  replace_source_executable executable (SourceRetained original previous) =
    SourceRetained original executable
End

Definition source_module_declarations_def:
  source_module_declarations (SourceModule declarations) = declarations
End

Definition source_module_imports_def:
  source_module_imports (SourceModule declarations) =
    FILTER (\d. case d of SD_Import _ => T | _ => F) declarations
End

Definition source_default_syntax_def:
  source_default_syntax (SourceModule declarations) =
    FLAT (MAP (\d. case d of
      SD_Function name decorators args defaults returns body => [(name,defaults)]
      | _ => []) declarations)
End

Definition source_structural_imports_def:
  source_structural_imports retained =
    case retained_source retained of SourceProgram main imports =>
      MAP source_module_imports (main::imports)
End

Definition source_structural_defaults_def:
  source_structural_defaults retained =
    case retained_source retained of SourceProgram main imports =>
      MAP source_default_syntax (main::imports)
End

Theorem replace_source_executable_preserves_original:
  retained_source (replace_source_executable executable retained) =
  retained_source retained
Proof
  Cases_on `retained` >> simp[replace_source_executable_def, retained_source_def]
QED

Theorem source_structural_consumers_keep_original:
  source_structural_imports (replace_source_executable executable retained) =
    source_structural_imports retained /\
  source_structural_defaults (replace_source_executable executable retained) =
    source_structural_defaults retained
Proof
  simp[source_structural_imports_def, source_structural_defaults_def,
       replace_source_executable_preserves_original]
QED
