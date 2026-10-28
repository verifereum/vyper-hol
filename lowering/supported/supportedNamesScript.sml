(* PLAN 5.6 name whitelist. TOP-LEVEL: supported_declaration_names,
   supported_function_bindings, supported_selectors_distinct.
   Helpers: supported_module_names, supported_function_names,
   supported_event_names, supported_function_header_names.
   TASK_021 supplies ALL AnnAssign and For names (including nested branches)
   to supported_function_bindings. No body traversal or body placeholder. *)
Theory supportedNames
Ancestors
  supportedDecls supportedTypes compileVyper vyperContext vyperAST
  list string pair

Definition supported_module_names_def:
  supported_module_names ([] : toplevel list) = [] /\
  supported_module_names (top :: rest) =
    (case top of
       VariableDecl vis mut name ty slot => [name]
     | HashMapDecl vis transient name kt vt slot => [name]
     | _ => []) ++ supported_module_names rest
End

Definition supported_function_names_def:
  supported_function_names ([] : toplevel list) = [] /\
  supported_function_names (top :: rest) =
    (case top of
       FunctionDecl vis mut nr rr name args defaults ret stmts => [name]
     | _ => []) ++ supported_function_names rest
End

Definition supported_event_names_def:
  supported_event_names ([] : toplevel list) = [] /\
  supported_event_names (top :: rest) =
    (case top of EventDecl name fields => [name] | _ => []) ++
    supported_event_names rest
End

(* Lists, not sets: repeated names in different branches/loops must fail.
   Concatenating catches cross-class collisions as well as duplicates.
   No binding contains "." (no Vyper identifier does), so none is a
   module_var_key ("self." ++ name) and none shadows a module variable. *)
Definition supported_function_bindings_def:
  supported_function_bindings tops (args : argument list) locals loops <=>
    ALL_DISTINCT (MAP FST args ++ locals ++ loops) /\
    EVERY (\n. ~MEM #"." n) (MAP FST args ++ locals ++ loops)
End

Definition supported_function_header_names_def:
  supported_function_header_names tops top <=>
    case top of
      FunctionDecl vis mut nr rr name args defaults ret stmts =>
        (name = "__default__" ==> NULL args) /\
        supported_function_bindings tops args [] []
    | _ => T
End

(* Use the compiler's actual table, not a second selector implementation.
   classify_functions omits External __default__, Internal and Deploy. *)
Definition supported_selectors_distinct_def:
  supported_selectors_distinct tops <=>
    ALL_DISTINCT (MAP FST
      (build_selectors (type_env tops) (FST (classify_functions tops))))
End

(* Only body-independent names. Binding checks with locals/loops still must
   be applied by TASK_021 in addition to this predicate. *)
Definition supported_declaration_names_def:
  supported_declaration_names tops <=>
    ALL_DISTINCT (supported_function_names tops) /\
    ALL_DISTINCT (supported_event_names tops) /\
    EVERY (supported_function_header_names tops) tops /\
    supported_selectors_distinct tops
End

(* ===== Consumer contracts ===== *)

Theorem supported_bindings_distinct:
  supported_function_bindings tops args locals loops ==>
    ALL_DISTINCT (MAP FST args ++ locals ++ loops)
Proof
  simp[supported_function_bindings_def]
QED

Theorem supported_fallback_no_arguments:
  supported_function_header_names tops
    (FunctionDecl vis mut nr rr "__default__" args defaults ret stmts) ==>
  args = []
Proof
  simp[supported_function_header_names_def, NULL_EQ]
QED

Theorem supported_declaration_names_unique:
  supported_declaration_names tops ==>
    ALL_DISTINCT (supported_function_names tops) /\
    ALL_DISTINCT (supported_event_names tops) /\
    supported_selectors_distinct tops
Proof
  simp[supported_declaration_names_def]
QED
