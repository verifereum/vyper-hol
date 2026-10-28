(* Permanent plain-EVAL contracts for PLAN 5.6 names and real selectors. *)
Theory supportedNameProps
Ancestors
  supportedNames supportedDecls supportedTypes supportedDeclProps
  compileVyper vyperContext vyperAST list finite_map

Theorem supported_bindings_accept:
  supported_function_bindings supported_test_declarations
    [("arg", BaseT BoolT); ("second", BaseT (UintT 256))]
    ["local"; "other_branch"] ["i"; "j"] /\
  supported_function_bindings [] [] [] []
Proof
  EVAL_TAC
QED

Theorem supported_binding_duplicates_reject:
  ~supported_function_bindings [] [("x", BaseT BoolT); ("x", BaseT AddressT)] [] [] /\
  ~supported_function_bindings [] [] ["x"; "x"] [] /\
  ~supported_function_bindings [] [] [] ["i"; "i"] /\
  ~supported_function_bindings [] [("x", BaseT BoolT)] ["x"] [] /\
  ~supported_function_bindings [] [("i", BaseT BoolT)] [] ["i"] /\
  ~supported_function_bindings [] [] ["i"] ["i"]
Proof
  EVAL_TAC
QED

(* The return PC and return buffer live in dedicated compile_env fields, so
   their Python attribute names are ordinary user identifiers (#557, a04-04). *)
Theorem supported_compiler_slot_names_accept:
  supported_function_bindings [] [("__return_buf__", BaseT BoolT)] [] [] /\
  supported_function_bindings [] [("__return_pc__", BaseT BoolT)] [] [] /\
  supported_function_bindings [] [] ["__return_buf__"] [] /\
  supported_function_bindings [] [] ["__return_pc__"] [] /\
  supported_function_bindings [] [] [] ["__return_buf__"] /\
  supported_function_bindings [] [] [] ["__return_pc__"]
Proof
  EVAL_TAC
QED

(* Module variables are keyed "self." ++ name in compile_env, so locals may
   shadow them as in Python Vyper (#557, a04-03). *)
Theorem supported_module_binding_shadowing_accept:
  supported_function_bindings supported_test_declarations
    [("number", BaseT (UintT 256))] [] [] /\
  supported_function_bindings supported_test_declarations [] ["scratch"] [] /\
  supported_function_bindings supported_test_declarations [] [] ["items"] /\
  supported_function_bindings supported_test_declarations [("map", BaseT BoolT)] [] [] /\
  supported_function_bindings supported_test_declarations [] ["map"] [] /\
  supported_function_bindings supported_test_declarations [] [] ["map"] /\
  supported_declaration_names
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External View F F "f" [("x", BaseT BoolT)] [] NoneT []]
Proof
  EVAL_TAC
QED

Theorem supported_dotted_binding_reject:
  ~supported_function_bindings [] [("self.x", BaseT BoolT)] [] [] /\
  ~supported_function_bindings [] [] ["self.x"] [] /\
  ~supported_function_bindings [] [] [] ["self.x"]
Proof
  EVAL_TAC
QED

Theorem supported_fallback_header_names_contract:
  supported_function_header_names []
    (FunctionDecl External Payable F F "__default__" [] [] NoneT []) /\
  ~supported_function_header_names []
    (FunctionDecl External Payable F F "__default__" [("x", BaseT BoolT)] [] NoneT []) /\
  ~supported_function_header_names []
    (FunctionDecl Internal Pure F F "__default__" [("x", BaseT BoolT)] [] NoneT [])
Proof
  EVAL_TAC
QED

Theorem supported_function_header_names_contract:
  supported_function_header_names []
    (FunctionDecl External View F F "revert" [] [] NoneT []) /\
  supported_function_header_names []
    (FunctionDecl Internal Pure F F "revert" [] [] NoneT []) /\
  supported_function_header_names []
    (FunctionDecl External View F F "f" [("__return_pc__", BaseT BoolT)] [] NoneT []) /\
  supported_function_header_names []
    (FunctionDecl Deploy Payable F F "__init__" [("__return_buf__", BaseT BoolT)] [] NoneT [])
Proof
  EVAL_TAC
QED

Theorem supported_struct_module_collisions_contract:
  supported_declaration_names
    [VariableDecl Private Storage "number" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Transient "scratch" (BaseT (UintT 256)) (SOME 1);
     HashMapDecl Private F "map" (BaseT AddressT)
       (Type (BaseT (UintT 256))) (SOME 2);
     StructDecl "Fields" [("number", BaseT (UintT 256));
       ("scratch", BaseT (UintT 256)); ("map", BaseT (UintT 256))]]
Proof
  EVAL_TAC
QED

Theorem supported_function_name_duplicates_reject:
  ~supported_declaration_names
    [FunctionDecl External View F F "f" [] [] NoneT [];
     FunctionDecl Internal Pure F F "f" [] [] NoneT []] /\
  ~supported_declaration_names
    [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [];
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT []]
Proof
  EVAL_TAC
QED

Theorem supported_event_name_duplicates_reject:
  ~supported_declaration_names
    [EventDecl "E" [(("a", BaseT BoolT), F)]; EventDecl "E" []]
Proof
  EVAL_TAC
QED

(* Internal labels are compiler-generated, so user function names no longer
   need to avoid the compiler's label spellings. *)
Theorem supported_internal_label_names_accept:
  supported_declaration_names
    [FunctionDecl Internal Pure F F "return_label_42" [] [] NoneT [];
     FunctionDecl Internal Pure F F "revert" [] [] NoneT [];
     FunctionDecl Internal Pure F F "code_end" [] [] NoneT [];
     FunctionDecl Internal Pure F F "reachable_0" [] [] NoneT []]
Proof
  EVAL_TAC
QED

Theorem supported_declaration_name_checks_reject:
  ~supported_declaration_names
    [FunctionDecl External Payable F F "__default__" [("x", BaseT BoolT)] [] NoneT []]
Proof
  EVAL_TAC
QED

Theorem supported_empty_headers_names_accept:
  supported_declaration_headers [] /\ supported_declaration_names []
Proof
  EVAL_TAC
QED

Theorem supported_declaration_names_accept:
  supported_declaration_names supported_test_declarations
Proof
  EVAL_TAC
QED

(* Classification is the actual dispatcher classification, with fallback,
   internal and deploy declarations absent from the selector table. *)
Theorem supported_selector_domain_contract:
  FST (classify_functions
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [];
     FunctionDecl Internal Pure F F "helper" [] [] NoneT [];
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [];
     FunctionDecl External View F F "f" [("x", BaseT BoolT)] [] NoneT []]) =
    [(View, F, F, "f", [("x", BaseT BoolT)], [], NoneT, [])] /\
  supported_selectors_distinct
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [];
     FunctionDecl Internal Pure F F "helper" [] [] NoneT [];
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT []]
Proof
  EVAL_TAC
QED

(* General contract: even distinct function names are rejected exactly when
   their actual 4-byte selectors coincide. No expensive hash needs to be
   recomputed to prove this structural fact. Concrete predicates remain EVAL
   computable; two full Keccak computations can exceed the 10s tactic limit. *)
Theorem supported_selector_pair_contract:
  name1 <> "__default__" /\ name2 <> "__default__" ==>
  (supported_selectors_distinct
    [FunctionDecl External mut1 nr1 rr1 name1 args1 defaults1 ret1 stmts1;
     FunctionDecl External mut2 nr2 rr2 name2 args2 defaults2 ret2 stmts2] <=>
   FST (compute_selector FEMPTY name1 (MAP SND args1)) <>
   FST (compute_selector FEMPTY name2 (MAP SND args2)))
Proof
  simp[supported_selectors_distinct_def, classify_functions_def,
       classify_function_def, type_env_def, type_env_for_module_def,
       build_selectors_def]
QED

Theorem supported_selector_duplicates_reject:
  ~supported_selectors_distinct
    [FunctionDecl External View F F "f" [] [] NoneT [];
     FunctionDecl External Pure F F "f" [] [] NoneT [Pass]]
Proof
  simp[supported_selector_pair_contract]
QED
