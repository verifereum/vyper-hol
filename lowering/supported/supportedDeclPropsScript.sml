(* Permanent plain-EVAL contracts for PLAN 5.6 declaration headers/lookups.
   Header acceptance is deliberately NOT body or program acceptance. *)
Theory supportedDeclProps
Ancestors
  supportedDecls supportedTypes vyperAST list

Definition supported_test_declarations_def:
  supported_test_declarations =
    [StructDecl "S" [("a", BaseT (UintT 256)); ("b", BaseT (IntT 256))];
     VariableDecl Private Storage "number" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "array" (ArrayT (BaseT (IntT 256)) (Fixed 2)) (SOME 1);
     VariableDecl Private Storage "items" (ArrayT (BaseT (UintT 256)) (Dynamic 4)) (SOME 3);
     VariableDecl Private Storage "record" (StructT (NONE, "S")) (SOME 8);
     VariableDecl Private Transient "scratch" (BaseT (BytesT (Fixed 32))) (SOME 0);
     HashMapDecl Private F "map" (BaseT AddressT) (Type (BaseT (UintT 256))) (SOME 10);
     EventDecl "Notice" [(("sender", BaseT AddressT), T);
                         (("message", BaseT (StringT 16)), F)];
     InterfaceDecl "I" [("remote", [("n", BaseT (UintT 256))], BaseT BoolT, View)];
     FunctionDecl External View F F "read" [("x", BaseT (UintT 8))] []
       (TupleT [BaseT BoolT; BaseT (StringT 16)]) [];
     FunctionDecl Internal Pure F F "helper" [] [] NoneT [];
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [];
     FunctionDecl External Payable F F "__default__" [] [] NoneT []]
End

Theorem supported_declaration_headers_accept:
  supported_declaration_headers supported_test_declarations
Proof
  EVAL_TAC
QED

Theorem supported_function_flags_defaults_reject:
  ~supported_declaration_header []
    (FunctionDecl External View T F "f" [] [] NoneT []) /\
  ~supported_declaration_header []
    (FunctionDecl Internal Pure F T "f" [] [] NoneT []) /\
  ~supported_declaration_header []
    (FunctionDecl External View F F "f" [("x", BaseT BoolT)]
      [Literal (BaseT BoolT) (BoolL T)] NoneT [])
Proof
  EVAL_TAC
QED

Theorem supported_function_types_reject:
  ~supported_declaration_header []
    (FunctionDecl External View F F "f" [("x", BaseT (BytesT (Fixed 20)))] [] NoneT []) /\
  ~supported_declaration_header []
    (FunctionDecl Internal Pure F F "f" [("x", NoneT)] [] NoneT []) /\
  ~supported_declaration_header []
    (FunctionDecl Deploy Payable F F "f" [] [] (TupleT []) [])
Proof
  EVAL_TAC
QED

Theorem supported_storage_declarations_reject:
  EVERY (\top. ~supported_declaration_header [] top)
    [VariableDecl Public Storage "x" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "x" (BaseT (UintT 256)) NONE;
     VariableDecl Private Transient "x" (BaseT (UintT 256)) NONE;
     VariableDecl Private Immutable "x" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private (Constant (Literal (BaseT BoolT) (BoolL T)))
       "x" (BaseT BoolT) NONE;
     VariableDecl Private Storage "x" (BaseT (UintT 8)) (SOME 0);
     VariableDecl Private Storage "x" (BaseT (StringT 16)) (SOME 0);
     VariableDecl Private Storage "x" (BaseT (BytesT (Dynamic 16))) (SOME 0);
     VariableDecl Private Storage "x" (ArrayT (BaseT (UintT 256)) (Fixed 0)) (SOME 0);
     VariableDecl Private Transient "x" (ArrayT (BaseT (UintT 256)) (Dynamic 4)) (SOME 0)]
Proof
  EVAL_TAC
QED

Theorem supported_hashmap_declarations_reject:
  EVERY (\top. ~supported_declaration_header [] top)
    [HashMapDecl Public F "m" (BaseT BoolT) (Type (BaseT (UintT 256))) (SOME 0);
     HashMapDecl Private F "m" (BaseT BoolT) (Type (BaseT (UintT 256))) NONE;
     HashMapDecl Private T "m" (BaseT BoolT) (Type (BaseT (UintT 256))) (SOME 0);
     HashMapDecl Private F "m" (BaseT (BytesT (Fixed 32)))
       (Type (BaseT (UintT 256))) (SOME 0);
     HashMapDecl Private F "m" (BaseT DecimalT) (Type (BaseT (UintT 256))) (SOME 0);
     HashMapDecl Private F "m" (BaseT AddressT) (Type (BaseT BoolT)) (SOME 0);
     HashMapDecl Private F "m" (BaseT AddressT)
       (Type (ArrayT (BaseT (UintT 256)) (Fixed 1))) (SOME 0);
     HashMapDecl Private F "m" (BaseT AddressT)
       (HashMapT (BaseT BoolT) (Type (BaseT (UintT 256)))) (SOME 0)]
Proof
  EVAL_TAC
QED

Theorem supported_type_declarations_contract:
  supported_declaration_header [] (StructDecl "S" [("s", BaseT (StringT 16))]) /\
  supported_declaration_header []
    (InterfaceDecl "I" [("f", [("s", BaseT (StringT 16))], NoneT, Nonpayable)]) /\
  EVERY (\top. ~supported_declaration_header [] top)
    [FlagDecl "F" ["A"; "B"];
     StructDecl "S" [("bad", BaseT (BytesT (Fixed 20)))];
     InterfaceDecl "I" [("f", [("bad", TupleT [])], NoneT, View)];
     InterfaceDecl "I" [("f", [], FlagT (NONE, "F"), View)]]
Proof
  EVAL_TAC
QED

Theorem supported_event_fields_contract:
  supported_declaration_header []
    (EventDecl "E" [(("bytes", BaseT (BytesT (Fixed 16))), T);
                    (("string", BaseT (StringT 16)), F);
                    (("data", BaseT (BytesT (Dynamic 16))), F)]) /\
  EVERY (\top. ~supported_declaration_header [] top)
    [EventDecl "E" [(("address_like", BaseT (BytesT (Fixed 20))), T)];
     EventDecl "E" [(("pair", TupleT [BaseT BoolT]), T)];
     EventDecl "E" [(("array", ArrayT (BaseT (UintT 256)) (Fixed 1)), F)]]
Proof
  EVAL_TAC
QED

Theorem supported_declaration_namespace_reject:
  ~supported_declaration_header supported_test_declarations
    (VariableDecl Private Storage "x" (StructT (SOME 0, "S")) (SOME 20)) /\
  ~supported_declaration_header supported_test_declarations
    (FunctionDecl External View F F "f" [("x", StructT (SOME 0, "S"))] [] NoneT [])
Proof
  EVAL_TAC
QED

Theorem supported_declaration_lookups_accept:
  supported_variable_decl supported_test_declarations (NONE, "items") =
    SOME (Private, Storage, ArrayT (BaseT (UintT 256)) (Dynamic 4), SOME 3) /\
  supported_hashmap_decl supported_test_declarations (NONE, "map") =
    SOME (Private, F, BaseT AddressT, Type (BaseT (UintT 256)), SOME 10) /\
  supported_function_decl supported_test_declarations (NONE, "helper") Internal =
    SOME (Pure, F, F, [], [], NoneT, []) /\
  supported_event_fields supported_test_declarations (NONE, "Notice") =
    SOME [(("sender", BaseT AddressT), T); (("message", BaseT (StringT 16)), F)]
Proof
  EVAL_TAC
QED

Theorem supported_declaration_lookups_reject:
  supported_variable_decl supported_test_declarations (NONE, "missing") = NONE /\
  supported_hashmap_decl supported_test_declarations (NONE, "items") = NONE /\
  supported_function_decl supported_test_declarations (NONE, "helper") External = NONE /\
  supported_event_fields supported_test_declarations (NONE, "read") = NONE /\
  supported_variable_decl supported_test_declarations (SOME 0, "items") = NONE /\
  supported_hashmap_decl supported_test_declarations (SOME 0, "map") = NONE /\
  supported_function_decl supported_test_declarations (SOME 0, "helper") Internal = NONE /\
  supported_event_fields supported_test_declarations (SOME 0, "Notice") = NONE
Proof
  EVAL_TAC
QED

Theorem supported_declaration_lookups_first_match:
  supported_variable_decl
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 1);
     VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 2)] (NONE, "x") =
    SOME (Private, Storage, BaseT (UintT 256), SOME 1) /\
  supported_hashmap_decl
    [HashMapDecl Private F "m" (BaseT BoolT) (Type (BaseT (UintT 256))) (SOME 1);
     HashMapDecl Private F "m" (BaseT BoolT) (Type (BaseT (UintT 256))) (SOME 2)]
    (NONE, "m") = SOME (Private, F, BaseT BoolT, Type (BaseT (UintT 256)), SOME 1) /\
  supported_event_fields [EventDecl "E" [(("first", BaseT BoolT), F)]; EventDecl "E" []]
    (NONE, "E") = SOME [(("first", BaseT BoolT), F)]
Proof
  EVAL_TAC
QED

Theorem supported_interface_resolution_accept:
  supported_interface_method supported_test_declarations "remote" =
    SOME (T, [("n", BaseT (UintT 256))], BaseT BoolT, View) /\
  supported_external_call_signature supported_test_declarations "remote" [BaseT (UintT 256)] /\
  ~supported_external_call_signature supported_test_declarations "remote" [BaseT BoolT] /\
  ~supported_external_call_signature supported_test_declarations "read" [BaseT (UintT 8)] /\
  ~supported_external_call_signature supported_test_declarations "missing" []
Proof
  EVAL_TAC
QED

Theorem supported_interface_resolution_order_contract:
  ~supported_external_call_signature
    [FunctionDecl External View F F "f" [("x", BaseT BoolT)] [] NoneT [];
     InterfaceDecl "I" [("f", [("x", BaseT BoolT)], NoneT, View)]] "f" [BaseT BoolT] /\
  supported_external_call_signature
    [InterfaceDecl "I" [("f", [("x", BaseT BoolT)], NoneT, View)];
     FunctionDecl External View F F "f" [("x", BaseT BoolT)] [] NoneT []] "f" [BaseT BoolT] /\
  supported_external_call_signature
    [InterfaceDecl "Empty" [];
     FunctionDecl Internal View F F "f" [] [] NoneT [];
     InterfaceDecl "I" [("f", [("x", BaseT BoolT)], NoneT, View);
                         ("f", [("x", BaseT AddressT)], NoneT, View)]] "f" [BaseT BoolT] /\
  ~supported_external_call_signature
    [InterfaceDecl "First" [("f", [("x", BaseT AddressT)], NoneT, View)];
     InterfaceDecl "Second" [("f", [("x", BaseT BoolT)], NoneT, View)]] "f" [BaseT BoolT]
Proof
  EVAL_TAC
QED
