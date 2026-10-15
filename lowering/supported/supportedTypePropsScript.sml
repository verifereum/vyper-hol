(* Permanent plain-EVAL contracts for every PLAN 5.6 type class. *)
Theory supportedTypeProps
Ancestors
  supportedTypes vyperAST list arithmetic

Theorem supported_integer_widths_accept:
  EVERY (\n. supported_word_type (BaseT (UintT n)) /\
             supported_word_type (BaseT (IntT n)))
    (GENLIST (\i. 8 * (i + 1)) 32)
Proof
  EVAL_TAC
QED

Theorem supported_integer_widths_reject:
  EVERY (\n. ~supported_word_type (BaseT (UintT n)) /\
             ~supported_word_type (BaseT (IntT n)))
    [0; 1; 7; 9; 134; 255; 257; 264]
Proof
  EVAL_TAC
QED

Theorem supported_bytes_widths_accept:
  EVERY (\n. supported_word_type (BaseT (BytesT (Fixed n))))
    (FILTER (\n. n <> 20) (GENLIST (\i. i + 1) 32))
Proof
  EVAL_TAC
QED

Theorem supported_bytes_widths_reject:
  EVERY (\n. ~supported_word_type (BaseT (BytesT (Fixed n)))) [0; 20; 33]
Proof
  EVAL_TAC
QED

Theorem supported_scalar_classes_accept:
  EVERY supported_word_type [BaseT BoolT; BaseT DecimalT; BaseT AddressT] /\
  EVERY supported_full_word_type
    [BaseT (UintT 256); BaseT (IntT 256); BaseT (BytesT (Fixed 32))] /\
  EVERY supported_string_type
    [BaseT (StringT 0); BaseT (StringT 96);
     BaseT (BytesT (Dynamic 0)); BaseT (BytesT (Dynamic 96))]
Proof
  EVAL_TAC
QED

Theorem supported_scalar_classes_do_not_overlap:
  ~supported_string_type (BaseT (BytesT (Fixed 32))) /\
  ~supported_word_type (BaseT (BytesT (Dynamic 32))) /\
  ~supported_full_word_type (BaseT (UintT 248)) /\
  ~supported_full_word_type (BaseT (IntT 248)) /\
  ~supported_full_word_type (BaseT BoolT) /\
  ~supported_full_word_type (BaseT DecimalT) /\
  ~supported_full_word_type (BaseT AddressT) /\
  ~supported_full_word_type (BaseT (BytesT (Fixed 31)))
Proof
  EVAL_TAC
QED

Theorem supported_value_shapes_accept:
  EVERY (supported_value_type [])
    [BaseT BoolT; BaseT (StringT 16); BaseT (BytesT (Dynamic 16));
     TupleT [BaseT (UintT 8)];
     TupleT [BaseT (UintT 256); BaseT (StringT 16); BaseT (BytesT (Dynamic 16))];
     ArrayT (BaseT (IntT 8)) (Fixed 1);
     ArrayT (BaseT (IntT 8)) (Dynamic 0);
     ArrayT (BaseT (UintT 256)) (Dynamic 4)]
Proof
  EVAL_TAC
QED

Theorem supported_value_depth_reject:
  EVERY (\ty. ~supported_value_type [] ty)
    [NoneT; FlagT (NONE, "Flags"); StructT (NONE, "Missing"); TupleT [];
     TupleT [TupleT [BaseT BoolT]];
     TupleT [ArrayT (BaseT (UintT 256)) (Fixed 1)];
     ArrayT (BaseT BoolT) (Fixed 0);
     ArrayT (BaseT (StringT 16)) (Fixed 1);
     ArrayT (BaseT (BytesT (Dynamic 16))) (Dynamic 2);
     ArrayT (TupleT [BaseT BoolT]) (Dynamic 2);
     ArrayT (ArrayT (BaseT BoolT) (Fixed 1)) (Fixed 1)]
Proof
  EVAL_TAC
QED

Theorem supported_storage_shapes_accept:
  EVERY (supported_storage_type [])
    [BaseT (UintT 256); BaseT (IntT 256); BaseT (BytesT (Fixed 32));
     ArrayT (BaseT (UintT 256)) (Fixed 1);
     ArrayT (BaseT (IntT 256)) (Dynamic 0);
     ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4)]
Proof
  EVAL_TAC
QED

Theorem supported_storage_shapes_reject:
  EVERY (\ty. ~supported_storage_type [] ty)
    [BaseT (UintT 8); BaseT (IntT 8); BaseT BoolT; BaseT DecimalT;
     BaseT AddressT; BaseT (BytesT (Fixed 16));
     BaseT (StringT 16); BaseT (BytesT (Dynamic 16));
     ArrayT (BaseT (UintT 256)) (Fixed 0);
     ArrayT (BaseT (UintT 8)) (Dynamic 4);
     ArrayT (ArrayT (BaseT (IntT 256)) (Fixed 1)) (Dynamic 4);
     TupleT [BaseT (UintT 256)]; NoneT; FlagT (NONE, "Flags")]
Proof
  EVAL_TAC
QED

Definition supported_test_structs_def:
  supported_test_structs =
    [StructDecl "Word" [("small", BaseT (UintT 8)); ("ok", BaseT BoolT)];
     StructDecl "Full" [("number", BaseT (UintT 256));
                        ("bytes", BaseT (BytesT (Fixed 32)))];
     StructDecl "String" [("text", BaseT (StringT 16))];
     StructDecl "Tuple" [("pair", TupleT [BaseT BoolT])];
     StructDecl "Nested" [("record", StructT (NONE, "Full"))]]
End

Theorem supported_struct_depth_contract:
  supported_value_type supported_test_structs (StructT (NONE, "Word")) /\
  supported_value_type supported_test_structs (StructT (NONE, "Full")) /\
  supported_storage_type supported_test_structs (StructT (NONE, "Full")) /\
  ~supported_storage_type supported_test_structs (StructT (NONE, "Word")) /\
  EVERY (\s. ~supported_value_type supported_test_structs (StructT (NONE, s)) /\
              ~supported_storage_type supported_test_structs (StructT (NONE, s)))
    ["String"; "Tuple"; "Nested"; "Missing"] /\
  ~supported_value_type supported_test_structs (StructT (SOME 0, "Full")) /\
  ~supported_storage_type supported_test_structs (StructT (SOME 0, "Full")) /\
  ~supported_value_type supported_test_structs (TupleT [StructT (NONE, "Full")])
Proof
  EVAL_TAC
QED

Theorem supported_struct_lookup_first_type_wins:
  supported_struct_fields
    [StructDecl "S" [("first", BaseT BoolT)]; StructDecl "S" []]
    (NONE, "S") = SOME [("first", BaseT BoolT)] /\
  supported_struct_fields [InterfaceDecl "S" []; StructDecl "S" []]
    (NONE, "S") = NONE /\
  supported_struct_fields [FlagDecl "S" []; StructDecl "S" []]
    (NONE, "S") = NONE
Proof
  EVAL_TAC
QED

Theorem supported_hashmap_keys_contract:
  EVERY supported_hashmap_key_type
    [BaseT (UintT 8); BaseT (IntT 256); BaseT BoolT; BaseT AddressT] /\
  EVERY (\ty. ~supported_hashmap_key_type ty)
    [BaseT (UintT 9); BaseT DecimalT; BaseT (BytesT (Fixed 32));
     BaseT (BytesT (Dynamic 32)); BaseT (StringT 32);
     TupleT [BaseT (UintT 256)]]
Proof
  EVAL_TAC
QED

Theorem supported_return_none_is_not_a_value:
  supported_return_type [] NoneT /\ ~supported_value_type [] NoneT
Proof
  EVAL_TAC
QED

Theorem supported_namespace_contract:
  supported_main_nsid (NONE, "x") /\
  ~supported_main_nsid (SOME 0, "x") /\
  ~supported_main_nsid (SOME 1, "x")
Proof
  EVAL_TAC
QED
