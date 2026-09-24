(*
 * Compiler subset fixtures for supported storage and transient state access.
 *)

Theory evalCompilerSubsetState
Ancestors evalCompiler

Definition storage_scalar_loop_program_def:
  storage_scalar_loop_program =
    [VariableDecl Private Storage "counter" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "set_add_in_loop"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "counter")))
          (Name (BaseT (UintT 256)) "x");
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [AugAssign (BaseT (UintT 256))
             (TopLevelNameTarget (NONE, "counter")) Add
             (Name (BaseT (UintT 256)) "i")];
        Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "counter")))]]
End

Definition storage_array_program_def:
  storage_array_program =
    [VariableDecl Private Storage "anchor" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "values"
       (ArrayT (BaseT (UintT 256)) (Fixed 3)) (SOME 1);
     FunctionDecl External Nonpayable F F "set_and_get"
       [("i", BaseT (UintT 256)); ("x", BaseT (UintT 256))]
       ([] : expr list) (BaseT (UintT 256))
       [Assign
          (BaseTarget
            (SubscriptTarget (TopLevelNameTarget (NONE, "values"))
              (Name (BaseT (UintT 256)) "i")))
          (Name (BaseT (UintT 256)) "x");
        Return (SOME
          (Subscript (BaseT (UintT 256))
            (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 3))
              (NONE, "values"))
            (Name (BaseT (UintT 256)) "i")))]]
End

Definition storage_dynarray_program_def:
  storage_dynarray_program =
    [VariableDecl Private Storage "anchor" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "items"
       (ArrayT (BaseT (UintT 256)) (Dynamic 4)) (SOME 1);
     FunctionDecl External Nonpayable F F "append_write_pop"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Append (TopLevelNameTarget (NONE, "items"))
          (Name (BaseT (UintT 256)) "x");
        Assign
          (BaseTarget
            (SubscriptTarget (TopLevelNameTarget (NONE, "items"))
              (Literal (BaseT (IntT 8)) (IntL 0))))
          (Name (BaseT (UintT 256)) "x");
        Return (SOME
          (Pop (BaseT (UintT 256))
            (TopLevelNameTarget (NONE, "items"))))]]
End

Definition storage_mapping_program_def:
  storage_mapping_program =
    [VariableDecl Private Storage "anchor" (BaseT (UintT 256)) (SOME 0);
     HashMapDecl Private F "balances" (BaseT AddressT)
       (Type (BaseT (UintT 256))) (SOME 1);
     FunctionDecl External Nonpayable F F "set_and_get"
       [("owner", BaseT AddressT); ("x", BaseT (UintT 256))]
       ([] : expr list) (BaseT (UintT 256))
       [Assign
          (BaseTarget
            (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
              (Name (BaseT AddressT) "owner")))
          (Name (BaseT (UintT 256)) "x");
        Return (SOME
          (Subscript (BaseT (UintT 256))
            (TopLevelName NoneT (NONE, "balances"))
            (Name (BaseT AddressT) "owner")))]]
End

Definition storage_struct_program_def:
  storage_struct_program =
    [StructDecl "Pair"
       [("left", BaseT (UintT 256)); ("right", BaseT (UintT 256))];
     VariableDecl Private Storage "anchor" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Storage "pair" (StructT (NONE, "Pair")) (SOME 1);
     FunctionDecl External Nonpayable F F "set_and_get"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign
          (BaseTarget
            (AttributeTarget (TopLevelNameTarget (NONE, "pair")) "left"))
          (Name (BaseT (UintT 256)) "x");
        Return (SOME
          (Attribute (BaseT (UintT 256))
            (TopLevelName (StructT (NONE, "Pair")) (NONE, "pair"))
            "left"))]]
End

Definition transient_scalar_program_def:
  transient_scalar_program =
    [VariableDecl Private Storage "anchor" (BaseT (UintT 256)) (SOME 0);
     VariableDecl Private Transient "scratch" (BaseT (UintT 256)) (SOME 1);
     FunctionDecl External Nonpayable F F "set_add_read"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "scratch")))
          (Name (BaseT (UintT 256)) "x");
        AugAssign (BaseT (UintT 256))
          (TopLevelNameTarget (NONE, "scratch")) Add
          (Literal (BaseT (UintT 256)) (IntL 1));
        Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "scratch")))]]
End
