(* Prepared hand-written inputs, NOT independently validated parity fixtures.
 * Source/AST/layout correspondence remains pending; see assignment-order-pending.md.
 *)
Theory evalAssignmentOrderInputs
Ancestors evalCompiler

Definition c08_storage_arr_assign_computed_rhs_program_def:
  c08_storage_arr_assign_computed_rhs_program =
  [VariableDecl Private Storage "arr" (ArrayT (BaseT (UintT 256)) (Fixed 3)) (SOME 0);
   FunctionDecl External Nonpayable F F "f"
    [("i", BaseT (UintT 256)); ("x", BaseT (UintT 256))] [] NoneT
    [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"arr"))
      (Name (BaseT (UintT 256)) "i")))
      (Builtin (BaseT (UintT 256)) (Bop Add)
        [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 1)])]]
End

Definition c09_storage_map_assign_computed_rhs_program_def:
  c09_storage_map_assign_computed_rhs_program =
  [HashMapDecl Private F "m" (BaseT (UintT 256)) (Type (BaseT (UintT 256))) (SOME 0);
   FunctionDecl External Nonpayable F F "f"
    [("k", BaseT (UintT 256)); ("x", BaseT (UintT 256))] [] NoneT
    [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
      (Builtin (BaseT (UintT 256)) (Bop Add)
       [Name (BaseT (UintT 256)) "k"; Literal (BaseT (UintT 256)) (IntL 1)])))
      (Builtin (BaseT (UintT 256)) (Bop Mul)
        [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 2)])]]
End

Definition g6_write_order_side_program_def:
  g6_write_order_side_program =
  [VariableDecl Private Storage "a" (ArrayT (BaseT (UintT 256)) (Fixed 3)) (SOME 0);
   VariableDecl Private Storage "i" (BaseT (UintT 256)) (SOME 3);
   FunctionDecl External Nonpayable F F "f" [("x", BaseT (UintT 256))] [] NoneT
    [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
      (TopLevelName (BaseT (UintT 256)) (NONE,"i"))))
      (Builtin (BaseT (UintT 256)) (Bop Add)
       [Subscript (BaseT (UintT 256))
         (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 3)) (NONE,"a"))
         (TopLevelName (BaseT (UintT 256)) (NONE,"i"));
        Name (BaseT (UintT 256)) "x"])]]
End

Definition x04_assign_sideeffect_order_program_def:
  x04_assign_sideeffect_order_program =
  [VariableDecl Private Storage "c" (BaseT (UintT 256)) (SOME 0);
   HashMapDecl Private F "m" (BaseT (UintT 256)) (Type (BaseT (UintT 256))) (SOME 1);
   FunctionDecl Internal Nonpayable F F "inc" [] [] (BaseT (UintT 256))
    [AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"c")) Add
       (Literal (BaseT (UintT 256)) (IntL 1));
     Return (SOME (TopLevelName (BaseT (UintT 256)) (NONE,"c")))];
   FunctionDecl External Nonpayable F F "f" [] [] NoneT
    [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
      (Call (BaseT (UintT 256)) (IntCall (NONE,"inc")) [] NONE)))
      (Call (BaseT (UintT 256)) (IntCall (NONE,"inc")) [] NONE)]]
End

Definition g19_aug_rhs_modifies_target_program_def:
  g19_aug_rhs_modifies_target_program =
  [VariableDecl Private Storage "c" (BaseT (UintT 256)) (SOME 0);
   FunctionDecl Internal Nonpayable F F "inc" [] [] (BaseT (UintT 256))
    [AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"c")) Add
       (Literal (BaseT (UintT 256)) (IntL 10));
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
   FunctionDecl External Nonpayable F F "f" [] [] NoneT
    [AugAssign (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"c")) Add
      (Call (BaseT (UintT 256)) (IntCall (NONE,"inc")) [] NONE)]]
End

Definition x03_assign_elem_from_pop_program_def:
  x03_assign_elem_from_pop_program =
  [FunctionDecl External Nonpayable F F "f" [("a", BaseT (UintT 256))] [] (BaseT (UintT 256))
    [AnnAssign "d" (ArrayT (BaseT (UintT 256)) (Dynamic 3))
      (Builtin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (MakeArray NONE (Dynamic 3))
        [Name (BaseT (UintT 256)) "a"]);
     Assign (BaseTarget (SubscriptTarget (NameTarget "d")
      (Literal (BaseT (IntT 8)) (IntL 0))))
      (Pop (BaseT (UintT 256)) (NameTarget "d"));
     Return (SOME (Builtin (BaseT (UintT 256)) Len
       [Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d"]))]]
End

Definition s11_storage_map_assign_extcall_rhs_program_def:
  s11_storage_map_assign_extcall_rhs_program =
  [InterfaceDecl "I" [("g", [], BaseT (UintT 256), View)];
   HashMapDecl Private F "m" (BaseT (UintT 256)) (Type (BaseT (UintT 256))) (SOME 0);
   FunctionDecl External Nonpayable F F "f"
    [("a", BaseT AddressT); ("k", BaseT (UintT 256))] [] NoneT
    [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
      (Name (BaseT (UintT 256)) "k")))
      (Call (BaseT (UintT 256)) (ExtCall T F ("g", [], BaseT (UintT 256)))
       [Name (BaseT AddressT) "a"] NONE)]]
End

(* Type-check the intended checked-compiler entry point, without claiming
 * acceptance or comparing its output to implementation-derived bytes. *)
Definition assignment_order_checked_compilation_def:
  assignment_order_checked_compilation =
    MAP (compile_vyper (K SOME) (o1_policy all_capabilities))
     [c08_storage_arr_assign_computed_rhs_program;
      c09_storage_map_assign_computed_rhs_program; g6_write_order_side_program;
      x04_assign_sideeffect_order_program; s11_storage_map_assign_extcall_rhs_program;
      g19_aug_rhs_modifies_target_program; x03_assign_elem_from_pop_program]
End

(* Behavioral input terms available for reuse by C7.1, without duplicating
 * its interpreter result proofs. *)
Definition assign_delayed_storage_read_program_def:
  assign_delayed_storage_read_program =
    TAKE 3 x04_assign_sideeffect_order_program ++
    [FunctionDecl External Nonpayable F F "f" [] [] NoneT
      [Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
        (Call (BaseT (UintT 256)) (IntCall (NONE,"inc")) [] NONE)))
        (TopLevelName (BaseT (UintT 256)) (NONE,"c"))]]
End

Definition assign_delayed_popped_read_program_def:
  assign_delayed_popped_read_program =
  [HashMapDecl Private F "m" (BaseT (UintT 256)) (Type (BaseT (UintT 256))) (SOME 0);
   FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
    [AnnAssign "d" (ArrayT (BaseT (UintT 256)) (Dynamic 3))
      (Builtin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (MakeArray NONE (Dynamic 3))
        [Literal (BaseT (UintT 256)) (IntL 5)]);
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
        (Pop (BaseT (UintT 256)) (NameTarget "d"))))
       (Subscript (BaseT (UintT 256))
         (Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d")
         (Literal (BaseT (IntT 8)) (IntL 0)));
     Return (SOME (Subscript (BaseT (UintT 256))
       (TopLevelName NoneT (NONE,"m")) (Literal (BaseT (UintT 256)) (IntL 5))))]]
End

Definition aug_storage_shrink_program_def:
  aug_storage_shrink_program =
  [VariableDecl Private Storage "d" (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (SOME 0);
   FunctionDecl Internal Nonpayable F F "shrink" [] [] (BaseT (UintT 256))
    [Return (SOME (Pop (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"d"))))];
   FunctionDecl External Nonpayable F F "f" [] [] NoneT
    [AugAssign (BaseT (UintT 256))
      (SubscriptTarget (TopLevelNameTarget (NONE,"d"))
        (Literal (BaseT (IntT 8)) (IntL 0))) Add
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)]]
End

Definition aug_memory_shrink_program_def:
  aug_memory_shrink_program =
  [FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
    [AnnAssign "d" (ArrayT (BaseT (UintT 256)) (Dynamic 3))
      (Builtin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (MakeArray NONE (Dynamic 3))
        [Literal (BaseT (UintT 256)) (IntL 5)]);
     AugAssign (BaseT (UintT 256)) (SubscriptTarget (NameTarget "d")
        (Literal (BaseT (IntT 8)) (IntL 0))) Add
        (Pop (BaseT (UintT 256)) (NameTarget "d"));
     Return (SOME (Builtin (BaseT (UintT 256)) Len
       [Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d"]))]]
End

Definition aug_memory_shrink_append_program_def:
  aug_memory_shrink_append_program =
  [FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
    [AnnAssign "d" (ArrayT (BaseT (UintT 256)) (Dynamic 3))
      (Builtin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (MakeArray NONE (Dynamic 3))
        [Literal (BaseT (UintT 256)) (IntL 5)]);
     AugAssign (BaseT (UintT 256)) (SubscriptTarget (NameTarget "d")
        (Literal (BaseT (IntT 8)) (IntL 0))) Add
        (Pop (BaseT (UintT 256)) (NameTarget "d"));
     Append (NameTarget "d") (Literal (BaseT (UintT 256)) (IntL 7));
     Return (SOME (Subscript (BaseT (UintT 256))
       (Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d")
       (Literal (BaseT (IntT 8)) (IntL 0))))]]
End

Definition assign_nested_popped_read_program_def:
  assign_nested_popped_read_program =
  [HashMapDecl Private F "m" (BaseT (UintT 256))
     (Type (ArrayT (BaseT (UintT 256)) (Dynamic 3))) (SOME 0);
   FunctionDecl External Nonpayable F F "f" [] [] NoneT
    [AnnAssign "d" (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Dynamic 3))
      (Builtin (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Dynamic 3))
       (MakeArray NONE (Dynamic 3))
       [Builtin (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (MakeArray NONE (Dynamic 3))
        [Literal (BaseT (UintT 256)) (IntL 1); Literal (BaseT (UintT 256)) (IntL 2)]]);
     Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
       (Builtin (BaseT (UintT 256)) (Bop Add)
        [Pop (BaseT (UintT 256)) (SubscriptTarget (NameTarget "d")
          (Literal (BaseT (IntT 8)) (IntL 0)));
         Subscript (BaseT (UintT 256))
           (Pop (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (NameTarget "d"))
           (Literal (BaseT (IntT 8)) (IntL 0))])))
       (Subscript (ArrayT (BaseT (UintT 256)) (Dynamic 3))
         (Name (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Dynamic 3)) "d")
         (Literal (BaseT (IntT 8)) (IntL 0)))]]
End
