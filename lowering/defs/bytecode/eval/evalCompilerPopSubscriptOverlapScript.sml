(* A subscript of a pop() result whose index can write the popped array.
   Python's _array_element_ptr panics with "risky overlap" there
   (vyperlang/vyper#5350): the popped element lies past the array's new
   length, so the index could overwrite it before the base is read.  The
   runtime lowering rejects the same functions up front (fn_allocs_ok, through
   alloc_limits_expr's pop_subscript_overlap).
   TOP-LEVEL: pop_subscript_memory_rejected,
              pop_subscript_constant_index_ok,
              pop_subscript_storage_rejected,
              pop_subscript_storage_view_index_ok,
              pop_subscript_storage_program_rejected. *)
Theory evalCompilerPopSubscriptOverlap
Ancestors compileVyper

(* The element and array types: uint256[1] and DynArray[uint256[1], 2]. *)
Definition pop_elem_ty_def:
  pop_elem_ty = ArrayT (BaseT (UintT 256)) (Fixed 1)
End

Definition pop_array_ty_def:
  pop_array_ty = ArrayT pop_elem_ty (Dynamic 2)
End

(* @internal
   def f(x: DynArray[uint256[1], 2]) -> uint256:
       return x.pop()[idx]                                                  *)
Definition pop_subscript_memory_fn_def:
  pop_subscript_memory_fn idx =
    (Nonpayable, F, F, "f", [("x", pop_array_ty)], [] : expr list,
     BaseT (UintT 256),
     [Return (SOME (Subscript (BaseT (UintT 256))
                      (Pop pop_elem_ty (NameTarget "x")) idx))])
End

(* return x.pop()[x.pop()[0]]
   Python: risky overlap, since the index writes x, which the base reads. *)
val pop_subscript_memory_rejected_eval =
  EVAL ``fn_allocs_ok []
           (pop_subscript_memory_fn
              (Subscript (BaseT (UintT 256))
                 (Pop pop_elem_ty (NameTarget "x"))
                 (Literal (BaseT (UintT 256)) (IntL 0))))``

Theorem pop_subscript_memory_rejected:
  ¬fn_allocs_ok []
     (pop_subscript_memory_fn
        (Subscript (BaseT (UintT 256))
           (Pop pop_elem_ty (NameTarget "x"))
           (Literal (BaseT (UintT 256)) (IntL 0))))
Proof
  ACCEPT_TAC (EQF_ELIM pop_subscript_memory_rejected_eval)
QED

(* return x.pop()[0]: compiled, since the index writes nothing. *)
val pop_subscript_constant_index_ok_eval =
  EVAL ``fn_allocs_ok []
           (pop_subscript_memory_fn (Literal (BaseT (UintT 256)) (IntL 0)))``

Theorem pop_subscript_constant_index_ok:
  fn_allocs_ok []
    (pop_subscript_memory_fn (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  ACCEPT_TAC (EQT_ELIM pop_subscript_constant_index_ok_eval)
QED

(* a: DynArray[uint256[1], 2]

   @internal
   def bar() -> uint256:
       self.a.pop()            # only when writes_a
       return 0

   @external
   def f() -> uint256:
       return self.a.pop()[self.bar()]                                      *)
Definition pop_subscript_bar_def:
  pop_subscript_bar writes_a =
    FunctionDecl Internal (if writes_a then Nonpayable else View) F F "bar"
      [] [] (BaseT (UintT 256))
      ((if writes_a
        then [Expr (Pop pop_elem_ty (TopLevelNameTarget (NONE, "a")))]
        else []) ++
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))])
End

Definition pop_subscript_storage_body_def:
  pop_subscript_storage_body =
    [Return (SOME (Subscript (BaseT (UintT 256))
                     (Pop pop_elem_ty (TopLevelNameTarget (NONE, "a")))
                     (Call (BaseT (UintT 256)) (IntCall (NONE, "bar")) []
                        NONE)))]
End

Definition pop_subscript_storage_program_def:
  pop_subscript_storage_program writes_a =
    [VariableDecl Private Storage "a" pop_array_ty NONE;
     pop_subscript_bar writes_a;
     FunctionDecl External Nonpayable F F "f" [] [] (BaseT (UintT 256))
       pop_subscript_storage_body]
End

Definition pop_subscript_storage_fn_def:
  pop_subscript_storage_fn =
    (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list,
     BaseT (UintT 256), pop_subscript_storage_body)
End

(* Python: risky overlap, since bar writes self.a. *)
val pop_subscript_storage_rejected_eval =
  EVAL ``fn_allocs_ok (pop_subscript_storage_program T)
           pop_subscript_storage_fn``

Theorem pop_subscript_storage_rejected:
  ¬fn_allocs_ok (pop_subscript_storage_program T) pop_subscript_storage_fn
Proof
  ACCEPT_TAC (EQF_ELIM pop_subscript_storage_rejected_eval)
QED

(* Compiled when bar writes nothing. *)
val pop_subscript_storage_view_index_ok_eval =
  EVAL ``fn_allocs_ok (pop_subscript_storage_program F)
           pop_subscript_storage_fn``

Theorem pop_subscript_storage_view_index_ok:
  fn_allocs_ok (pop_subscript_storage_program F) pop_subscript_storage_fn
Proof
  ACCEPT_TAC (EQT_ELIM pop_subscript_storage_view_index_ok_eval)
QED

(* The whole runtime unit is rejected. *)
val pop_subscript_storage_program_eval =
  EVAL ``lower_vyper_runtime_unit (pop_subscript_storage_program T) rpolicy``

Theorem pop_subscript_storage_program_rejected:
  !rpolicy.
    lower_vyper_runtime_unit (pop_subscript_storage_program T) rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC pop_subscript_storage_program_eval
QED
