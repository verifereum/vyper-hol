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
              pop_subscript_storage_program_rejected,
              nested_pop_target_rejected,
              nested_pop_target_constant_index_ok. *)
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

(* The target side (vyperlang/vyper#5280): a subscript in an assignment target,
   or in the array of an append or pop, whose base passes through a
   dynamic-array element and whose index can write that base.  The runtime
   lowering rejects it through alloc_limits_target's target_subscript_overlap.
   d is a local, so its type comes from the declaration as compile_stmts
   threads it.

   @internal
   def g():
       d: DynArray[DynArray[DynArray[uint256, 1], 1], 1] = empty(...)
       d[0][idx].pop()                                                      *)
Definition nested_inner_ty_def:
  nested_inner_ty = ArrayT (BaseT (UintT 256)) (Dynamic 1)
End

Definition nested_elem_ty_def:
  nested_elem_ty = ArrayT nested_inner_ty (Dynamic 1)
End

Definition nested_array_ty_def:
  nested_array_ty = ArrayT nested_elem_ty (Dynamic 1)
End

Definition nested_pop_target_fn_def:
  nested_pop_target_fn idx =
    (Nonpayable, F, F, "g", [] : (string # type) list, [] : expr list, NoneT,
     [AnnAssign "d" nested_array_ty
        (TypeBuiltin nested_array_ty Empty nested_array_ty []);
      Expr (Pop (BaseT (UintT 256))
              (SubscriptTarget
                 (SubscriptTarget (NameTarget "d")
                    (Literal (BaseT (UintT 256)) (IntL 0)))
                 idx))])
End

(* d[0][d.pop()[0][0]].pop()
   Python: risky overlap, since the index pops d, through whose element the
   target's base d[0] passes. *)
val nested_pop_target_rejected_eval =
  EVAL ``fn_allocs_ok []
           (nested_pop_target_fn
              (Subscript (BaseT (UintT 256))
                 (Subscript nested_inner_ty
                    (Pop nested_elem_ty (NameTarget "d"))
                    (Literal (BaseT (UintT 256)) (IntL 0)))
                 (Literal (BaseT (UintT 256)) (IntL 0))))``

Theorem nested_pop_target_rejected:
  ¬fn_allocs_ok []
     (nested_pop_target_fn
        (Subscript (BaseT (UintT 256))
           (Subscript nested_inner_ty
              (Pop nested_elem_ty (NameTarget "d"))
              (Literal (BaseT (UintT 256)) (IntL 0)))
           (Literal (BaseT (UintT 256)) (IntL 0))))
Proof
  ACCEPT_TAC (EQF_ELIM nested_pop_target_rejected_eval)
QED

(* d[0][0].pop(): compiled, since the index writes nothing. *)
val nested_pop_target_constant_index_ok_eval =
  EVAL ``fn_allocs_ok []
           (nested_pop_target_fn (Literal (BaseT (UintT 256)) (IntL 0)))``

Theorem nested_pop_target_constant_index_ok:
  fn_allocs_ok []
    (nested_pop_target_fn (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  ACCEPT_TAC (EQT_ELIM nested_pop_target_constant_index_ok_eval)
QED
