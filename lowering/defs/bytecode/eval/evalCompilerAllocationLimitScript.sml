(* The external return buffer at Python's allocation limit.  Python's
   Context.allocate_buffer raises MemoryAllocationException for 2**64 bytes
   or more, and _lower_external_return allocates the ABI return buffer there
   on each valued return; the runtime lowering rejects the same programs.
   It does the same for a function's locals, as Context.new_variable
   allocates each, and for its parameters, which an external function
   decodes into such a variable, and for its return type, as a caller stages
   an internal call's result in a temporary.
   TOP-LEVEL: allocation_limit_return_rejected,
              allocation_limit_raise_return_buffer_ok,
              allocation_limit_boundary_ok,
              allocation_limit_boundary_rejected,
              allocation_limit_local_rejected,
              allocation_limit_local_boundary_ok,
              allocation_limit_local_boundary_rejected,
              allocation_limit_param_rejected,
              allocation_limit_internal_return_rejected. *)
Theory evalCompilerAllocationLimit
Ancestors compileVyper

(* @external
   def f(x: Bytes[1]) -> Bytes[2**64]:
       return x
   Python: MemoryAllocationException for the return buffer of 64 + 2**64
   bytes, the only allocation over the limit.  (A static type of 2**64 bytes
   is a fixed array of 2**59 words, whose decoding info the evaluator would
   unroll.) *)
Definition allocation_limit_return_program_def:
  allocation_limit_return_program =
    [FunctionDecl External Nonpayable F F "f"
       [("x", BaseT (BytesT (Dynamic 1)))]
       ([] : expr list) (BaseT (BytesT (Dynamic (2 ** 64))))
       [Return (SOME (Name (BaseT (BytesT (Dynamic (2 ** 64)))) "x"))]]
End

val allocation_limit_return_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_return_program rpolicy``

Theorem allocation_limit_return_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_return_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_return_eval
QED

val allocation_limit_raise_eval =
  EVAL ``external_return_buffer_ok
           (package_external_fn [] F (K 0)
              (Nonpayable, F, F, "f", [], ([] : expr list),
               BaseT (BytesT (Dynamic (2 ** 64))),
               [Raise RaiseBare]))``

(* @external
   def f() -> Bytes[2**64]:
       raise
   Python compiles it: no valued return, so no return buffer. *)
Theorem allocation_limit_raise_return_buffer_ok:
  external_return_buffer_ok
    (package_external_fn [] F (K 0)
       (Nonpayable, F, F, "f", [], ([] : expr list),
        BaseT (BytesT (Dynamic (2 ** 64))), [Raise RaiseBare]))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_raise_eval)
QED

(* The return buffer of Bytes[n] is 64 + ceil32(n) bytes: the tuple head,
   the length word and the data.  It fits for n = 2**64 - 96 and reaches the
   limit for n = 2**64 - 95.
   @external
   def f() -> Bytes[n]:
       return empty(Bytes[n]) *)
Definition allocation_limit_boundary_fn_def:
  allocation_limit_boundary_fn n =
    package_external_fn [] F (K 0)
      (Nonpayable, F, F, "f", [], ([] : expr list),
       BaseT (BytesT (Dynamic n)),
       [Return (SOME (TypeBuiltin (BaseT (BytesT (Dynamic n))) Empty
                       (BaseT (BytesT (Dynamic n))) []))])
End

val allocation_limit_boundary_ok_eval =
  EVAL ``external_return_buffer_ok
           (allocation_limit_boundary_fn (2 ** 64 - 96))``

Theorem allocation_limit_boundary_ok:
  external_return_buffer_ok (allocation_limit_boundary_fn (2 ** 64 - 96))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_boundary_ok_eval)
QED

val allocation_limit_boundary_rejected_eval =
  EVAL ``external_return_buffer_ok
           (allocation_limit_boundary_fn (2 ** 64 - 95))``

Theorem allocation_limit_boundary_rejected:
  ¬external_return_buffer_ok (allocation_limit_boundary_fn (2 ** 64 - 95))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_boundary_rejected_eval)
QED

(* @external
   def f():
       y: Bytes[2**64] = b""
   Python: MemoryAllocationException for y's 32 + 2**64 bytes. *)
Definition allocation_limit_local_program_def:
  allocation_limit_local_program =
    [FunctionDecl External Nonpayable F F "f" [] ([] : expr list) NoneT
       [AnnAssign "y" (BaseT (BytesT (Dynamic (2 ** 64))))
          (Literal (BaseT (BytesT (Dynamic 0))) (BytesL []))]]
End

val allocation_limit_local_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_local_program rpolicy``

Theorem allocation_limit_local_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_local_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_local_eval
QED

(* A local of type Bytes[n] takes 32 + ceil32(n) bytes: it fits for
   n = 2**64 - 64 and reaches the limit for n = 2**64 - 63.
   def f():
       y: Bytes[n] = b"" *)
Definition allocation_limit_local_fn_def:
  allocation_limit_local_fn n =
    (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list, NoneT,
     [AnnAssign "y" (BaseT (BytesT (Dynamic n)))
        (Literal (BaseT (BytesT (Dynamic 0))) (BytesL []))])
End

val allocation_limit_local_boundary_ok_eval =
  EVAL ``fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 64))``

Theorem allocation_limit_local_boundary_ok:
  fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 64))
Proof
  ACCEPT_TAC (EQT_ELIM allocation_limit_local_boundary_ok_eval)
QED

val allocation_limit_local_boundary_rejected_eval =
  EVAL ``fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 63))``

Theorem allocation_limit_local_boundary_rejected:
  ¬fn_allocs_ok [] (allocation_limit_local_fn (2 ** 64 - 63))
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_local_boundary_rejected_eval)
QED

(* @external
   def f(x: Bytes[2**256-1]):
       pass
   Python: MemoryAllocationException for x's 32 + 2**256 bytes, which a
   word-sized ALLOCA would wrap to 32. *)
Definition allocation_limit_param_program_def:
  allocation_limit_param_program =
    [FunctionDecl External Nonpayable F F "f"
       [("x", BaseT (BytesT (Dynamic (2 ** 256 - 1))))]
       ([] : expr list) NoneT [Pass]]
End

val allocation_limit_param_eval =
  EVAL ``lower_vyper_runtime_unit allocation_limit_param_program rpolicy``

Theorem allocation_limit_param_rejected:
  !rpolicy.
    lower_vyper_runtime_unit allocation_limit_param_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_param_eval
QED

(* @internal
   def f() -> Bytes[2**64]:
       ...
   Python: MemoryAllocationException at each call site, which stages the
   result in new_temporary_value(Bytes[2**64]). *)
val allocation_limit_internal_return_rejected_eval =
  EVAL ``fn_allocs_ok []
           (Nonpayable, F, F, "f", [] : (string # type) list,
            [] : expr list, BaseT (BytesT (Dynamic (2 ** 64))), [Pass])``

Theorem allocation_limit_internal_return_rejected:
  ¬fn_allocs_ok []
     (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list,
      BaseT (BytesT (Dynamic (2 ** 64))), [Pass])
Proof
  ACCEPT_TAC (EQF_ELIM allocation_limit_internal_return_rejected_eval)
QED
