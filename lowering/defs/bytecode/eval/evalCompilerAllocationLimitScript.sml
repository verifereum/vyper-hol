(* The external return buffer at Python's allocation limit.  Python's
   Context.allocate_buffer raises MemoryAllocationException for 2**64 bytes
   or more, and _lower_external_return allocates the ABI return buffer there
   on each valued return; the runtime lowering rejects the same programs.
   TOP-LEVEL: allocation_limit_return_rejected,
              allocation_limit_raise_return_buffer_ok,
              allocation_limit_boundary_ok,
              allocation_limit_boundary_rejected,
              allocation_limit_defaults_return_rejected. *)
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

(* Default arguments use grouped lowering, but must not bypass the same
   return-buffer allocation limit as ordinary external entries. *)
Definition allocation_limit_defaults_return_program_def:
  allocation_limit_defaults_return_program =
    [FunctionDecl External Nonpayable F F "f"
       [("x", BaseT (BytesT (Dynamic 1))); ("n", BaseT (UintT 256))]
       [Literal (BaseT (UintT 256)) (IntL 0)]
       (BaseT (BytesT (Dynamic (2 ** 64))))
       [Return (SOME (Name (BaseT (BytesT (Dynamic (2 ** 64)))) "x"))]]
End

val allocation_limit_defaults_return_eval =
  EVAL ``lower_vyper_runtime_unit
           allocation_limit_defaults_return_program rpolicy``

Theorem allocation_limit_defaults_return_rejected:
  !rpolicy.
    lower_vyper_runtime_unit
      allocation_limit_defaults_return_program rpolicy = NONE
Proof
  gen_tac >> ACCEPT_TAC allocation_limit_defaults_return_eval
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
