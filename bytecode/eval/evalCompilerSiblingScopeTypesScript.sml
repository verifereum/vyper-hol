(* Sibling scopes may declare one name at different types.  The allocation
   checks read a local's type from the env as compile_stmts threads it
   (decl_var_type), not from the function-wide map build_compile_env makes,
   in which the last declaration of a name wins.  So each declaration is
   checked at its own type and these functions are accepted, as Python
   compiles them.
   TOP-LEVEL: sibling_for_types_ok, sibling_if_types_ok. *)
Theory evalCompilerSiblingScopeTypes
Ancestors compileVyper

Definition u256_lit_def:
  u256_lit n = Literal (BaseT (UintT 256)) (IntL n)
End

(* @internal
   def f():
       for i: uint256 in range(2):
           pass
       for i: int128 in range(2):
           pass                                                            *)
Definition sibling_for_fn_def:
  sibling_for_fn =
    (Nonpayable, F, F, "f", [] : (string # type) list, [] : expr list, NoneT,
     [For "i" (BaseT (UintT 256)) (Range (u256_lit 0) (u256_lit 2)) 2 [Pass];
      For "i" (BaseT (IntT 128)) (Range (u256_lit 0) (u256_lit 2)) 2 [Pass]])
End

val sibling_for_types_ok_eval = EVAL ``fn_allocs_ok [] sibling_for_fn``

Theorem sibling_for_types_ok:
  fn_allocs_ok [] sibling_for_fn
Proof
  ACCEPT_TAC (EQT_ELIM sibling_for_types_ok_eval)
QED

(* @internal
   def g(c: bool):
       if c:
           x: uint256 = 0
       else:
           x: int128 = 0                                                   *)
Definition sibling_if_fn_def:
  sibling_if_fn =
    (Nonpayable, F, F, "g", [("c", BaseT BoolT)], [] : expr list, NoneT,
     [If (Name (BaseT BoolT) "c")
        [AnnAssign "x" (BaseT (UintT 256)) (u256_lit 0)]
        [AnnAssign "x" (BaseT (IntT 128))
           (Literal (BaseT (IntT 128)) (IntL 0))]])
End

val sibling_if_types_ok_eval = EVAL ``fn_allocs_ok [] sibling_if_fn``

Theorem sibling_if_types_ok:
  fn_allocs_ok [] sibling_if_fn
Proof
  ACCEPT_TAC (EQT_ELIM sibling_if_types_ok_eval)
QED
