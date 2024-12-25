open HolKernel boolLib bossLib Parse
open listTheory finite_mapTheory
open vyperAstTheory vfmContextTheory

val _ = new_theory "vyperVm";

Datatype:
  value
  = VoidV
  | BoolV bool
  | TupleV (value list)
  | IntV int
End

Datatype:
  function_context = <|
    scopes: identifier |-> value
  |>
End

Datatype:
  execution_context = <|
    function_contexts: function_context list
  |>
End

val _ = export_theory();
