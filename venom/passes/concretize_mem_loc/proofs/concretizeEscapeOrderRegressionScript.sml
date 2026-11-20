Theory concretizeEscapeOrderRegression
Ancestors
  concretizeMemLocDefs venomInst list option
Libs
  finite_mapLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset

(* SSTORE %a, %b has internal operands [b; a]. Both pointers escape at
   the same instruction, with the same lifetime. Vyper lays out b first. *)
Definition escaped_allocas_fn_def:
  escaped_allocas_fn =
    mk_raw_function "entry"
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit 32w] ["a"];
         mk_inst 1 ALLOCA [Lit 32w] ["b"];
         mk_inst 2 SSTORE [Var "b"; Var "a"] [];
         mk_inst 3 STOP [] []]|>]
End

Theorem escaped_allocas_follow_discovery_order:
  OPTION_MAP (TAKE 2 o fn_insts)
    (concretize_function_fuel_in_context
      (concretize_memloc_fuel escaped_allocas_fn)
      (mk_venom_context [escaped_allocas_fn] (SOME "entry"))
      [] escaped_allocas_fn) =
  SOME [mk_inst 0 ASSIGN [Lit 32w] ["a"]; mk_inst 1 ASSIGN [Lit 0w] ["b"]]
Proof
  EVAL_TAC
QED
