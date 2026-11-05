(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: floor, as_wei_value, uint256_addmod, uint256_mulmod and
   pow_mod256 (S1: exprSimWordBuiltins' word_builtin_case). *)
Theory bodyMemBiWord
Ancestors
  bodyMemoryPreds

Theorem body_builtin_word_mem:
  !cx ty bt es.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/
     bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  cheat
QED
