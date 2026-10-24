(*
 * Expression simulation: aggregates and type builtins (#636, Aggregates
 * and type builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for struct and array
 * literals and the type builtins but extract32.  All cheated, for the
 * later #636 PRs.
 *
 * TOP-LEVEL:
 *   compile_struct_lit_sim, compile_make_array_sim — StructLit, MakeArray
 *                           (lists and tuples), row 1
 *   compile_empty_sim, compile_max_value_sim, compile_min_value_sim,
 *   compile_epsilon_sim   — empty(T), max_value, min_value, epsilon, row 2
 *   compile_convert_sim   — convert (#548), row 3
 *   compile_abi_encode_sim, compile_abi_decode_sim — abi_encode (#551),
 *                           abi_decode with its validation aborts, row 4
 *
 * compile_struct_lit_sim is false as the lowering stands: the StructLit case
 * passes the caller's ty, not the literal's StructT, to compile_struct_lit,
 * which takes the field layout from it.  At any other ty every field gets
 * 32 bytes, so a struct with a uint256[2] field followed by a uint256 stores
 * the second field at offset 32, not 64.  The fix is in the lowering (take
 * the layout from the literal's own name, as Vyper does).
 *
 * The elements of a struct or array literal are lowered as
 * cfn ...; ADD ...; unwrap_value, so the code from the start is not
 * lower_value's fragment whenever unwrap_value loads, and an element that
 * is a storage or transient array evaluates to an ArrayRef.  The induction
 * hypothesis (expr_sim_ok of each element, expr_sim_below_mem) covers
 * neither: these lemmas need a judgment on compile_expr's value (see
 * exprSimHyps), and composing the elements needs the operand composition
 * of #636's Infrastructure (a value an earlier operand left in memory
 * survives a later operand's fragment).
 *)

Theory exprSimAggregates
Ancestors
  list exprSim exprSimHyps vyperAST

Theorem compile_struct_lit_sim:
  !cenv ann nsid fields.
    expr_sim_below cenv (expr_size (StructLit ann nsid fields)) ==>
    expr_sim_ok cenv (StructLit ann nsid fields)
Proof
  cheat
QED

Theorem compile_make_array_sim:
  !cenv ann topt bnd args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (MakeArray topt bnd) args)
Proof
  cheat
QED

Theorem compile_empty_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

Theorem compile_max_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann MaxValue t args)
Proof
  cheat
QED

Theorem compile_min_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann MinValue t args)
Proof
  cheat
QED

Theorem compile_epsilon_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann Epsilon t args)
Proof
  cheat
QED

Theorem compile_convert_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann Convert t args)
Proof
  cheat
QED

Theorem compile_abi_encode_sim:
  !cenv ann ensure mid t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann (AbiEncode ensure mid) t args)
Proof
  cheat
QED

Theorem compile_abi_decode_sim:
  !cenv ann unwrap t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann (AbiDecode unwrap) t args)
Proof
  cheat
QED
