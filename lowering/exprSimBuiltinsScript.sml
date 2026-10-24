(*
 * Expression simulation: the builtins (#636, Builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the builtins that
 * are neither operators nor aggregates.  All cheated, for the later #636
 * PRs; each #636 Builtins row is:
 *   1 len, len(msg.data), msg.data slices: compile_len_sim,
 *     compile_calldata_len_sim, compile_calldata_slice_sim
 *   2 keccak256, sha256: compile_keccak256_sim, compile_sha256_sim
 *   3 as_wei_value, ceil, floor (#566), uint256_addmod, uint256_mulmod,
 *     pow_mod256: compile_as_wei_value_sim, compile_ceil_sim,
 *     compile_floor_sim, compile_addmod_sim, compile_mulmod_sim,
 *     compile_pow_mod256_sim, and compile_addmod_names_sim,
 *     compile_mulmod_names_sim, compile_powmod256_names_sim for the three
 *     on names, which compile_expr lowers itself (names_builtin)
 *   4 concat, slice, extract32 (#566), uint2str (#561): compile_concat_sim,
 *     compile_slice_sim, compile_extract32_sim, compile_uint2str_sim
 *   5 blockhash, blobhash: compile_blockhash_sim, compile_blobhash_sim.
 *     compile_blockhash_sim is unprovable as the definitions stand: the
 *     source raises a RuntimeError where BLOCKHASH returns 0 (#671), and
 *     call_ctx_rel does not relate the block hashes
 *   6 account reads: compile_acc_sim
 *   7 method_id: compile_method_id_sim
 *   8 ecrecover, ecadd, ecmul: compile_ecrecover_sim, compile_ecadd_sim,
 *     compile_ecmul_sim
 *
 * len, the hashes of a bytestring and slice read their operand's
 * LocatedValue (compile_expr without unwrap_value, or a msg.data/.code
 * operand that is never evaluated as a value), which expr_sim does not
 * describe: their proofs need more than the induction hypothesis's
 * expr_sim_ok of the operand (see exprSimPlaces).
 *)

Theory exprSimBuiltins
Ancestors
  list exprSim exprSimHyps vyperAST

(* ===== Lengths and calldata ===== *)

Theorem compile_len_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann Len args)
Proof
  cheat
QED

Theorem compile_calldata_len_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann CalldataLen args)
Proof
  cheat
QED

Theorem compile_calldata_slice_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (CalldataSlice n) args)
Proof
  cheat
QED

(* ===== Hashes ===== *)

Theorem compile_keccak256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann Keccak256 args)
Proof
  cheat
QED

Theorem compile_sha256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann Sha256 args)
Proof
  cheat
QED

(* ===== Arithmetic builtins ===== *)

Theorem compile_as_wei_value_sim:
  !cenv ann d args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (AsWeiValue d) args)
Proof
  cheat
QED

Theorem compile_ceil_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann Ceil args)
Proof
  cheat
QED

Theorem compile_floor_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann Floor args)
Proof
  cheat
QED

Theorem compile_addmod_sim:
  !cenv ann args.
    ~names_builtin AddMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann AddMod args)
Proof
  cheat
QED

Theorem compile_mulmod_sim:
  !cenv ann args.
    ~names_builtin MulMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann MulMod args)
Proof
  cheat
QED

Theorem compile_pow_mod256_sim:
  !cenv ann args.
    ~names_builtin PowMod256 args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann PowMod256 args)
Proof
  cheat
QED

Theorem compile_addmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_sim_ok cenv (Builtin ann AddMod [Name aty a; Name bty b; Name mty m])
Proof
  cheat
QED

Theorem compile_mulmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_sim_ok cenv (Builtin ann MulMod [Name aty a; Name bty b; Name mty m])
Proof
  cheat
QED

Theorem compile_powmod256_names_sim:
  !cenv ann aty a bty b.
    expr_sim_ok cenv (Builtin ann PowMod256 [Name aty a; Name bty b])
Proof
  cheat
QED

(* ===== Bytestrings ===== *)

Theorem compile_concat_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Concat n) args)
Proof
  cheat
QED

Theorem compile_slice_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Slice n) args)
Proof
  cheat
QED

Theorem compile_extract32_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (TypeBuiltin ann Extract32 t args)
Proof
  cheat
QED

Theorem compile_uint2str_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Uint2Str n) args)
Proof
  cheat
QED

(* ===== Chain and account reads ===== *)

Theorem compile_blockhash_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann BlockHash args)
Proof
  cheat
QED

Theorem compile_blobhash_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann BlobHash args)
Proof
  cheat
QED

Theorem compile_acc_sim:
  !cenv ann item args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Acc item) args)
Proof
  cheat
QED

Theorem compile_method_id_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann MethodId args)
Proof
  cheat
QED

(* ===== Precompiles ===== *)

Theorem compile_ecrecover_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann ECRecover args)
Proof
  cheat
QED

Theorem compile_ecadd_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann ECAdd args)
Proof
  cheat
QED

Theorem compile_ecmul_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann ECMul args)
Proof
  cheat
QED
