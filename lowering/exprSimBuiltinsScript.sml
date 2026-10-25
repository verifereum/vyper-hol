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
 *   5 blobhash: compile_blobhash_sim (blockhash, compile_blockhash_sim, is
 *     #636 Leaves row 5, with block.prevhash)
 *   6 account reads: compile_acc_sim
 *   7 method_id: compile_method_id_sim
 *   8 ecrecover, ecadd, ecmul: compile_ecrecover_sim, compile_ecadd_sim,
 *     compile_ecmul_sim
 *
 * Unprovable as the definitions stand, to be fixed in the lowering or in
 * state_rel before their PRs:
 *   - compile_blockhash_sim: the source raises a RuntimeError where
 *     BLOCKHASH returns 0 (#671), and call_ctx_rel does not relate the block
 *     hashes.
 *   - compile_calldata_len_sim, compile_calldata_slice_sim,
 *     compile_blobhash_sim, and compile_acc_sim for balance, codesize,
 *     codehash and is_contract: call_ctx_rel relates neither calldata nor
 *     blob hashes, and nothing relates the accounts.
 *   - compile_acc_sim for .code: the lowering emits INVALID.
 *   - compile_len_sim: well_typed_builtin_app Len admits fixed arrays and
 *     bytesN, but the lowering always loads the operand's first word.
 *
 * len, the hashes of a bytestring and slice read their operand's value_vv
 * (compile_expr without unwrap_value), which the induction hypothesis's
 * expr_vv_ok of the operand describes.  A msg.data or .code operand is
 * never evaluated as a value, so for those the hypothesis says nothing and
 * the lemmas need a judgment of their own.
 *)

Theory exprSimBuiltins
Ancestors
  list exprSim exprSimHyps vyperAST

(* ===== Lengths and calldata ===== *)

Theorem compile_len_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Len args)
Proof
  cheat
QED

Theorem compile_calldata_len_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann CalldataLen args)
Proof
  cheat
QED

Theorem compile_calldata_slice_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (CalldataSlice n) args)
Proof
  cheat
QED

(* ===== Hashes ===== *)

Theorem compile_keccak256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Keccak256 args)
Proof
  cheat
QED

Theorem compile_sha256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Sha256 args)
Proof
  cheat
QED

(* ===== Arithmetic builtins ===== *)

Theorem compile_as_wei_value_sim:
  !cenv ann d args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (AsWeiValue d) args)
Proof
  cheat
QED

Theorem compile_ceil_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Ceil args)
Proof
  cheat
QED

Theorem compile_floor_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Floor args)
Proof
  cheat
QED

Theorem compile_addmod_sim:
  !cenv ann args.
    ~names_builtin AddMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann AddMod args)
Proof
  cheat
QED

Theorem compile_mulmod_sim:
  !cenv ann args.
    ~names_builtin MulMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann MulMod args)
Proof
  cheat
QED

Theorem compile_pow_mod256_sim:
  !cenv ann args.
    ~names_builtin PowMod256 args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann PowMod256 args)
Proof
  cheat
QED

Theorem compile_addmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann AddMod [Name aty a; Name bty b; Name mty m])
Proof
  cheat
QED

Theorem compile_mulmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann MulMod [Name aty a; Name bty b; Name mty m])
Proof
  cheat
QED

Theorem compile_powmod256_names_sim:
  !cenv ann aty a bty b.
    expr_vv_ok cenv (Builtin ann PowMod256 [Name aty a; Name bty b])
Proof
  cheat
QED

(* ===== Bytestrings ===== *)

Theorem compile_concat_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Concat n) args)
Proof
  cheat
QED

Theorem compile_slice_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Slice n) args)
Proof
  cheat
QED

Theorem compile_extract32_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Extract32 t args)
Proof
  cheat
QED

Theorem compile_uint2str_sim:
  !cenv ann n args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Uint2Str n) args)
Proof
  cheat
QED

(* ===== Chain and account reads ===== *)

Theorem compile_blockhash_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann BlockHash args)
Proof
  cheat
QED

Theorem compile_blobhash_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann BlobHash args)
Proof
  cheat
QED

Theorem compile_acc_sim:
  !cenv ann item args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Acc item) args)
Proof
  cheat
QED

Theorem compile_method_id_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann MethodId args)
Proof
  cheat
QED

(* ===== Precompiles ===== *)

Theorem compile_ecrecover_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECRecover args)
Proof
  cheat
QED

Theorem compile_ecadd_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECAdd args)
Proof
  cheat
QED

Theorem compile_ecmul_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECMul args)
Proof
  cheat
QED
