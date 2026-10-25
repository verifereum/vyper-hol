(*
 * Expression simulation: the builtins (#636, Builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the builtins that
 * are neither operators nor aggregates.  Row 3's word builtins but ceil are
 * proved, in exprSimWordBuiltins; the rest are cheated, for the later #636
 * PRs.  Each #636 Builtins row is:
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
 *   - compile_keccak256_sim and compile_sha256_sim for a Bytes or String
 *     operand: compile_keccak256_bytes and compile_sha256_bytes read the
 *     bytes from ADD ptr 32, which wraps at 2 ** 256, while val_in_memory
 *     reads them at w2n ptr + 32, and nothing in stmt_state_rel or
 *     expr_val_at keeps a memory value below 2 ** 256 (exec_alloca's
 *     vs_alloca_next is unbounded).
 *
 * The STATICCALLs of sha256, ecrecover, ecadd and ecmul go to computed
 * precompiles: take_outcome answers them with precompile_result and leaves
 * the outcomes and requests alone (extCallOracle), as the source does.
 *
 * len, the hashes of a bytestring and slice read their operand's value_vv
 * (compile_expr without unwrap_value), which the induction hypothesis's
 * expr_vv_ok of the operand describes.  A msg.data or .code operand is
 * never evaluated as a value, so for those the hypothesis says nothing and
 * the lemmas need a judgment of their own.
 *)

Theory exprSimBuiltins
Ancestors
  list exprSim exprSimHyps vyperAST exprSimWordBuiltins

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

(* Notes for the word cases below (all StackValue lowerings; the result is
   a word_value, IntV):
   - as_wei_value: well_typed_builtin_app admits only unsigned operands, so
     compile_as_wei_value_int with is_signed = F applies.  For x < 2 ** 256
     and m > 0, x * m < 2 ** 256 exactly when x = 0 or MUL's product mod
     2 ** 256 divided by x is m (mul_mod_div_no_overflow), which is
     evaluate_as_wei_value's bound check;
     an overflow is a RuntimeError at the source and a failed ASSERT below.
     Wei (m = 1) emits no code.
   - floor: the source's i / decimal_scale rounds toward negative infinity;
     the lowering subtracts divisor - 1 from a negative operand and then
     rounds toward zero (SDIV).  Decimal operands are far inside 256 bits.
   - addmod/mulmod: ASSERT c, then ADDMOD/MULMOD, which are exact
     (venomExecSemantics addmod_def/mulmod_def); c = 0 is the source's
     RuntimeError.  pow_mod256: EXP on words is modexp mod 2 ** 256.
   - the *_names forms: compile_addmod_names and friends lower each name
     the way lower_value compile_expr lowers Name (compile_name_vv, then
     unwrap_value), so they are the dispatch form on Name operands.  A
     well-typed uint256 local holds an IntV, a word_value, so
     exprSim's compile_name_word_sim applies to each. *)

Theorem compile_as_wei_value_sim:
  !cenv ann d args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (AsWeiValue d) args)
Proof
  rpt strip_tac >> irule word_builtin_below_sim >> simp[]
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
  rpt strip_tac >> irule word_builtin_below_sim >> simp[]
QED

Theorem compile_addmod_sim:
  !cenv ann args.
    ~names_builtin AddMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann AddMod args)
Proof
  rpt strip_tac >> irule word_builtin_below_sim >> simp[]
QED

Theorem compile_mulmod_sim:
  !cenv ann args.
    ~names_builtin MulMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann MulMod args)
Proof
  rpt strip_tac >> irule word_builtin_below_sim >> simp[]
QED

Theorem compile_pow_mod256_sim:
  !cenv ann args.
    ~names_builtin PowMod256 args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann PowMod256 args)
Proof
  rpt strip_tac >> irule word_builtin_below_sim >> simp[]
QED

Theorem compile_addmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann AddMod [Name aty a; Name bty b; Name mty m])
Proof
  rpt gen_tac >> irule word_modular_names_sim >> simp[]
QED

Theorem compile_mulmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann MulMod [Name aty a; Name bty b; Name mty m])
Proof
  rpt gen_tac >> irule word_modular_names_sim >> simp[]
QED

Theorem compile_powmod256_names_sim:
  !cenv ann aty a bty b.
    expr_vv_ok cenv (Builtin ann PowMod256 [Name aty a; Name bty b])
Proof
  rpt gen_tac >> irule word_modular_names_sim >> simp[]
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
