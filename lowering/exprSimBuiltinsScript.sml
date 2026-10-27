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
 *   6 account reads: compile_acc_sim; all but .code by exprSimAccounts'
 *     compile_acc_read_sim, .code in compile_acc_code_sim (unprovable for
 *     now, below)
 *   7 method_id: compile_method_id_sim; a literal signature with
 *     output_type=bytes4 by compile_method_id_literal_word_sim (the folded
 *     selector, a word literal), the rest in compile_method_id_other_sim
 *     (unprovable for now, below)
 *   8 ecrecover, ecadd, ecmul: compile_ecrecover_sim, compile_ecadd_sim,
 *     compile_ecmul_sim
 *
 * Unprovable as the definitions stand, to be fixed in the lowering or in
 * state_rel before their PRs:
 *   - compile_blockhash_sim: the source raises a RuntimeError where
 *     BLOCKHASH returns 0 (#671), and call_ctx_rel does not relate the block
 *     hashes.
 *   - compile_blobhash_sim: call_ctx_rel does not relate the blob hashes.
 *   - compile_acc_code_sim, a bare .code: the lowering emits INVALID, as
 *     Python's codegen refuses it; the supported subset leaves it out.
 *   - compile_keccak256_sim and compile_sha256_sim for a Bytes or String
 *     operand: compile_keccak256_bytes and compile_sha256_bytes read the
 *     bytes from ADD ptr 32, which wraps at 2 ** 256, while val_in_memory
 *     reads them at w2n ptr + 32, and nothing in stmt_state_rel or
 *     expr_val_at keeps a memory value below 2 ** 256 (exec_alloca's
 *     vs_alloca_next is unbounded).  They wait for S3's alloca-frontier
 *     invariant, vs_alloca_next < dimword (:256) along a run
 *     (raw_unit_memory_ok), to reach the judgment (stmtLoweringProps notes
 *     it as still unstated there), which gives the bound at the hash.  The
 *     bound can't go in stmt_state_rel: INVOKE copies the callee's frontier
 *     back, so a loop around an internal call keeps raising it.
 *   - compile_method_id_other_sim: a Bytes[4] output, and the runtime hash
 *     of a signature, use ALLOCA'd buffers or ADD ptr 32, so it waits for
 *     the same bound.
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
  list exprSim exprSimHyps vyperAST exprSimWordBuiltins exprSimWordArgs
  exprLowering compileEnv valueEncoding fragExec vyperInterpreter
  vyperState vyperContext vyperValueOperation venomState exprSimAccounts

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

(* A bare .code: the lowering emits INVALID (compile_acc), where the source
   reads the account's code, so this does not hold as the definitions
   stand.  Python's codegen rejects it too (CompilerPanic ".code requires
   slice() context", codegen_venom/expr.py): x.code is only lowered as
   slice's first argument, with EXTCODECOPY.  The supported subset leaves
   it out (supported_builtin_form), so expr_sim_pre needs that exclusion
   for this case to go. *)
Theorem compile_acc_code_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Acc Code) args)
Proof
  cheat
QED

Theorem compile_acc_sim:
  !cenv ann item args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (Acc item) args)
Proof
  rpt strip_tac >> Cases_on `item = Code`
  >- (gvs[] >> irule compile_acc_code_sim >> simp[]) >>
  irule compile_acc_read_sim >> simp[]
QED

Theorem eval_exprs_single_literal:
  !cx la l es. eval_exprs cx [Literal la l] es = (INL [evaluate_literal l], es)
Proof
  rpt gen_tac >>
  rpt (simp[Once evaluate_def, bind_def, return_def, materialise_def])
QED

(* A literal signature is folded to the literal selector (#711). *)
Theorem compile_expr_method_id_literal:
  !cenv ty ann la l bs st.
    method_id_literal (Literal la l) = SOME bs ==>
    compile_expr cenv ty (Builtin ann MethodId [Literal la l]) st =
    compile_literal_vv ann (BytesL (TAKE 4 (Keccak_256_w64 bs))) st
Proof
  rpt strip_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def]
QED

(* The source hashes a literal signature to the selector the lowering
   folds it to. *)
Theorem eval_expr_method_id_literal:
  !cx ann la l bs es res es'.
    method_id_literal (Literal la l) = SOME bs /\
    eval_expr cx (Builtin ann MethodId [Literal la l]) es = (res, es') ==>
    es' = es /\ res = INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) eval_expr_builtin_cases >>
  simp[builtin_args_length_ok_def, eval_exprs_single_literal] >>
  strip_tac >> gvs[builtin_result_def] >>
  Cases_on `l` >>
  gvs[method_id_literal_def, evaluate_literal_def, evaluate_builtin_def]
QED

(* method_id of a literal signature with output_type=bytes4: the folded
   selector as a word literal, no code. *)
Theorem compile_method_id_literal_word_sim:
  !cenv la l.
    IS_SOME (method_id_literal (Literal la l)) ==>
    expr_sim_ok cenv
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  rw[expr_sim_ok_def, expr_sim_def, optionTheory.IS_SOME_EXISTS] >>
  drule_all eval_expr_method_id_literal >> strip_tac >> gvs[] >>
  drule compile_expr_method_id_literal >> strip_tac >>
  gvs[lower_value_def, comp_bind_def, compile_literal_vv_def,
      unwrap_value_def, comp_return_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def]
QED

Theorem compile_method_id_literal_word_case_sim:
  !cenv la l.
    IS_SOME (method_id_literal (Literal la l)) ==>
    expr_ok cenv
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  rpt strip_tac >> irule expr_ok_stack >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value]
  >~ [`expr_sim_ok`] >- simp[compile_method_id_literal_word_sim] >>
  gvs[optionTheory.IS_SOME_EXISTS] >> rpt gen_tac >>
  drule compile_expr_method_id_literal >>
  simp[compile_literal_vv_def, comp_return_def]
QED

(* The other method_ids: a literal signature with the default Bytes[4]
   output, a buffer holding the length 4 and the selector, and a signature
   that is not a literal, hashed at run time (compile_method_id_runtime).
   Cheated, and unprovable as the definitions stand: a Bytes[4] output is
   an ALLOCA'd buffer, and the runtime hash reads a Bytes or String
   signature from ADD ptr 32 and copies a bytesN one into an ALLOCA'd
   buffer; nothing keeps vs_alloca_next below 2 ** 256, so they wait, with
   keccak256, for S3's alloca frontier (see the header). *)
Theorem compile_method_id_other_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) /\
    ~(ann = BaseT (BytesT (Fixed 4)) /\
      ?la l. args = [Literal la l] /\
             IS_SOME (method_id_literal (Literal la l))) ==>
    expr_vv_ok cenv (Builtin ann MethodId args)
Proof
  cheat
QED

Theorem compile_method_id_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann MethodId args)
Proof
  rpt strip_tac >>
  Cases_on `ann = BaseT (BytesT (Fixed 4)) /\
            ?la l. args = [Literal la l] /\
                   IS_SOME (method_id_literal (Literal la l))`
  >- (gvs[] >> metis_tac[compile_method_id_literal_word_case_sim, expr_ok_def]) >>
  irule compile_method_id_other_sim >> asm_rewrite_tac[]
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
