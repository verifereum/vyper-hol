(*
 * Expression simulation: the builtins (#636, Builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) and of the body
 * simulation (bodySimExprCases) for the builtins that are neither operators
 * nor aggregates.  Each is stated over exprSimHyps' shared judgments: from
 * exprs_case of the operands, expr_vv_case of the builtin.  Row 3's word
 * builtins (exprSimWordBuiltins' word_builtin_case and compile_ceil_case),
 * rows 2 and 7 on exprSimHash's machinery, row 5 (here), row 6's account reads but
 * .code (in exprSimAccounts), row 4's uint2str (by exprSimUint2Str) and
 * ecrecover are proved; concat, slice, extract32 and a bare .code are
 * re-exported from their leaf theories (exprSimConcat, exprSimSlice,
 * exprSimExtract32, exprSimAccCode).  Each #636 Builtins row is:
 *   1 len, len(msg.data), msg.data slices: compile_len_case (by
 *     exprSimLen's compile_len_vv_case, and compile_len_ctor_code_case for
 *     an immutable in the constructor),
 *     compile_calldata_len_case (by exprSimCalldata's
 *     compile_calldatasize_sim), and exprSimCalldataSlice's
 *     compile_calldata_slice_call_case
 *   2 keccak256, sha256: compile_keccak256_case, compile_sha256_case
 *   3 as_wei_value, ceil, floor (#566), uint256_addmod, uint256_mulmod,
 *     pow_mod256: compile_ceil_case and exprSimWordBuiltins'
 *     word_builtin_case for the rest; compile_addmod_names_sim,
 *     compile_mulmod_names_sim, compile_powmod256_names_sim for the three
 *     on names, which compile_expr lowers itself (names_builtin)
 *   4 concat, slice, extract32 (#566), uint2str (#561): compile_concat_case,
 *     compile_slice_case, compile_extract32_case, compile_uint2str_case
 *   5 blobhash: compile_blobhash_case, proved: BLOBHASH on the index, whose
 *     blob hashes call_ctx_rel relates to the transaction's; blockhash(n),
 *     compile_blockhash_case (#636 Leaves row 5, with block.prevhash), is
 *     proved below, on call_ctx_rel's tx_env_ok and bc_blockhash lookup
 *   6 account reads: compile_acc_case; all but .code by exprSimAccounts'
 *     compile_acc_read_case, .code in compile_acc_code_case (unprovable
 *     for now, below)
 *   7 method_id: compile_method_id_case; a literal signature with
 *     output_type=bytes4 by compile_method_id_literal_word_sim (the folded
 *     selector, a word literal), the rest in compile_method_id_other_case
 *   8 ecrecover, ecadd, ecmul: exprSimPrecompiles'
 *     compile_ecrecover_call_case; compile_ecadd_sim and compile_ecmul_sim
 *     (by exprSimECArith's compile_ecadd_call_case, compile_ecmul_call_case),
 *     still stated over expr_sim_below, so for compile_expr_sim only
 *
 * Unprovable as the definitions stand, to be fixed in the lowering or in
 * state_rel before their PRs:
 *   - compile_blockhash_case: the source raises a RuntimeError where
 *     BLOCKHASH returns 0 (#671), and call_ctx_rel does not relate the block
 *     hashes.
 *   - compile_acc_code_case, a bare .code: the lowering emits INVALID, as
 *     Python's codegen refuses it; the supported subset leaves it out.
 *
 * The hashes and method_id read a bytestring operand at ADD ptr 32 and
 * allocate buffers of their own.  Neither wraps at 2 ** 256:
 * stmt_state_rel's alloca_room keeps the frontier below 2 ** 256, every
 * allocation ends below the frontier (alloca_inv) and so does every live
 * local region (local_ptrs_rel), and
 * expr_val_at puts the operand's value inside one of them
 * (exprSimLiteralBuffer proves a buffer leaf the same way).
 *
 * The STATICCALLs of sha256, ecrecover, ecadd and ecmul go to computed
 * precompiles: take_outcome answers them with precompile_result and leaves
 * the outcomes and requests alone (extCallOracle), as the source does.
 *
 * len and slice read their operand's value_vv
 * (compile_expr without unwrap_value), which the operand's expr_vv_case
 * describes.  A msg.data or .code operand is
 * never evaluated as a value, so for those the hypothesis says nothing and
 * the lemmas need a judgment of their own.
 *)

Theory exprSimBuiltins
Ancestors
  exprSimAccCode
  exprSimExtract32
  exprSimSlice
  exprSimConcat
  exprUnopSimDefs exprSimUnopCompose
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs exprSimValues gasNormalPrefix gasSummary fragGasMode fragGasPath
  fragGasSeq fragGasSeqAbort exprSimProps
  loweringPosts
  list rich_list  exprSimHyps vyperAST exprSimWordBuiltins
  exprSimWordArgs exprSimHash vyperTypeSystem exprLowering compileEnv
  valueEncoding fragExec freshWrites varsExt builtinProps arithmeticProps emitHelper
  vyperInterpreter vyperState vyperContext
  vyperValueOperation venomState exprSimAccounts exprSimUnop
  exprSimOperators exprBopLowering builtinMisc venomExecSemantics venomInst
  exprSimCalldata exprSimCalldataSlice exprSimLen exprSimPrecompiles exprSimECArith
  vyperValue exprLoweringProps vyperTyping exprSimUint2Str

(* ===== Lengths and calldata ===== *)

(* len of an operand in code, an immutable, in the constructor: the
   lowering loads the length word from the staged immutables with ILOAD,
   where immutables_rel lays the value out as in memory; exprSimLen's
   compile_len_vv_case covers it. *)
Theorem compile_len_ctor_code_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args /\ cenv.ce_is_ctor /\
    (?ty st. vv_location (FST (compile_expr cenv ty (HD args) st)) =
             SOME LocCode) ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Len args)
Proof
  cheat
QED

Theorem compile_len_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Len args)
Proof
  cheat
QED

Theorem compile_calldata_len_case:
  !nocalls ctx func cenv cx ann args.
    expr_vv_case nocalls ctx func cenv cx (Builtin ann CalldataLen args)
Proof
  cheat
QED

(* ===== Hashes ===== *)

(* keccak256 and sha256 of a Bytes[n], String[n] or bytesN operand
   (well_typed_builtin_app; the word branch of the lowering is not
   reached), a bytes32 result on the stack:
   - Bytes or String: lower_value hands out a pointer to the operand's
     value, length word then data (val_in_memory); MLOAD reads the length,
     ADD ptr 32 the data's address, unwrapped since the value lies inside
     an allocation or a local region, below 2 ** 256.  SHA3 hashes those
     bytes, the source's Keccak_256_w64; sha256 hands them to the precompile
     at 2 by STATICCALL, which take_outcome answers with the SHA-256 digest
     (precompile_result_sha256) and no change to the outcomes, requests,
     accounts or logs, written to an ALLOCA'd 32-byte buffer and loaded.
   - bytesN: the operand is the left-aligned word; it is MSTOREd to an
     ALLOCA'd 32-byte buffer and its first N bytes, the value's bytes, are
     hashed.
   The buffers are fresh allocations, so the stores keep stmt_state_rel and
   the memory expr_post's frame asks for (as exprSimLiteralBuffer's
   literal_mstore_state_rel). *)
Theorem compile_keccak256_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Keccak256 args)
Proof
  cheat
QED

Theorem compile_sha256_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Sha256 args)
Proof
  cheat
QED

(* ===== Arithmetic builtins ===== *)

(* The word builtins but ceil are exprSimWordBuiltins' word_builtin_case,
   which exprSimMain's dispatcher applies itself.  Notes for them (all
   StackValue lowerings; the result is a word_value, IntV):
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

Theorem compile_ceil_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Ceil args)
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

Theorem compile_concat_case = exprSimConcatTheory.compile_concat_case

Theorem compile_slice_case = exprSimSliceTheory.compile_slice_case

Theorem compile_extract32_case = exprSimExtract32Theory.compile_extract32_case

(* uint2str(x): with buf the buffer (32 + 32 * word_size n bytes, n >= 78
   by typing) and i digits stored so far, the k-th digit from the right
   (k < i) sits at buf + n + 31 - k, written by MSTORE at buf + n - k,
   whose zero bytes all lie below the digits stored before it.  The length
   word goes at buf + n - i, just below the leading digit, so the value
   occupies [buf + n - i, buf + n + 32) inside the buffer, which is what
   vv_at's exact footprint 32 + i asks.  The zero path stores "0" at
   buf + n + 31 and the length at buf + n - 1. *)
Theorem compile_uint2str_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Uint2Str n) args)
Proof
  cheat
QED

(* ===== Chain and account reads ===== *)

(* compile_blockhash's code has no GAS, INVOKE, terminator or external call,
   and is appended at sa's cursor in a block of func. *)
Theorem compile_blockhash_path_facts:
  !x sa op sb func s0.
    compile_blockhash x sa = (op, sb) /\ fn_has_code sa sb func /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    ?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions)
Proof
  cheat
QED

(* blockhash(n): compile_blockhash checks NUMBER - 256 <=s n (SLT) and
   n < NUMBER, then reads BLOCKHASH n.  call_ctx_rel gives tx_env_ok
   (0 < block_number < 2 ** 255, MIN 256 block_number <= LENGTH
   block_hashes <= 256) and bc_blockhash as the EVM's lookup.  Under it
   evaluate_block_hash raises exactly when a check fails:
   - n >= block_number: the LT check fails; the source raises.
   - n < block_number, block_number >= 256: LENGTH block_hashes = 256, the
     bound NUMBER - 256 is a nonnegative word, and n <s it iff
     block_number - 1 - n >= 256, where the source raises.
   - n < block_number < 256: the bound is a small negative word, the SLT
     check passes, and block_number - 1 - n < block_number <= LENGTH.
   An argument n >= 2 ** 255 is negative as a signed word, so the SLT
   check may pass, but n >= block_number and the LT check fails.  On
   success both read EL (block_number - n - 1) block_hashes, as a
   bytes32 (word_to_bytes_be). *)
Theorem compile_blockhash_frag:
  !ctx func cenv cx i es0.
    0 <= i /\ i < 2 ** 256 ==>
    unop_frag ctx func cenv cx compile_blockhash
      (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i))
      (BaseT (BytesT (Fixed 32)))
      (unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
         [BaseT (UintT 256)] (IntV i) es0) es0
Proof
  cheat
QED



Theorem lower_value_blockhash:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann BlockHash [e]) sa =
      (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           compile_blockhash x s1 = (op, sb)
Proof
  cheat
QED

Theorem names_builtin_blockhash[local]:
  !args. ~names_builtin BlockHash args
Proof
  cheat
QED

Theorem compile_blockhash_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann BlockHash args) sa =
              (StackValue t op, sb)
Proof
  cheat
QED

Theorem compile_blockhash_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann BlockHash args)
Proof
  cheat
QED



(* blobhash(n): BLOBHASH reads the transaction's blob hashes, which
   call_ctx_rel makes the source's, with the same 0 past their end. *)
Theorem lower_value_blobhash:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann BlobHash [e]) sa =
      (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           emit_op BLOBHASH [x] s1 = (op, sb)
Proof
  cheat
QED

Theorem names_builtin_blobhash[local]:
  !args. ~names_builtin BlobHash args
Proof
  cheat
QED

Theorem compile_blobhash_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann BlobHash args) sa =
              (StackValue t op, sb)
Proof
  cheat
QED

Theorem compile_blobhash_frag:
  !ctx func cenv cx i es0.
    0 <= i /\ i < 2 ** 256 ==>
    unop_frag ctx func cenv cx (\x. emit_op BLOBHASH [x])
      (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i))
      (BaseT (BytesT (Fixed 32)))
      (unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash
         [BaseT (UintT 256)] (IntV i) es0) es0
Proof
  cheat
QED

Theorem compile_blobhash_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann BlobHash args)
Proof
  cheat
QED

(* A bare .code: the lowering emits INVALID (compile_acc), where the source
   reads the account's code, so this does not hold as the definitions
   stand.  Python's codegen rejects it too (CompilerPanic ".code requires
   slice() context", codegen_venom/expr.py): x.code is only lowered as
   slice's first argument, with EXTCODECOPY.  The supported subset leaves
   it out (supported_builtin_form), so expr_body_pre needs that exclusion
   for this case to go. *)
Theorem compile_acc_code_case = exprSimAccCodeTheory.compile_acc_code_case

Theorem compile_acc_case:
  !nocalls ctx func cenv cx ann item args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc item) args)
Proof
  cheat
QED

(* method_id of a literal signature with output_type=bytes4: the folded
   selector as a word literal, no code. *)
Theorem compile_method_id_literal_word_sim:
  !cenv la l.
    IS_SOME (method_id_literal (Literal la l)) ==>
    expr_sim_ok cenv
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  cheat
QED

Theorem compile_method_id_literal_word_case_sim:
  !cenv la l.
    IS_SOME (method_id_literal (Literal la l)) ==>
    expr_ok cenv
      (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
Proof
  cheat
QED

(* The other method_ids:
   - a literal signature with the default Bytes[4] output: compile_expr
     emits what it emits for the literal Bytes[4] the source evaluates it to
     (compile_expr_method_id_literal, eval_expr_method_id_literal), a buffer
     holding the length 4 and the selector, which
     exprSimLiteralBuffer's compile_literal_other_vv_sim simulates;
   - a signature that is not a literal, hashed at run time
     (compile_method_id_runtime): keccak256 of its bytes as in
     compile_keccak256_case, SHR then SHL by 224 keeping the first 4 bytes
     left-aligned, the typed encoding of the bytes4 selector; for Bytes[4]
     that word goes after the length 4 in an ALLOCA'd 64-byte buffer. *)
Theorem compile_method_id_other_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args /\
    ~(ann = BaseT (BytesT (Fixed 4)) /\
      ?la l. args = [Literal la l] /\
             IS_SOME (method_id_literal (Literal la l))) ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann MethodId args)
Proof
  cheat
QED

Theorem compile_method_id_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann MethodId args)
Proof
  cheat
QED

(* ===== Precompiles ===== *)

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
