(*
 * Expression simulation: the builtins (#636, Builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) and of the body
 * simulation (bodySimExprCases) for the builtins that are neither operators
 * nor aggregates.  Each is stated over exprSimHyps' shared judgments: from
 * exprs_case of the operands, expr_vv_case of the builtin.  Row 3's word
 * builtins but ceil (exprSimWordBuiltins' word_builtin_case), rows 2 and 7
 * on exprSimHash's machinery, row 5 (here), row 6's account reads but
 * .code (in exprSimAccounts) and ecrecover are proved; the rest are
 * cheated, for the later #636 PRs.  Each #636 Builtins row is:
 *   1 len, len(msg.data), msg.data slices: compile_len_case (by
 *     exprSimLen's compile_len_vv_case, and compile_len_ctor_code_case for
 *     an immutable in the constructor, unprovable for now, below),
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
 *     blob hashes call_ctx_rel relates to the transaction's (blockhash,
 *     compile_blockhash_case, is #636 Leaves row 5, with block.prevhash)
 *   6 account reads: compile_acc_case; all but .code by exprSimAccounts'
 *     compile_acc_read_case, .code in compile_acc_code_case (unprovable
 *     for now, below)
 *   7 method_id: compile_method_id_case; a literal signature with
 *     output_type=bytes4 by compile_method_id_literal_word_sim (the folded
 *     selector, a word literal), the rest in compile_method_id_other_case
 *   8 ecrecover, ecadd, ecmul: exprSimPrecompiles'
 *     compile_ecrecover_call_case; compile_ecadd_sim and compile_ecmul_sim,
 *     still stated over expr_sim_below, so for compile_expr_sim only
 *
 * Unprovable as the definitions stand, to be fixed in the lowering or in
 * state_rel before their PRs:
 *   - compile_len_ctor_code_case, len of an immutable in the constructor:
 *     immutables_rel relates the immutable's first word to its whole
 *     value, not to its length.
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
  list rich_list exprSim exprSimHyps vyperAST exprSimWordBuiltins
  exprSimWordArgs exprSimHash vyperTypeSystem exprLowering compileEnv
  valueEncoding fragExec vyperInterpreter vyperState vyperContext
  vyperValueOperation venomState exprSimAccounts exprSimUnop
  exprSimOperators exprBopLowering builtinMisc venomExecSemantics venomInst
  exprSimCalldata exprSimCalldataSlice exprSimLen exprSimPrecompiles
  vyperValue exprLoweringProps vyperTyping

(* ===== Lengths and calldata ===== *)

(* len of an operand in code, an immutable, in the constructor: the
   lowering loads the immutable's first word with ILOAD, but immutables_rel
   relates that word to typed_val_to_w256 of the whole value, not to its
   length, so this does not hold as the definitions stand.  (At runtime it
   is exprSimLen's compile_len_vv_case.) *)
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
  rpt strip_tac >>
  Cases_on `cenv.ce_is_ctor /\
            ?ty st. vv_location (FST (compile_expr cenv ty (HD args) st)) =
                    SOME LocCode`
  >- (irule compile_len_ctor_code_case >> metis_tac[]) >>
  irule compile_len_vv_case >> gvs[] >> metis_tac[]
QED

Theorem compile_calldata_len_case:
  !nocalls ctx func cenv cx ann args.
    expr_vv_case nocalls ctx func cenv cx (Builtin ann CalldataLen args)
Proof
  rpt gen_tac >> irule expr_vv_case_nil >> conj_tac
  >- rw[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
        vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rw[expr_vv_ok_def] >>
  `args = []` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> irule (SRULE [expr_vv_ok_def] compile_calldatasize_sim) >>
  simp[expr_sim_below_def, list_size_def] >> metis_tac[]
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
  rw[expr_vv_case_def] >>
  `well_typed_builtin_app ann Keccak256 (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  mp_tac (Q.INST [`b` |-> `Keccak256`, `ty` |-> `ann`,
    `ts` |-> `MAP expr_type args`] hash_builtin_types) >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `Builtin _ Keccak256 [e]` >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[unop_operand_sim] >>
  irule compile_keccak256_typed_vv_sim >> simp[] >> metis_tac[]
QED

Theorem compile_sha256_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Sha256 args)
Proof
  rw[expr_vv_case_def] >>
  `well_typed_builtin_app ann Sha256 (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  mp_tac (Q.INST [`b` |-> `Sha256`, `ty` |-> `ann`,
    `ts` |-> `MAP expr_type args`] hash_builtin_types) >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `Builtin _ Sha256 [e]` >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[unop_operand_sim] >>
  irule compile_sha256_typed_vv_sim >> simp[] >> metis_tac[]
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

Theorem compile_concat_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Concat n) args)
Proof
  cheat
QED

Theorem compile_slice_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  cheat
QED

Theorem compile_extract32_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Extract32 t args)
Proof
  cheat
QED

Theorem compile_uint2str_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Uint2Str n) args)
Proof
  cheat
QED

(* ===== Chain and account reads ===== *)

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
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, compile_blobhash_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem names_builtin_blobhash[local]:
  !args. ~names_builtin BlobHash args
Proof
  `!bt args. names_builtin bt args ==> bt <> BlobHash` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_blobhash_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann BlobHash args) sa =
              (StackValue t op, sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_blobhash] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, as_stack_val_pair] >>
  simp[pairTheory.UNCURRY]
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
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def, evaluate_blob_hash_def] >>
  irule unop_frag_read >>
  simp[vyperValueTheory.evaluate_type_def, is_word_type_def,
       is_terminator_def, typed_val_to_w256_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
  rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
      stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[val_to_w256_def, integer_wordTheory.i2w_pos, wordsTheory.dimword_def]
QED

Theorem compile_blobhash_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann BlobHash args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_blobhash_stack] >>
  rw[expr_sim_case_def] >>
  `?e1. args = [e1] /\ ann = BaseT (BytesT (Fixed 32)) /\
        expr_type e1 = BaseT (UintT 256)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  `expr_body_pre cenv cx env e1 es /\
   expr_sim ctx func cenv cx ty e1 es` by
    metis_tac[unop_operand_sim] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `BaseT (BytesT (Fixed 32))`,
               `BlobHash`, `e1`, `ty`, `\x. emit_op BLOBHASH [x]`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_blobhash >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
        drule emit_op_extends_next_var >> simp[])
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `v1`, `es1`] mp_tac
      expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def] >>
    Cases_on `v1` >> gvs[value_has_type_def] >>
    irule compile_blobhash_frag >>
    `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >> gvs[]) >>
  simp[]
QED

(* A bare .code: the lowering emits INVALID (compile_acc), where the source
   reads the account's code, so this does not hold as the definitions
   stand.  Python's codegen rejects it too (CompilerPanic ".code requires
   slice() context", codegen_venom/expr.py): x.code is only lowered as
   slice's first argument, with EXTCODECOPY.  The supported subset leaves
   it out (supported_builtin_form), so expr_body_pre needs that exclusion
   for this case to go. *)
Theorem compile_acc_code_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc Code) args)
Proof
  cheat
QED

Theorem compile_acc_case:
  !nocalls ctx func cenv cx ann item args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc item) args)
Proof
  rpt strip_tac >> Cases_on `item = Code`
  >- (gvs[] >> irule compile_acc_code_case >> simp[]) >>
  irule compile_acc_read_case >> simp[]
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
  Cases_on `eval_expr cx
    (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]) es` >>
  drule_all eval_expr_method_id_literal >> strip_tac >>
  gvs[bind_def, read_result_def, return_def] >>
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
  rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  `well_typed_builtin_app ann MethodId (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`,
    `ts` |-> `MAP expr_type args`] hash_builtin_types) >>
  simp[] >>
  disch_then (qx_choose_then `t` (mp_tac o CONJUNCT1)) >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `Builtin _ MethodId [e]` >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[unop_operand_sim] >>
  irule compile_method_id_other_typed_vv_sim >> simp[] >> metis_tac[]
QED

Theorem compile_method_id_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann MethodId args)
Proof
  rpt strip_tac >>
  Cases_on `ann = BaseT (BytesT (Fixed 4)) /\
            ?la l. args = [Literal la l] /\
                   IS_SOME (method_id_literal (Literal la l))`
  >- (gvs[] >> irule (cj 2 expr_case_of_ok) >>
      simp[compile_method_id_literal_word_case_sim,
           vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  irule compile_method_id_other_case >> asm_rewrite_tac[]
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

