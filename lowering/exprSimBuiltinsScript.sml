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
  exprSimWordArgs exprSimHash vyperTypeSystem exprLowering compileEnv loweringStateRelDefs
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
  rpt strip_tac >> irule compile_len_vv_case >> simp[]
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
  rpt gen_tac >> disch_tac >>
  rewrite_tac[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  irule ceil_ready_vv_sim >> qexists_tac `env` >> simp[] >>
  gen_tac >> irule wb_args_ready_of_case >> qexists_tac `nocalls` >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (irule expr_body_pre_builtin_arg >>
      first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[])
  >- metis_tac[int_calls_builtin_arg] >>
  drule ceil_operand_types >> simp[EVERY_MEM]
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
  rw[expr_vv_case_def] >>
  `well_typed_expr env (Builtin ann (Uint2Str n) args)` by
    gvs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  irule compile_uint2str_typed_vv_sim >>
  conj_tac >- metis_tac[] >>
  metis_tac[unop_operand_sim]
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
  rpt gen_tac >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  drule compile_blockhash_outputs >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
        rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[])
  >- simp[]
  >- simp[] >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  simp[DROP_APPEND]
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
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def] >>
  rw[unop_frag_def] >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    (qpat_x_assum `stmt_state_rel ctx func cenv cx es0 s0` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def]) >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos] >>
  `tx_env_ok cx.txn` by gvs[call_ctx_rel_def] >>
  `0 < cx.txn.block_number /\ cx.txn.block_number < 2 ** 255` by
    gvs[tx_env_ok_def] >>
  `s0.vs_block_ctx.bc_number = n2w cx.txn.block_number` by
    gvs[call_ctx_rel_def] >>
  drule_all compile_blockhash_path_facts >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0) /\ vars_ext (drop_fresh sa s0) s0` by
    simp[fresh_vars_wrt_drop_fresh, vars_ext_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME (n2w n)` by
    simp[eval_operand_drop_fresh] >>
  `(drop_fresh sa s0).vs_block_ctx = s0.vs_block_ctx` by
    simp[drop_fresh_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >> fs[EVERY_MEM]) >>
  `(~word_lt (n2w n : bytes32) (n2w cx.txn.block_number - 256w) /\
    n < cx.txn.block_number <=>
    cx.txn.block_number - 256 <= n /\ n < cx.txn.block_number)` by
    (irule blockhash_signed_window >> simp[]) >>
  `cx.txn.block_number MOD dimword(:256) = cx.txn.block_number` by
    (irule arithmeticTheory.LESS_MOD >> fs[wordsTheory.dimword_def]) >>
  pop_assum (assume_tac o SIMP_RULE (srw_ss()) [wordsTheory.dimword_def]) >>
  qpat_assum `compile_blockhash x sa = _` (fn th0 =>
    qpat_assum `eval_operand x (drop_fresh sa s0) = _` (fn th1 =>
      qpat_assum `fresh_vars_wrt sa _` (fn th2 =>
        mp_tac (MATCH_MP compile_blockhash_run (LIST_CONJ [th0, th1, th2]))))) >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  IF_CASES_TAC
  >- (strip_tac >> simp[tx_env_ok_evaluate_block_hash] >>
      suspend "window_ok") >>
  strip_tac >>
  `~(n < cx.txn.block_number /\ cx.txn.block_number - 256 <= n)` by
    (qpat_x_assum `~(_ /\ _)` mp_tac >> decide_tac) >>
  simp[tx_env_ok_evaluate_block_hash] >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >> simp[vars_ext_result_def] >>
  strip_tac >>
  drule_at (Pat `run_inst_seq _ s0 = Abort _ _`) run_inst_seq_abort_zero_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
  impl_tac >- fs[EVERY_MEM] >>
  strip_tac >> goal_assum (drule_at Any) >>
  simp[exit_result_def, expr_exit_def]
QED

Resume compile_blockhash_frag[window_ok]:
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  simp[vars_ext_result_def] >> strip_tac >>
  rename1 `vars_ext tt t` >>
  drule_at (Pat `run_inst_seq _ s0 = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  impl_tac >- (simp[] >> fs[EVERY_MEM]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  simp[] >> strip_tac >>
  qexists_tac `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[gas_marked_path_def] >>
  drule_all compile_blockhash_frame >> strip_tac >>
  `eval_operand op t = SOME (s0.vs_block_ctx.bc_blockhash n)` by
    (gvs[vars_ext_def] >>
     qpat_x_assum `t = tt with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  `s0.vs_block_ctx.bc_blockhash n =
   word_of_bytes_be (word_to_bytes_be
     (EL (cx.txn.block_number - n - 1) cx.txn.block_hashes)) : bytes32` by
    (gvs[call_ctx_rel_def] >>
     drule tx_env_ok_hash_window >>
     disch_then (qspec_then `n` mp_tac) >> gvs[] >> strip_tac >>
     simp[word_of_bytes_be_to_bytes]) >>
  `stmt_state_rel ctx func cenv cx es0 (s0 with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[lookup_var_def]) >>
  qpat_x_assum `t = s0 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[stmt_state_rel_inst_idx, lookup_var_def, expr_val_rel_def,
      typed_val_to_w256_def, vyperValueTheory.evaluate_type_def,
      is_word_type_def, PAD_RIGHT, length_word_to_bytes_be,
      word_of_bytes_be_to_bytes]
QED

Finalise compile_blockhash_frag

Theorem lower_value_blockhash:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann BlockHash [e]) sa =
      (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           compile_blockhash x s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem names_builtin_blockhash[local]:
  !args. ~names_builtin BlockHash args
Proof
  `!bt args. names_builtin bt args ==> bt <> BlockHash` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_blockhash_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann BlockHash args) sa =
              (StackValue t op, sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_blockhash] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, as_stack_val_pair] >>
  simp[pairTheory.UNCURRY]
QED

Theorem compile_blockhash_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann BlockHash args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_blockhash_stack] >>
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
               `BlockHash`, `e1`, `ty`, `compile_blockhash`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_blockhash >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- suspend "shape"
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`, `v1`, `es1`] mp_tac
      expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def] >>
    Cases_on `v1` >> gvs[value_has_type_def] >>
    irule compile_blockhash_frag >>
    `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >> gvs[]) >>
  simp[]
QED

Resume compile_blockhash_case[shape]:
  simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >>
  simp[cs_extends_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Finalise compile_blockhash_case

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
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`, `v1`, `es1`] mp_tac
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
Theorem compile_acc_code_case = exprSimAccCodeTheory.compile_acc_code_case

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
  rw[expr_sim_ok_def, optionTheory.IS_SOME_EXISTS] >>
  irule expr_sim_values >> rpt gen_tac >> strip_tac >>
  rename1 `method_id_literal (Literal la l) = SOME bs` >>
  qexistsl_tac [`[]`, `BytesV (TAKE 4 (Keccak_256_w64 bs))`, `es`, `s0`] >>
  `!gs. bind (eval_expr cx
           (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l]))
         (read_result cx) (es with gas_obs := gs) =
        (INL (BytesV (TAKE 4 (Keccak_256_w64 bs))), es with gas_obs := gs)` by
    (gen_tac >>
     Cases_on `eval_expr cx
       (Builtin (BaseT (BytesT (Fixed 4))) MethodId [Literal la l])
       (es with gas_obs := gs)` >>
     drule_all eval_expr_method_id_literal >> strip_tac >>
     gvs[bind_def, read_result_def, return_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >> simp[NoAsms]) >>
  drule compile_expr_method_id_literal >> strip_tac >>
  gvs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
      lower_value_def, comp_bind_def, compile_literal_vv_def,
      unwrap_value_def, comp_return_def] >>
  conj_tac >- (irule (cj 1 gas_path_rules) >> simp[]) >>
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
  simp[expr_vv_ok_case] >>
  metis_tac[compile_ecadd_call_case, exprs_case_below]
QED

Theorem compile_ecmul_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECMul args)
Proof
  simp[expr_vv_ok_case] >>
  metis_tac[compile_ecmul_call_case, exprs_case_below]
QED
