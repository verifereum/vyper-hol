Theory exprSimHashes
Ancestors
  arithmetic list rich_list words exprSimHyps exprLowering exprLoweringProps
  compileEnv vyperAST vyperInterpreter vyperContext vyperTypeSystem
  vyperState vyperValue exprBopLowering valueEncoding valueEncodingProofs byte keccak
  venomExecSemantics venomInst venomState emitHelper builtinHashing
Libs
  pairLib supportedEvalLib cv_transLib

val () = supportedEvalLib.configure ();

Theorem well_typed_keccak256_args:
  !ann args.
    well_typed_builtin_app ann Keccak256 (MAP expr_type args) ==>
    ?e. args = [e] /\ ann = BaseT (BytesT (Fixed 32)) /\
        ((?m. expr_type e = BaseT (BytesT (Fixed m))) \/
         (?n. expr_type e = BaseT (BytesT (Dynamic n))) \/
         (?n. expr_type e = BaseT (StringT n)))
Proof
  rpt gen_tac >> simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `is_bytes_or_string_type (expr_type e)` >>
  Cases_on `expr_type e` >> gvs[] >>
  rename1 `is_bytes_or_string_type (BaseT bt)` >>
  Cases_on `bt` >> gvs[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[]
QED

Theorem eval_expr_keccak256_cases:
  !cx ann e es res es'.
    eval_expr cx (Builtin ann Keccak256 [e]) es = (res, es') ==>
    (?exc. eval_expr cx e es = (INR exc, es') /\ res = INR exc) \/
    (?tv es1. eval_expr cx e es = (INL tv, es1) /\ !v. tv <> Value v) \/
    ?v. eval_expr cx e es = (INL (Value v), es') /\
        res = (case evaluate_builtin cx es'.accounts ann Keccak256 [expr_type e] [v] of
                 INL w => INL (Value w)
               | INR err => INR (Error err))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `materialise cx tv es1` >>
  Cases_on `?v. tv = Value v` >> gvs[] >>
  simp[materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, lift_sum_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx es1.accounts ann Keccak256 [expr_type e] [v]` >>
  simp[return_def, raise_def] >> rw[] >> gvs[]
QED

Definition keccak256_tail_def:
  keccak256_tail ty x =
    if is_bytestring_type ty then compile_keccak256_bytes x
    else case ty of
      BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m
    | _ => compile_keccak256_word x
End

Theorem compile_expr_keccak256:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Keccak256 [e]) st =
    compile_builtin_dispatch cenv ann ty Keccak256 [e] st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def)] >>
  Cases_on `e` >> simp[compile_expr_body_def, expr_size_def,
    list_size_def, expr_type_def]
QED

Theorem lower_value_keccak256:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Keccak256 [e]) sa =
      (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
      keccak256_tail (expr_type e) x s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_keccak256] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def, keccak256_tail_def] >>
  Cases_on `is_bytestring_type (expr_type e)` >> simp[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  Cases_on `expr_type e` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem fixed_bytes_encoding_readback:
  !bd bs.
    LENGTH bs <= 32 ==>
    TAKE (LENGTH bs)
      (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV bs))) = bs
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       TAKE_word_to_bytes_be_word_of_bytes_be]
QED

Theorem keccak256_encoding:
  !bd bs.
    typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV (Keccak_256_w64 bs)) =
    word_of_bytes T (0w : bytes32) (Keccak_256_w64 bs)
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       word_of_bytes_be_def]
QED

Theorem hash_pointer_wrap_probe:
  w2n ((n2w (dimword(:256) - 32) : bytes32) + 32w) = 0 /\
  dimword(:256) - 32 + 32 = dimword(:256)
Proof
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  wordsLib.WORD_DECIDE_TAC
QED

Definition hash_wrap_memory_def:
  hash_wrap_memory : byte list =
    0w :: (REPLICATE (dimword(:256) - 2) 0w ++ [1w; 1w])
End

Theorem hash_wrap_payload_probe:
  mem_bytes_at (dimword(:256)) 1 hash_wrap_memory = [1w] /\
  mem_bytes_at 0 1 hash_wrap_memory = [0w]
Proof
  simp[hash_wrap_memory_def, mem_bytes_at_def, DROP_APPEND,
       DROP_REPLICATE, TAKE_APPEND, EL_APPEND_EQN,

       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem hash_wrap_value_probe:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [1w])
    (dimword(:256) - 32) hash_wrap_memory
Proof
  simp[val_in_memory_def] >> conj_tac
  >- (simp[hash_wrap_memory_def, mem_word_at_def, DROP_APPEND,
           DROP_REPLICATE, dimword_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC) >>
  simp[hash_wrap_memory_def, mem_bytes_at_def, DROP_APPEND,
       DROP_REPLICATE, TAKE_APPEND, EL_APPEND_EQN,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem hash_wrap_hashes_probe:
  word_of_bytes T (0w : bytes32) (Keccak_256_w64 [0w]) <>
  word_of_bytes T (0w : bytes32) (Keccak_256_w64 [1w])
Proof
  CONV_TAC (RAND_CONV (BINOP_CONV (RAND_CONV cv_eval))) >> EVAL_TAC
QED

Theorem hash_wrap_instruction_probe:
  !s.
    s.vs_memory = hash_wrap_memory ==>
    run_inst_seq
      [mk_inst 0 MLOAD [Lit (n2w (dimword(:256) - 32))] ["%0"];
       mk_inst 1 ADD [Lit (n2w (dimword(:256) - 32)); Lit 32w] ["%1"];
       mk_inst 2 SHA3 [Var "%1"; Var "%0"] ["%2"]] s =
    OK (update_var "%2" (word_of_bytes T 0w (Keccak_256_w64 [0w]))
          (update_var "%1" 0w (update_var "%0" 1w s)))
Proof
  rpt strip_tac >>
  `mload (dimword(:256) - 32) s = 1w` by
    (mp_tac hash_wrap_value_probe >>
     simp[val_in_memory_def, mem_word_at_def, mload_def]) >>
  pure_rewrite_tac[run_inst_seq_def, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def] >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[Once step_inst_base_def, eval_operand_def, lookup_var_def,
       update_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, hash_wrap_memory_def]
QED

Theorem hash_wrap_compiler_probe:
  !cs op cs'.
    cs.cs_next_id = 0 /\ cs.cs_next_var = 0 /\ cs.cs_current_insts = [] /\
    compile_keccak256_bytes (Lit (n2w (dimword(:256) - 32))) cs = (op, cs') ==>
    op = Var "%2" /\
    cs'.cs_current_insts =
      [mk_inst 0 MLOAD [Lit (n2w (dimword(:256) - 32))] ["%0"];
       mk_inst 1 ADD [Lit (n2w (dimword(:256) - 32)); Lit 32w] ["%1"];
       mk_inst 2 SHA3 [Var "%1"; Var "%0"] ["%2"]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_keccak256_bytes_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def] >> EVAL_TAC
QED

Theorem hash_wrap_compiled_run_probe:
  !cs op cs' s.
    cs.cs_next_id = 0 /\ cs.cs_next_var = 0 /\ cs.cs_current_insts = [] /\
    compile_keccak256_bytes (Lit (n2w (dimword(:256) - 32))) cs = (op, cs') /\
    s.vs_memory = hash_wrap_memory ==>
    run_inst_seq cs'.cs_current_insts s =
      OK (update_var "%2" (word_of_bytes T 0w (Keccak_256_w64 [0w]))
            (update_var "%1" 0w (update_var "%0" 1w s)))
Proof
  rpt strip_tac >> drule_all hash_wrap_compiler_probe >> strip_tac >>
  asm_rewrite_tac[] >> irule hash_wrap_instruction_probe >> asm_rewrite_tac[]
QED
