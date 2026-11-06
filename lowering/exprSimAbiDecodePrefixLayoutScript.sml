Theory exprSimAbiDecodePrefixLayout
Ancestors
  exprSimAbiDecodeRealizeCounted exprSimAbiDecodeRealizeFootprint
  exprSimAbiDecodeRealizeStraight abiDecoderAppend abiDecoderLoopCode
  exprLowering builtinAbi compileEnv emitHelper context vyperCompiler venomInst list
  exprSimAbiDecodeRealizeSource exprSimAbiDecodeSizeProbe fragExec
  exprSimAbiDecodeRealizeFunction rich_list arithmetic

Definition abi_decode_realize_prelude_def:
  abi_decode_realize_prelude lo hi =
    do buf <- compile_bytelike_literal (REPLICATE 32 (0w:word8)) 32;
       abi_decode_realize_guard_prefix buf.buf_operand lo hi
    od
End

Definition abi_decode_realize_prelude_code_def:
  abi_decode_realize_prelude_code lo hi entry =
    (SND (abi_decode_realize_prelude lo hi (initial_compile_state entry))).cs_current_insts
End

Theorem abi_decode_realize_prelude_code:
  abi_decode_realize_prelude_code lo hi entry =
  [mk_inst 0 ALLOCA [Lit 64w] ["%0"];
   mk_inst 1 MSTORE [Var "%0"; Lit 32w] [];
   mk_inst 2 ADD [Var "%0"; Lit 32w] ["%1"];
   mk_inst 3 MSTORE [Var "%1"; Lit 0w] [];
   mk_inst 4 MLOAD [Var "%0"] ["%2"];
   mk_inst 5 ADD [Var "%0"; Lit 32w] ["%3"];
   mk_inst 6 LT [Var "%2"; Lit (n2w lo)] ["%4"];
   mk_inst 7 ISZERO [Var "%4"] ["%5"];
   mk_inst 8 GT [Var "%2"; Lit (n2w hi)] ["%6"];
   mk_inst 9 ISZERO [Var "%6"] ["%7"];
   mk_inst 10 AND [Var "%5"; Var "%7"] ["%8"];
   mk_inst 11 ASSERT [Var "%8"] []]
Proof
  EVAL_TAC >> simp[]
QED

Definition abi_decode_realize_tail_def:
  abi_decode_realize_tail info p =
    do buf <- compile_alloc_buffer 64;
       compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD
         (FST p) (SND p) info;
       comp_return buf.buf_operand
    od
End

Theorem abi_decode_realize_tail_appends:
  cs_appends (abi_decode_realize_tail info p)
Proof
  rewrite_tac[abi_decode_realize_tail_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_abi_alloc_buffer] >> gen_tac >>
  irule cs_appends_ignore_bind >>
  simp[cs_appends_return, cj 1 cs_appends_abi_decode_mutual]
QED

Theorem abi_decode_realize_expr_prelude:
  0 < k ==>
  SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
    (abi_decode_realize_expr k) st) =
  SND (comp_bind (abi_decode_realize_prelude 32 (64 + 32 * k))
    (abi_decode_realize_tail
      (type_to_abi_dec_info ce.ce_struct_fields ce (abi_decode_size_probe_type k))) st)
Proof
  strip_tac >>
  simp_tac (srw_ss()) [abi_decode_realize_expr_def, vyperASTTheory.expr_type_def,
    Once compile_expr_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_component_eq, LET_THM] >>
  simp[abi_decode_realize_arg_compile, compile_literal_vv_def,
    comp_bind_def, comp_return_def] >>
  Cases_on `compile_bytelike_literal (REPLICATE 32 (0w:word8)) 32 st` >>
  gvs[unwrap_value_def, is_word_type_def, base_ptr_def, comp_return_def,
    abi_decode_size_probe_memory, abi_decode_size_probe_abi] >>
  `abi_static_size ce.ce_struct_fields (abi_decode_size_probe_type k) = 32` by
    (Cases_on `k` >> gvs[abi_decode_size_probe_type_def, abi_static_size_def,
       abi_embedded_static_size_def, abi_decode_size_probe_dynamic]) >>
  simp[abi_decode_realize_lower_prefix, as_ptr_val_def] >>
  simp[abi_decode_realize_prelude_def, abi_decode_realize_tail_def,
    comp_bind_assoc, comp_ignore_bind_def] >>
  simp[comp_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def]
QED

Theorem abi_decode_realize_after_prelude_extends:
  0 < k ==>
  cs_extends
    (SND (abi_decode_realize_prelude 32 (64 + 32 * k) (initial_compile_state entry)))
    (abi_decode_realize_final ce k entry)
Proof
  strip_tac >>
  simp[abi_decode_realize_final_def, abi_decode_realize_expr_prelude] >>
  Cases_on `abi_decode_realize_prelude 32 (32 * k + 64) (initial_compile_state entry)` >>
  simp[comp_bind_def] >>
  Cases_on `abi_decode_realize_tail
    (type_to_abi_dec_info ce.ce_struct_fields ce (abi_decode_size_probe_type k)) q r` >>
  simp[] >>
  irule (SRULE[cs_appends_def] abi_decode_realize_tail_appends) >>
  goal_assum (drule_at Any)
QED

Theorem abi_decode_realize_prelude_control:
  (SND (abi_decode_realize_prelude lo hi (initial_compile_state entry))).cs_blocks = [] /\
  (SND (abi_decode_realize_prelude lo hi (initial_compile_state entry))).cs_current_bb = entry
Proof
  EVAL_TAC
QED

Theorem abi_decode_realize_final_prelude_prefix:
  0 < k ==>
  isPREFIX (abi_decode_realize_prelude_code 32 (64 + 32 * k) entry)
    (abi_decode_realize_final ce k entry).cs_current_insts
Proof
  strip_tac >> drule abi_decode_realize_after_prelude_extends >>
  simp[cs_extends_def, abi_decode_realize_prelude_control,
       abi_decode_realize_final_single_block, abi_decode_realize_prelude_code_def]
QED

Theorem abi_decode_realize_function_prelude_prefix:
  0 < k ==>
  ?bb. lookup_block entry (abi_decode_realize_function ce k entry).fn_blocks = SOME bb /\
    isPREFIX (abi_decode_realize_prelude_code 32 (64 + 32 * k) entry) bb.bb_instructions
Proof
  strip_tac >> drule abi_decode_realize_final_prelude_prefix >>
  simp[abi_decode_realize_function_def, abi_decode_realize_final_single_block,
       mk_raw_function_def, lookup_block_def, FIND_thm]
QED

Theorem abi_decode_realize_prelude_length[simp]:
  LENGTH (abi_decode_realize_prelude_code lo hi entry) = 12
Proof
  simp[abi_decode_realize_prelude_code]
QED

Theorem abi_decode_realize_prelude_last:
  (LAST (abi_decode_realize_prelude_code lo hi entry)).inst_opcode = ASSERT
Proof
  simp[abi_decode_realize_prelude_code, mk_inst_def]
QED

Theorem abi_decode_realize_final_beyond_guard:
  0 < k /\ j < 12 ==>
  ~((abi_decode_realize_final ce k entry).cs_current_bb = entry /\
    LENGTH (abi_decode_realize_final ce k entry).cs_current_insts = j)
Proof
  strip_tac >> drule abi_decode_realize_final_prelude_prefix >>
  simp[IS_PREFIX_APPEND] >>
  disch_then (qspecl_then [`entry`, `ce`] strip_assume_tac) >> gvs[]
QED
