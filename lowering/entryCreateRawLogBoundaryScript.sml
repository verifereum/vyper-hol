Theory entryCreateRawLogBoundary
Ancestors
  bodyFullRawLogLayout exprSimCallRawLog exprSimBopInLiteralWord

(* The typed MakeArray supplies the topics directly to the word-list compiler. *)
Theorem create_raw_log_topic_layout:
  well_typed_expr env (Call ann RawLog args dflt) /\
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr (gas_shadow_env shadow_defaults ce) ty (gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr (gas_shadow_env shadow_defaults ce) (MAP gas_shadow_expr xs))) /\
  gas_shadow_state sa shadow_sa /\
  lower_value compile_expr cenv ty (Call ann RawLog args dflt) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env shadow_defaults cenv) ty
    (gas_shadow_expr (Call ann RawLog args dflt)) shadow_sa = (op,shadow_sb) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?topics data n.
    ann = NoneT /\ dflt = NONE /\ n <= 4 /\
    args = [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
                    (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
            data] /\
    LENGTH topics <= 4 /\ compatible_bound (Dynamic n) (LENGTH topics) /\
    well_typed_exprs env topics /\ well_typed_expr env data /\
    EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
      ?m. expr_type data = BaseT (BytesT (Dynamic m))) /\
    op = Lit 0w /\
    compile_call compile_expr cenv ann ty RawLog args dflt sa =
      (StackValue ann (Lit 0w),sb) /\
    ?ops sm shadow_sm sd shadow_sd value sn shadow_sn.
      lower_word_args cenv expr_type topics sa = (ops,sm) /\
      lower_word_args (gas_shadow_env shadow_defaults cenv) expr_type
        (MAP gas_shadow_expr topics) shadow_sa = (ops,shadow_sm) /\
      gas_shadow_state sm shadow_sm /\ gas_shadow_state sd shadow_sd /\
      gas_shadow_state sn shadow_sn /\
      lower_value compile_expr cenv (expr_type data) data sd = (value,sn) /\
      lower_value compile_expr (gas_shadow_env shadow_defaults cenv)
        (expr_type data) (gas_shadow_expr data) shadow_sd = (value,shadow_sn) /\
      ci_mono sa sm /\ ci_mono sm sd /\ ci_mono sd sn /\ ci_mono sn sb /\
      fn_has_code sa sm func /\ fn_has_code sm sd func /\
      fn_has_code sd sn func /\ fn_has_code sn sb func /\
      fn_has_code shadow_sa shadow_sm shadow_func /\
      fn_has_code shadow_sm shadow_sd shadow_func /\
      fn_has_code shadow_sd shadow_sn shadow_func /\
      fn_has_code shadow_sn shadow_sb shadow_func /\
      ((expr_type data = BaseT (BytesT (Fixed 32)) /\
        ?buf s1 shadow_s1.
          compile_alloc_buffer 32 sm = (buf,sd) /\
          compile_alloc_buffer 32 shadow_sm = (buf,shadow_sd) /\
          emit_inst MSTORE [buf.buf_operand;value] [] sn = ((),s1) /\
          emit_inst MSTORE [buf.buf_operand;value] [] shadow_sn = ((),shadow_s1) /\
          emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
            [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
          emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
            [Lit 32w;buf.buf_operand]) [] shadow_s1 = ((),shadow_sb)) \/
       (expr_type data <> BaseT (BytesT (Fixed 32)) /\
        ?len ptr s1 s2 shadow_s1 shadow_s2.
          sd = sm /\ shadow_sd = shadow_sm /\
          emit_op MLOAD [value] sn = (len,s1) /\
          emit_op MLOAD [value] shadow_sn = (len,shadow_s1) /\
          emit_op ADD [value;Lit 32w] s1 = (ptr,s2) /\
          emit_op ADD [value;Lit 32w] shadow_s1 = (ptr,shadow_s2) /\
          emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;ptr]) [] s2 = ((),sb) /\
          emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;ptr]) [] shadow_s2 = ((),shadow_sb)))
Proof
  strip_tac >> drule raw_log_typed_shape >>
  disch_then (qx_choose_then `topics` (qx_choose_then `data` (qx_choose_then `n`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  qexistsl_tac [`topics`, `data`, `n`] >>
  fs[] >> drule_all raw_log_full_layout_shadow >>
  simp[literal_compile_multi_exprs]
QED
