(* Literal shortcut compatibility: allocation capacity is not the value tag. *)
Theory bodyFullRaiseReasonLiteralLayout
Ancestors
  revertReasonLayout stringUnwrapLayout stmtReasonMemory context compileEnv
  exprLoweringProps exprLowering

Theorem reason_literal_encoder_memory_layout:
  compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) M sm = ((),sf) ==>
  ?sh.
    sh = sm with <|cs_next_var := sm.cs_next_var+3;
      cs_next_id := sm.cs_next_id+4;
      cs_current_insts := sm.cs_current_insts ++
        revert_reason_prefix sm.cs_next_id sm.cs_next_var M|> /\
    unwrap_value cenv
      (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) sh =
      (buf.buf_operand,sh) /\
    sf = sh with <|cs_next_var := sh.cs_next_var+23;
      cs_next_id := sh.cs_next_id+30;
      cs_current_insts := sh.cs_current_insts ++
        (revert_reason_copy sh.cs_next_id sh.cs_next_var
          (Var (STRING #"%" (toString (sm.cs_next_var+2)))) buf.buf_operand ++
         revert_reason_suffix (sh.cs_next_id+1) (sh.cs_next_var+1)
          (Var (STRING #"%" (toString sm.cs_next_var)))
          (Var (STRING #"%" (toString (sm.cs_next_var+1))))
          (Var (STRING #"%" (toString (sm.cs_next_var+2)))))|>
Proof
  strip_tac >> drule compile_revert_reason_layout >> strip_tac >>
  qexists_tac `sm'` >>
  gvs[unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def]
QED
