Theory bodyFullTypeBuiltinAbiDecode
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimAbiDecode
  vyperContext vyperInterpreter vyperState vyperAST
  bodyFullAbiDecodeExprConditional bodyFullAbiDecodeRecursive
  bodyFullAbiDecodeCallerCutChoice
  bodyFullPredsMods[qualified]

Theorem abi_decode_expr_full_ok:
  !cx v11 b typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  MATCH_MP_TAC abi_decode_expr_full_from_producers >>
  conj_tac
  >- (rpt gen_tac >>
      mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] abi_decode_guarded_to_buf_joint)) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      pure_rewrite_tac [GSYM CONJ_ASSOC] >> disch_then ACCEPT_TAC)
  >> ACCEPT_TAC abi_decode_caller_cut_choice
QED
