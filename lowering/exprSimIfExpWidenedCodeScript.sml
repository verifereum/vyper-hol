Theory exprSimIfExpWidenedCode
Ancestors
  exprSimIfExp exprSimUnwrap exprLoweringProps fragExec stmtSimProps
  emitHelperProps compileEnv

Theorem code_interface_probe[local]:
  compile_expr ce ty (IfExp ann c a b) st = (vv,st') /\
  fn_has_code st st' func /\ local_ptrs_reserved ce st /\
  (!sa sb op. lower_value compile_expr ce (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
  (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr ce ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) ==> ?x:compile_state. x = st
Proof
  strip_tac >> drule_all compile_expr_ifexp_states >> strip_tac >>
  imp_res_tac compile_expr_extends >>
  imp_res_tac cs_extends_emit_inst >>
  imp_res_tac cs_extends_new_block >>
  `ci_mono s7a s8` by
    metis_tac[ci_mono_compile_ifexp_arm, pairTheory.SND] >>
  `ci_mono s11a s12` by
    metis_tac[ci_mono_compile_ifexp_arm, pairTheory.SND] >>
  fs[ci_mono_def] >>
  `cs_extends s7a st' /\ cs_extends s11a st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code st s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s7 s7a func /\ fn_has_code s7a s8 func /\
   fn_has_code s8 s9 func /\ fn_has_code s9 s10 func /\
   fn_has_code s11 s11a func /\ fn_has_code s11a s12 func /\
   fn_has_code s12 s13 func /\ fn_has_code s13 s14 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `local_ptrs_reserved ce s7 /\ local_ptrs_reserved ce s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  imp_res_tac emit_inst_extends >>
  `!s b. s.vs_current_bb = s5.cs_current_bb /\
    s.vs_inst_idx = LENGTH s5.cs_current_insts /\ ~s.vs_halted /\
    eval_operand cond_op s = SOME (if b then 1w else 0w) ==>
    gas_path ctx func s 0 (OK (jump_to (if b then tl else el) s))` by
    (rpt strip_tac >> irule assert_jnz_zero_path >> metis_tac[]) >>
  simp[]
QED
