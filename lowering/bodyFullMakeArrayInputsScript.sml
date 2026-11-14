(* MakeArray-specific input boundaries for the joint child/store path. *)
Theory bodyFullMakeArrayInputs
Ancestors
  exprSimVVFrame exprOperandVar exprLowering loweringStateRelDefs
  venomState venomInst

Theorem make_array_add_original_post:
  !H ctx func ce cx e es sa sm s0 ee tv vv s buf off dst sn w.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    local_ptrs_reserved ce sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    eval_operand buf s = SOME w /\
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv s ==>
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv
      (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s)
Proof
  rpt strip_tac >>
  irule vv_post_update_var >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `sm` >>
  simp[not_fresh_at_def] >>
  metis_tac[compiler_compile_var, not_fresh_at_def]
QED
