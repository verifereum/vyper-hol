(* The code layout of a ternary, for its compilation and its gas shadow's
   compilation together: the selected arm's and the condition's code on
   both sides, at shadow-related compiler states. *)
Theory bodyFullIfExpShadow
Ancestors
  gasShadow gasShadowState exprSimIfExp exprLoweringProps exprLowering
  fragExec compileEnv loweringPosts vyperAST

(* The three spine premises are instances of gasShadowCompile's
   gas_shadow_compile_expr, gas_shadow_compiles_lower_value and the
   arm helpers' shadow compilation (alloc buffer, unwrap, store). *)
Theorem ifexp_shadow_code_layout:
  compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  compile_expr cenv ty (gas_shadow_expr (IfExp t c a b)) shadow_st =
    (vv,shadow_st') /\
  gas_shadow_state st shadow_st /\
  fn_has_code st st' func /\ fn_has_code shadow_st shadow_st' shadow_func /\
  local_ptrs_reserved cenv st /\
  (!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
             (compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
             (lower_value compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
                (compile_ifexp_arm cenv rt at av)) ==>
  ?cop sc shadow_sc sj sn tl el xl rv se shadow_se av sea shadow_sea aop
   sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr c)
      shadow_st = (cop,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\
    sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_expr cenv ty (gas_shadow_expr (if sel then a else b)) shadow_se =
      (av,shadow_sea) /\
    gas_shadow_state se shadow_se /\ gas_shadow_state sea shadow_sea /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b))
      av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code st sc func /\ fn_has_code shadow_st shadow_sc shadow_func /\
    fn_has_code sj sn func /\
    fn_has_code se sea func /\ fn_has_code shadow_se shadow_sea shadow_func /\
    fn_has_code sea sx func /\
    fn_has_code sx sy func /\ fn_has_code sy sz func /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    se.cs_next_var <= sea.cs_next_var /\ se.cs_next_id <= sea.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  cheat
QED
