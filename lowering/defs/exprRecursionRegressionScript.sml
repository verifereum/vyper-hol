(* Frozen from Thm.hyp exprLowering.compile_expr_component_eq, E[86] and
   E[203], before TASK063 changes (203 original hypotheses). This is a
   regression of the old opaque-callback Defn package, NOT a negation of
   the intended expression equations. No dependence on replacement indices. *)
Theory exprRecursionRegression
Ancestors
  compileEnv vyperAST relation exprLowering exprCallBounds list
  builtinSystem
Libs
  monadsyntax

Definition old_expr_opaque_package_def:
  old_expr_opaque_package
    (R : (compile_env # type # expr # compile_state +
          (compile_env # type # type # builtin # expr list # compile_state +
           compile_env # type # type # type_builtin # type # expr list # compile_state)) ->
         (compile_env # type # expr # compile_state +
          (compile_env # type # type # builtin # expr list # compile_state +
           compile_env # type # type # type_builtin # type # expr list # compile_state)) -> bool) =
    ((∀st ty cenv e ret_ty ann cond then_e else_e a b child_e child_st.
       ret_ty = expr_type e ∧ e = IfExp ann cond then_e else_e ⇒
       R (INL (a,b,child_e,child_st)) (INL (cenv,ty,e,st))) ∧ WF R)
End

Theorem old_expr_opaque_package_impossible:
  ¬old_expr_opaque_package R
Proof
  rewrite_tac[old_expr_opaque_package_def] >> strip_tac >>
  first_x_assum (qspecl_then
    [`ARB`, `ARB`, `ARB`, `IfExp ARB ARB ARB ARB`,
     `expr_type (IfExp ARB ARB ARB ARB)`, `ARB`, `ARB`, `ARB`, `ARB`,
     `ARB`, `ARB`, `IfExp ARB ARB ARB ARB`, `ARB`] mp_tac) >>
  simp[] >> metis_tac[WF_NOT_REFL]
QED

(* ===== Closed definition-interface regression checks ===== *)
(* Small recursive models check the reusable congruence and guarded-callback
   interfaces independently of full compiler equations. Kept with permanent
   regressions, not as a separate production probe theory. *)
Definition ifexp_callback_probe_def:
  ifexp_callback_probe cenv ty e st =
    (case e of
       IfExp ann cond then_e else_e =>
         let (cv, st1) = lower_value ifexp_callback_probe cenv (BaseT BoolT) cond st in
         let (tv, st2) = lower_value ifexp_callback_probe cenv ty then_e st1 in
         let (ev, st3) = lower_value ifexp_callback_probe cenv ty else_e st2 in
         (StackValue ann ev, st3)
     | _ => (StackValue ty (Lit 0w), st))
Termination
  WF_REL_TAC `measure (λ(cenv,ty,e,st). expr_size e)` >>
  simp[expr_size_def]
End

Theorem expr_size_member:
  ∀es e. MEM e es ⇒ expr_size e < list_size expr_size es
Proof
  Induct >> simp[list_size_def] >> rpt strip_tac >>
  gvs[] >> res_tac >> simp[]
QED

Definition list_callback_probe_def:
  list_callback_probe cenv ty e st =
    (case e of
       Builtin ann bi es =>
         let (ops, st1) = compile_multi_exprs list_callback_probe cenv es st in
         (StackValue ann (HD ops), st1)
     | _ => (StackValue ty (Lit 0w), st))
Termination
  WF_REL_TAC `measure (λ(cenv,ty,e,st). expr_size e)` >>
  simp[expr_size_def] >> rpt strip_tac >>
  drule expr_size_member >> simp[]
End

Theorem ifexp_callback_probe_equation:
  ifexp_callback_probe cenv ty (IfExp ann cond then_e else_e) st =
    (let (cv, st1) = lower_value ifexp_callback_probe cenv (BaseT BoolT) cond st in
     let (tv, st2) = lower_value ifexp_callback_probe cenv ty then_e st1 in
     let (ev, st3) = lower_value ifexp_callback_probe cenv ty else_e st2 in
     (StackValue ann ev, st3))
Proof
  simp[Once ifexp_callback_probe_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* ===== Calldata AST dispatch regressions ===== *)

Theorem calldata_len_dispatch:
  compile_builtin_dispatch_body cfn cenv ret_ty ty CalldataLen [] st =
    as_stack_val ret_ty (compile_builtin_calldatasize st)
Proof
  simp[compile_builtin_dispatch_body_def]
QED

(* The start is lowered exactly once; the fixed length is not an AST operand. *)
Theorem calldata_slice_dispatch:
  compile_builtin_dispatch_body cfn cenv ret_ty ty (CalldataSlice n) [start] st =
    (let (start_op, st1) = lower_value cfn cenv (expr_type start) start st in
     as_ptr_val ret_ty LocMemory
       (compile_slice_calldata start_op (Lit (n2w n))
          (type_memory_bytes cenv ret_ty) st1))
Proof
  simp[compile_builtin_dispatch_body_def]
QED

(* Calldata is copied directly, without lowering a fictitious bytes operand. *)
Theorem raw_call_calldata_dispatch:
  compile_call cfn cenv ret_ty ty (RawCallCalldataTarget rcf)
    (addr_e :: kw_es) default_ret st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     let ((data_ptr, data_len), st2) = compile_msg_data_to_memory st1 in
     let ((value_opt, gas_opt, _), st3) =
       compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws kw_es st2 in
     let value_op = (case value_opt of SOME v => v | NONE => Lit 0w) in
     let (gas_op, st4) =
       (case gas_opt of SOME g => (g, st3) | NONE => emit_op GAS [] st3) in
     let call_ty = if rcf.rcf_is_delegate then DelegateCall
                   else if rcf.rcf_is_static then StaticCall
                   else RegularCall in
     let (result_op, st5) = compile_raw_call addr_op data_ptr data_len gas_op
       value_op call_ty rcf.rcf_max_outsize rcf.rcf_revert_on_failure st4 in
     if rcf.rcf_max_outsize = 0 then (StackValue ret_ty result_op, st5)
     else (LocatedValue ret_ty (mk_ptr result_op LocMemory), st5))
Proof
  simp[compile_call_def]
QED

(* An opaque helper still receives a restricted recursive callback. *)
Definition opaque_callback_probe_def:
  opaque_callback_probe cenv ty e st =
    (case e of
       Attribute ann base_e fld =>
         compile_attribute (expr_child_callback (expr_size e) opaque_callback_probe)
           cenv ann ty base_e fld st
     | _ => (StackValue ty (Lit 0w), st))
Termination
  WF_REL_TAC `measure (λ(cenv,ty,e,st). expr_size e)` >> simp[]
End
