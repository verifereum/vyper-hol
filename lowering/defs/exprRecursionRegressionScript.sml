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
  simp[compile_builtin_dispatch_body_def, pairTheory.UNCURRY]
QED

(* The start is lowered exactly once; the fixed length is not an AST operand. *)
Theorem calldata_slice_dispatch:
  compile_builtin_dispatch_body cfn cenv ret_ty ty (CalldataSlice n) [start] st =
    (let (start_op, st1) = lower_value cfn cenv (expr_type start) start st in
     as_ptr_val ret_ty LocMemory
       (compile_slice_calldata start_op (Lit (n2w n))
          (type_memory_bytes cenv ret_ty) st1))
Proof
  simp[compile_builtin_dispatch_body_def, pairTheory.UNCURRY]
QED

(* Calldata is copied directly, without lowering a fictitious bytes operand. *)
Theorem raw_call_calldata_dispatch:
  compile_call cfn cenv ret_ty ty (RawCallCalldataTarget rcf)
    (addr_e :: kw_es) default_ret st =
    (let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
     let ((value_opt, gas_opt, _), st2) =
       compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws kw_es st1 in
     let value_op = (case value_opt of SOME v => v | NONE => Lit 0w) in
     let (gas_op, st3) =
       (case gas_opt of SOME g => (g, st2) | NONE => emit_op GAS [] st2) in
     let call_ty = if rcf.rcf_is_delegate then DelegateCall
                   else if rcf.rcf_is_static then StaticCall
                   else RegularCall in
     let ((out_val, out_ptr), st4) =
       compile_raw_call_outbuf rcf.rcf_max_outsize st3 in
     let ((data_ptr, data_len), st5) = compile_msg_data_to_memory st4 in
     let (result_op, st6) = compile_raw_call_finish addr_op data_ptr data_len
       gas_op value_op call_ty rcf.rcf_max_outsize rcf.rcf_revert_on_failure
       out_val out_ptr st5 in
     if rcf.rcf_max_outsize = 0 then (StackValue ret_ty result_op, st6)
     else (LocatedValue ret_ty (mk_ptr result_op LocMemory), st6))
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

(* RawLog lowers topics before data, but LOG consumes them in reverse order.
   The fixed-data path allocates before evaluating the data expression. *)
Theorem raw_log_four_topics_fixed_dispatch:
  expr_type data_e = BaseT (BytesT (Fixed 32)) ==>
  compile_call cfn cenv ret_ty ty RawLog
    [Builtin ann (MakeArray elem_ty bnd) [a;b;c;d]; data_e] default_ret st =
    (let (ops, st1) = compile_multi_exprs cfn cenv [a;b;c;d] st in
     let (tmp, st2) = compile_alloc_buffer 32 st1 in
     let (v, st3) = lower_value cfn cenv (BaseT (BytesT (Fixed 32))) data_e st2 in
     let (_, st4) = emit_void MSTORE [tmp.buf_operand; v] st3 in
     let (_, st5) = emit_inst LOG
       (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w; tmp.buf_operand]) [] st4 in
     (StackValue ret_ty (Lit 0w), st5))
Proof
  simp[compile_call_def, raw_log_topic_exprs_def]
QED

(* For dynamic Bytes, lower_value performs any required storage-to-memory copy.
   The log skips the length word of that memory representation. *)
Theorem raw_log_empty_topics_dynamic_dispatch:
  expr_type data_e <> BaseT (BytesT (Fixed 32)) ==>
  compile_call cfn cenv ret_ty ty RawLog
    [Builtin ann (MakeArray elem_ty bnd) []; data_e] default_ret st =
    (let (data, st1) = lower_value cfn cenv (expr_type data_e) data_e st in
     let (len, st2) = emit_op MLOAD [data] st1 in
     let (ptr, st3) = emit_op ADD [data; Lit 32w] st2 in
     let (_, st4) = emit_inst LOG [Lit 0w; len; ptr] [] st3 in
     (StackValue ret_ty (Lit 0w), st4))
Proof
  simp[compile_call_def, raw_log_topic_exprs_def, compile_multi_exprs_def,
       comp_return_def]
QED

val _ = List.app (fn (_,th) =>
  if null (List.filter (fn s => s <> "DISK_THM") (fst (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "expression regression oracle dependency")
  (DB.thms "exprRecursionRegression");

(* Bytestring comparisons: literal fast path and left-to-right hashing. *)
Theorem bytestring_string_literal_selection:
  (case bytestring_literal_hash (Literal ty (StringL s)) of
     SOME h => (Lit h,st)
   | NONE => fallback st) =
  (Lit (word_of_bytes_be (Keccak_256_w64 (MAP (n2w o ORD) s)) : bytes32),st)
Proof
  simp[bytestring_literal_hash_def]
QED

Theorem bytestring_bytes_literal_selection:
  (case bytestring_literal_hash (Literal ty (BytesL bs)) of
     SOME h => (Lit h,st)
   | NONE => fallback st) =
  (Lit (word_of_bytes_be (Keccak_256_w64 bs) : bytes32),st)
Proof
  simp[bytestring_literal_hash_def]
QED

(* In the mixed case, the runtime left hash is completed before the
   literal right digest is compared; the right literal is never lowered. *)
Theorem bytestring_mixed_eq_dispatch:
  is_bytestring_type (expr_type e) /\ bytestring_literal_hash e = NONE ==>
  compile_builtin_dispatch_body cfn cenv ret_ty ty (Bop Eq)
    [e; Literal ann (BytesL bs)] st =
  (let (p,st1) = lower_value cfn cenv (expr_type e) e st in
   let (h,st2) = compile_bytestring_hash p st1 in
   as_stack_val ret_ty
     (emit_op EQ [h; Lit (word_of_bytes_be (Keccak_256_w64 bs))] st2))
Proof
  simp[compile_builtin_dispatch_body_def, bytestring_literal_hash_def,
       pairTheory.UNCURRY]
QED

Theorem bytestring_runtime_hash_order:
  is_bytestring_type (expr_type e1) /\
  bytestring_literal_hash e1 = NONE /\ bytestring_literal_hash e2 = NONE ==>
  compile_builtin_dispatch_body cfn cenv ret_ty ty (Bop Eq) [e1;e2] st =
  (let (p1,st1) = lower_value cfn cenv (expr_type e1) e1 st in
   let (h1,st2) = compile_bytestring_hash p1 st1 in
   let (p2,st3) = lower_value cfn cenv (expr_type e1) e2 st2 in
   let (h2,st4) = compile_bytestring_hash p2 st3 in
   as_stack_val ret_ty (emit_op EQ [h1;h2] st4))
Proof
  simp[compile_builtin_dispatch_body_def, pairTheory.UNCURRY]
QED

val () = List.app (fn (name, th) =>
  let val (oracles, _) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles then
      print ("Kernel-closed: " ^ name ^ "\n")
    else raise Fail ("Unexpected oracle dependency: " ^ name)
  end)
  [("bytestring_string_literal_selection", bytestring_string_literal_selection),
   ("bytestring_bytes_literal_selection", bytestring_bytes_literal_selection),
   ("bytestring_mixed_eq_dispatch", bytestring_mixed_eq_dispatch),
   ("bytestring_runtime_hash_order", bytestring_runtime_hash_order)];
