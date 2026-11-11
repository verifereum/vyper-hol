(* Expression-level composition for the memory ABI decoder. *)
Theory abiDecodePtrExpr
Ancestors
  abiDecodePtrOutcome abiDecodePtrTarget abiDecodePtrSupportedTarget
  bodyPtrHashBuiltinsUnary bodyPtrHashBuiltinsSuffix bodyPtrDefs
  exprSimHash exprSimSource exprSimDefs fragGasPathPtr gasOutcome vyperABI
  exprSimExtract32Source exprSimHyps exprSimHypsDefs vyperTypeBuiltins vyperTypeSystem
  exprLowering exprCallBounds context builtinAbi compileEnv
  vyperInterpreter vyperContext vyperState vyperAST list

Theorem type_builtin_body_pre_arity:
  expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
  type_builtin_args_length_ok tb (LENGTH args)
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  drule well_typed_type_builtin_args_length >> simp[]
QED

Theorem eval_expr_unary_type_builtin_action:
  type_builtin_args_length_ok tb 1 ==>
  eval_expr cx (TypeBuiltin ann tb typ [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
       (\w. return (Value w)))
Proof
  strip_tac >> simp[Once evaluate_def] >>
  simp[type_check_def, assert_def, return_def, ignore_bind_def,
       Once evaluate_def, bind_assoc] >>
  simp[Once evaluate_def, assert_def, bind_def, return_def, FUN_EQ_THM]
QED

Theorem abi_decode_body_pre_shape:
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ args) es ==>
  ?e cap. args = [e] /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
    ann = typ /\ expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `LENGTH args = 1` by
    (drule type_builtin_body_pre_arity >> simp[type_builtin_args_length_ok_def]) >>
  Cases_on `args` >> gvs[] >>
  rename1 `TypeBuiltin ann (AbiDecode b) typ [e]` >>
  `expr_body_pre cenv cx env e es` by
    (irule exprOpenFirstOperandTheory.expr_body_pre_type_builtin_head >>
     goal_assum (drule_at Any)) >>
  gvs[expr_body_pre_def, well_typed_expr_def,
      well_typed_type_builtin_args_def, type_builtin_result_ok_def]
QED

Theorem compile_abi_decode_stages:
  compile_expr cenv ty (TypeBuiltin ann (AbiDecode b) typ [e]) sa =
    (let (op,sm) = lower_value compile_expr cenv (expr_type e) e sa in
     let target = if b /\ needs_external_call_wrap typ then TupleT [typ] else typ in
     as_ptr_val ann LocMemory
       (lower_abi_decode op (type_to_abi_dec_info cenv.ce_struct_fields cenv target)
         (abi_static_size cenv.ce_struct_fields target)
         (abi_size_bound cenv.ce_struct_fields target)
         (type_memory_bytes cenv target) sm))
Proof
  rewrite_tac[compile_expr_type_builtin_dispatch] >>
  simp[Once compile_type_builtin_dispatch_component_eq,
       lower_value_def, comp_bind_def, expr_child_callback_def,
       list_size_def, expr_size_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_decode_tuple_source_no_wrap:
  2 <= LENGTH tys ==>
  evaluate_type_builtin cx (AbiDecode b) (TupleT tys) arg_tys [BytesV bs] =
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs]
Proof
  simp[evaluate_type_builtin_def, needs_external_call_wrap_def]
QED

(* A unary TypeBuiltin only needs a pointer-safe suffix for normal operand
   returns; exceptional and exempt operand paths are transported generically. *)
Theorem type_builtin_unary_vv_sim_ptr_suffix:
  expr_body_pre cenv cx env e es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
  type_builtin_args_length_ok tb 1 /\
  (!sa sb vv. compile_expr cenv ty (TypeBuiltin ann tb typ [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 G0 tn0 gs v ee G tn s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
    ee.gas_obs = [] /\
    expr_post ctx func cenv cx e es sa sm s0 ee v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn s /\
    ptr_val_ok cx (expr_type e) v x G tn s /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,func) PG marks
      (bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w))) (ee,s,G,tn)
      (\res ef G' tn' t. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (TypeBuiltin ann tb typ [e]) es sa sb s0 ef tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d cenv cx ef G' tn' t /\
        ptr_vv_ok cx (expr_type (TypeBuiltin ann tb typ [e])) tv vv ef G' tn' t /\
        (!t' op. vv = StackValue t' op /\
          ~is_word_type (expr_type (TypeBuiltin ann tb typ [e])) ==>
          ptr_buf_ok cenv (TypeBuiltin ann tb typ [e]) op G' t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (TypeBuiltin ann tb typ [e]) p.ptr_operand G' t) /\
        ghost_kept cenv es sa G0 tn0 s0 G' tn')
      (\res ef gt r. expr_exit res r)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann tb typ [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann tb typ [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w)))` by
    (irule eval_expr_unary_type_builtin_action >> simp[]) >>
  asm_rewrite_tac[] >> irule hash_expr_sim_ptr_suffix >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[hash_expr_exit_cast]) >>
  rpt strip_tac >>
  qpat_x_assum `!sa sm sb x vv s0 G0 tn0 gs v ee G tn s. _` drule_all >> simp[]
QED
