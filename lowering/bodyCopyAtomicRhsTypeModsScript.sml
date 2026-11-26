(* Physical typing at the successful source read of a narrowed atomic RHS. *)
Theory bodyCopyAtomicRhsTypeMods
Ancestors
  exprBodyPreProps exprLowering exprSimProps vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperInterpreter vyperValueOperation
  vyperStatePreservation vyperState vyperValue vyperTypeExprSoundness

Theorem copy_literal_read_lowered_mods:
  (!n s.
     well_typed_expr env (Literal (BaseT (StringT n)) (StringL s)) /\
     (do r <- eval_expr cx (Literal (BaseT (StringT n)) (StringL s));
         read_result cx r od) es = (INL v,es') ==>
     value_runtime_typed env
       (lowered_value_type ce (Literal (BaseT (StringT n)) (StringL s))) v) /\
  (!n bs.
     well_typed_expr env (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) /\
     (do r <- eval_expr cx (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs));
         read_result cx r od) es = (INL v,es') ==>
     value_runtime_typed env
       (lowered_value_type ce
         (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs))) v) /\
  (!n bs.
     well_typed_expr env (Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) /\
     (do r <- eval_expr cx (Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs));
         read_result cx r od) es = (INL v,es') ==>
     value_runtime_typed env
       (lowered_value_type ce
         (Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs))) v)
Proof
  rpt conj_tac >> rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, read_result_def,
      evaluate_literal_def] >>
  gvs[well_typed_expr_def, well_typed_literal_def,
      well_formed_type_def, evaluate_type_def] >>
  simp[value_runtime_typed_def, evaluate_type_def,
       value_has_type_def, compatible_bound_def] >>
  gvs[type_slot_size_def, compatible_bound_def] >>
  imp_res_tac word_size_monotone >> decide_tac
QED

Theorem copy_intcall_read_cast[local]:
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,params,dflts,ret,bd) /\
  (do r <- eval_expr cx (Call ty (IntCall (src,fn)) args drv);
      read_result cx r od) es = (INL v,es') ==>
  ?rtv. evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v
Proof
  strip_tac >>
  qpat_x_assum `(do r <- eval_expr _ _; read_result _ r od) _ = _`
    (assume_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
  fs[ignore_bind_def] >>
  rpt (dxrule bind_split >> strip_tac >> gvs[]) >>
  gvs[lift_option_type_def, return_def, raise_def, read_result_def] >>
  Cases_on `evaluate_type (get_tenv cx) ret` >> gvs[raise_def, return_def] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >> gvs[raise_def, return_def] >>
  metis_tac[safe_cast_result_well_typed]
QED

Theorem copy_intcall_read_lowered_mods:
  expr_sim_inv_mods mods ce cx env es /\
  well_typed_expr env (Call ty (IntCall fid) args drv) /\
  (do r <- eval_expr cx (Call ty (IntCall fid) args drv);
      read_result cx r od) es = (INL v,es') ==>
  value_runtime_typed env (lowered_value_type ce (Call ty (IntCall fid) args drv)) v
Proof
  strip_tac >> PairCases_on `fid` >>
  rename1 `well_typed_expr env (Call _ (IntCall (src,fn)) _ _)` >>
  `?sg. FLOOKUP env.fn_sigs (src,fn) = SOME sg` by
    fs[well_typed_expr_def] >>
  drule_all expr_sim_inv_mods_return_type >> strip_tac >>
  (* Signature consistency relates the same qualified key to the evaluator's
     module and callable lookup, including in the singleton specialization. *)
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (drule expr_sim_inv_mods_env >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  drule_all copy_intcall_read_cast >>
  simp[value_runtime_typed_def, lowered_value_type_def]
QED
