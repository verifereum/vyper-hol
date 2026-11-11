Theory bodyPtrTypeBuiltinsWidenPost
Ancestors
  bodyPtrTypeBuiltinsWidenFrame bodyPtrTypeBuiltinsWidenActual
  bodyPtrTypeBuiltinsMemoryInterface rawCallBufferPtr bodyFieldMemoryProps
  exprSimExtract32Post exprSimConvertBytes exprLoweringProps
  bodyPtrDefs loweringPosts exprLowering compileEnv venomState

(* The robust encoding is consumed at the supplied raw-run endpoint. *)
Theorem widen_convert_run_success_post:
  compile_bytestring_widen_copy capacity (Var src) n sa = (Var dst,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ not_fresh_at sa src /\ lookup_var src s = SOME a /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v (Var src) s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv ca /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ca.cs_next_var <= sa.cs_next_var /\ ca.cs_next_id <= sa.cs_next_id /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type target /\ ~is_word_type target /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) target = SOME tout /\ value_has_type tv v /\
  convert_result cx (expr_type e) target v = INL vout /\
  val_footprint tv v <= n /\
  lookup_var dst t = SOME b /\
  (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tout vout (w2n b) m) ==>
  expr_post ctx fn cenv cx (TypeBuiltin target Convert target [e]) es ca sb s0
    (ee with gas_obs := []) vout (Var dst) (t with vs_inst_idx := j)
Proof
  strip_tac >>
  `val_wf tout vout` by (irule convert_bytestring_wf >> metis_tac[]) >>
  `val_footprint tout vout <= capacity` by
    (drule_all convert_bytestring_memory >> strip_tac >> simp[]) >>
  `expr_post ctx fn cenv cx (TypeBuiltin target Convert target [e]) ee sa sb s
    ee vout (Var dst) t` by
    (irule widen_copy_run_parent_post >>
     simp[post_value_type_not_int_call, vyperASTTheory.expr_type_def] >>
     qexistsl_tac [`a`,`capacity`,`n`,`Var src`] >>
     simp[eval_operand_def] >> rpt strip_tac >> gvs[] >>
     first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  simp[bodyFieldMemoryPropsTheory.body_field_expr_post_inst_idx,
       extract32_expr_post_end_gas_obs] >>
  `~expr_has_effect (TypeBuiltin target Convert target [e]) ==>
   ~expr_has_effect e` by simp[] >>
  irule convert_expr_post_compose >> metis_tac[]
QED
