(* Instruction ownership for the bytestring-to-scalar Convert suffix. *)
Theory entryCreateConvertDynamic
Ancestors
  entryCreateAdminSequence entryCreateNativeFirstExit entryCreateFocusSpec
  createSizeTypeBuiltinCode createSizeCutCode exprSimAbiGasBridge
  bodyFullConvertDynamicJoint exprSimConvertFromBytes exprLoweringProps
  exprSimHyps typeBuiltinPrereqs exprCallBounds gasShadowCompileConvert
  entryCreateBodyCut exprSimConvert vyperContext
  fragExec venomInst vyperState vyperInterpreter list

Theorem create_convert_dynamic_suffix_code[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  compile_type_convert x (mk_convert_op src dst) m = (out,b) ==>
  b.cs_current_bb = m.cs_current_bb /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  b.cs_blocks = m.cs_blocks /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\ i.inst_opcode <> GAS)
    (emitted_insts m b)
Proof
  strip_tac >> drule_all dynamic_scalar_straight_read_fresh >>
  simp[dynamic_straight_fresh_def] >> disch_then drule >> strip_tac >> simp[] >>
  drule dynamic_writes_fresh_path_opcodes >>
  simp[EVERY_MEM] >> strip_tac >>
  rpt strip_tac >> res_tac >>
  qpat_x_assum `dynamic_writes_fresh m _`
    (mp_tac o REWRITE_RULE [dynamic_writes_fresh_def,EVERY_MEM]) >>
  disch_then (qspec_then `i` mp_tac) >>
  gvs[freshWritesTheory.fresh_write_op_def]
QED

Theorem create_convert_dynamic_eval[local]:
  eval_expr cx (TypeBuiltin dst Convert dst [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) dst v)
         (\w. INL (Value w)) INR, ee))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
    assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `_ = (raw,ee)` >>
  Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
  Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
    convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val dst` >>
  simp[return_def, raise_def]
QED

Theorem create_convert_dynamic_visit[local]:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m func /\
  create_cut_code {} m b /\ fn_has_code m b func /\
  (m = b \/
   (is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
    valid_conversion (expr_type e) dst /\
    compile_type_convert x (mk_convert_op (expr_type e) dst) m = (out,b))) /\
  create_operand_cut a m E ctx func tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
  create_operand_cut a b E ctx func tops cx st0
    (eval_expr cx (TypeBuiltin dst Convert dst [e])) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (simp[create_convert_dynamic_eval] >> irule create_cut_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_def] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  Cases_on `m = b` >- metis_tac[create_operand_empty_scope,create_interior_visit_def] >>
  qpat_x_assum `m = b \/ _` mp_tac >> simp[] >> strip_tac >>
  `b.cs_current_bb = m.cs_current_bb /\
   b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (emitted_insts m b)` by
    (drule_all create_convert_dynamic_suffix_code >> simp[EVERY_MEM] >> metis_tac[]) >>
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut m b E ctx func tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >> simp[]) >>
  qpat_x_assum `create_operand_cut m b _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED
