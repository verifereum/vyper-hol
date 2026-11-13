Theory runtimeSymSrcGetterExpr
Ancestors
  runtimeSymSrcOperandSequences runtimeSymSrcContextComplete
  runtimeSymSrcSubscriptGenerators runtimeSymSrcSubscriptPrimitives
  runtimeSymSrcInterfaces runtimeSymSrcEmission exprLowering vyperGetter
  vyperAST compileEnv context list venomInst stackPlanTypes

Theorem runtime_sym_getter_lower_value_raw:
  (!s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  lower_value cfn ce ty e s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_all runtime_sym_unwrap_value >> simp[]
QED

Theorem runtime_sym_getter_subscript_raw:
  (!t s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce t be s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!t s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    cfn ce t key s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_subscript cfn ce rt ty be key s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> Cases_on `cfn ce ty be s` >>
  `EVERY runtime_sym_inst (state_insts r) /\ runtime_sym_value q` by
    metis_tac[] >>
  Cases_on `(if copies_subscript_base ce be key then compile_snapshot_vv ce T q else comp_return q) r` >>
  rename1 `(if copies_subscript_base ce be key then compile_snapshot_vv ce T q else comp_return q) r = (bv,bs)` >>
  `EVERY runtime_sym_inst (state_insts bs) /\ runtime_sym_value bv` by
    (Cases_on `copies_subscript_base ce be key` >>
     gvs[comp_return_def] >> metis_tac[runtime_sym_snapshot_vv]) >>
  drule_at (Pat `runtime_sym_value bv`) runtime_sym_value_operand >> strip_tac >>
  qpat_x_assum `compile_subscript _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_subscript_def, comp_bind_def] >>
  `!kt op t. lower_value cfn ce kt key bs = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     drule_at (Pat `lower_value _ _ _ _ _ = _`) runtime_sym_getter_lower_value_raw >>
     simp[] >> disch_then irule >>
     rpt gen_tac >> strip_tac >> first_assum drule_all >> simp[]) >>
  pop_assum (mk_asm "key_safe") >>
  (Cases_on `place_type ce be` >> simp[NoAsms]
   >- (strip_tac >> irule runtime_sym_map_sequence >>
       conj_tac >- metis_tac[runtime_sym_keccak256_key] >>
       conj_tac >- metis_tac[runtime_sym_mapping_subscript] >>
       goal_assum (drule_at (Pos last)) >> asm_rewrite_tac[] >>
       asm "key_safe" (qspec_then `expr_type key` MATCH_ACCEPT_TAC)) >>
   Cases_on `t` >> simp[NoAsms] >>
   CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC HO_REWR_CONV (GSYM comp_bind_assoc))) >> strip_tac >>
   irule runtime_sym_locate_sequence >>
   goal_assum (drule_at (Pos last)) >> rpt gen_tac >> strip_tac
   >>~- ([`place_type ce be = ValPT (TupleT _)`], metis_tac[runtime_sym_tuple_subscript])
   >>~- ([`place_type ce be = ValPT (StructT _)`], metis_tac[runtime_sym_tuple_subscript]) >>
   irule runtime_sym_operand_sequence >>
   goal_assum (drule_at (Pos last)) >>
   (conj_tac >- (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
     drule_at (Pos last) runtime_sym_array_subscript >> simp[]) >>
    rpt gen_tac >> strip_tac >> asm "key_safe" irule >> qexists_tac `ty` >> asm_rewrite_tac[]))
QED

Theorem runtime_sym_getter_name_raw:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty (Name rt n) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  metis_tac[runtime_sym_compile_name]
QED

Theorem runtime_sym_getter_topname_raw:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce ty (TopLevelName rt ns) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars ns` >>
  simp[NoAsms, runtime_sym_value_def, mk_ptr_def, is_label_operand_def] >>
  strip_tac >> gvs[] >>
  TRY (Cases_on `x` >> gvs[runtime_sym_value_def, mk_ptr_def, is_label_operand_def]) >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_inst_def, mk_inst_def, runtime_sym_value_def,
       is_label_operand_def]
QED

Theorem runtime_sym_getter_subscript_expr_raw:
  (!ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty be s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty key s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) ==>
  !ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
     compile_expr ce ty (Subscript rt be key) s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once compile_expr_def, expr_type_def] >> strip_tac >>
  drule_at (Pos last) runtime_sym_getter_subscript_raw >> simp[] >>
  disch_then irule >> metis_tac[]
QED

Theorem runtime_sym_build_getter_expr:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) /\
    (!ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
       compile_expr ce ty e s = (v,s') ==>
       EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) ==>
    !ce ty s v s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
       compile_expr ce ty exp s = (v,s') ==>
       EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  pure_rewrite_tac[LET_THM] >>
  BETA_TAC >> Cases_on `is_ArrayT vt` >> asm_rewrite_tac[] >>
  simp_tac std_ss [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
  rpt (pairarg_tac >> gvs[IgnAsm `!vn. _`]) >> strip_tac >> gvs[]
  >>~- ([`build_getter _ _ _ _ = _`],
         qpat_x_assum `(_ ==> !ce ty s v s'. _)` ho_match_mp_tac >>
         ho_match_mp_tac runtime_sym_getter_subscript_expr_raw >>
         conj_tac >- (first_assum ACCEPT_TAC) >>
         rpt gen_tac >> strip_tac >> drule_all runtime_sym_getter_name_raw >> simp[]) >>
  ho_match_mp_tac runtime_sym_getter_subscript_expr_raw >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> drule_all runtime_sym_getter_name_raw >> simp[]
QED
