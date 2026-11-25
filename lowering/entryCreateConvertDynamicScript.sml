(* Instruction ownership for the bytestring-to-scalar Convert suffix. *)
Theory entryCreateConvertDynamic
Ancestors
  entryCreateAdminSequence entryCreateNativeFirstExit entryCreateFocusSpec
  createSizeTypeBuiltinCode createSizeCutCode exprSimAbiGasBridge
  bodyFullConvertDynamicJoint exprSimConvertFromBytes exprLoweringProps
  exprSimHyps typeBuiltinPrereqs exprCallBounds gasShadowCompileConvert
  entryCreateBodyCut exprSimConvert vyperContext
  fragExec venomInst vyperState vyperInterpreter list
  entryCreateScopedForce entryCreateScopedBind entryCreateCompletedCut
  gasExemptCert vyperStorageTrace stmtSimDefs exprSimDefs
  entryCreateAdminAbortScope bodyFullConvertDynamicEmptySelected
  entryCreateBlueprintStageJoins createSizeOperandCode bodyFullConvertDynamicSource
  bodyFullConvertDynamicOriginRule bodyFullConvertDynamicSite bodyFullConvertSignedOrigin
  bodyFullConvertBytesWordSuffix bodyPtrTypeBuiltinsBytesWordTypes fragGasOriginPtr abiEncoderProps
  bodyFullEmptyLeafData exprSimFullBundleProps s1PrefixDefs entryCreateIntervalLayout

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
  rewrite_tac[convert_dynamic_source_bind]
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

(* Re-type only the exceptional result; the selected endpoint and ghosts
   (including the witnesses outside the horizon quantifier) stay fixed. *)
Theorem create_convert_dynamic_child_exit[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source
    (es,s,G,tn) Q (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source
    (es,s,G,tn) Q
    (\H (res : value + vyperState$exception) ee gt r.
       ?exc. res = INR exc /\
         create_operand_exit_post C cx H (INR exc : eval_result + vyperState$exception)
           ee gt r)
Proof
  rewrite_tac[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[]) >>
  all_tac >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >>
      fs[create_operand_exit_post_def, expr_exit_def, halt_exit_def,
         stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The continuation is supplied at the actual normal return of the forced
   child. The cut itself does not rely on any successful child outcome. *)
Theorem create_convert_dynamic_bind_at:
  create_force_read_site (\vv. T) /\
  (!ce' cx' tops' vv m op b E C f p d k t before key g i u after.
     body_inv tops' C ce' cx' /\ MEM f C.ctx_functions /\
     unwrap_value ce' vv m = (op,b) /\ fn_has_code m b f /\
     create_interior_visit m b E C f (p,d,k) t (before,(key,g,i,u),after) ==>
     ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) /\
  (!a m b. cs_extends a m /\ cs_extends m b /\ L a b ==> L a m) /\
  (!a m b u. cs_extends a m /\ cs_extends m b /\ L a b /\
     create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) /\
  (!a m b s.
     body_inv tops C ce cx /\ MEM f C.ctx_functions /\
     create_cut_code {} a m /\ fn_has_code a m f /\ create_cut_region a m s /\
     a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
     (!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) ==>
     (!marks t. create_expr_prefix a m E C f s marks t ==> create_expr_prefix a b E C f s marks t) /\
     (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
                create_operand_full_scope a b E C f s marks r) /\
     (!marks. create_operand_focus_scope a m E C f s marks ==>
              create_operand_focus_scope a b E C f s marks)) /\
  (!a m b E C f ce cx tops p d k s before hit after.
     body_inv tops C ce cx /\ MEM f C.ctx_functions /\
     create_cut_code {} a m /\ fn_has_code a m f /\
     create_cut_code {} m b /\ fn_has_code m b f /\
     create_interior_visit a b E C f (p,d,k) s (before,hit,after) ==>
     create_interior_visit a m E C f (p,d,k) s (before,hit,after) \/
     ?t d1 k1 front back. before = front ++ back /\ create_operand_at m t /\
       RTC (create_operand_native_step a m E C f p) (d,k,s,[]) (d1,k1,t,front) /\
       create_expr_prefix a m E C f s (create_cut_marks E front) t /\
       create_interior_visit m b E C f (p,d1,k1) t (back,hit,after)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        ~is_word_type (post_value_type ce e) ==>
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,m,sha,shm,x,s0,G0,tn0) /\ L a m /\
  (!u shu w. expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
      (st0,a,u,sha,shu,w,s0,G0,tn0) /\ L a u ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a u
      (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,D,C,f) ce cx e
         (es,a,u,s0,w,G0,tn0) H res ee G tn t /\ create_operand_at u t)
      (create_operand_exit_post C cx) /\
    create_operand_cut a u E C f tops cx st0 (eval_expr cx e) (es,s0)) /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  (m = b \/
   (is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
    valid_conversion (expr_type e) dst /\
    compile_type_convert x (mk_convert_op (expr_type e) dst) m = (out,b))) /\
  (!marks. create_operand_focus_scope a m E C f s0 marks ==>
           create_operand_focus_scope a b E C f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s0 marks r ==>
             create_operand_full_scope a b E C f s0 marks r) /\
  (!left t right. create_operand_full_scope a m E C f s0 left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s0 (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s0 left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s0 (left ++ right) r) /\
  (!marks res mid G1 tn1 t.
     (!tail. bind (eval_expr cx e) (read_result cx)
                (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
              (res,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     create_operand_at m t /\
     create_operand_full_scope a m E C f s0 marks (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,m,s0,x,G0,tn0)
         H res mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
     ?v. res = INL v /\
       scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 m b
         (\ee. (sum_CASE (convert_result cx (expr_type e) dst v)
                   (\w. INL (Value w)) INR, ee)) (mid,t,G1,tn1)
         (\H res ee G tn z. create_operand_vv_post (DF,lo,D,C,f) ce cx
            (TypeBuiltin dst Convert dst [e]) (es,a,b,s0,vv,G0,tn0)
            H res ee G tn z /\ create_operand_at b z)
         (create_operand_exit_post C cx)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a b
    (eval_expr cx (TypeBuiltin dst Convert dst [e])) (es,s0,G0,tn0)
    (\H res ee G tn z. create_operand_vv_post (DF,lo,D,C,f) ce cx
       (TypeBuiltin dst Convert dst [e]) (es,a,b,s0,vv,G0,tn0)
       H res ee G tn z /\ create_operand_at b z)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b E C f tops cx st0
    (eval_expr cx (TypeBuiltin dst Convert dst [e])) (es,s0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a m
     (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,m,s0,x,G0,tn0))
     (create_operand_exit_post C cx) /\
   create_operand_cut a m E C f tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s0)` by
   (irule create_value_of_vv_scoped_cut >>
    qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
    qpat_assum `evaluate_type _ _ = SOME _` (irule_at Any) >>
    asm_simp_tac bool_ss [] >> qexists_tac `L` >> rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >> res_tac) >>
  reverse conj_tac
  >- (irule create_convert_dynamic_visit >> first_assum (irule_at Any) >> simp[] >>
      metis_tac[]) >>
  simp[create_convert_dynamic_eval] >> irule scoped_operand_bind_all_mixed >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_def]
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_value >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      first_assum (ACCEPT_TAC o BETA_RULE o REWRITE_RULE [ignore_bind_def]))
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`create_force_read_post (DF,lo,D,C,f) ce cx e
                  (es,a,m,s0,x,G0,tn0)`,`m`] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule create_convert_dynamic_child_exit >> first_assum ACCEPT_TAC
QED

Theorem create_convert_dynamic_run_scope[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  compile_type_convert x (mk_convert_op src dst) m = (out,b) /\
  fn_has_code m b f /\ create_operand_at m s /\ ~s.vs_halted /\
  ((?u. run_inst_seq (emitted_insts m b) s = OK u /\
        r = OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts m b))) \/
   (?raw q. run_inst_seq (emitted_insts m b) s = Abort Revert_abort raw /\
            r = Abort Revert_abort q /\ gas_origin_path T E C f s [] r)) ==>
  create_operand_full_scope m b E C f s [] r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_convert_dynamic_suffix_code >> strip_tac >>
  `create_cut_code {} m b` by
    metis_tac[compile_type_convert_cut_code,pairTheory.SND] >>
  `EVERY (\i. i.inst_id IN frag_ids m b /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
     (emitted_insts m b)` by
    fs[EVERY_MEM,create_cut_code_def,frag_code_def,emitted_blocks_def] >>
  `s.vs_inst_idx + LENGTH (emitted_insts m b) = LENGTH b.cs_current_insts` by
    fs[create_operand_at_def] >>
  qpat_x_assum `(?u. _ = OK u /\ _) \/ _` strip_assume_tac >> gvs[]
  >- (drule_all create_admin_sequence_scope >> simp[]) >>
  irule create_admin_sequence_abort_scope >> simp[] >> qexists_tac `raw` >> simp[]
QED

Theorem create_convert_dynamic_origin_scope[local]:
  convert_dynamic_origin_rule
    (\m b s r. create_operand_full_scope m b E C f s [] r) lo E C f PG
Proof
  simp_tac std_ss [convert_dynamic_origin_rule_def] >> rpt gen_tac >> strip_tac >>
  `create_operand_at m s` by simp[create_operand_at_def] >>
  `!u. run_inst_seq (emitted_insts m b) s = OK u ==>
      create_operand_full_scope m b E C f s []
        (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts m b)))` by
    (rpt strip_tac >> irule create_convert_dynamic_run_scope >>
     first_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
  `!raw q. run_inst_seq (emitted_insts m b) s = Abort Revert_abort raw /\
      gas_origin_path T E C f s [] (Abort Revert_abort q) ==>
      create_operand_full_scope m b E C f s [] (Abort Revert_abort q)` by
    (rpt strip_tac >> irule create_convert_dynamic_run_scope >>
     first_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `(?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT`
  >- (drule_all signed_convert_origin_path_selected >>
      disch_then (qspecl_then [`E`,`PG`] mp_tac) >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >> res_tac >> metis_tac[gas_origin_ptr_path_projections]) >>
  Q.SUBGOAL_THEN
    `dst = BaseT BoolT \/ (?k. dst = BaseT (UintT k)) \/
     dst = BaseT AddressT \/ (?k. dst = BaseT (BytesT (Fixed k)))` assume_tac
  >- (drule_all bytestring_scalar_type_partition_cases >>
      qpat_x_assum `~((?k. dst = _) \/ _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  Cases_on `v = BytesV [] \/ v = StringV []`
  >- (drule_all bytes_word_empty_convert_origin_path_selected >>
      disch_then (qspecl_then [`E`,`PG`] mp_tac) >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >> res_tac >> metis_tac[gas_origin_ptr_path_projections]) >>
  `v <> BytesV [] /\ v <> StringV []` by gvs[] >>
  drule_all bytes_word_convert_origin_path_selected >>
  disch_then (qspecl_then [`E`,`PG`] mp_tac) >> strip_tac >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> metis_tac[gas_origin_ptr_path_projections]
QED

(* The observation, source equation, path and post share the selected result. *)
Theorem create_convert_dynamic_suffix_outcome[local]:
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. next (mid with gas_obs := tail) = (res,mid with gas_obs := tail)) /\
  create_operand_full_scope m b E C f t [] r /\
  ((?u. r = OK u) \/ exit_result r) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) [] (r,Gf,tnf) /\
       (case r of OK u => Q H res mid Gf tnf u | _ => R H res mid (Gf,tnf) r)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b next
    (mid,t,G1,tn1) Q R
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`mid`,`r`,`Gf`,`tnf`] >>
  Cases_on `r` >> gvs[gasSummaryTheory.gas_explicit_def,exit_result_def]
QED

Theorem create_convert_dynamic_vv_post[local]:
  expr_vv_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,b,s,vv,G,tn)
    H res ee G1 tn1 u ==>
  create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,b,s,vv,G,tn)
    H res ee G1 tn1 u /\ create_operand_at b u
Proof
  simp[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,
       create_operand_vv_post_def,create_operand_at_def] >>
  strip_tac >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem create_convert_dynamic_selected_suffix[local]:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type (BaseT bt) /\
  is_word_type (BaseT bt) /\ well_formed_type env.type_defs (BaseT bt) /\
  valid_conversion (expr_type e) (BaseT bt) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  lower_value compile_expr ce (expr_type e) e a = (x,m) /\
  local_ptrs_reserved ce a /\ fn_has_code m b f /\ fn_inst_ids_distinct f /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  (if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type ce e = BaseT (StringT 0) then
     m = b /\ vv = StackValue (BaseT bt) (Lit 0w)
   else ?out. vv = StackValue (BaseT bt) out /\
     compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) m = (out,b)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (child_res, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     create_force_read_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,x,G0,tn0)
       H child_res mid G1 tn1 t /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG)
       (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
  ?v. child_res = INL v /\
      scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG)
        (cx_tops cx) cx st0 m b
        (\ee. (sum_CASE (convert_result cx (expr_type e) (BaseT bt) v)
                   (\w. INL (Value w)) INR, ee)) (mid,t,G1,tn1)
        (\H res ee G tn z. create_operand_vv_post (DF,lo,d,C,f) ce cx
           (TypeBuiltin (BaseT bt) Convert (BaseT bt) [e]) (es,a,b,s0,vv,G0,tn0)
           H res ee G tn z /\ create_operand_at b z)
        (create_operand_exit_post C cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `~t.vs_halted` by
    (qpat_assum `!H. _ ==> create_force_read_post _ _ _ _ _ H _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     metis_tac[gas_origin_ptr_path_projections,fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  `(if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type ce e = BaseT (StringT 0) then
       m = b /\ vv = StackValue (BaseT bt) (Lit 0w) /\
       create_operand_full_scope m b (gas_explicit_sites C shC) C f t [] (OK t)
     else ?out. vv = StackValue (BaseT bt) out /\
       compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) m = (out,b))` by
    (IF_CASES_TAC >> fs[] >> metis_tac[create_operand_empty_scope]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,x,G0,tn0)
       H child_res mid G1 tn1 t /\
     (~is_word_type (post_value_type ce e) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
             eval_operand x t = SOME w ==>
             type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)` by
    (rpt strip_tac >> first_x_assum drule >> simp[create_force_read_post_def]) >>
  drule_all (REWRITE_RULE [create_convert_dynamic_origin_scope] (BETA_RULE (Q.INST
    [`ctx` |-> `C`, `shadow_ctx` |-> `shC`, `func` |-> `f`,
     `P` |-> `\m b t r. create_operand_full_scope m b (gas_explicit_sites C shC) C f t [] r`]
    convert_dynamic_selected_continuation))) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists_tac `v` >> simp[] >>
  irule create_convert_dynamic_suffix_outcome >>
  first_assum (irule_at Any) >>
  qexistsl_tac [`tnf`,`res`,`Gf`] >> Cases_on `r` >>
  gvs[exit_result_def] >> rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  simp[create_operand_exit_post_def] >>
  drule create_convert_dynamic_vv_post >> simp[]
QED

Theorem create_convert_dynamic_normalize_child[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source
    (es,s,G,tn) Q (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source
    (es,s,G,tn) (\H res ee G' tn' t. Q H res ee G' tn' t /\ ee.gas_obs = [])
    (\H (res : value + vyperState$exception) ee gt r.
       ?exc. res = INR exc /\
         create_operand_exit_post C cx H (INR exc : eval_result + vyperState$exception) ee gt r)
Proof
  strip_tac >> drule create_convert_dynamic_child_exit >>
  simp[scoped_operand_outcome_def]
QED

Theorem create_convert_dynamic_vv_case:
  body_inv tops C ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  create_layout a b /\
  expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert dst [e]) es (st0,a,b,sha,shb,vv,s0,G0,tn0) /\
  (!m shm x. create_layout a m /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,x,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (create_force_read_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,x,G0,tn0))
      (create_operand_exit_post C cx) /\
    create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG)
    (cx_tops cx) cx st0 a b (eval_expr cx (TypeBuiltin ann Convert dst [e])) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,C,f) ce cx
      (TypeBuiltin ann Convert dst [e]) (es,a,b,s0,vv,G0,tn0) H res ee G tn t /\
      create_operand_at b t)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0
    (eval_expr cx (TypeBuiltin ann Convert dst [e])) (es,s0)
Proof
  strip_tac >>
  `expr_vv_sim_full_hypotheses (DF,lo,d,C,shC,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert dst [e]) es (st0,a,b,sha,shb,vv,s0,G0,tn0)` by
    (fs[expr_vv_sim_full_pre_def,expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all convert_dynamic_child_site >> strip_tac >> gvs[] >>
  rename1 `is_word_type (BaseT bt)` >>
  rename1 `cs_extends a m` >>
  `create_layout a m` by metis_tac[create_layout_subinterval,compileEnvTheory.cs_extends_refl] >>
  qpat_assum `expr_sim_full_hypotheses _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_hypotheses_def,expr_sim_full_code_def]) >>
  `expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shadow_sm,x,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!m shm x. _ ==> _` (drule_all_then strip_assume_tac) >>
  `create_cut_code {} a m` by metis_tac[cj 2 create_operand_cut_code,pairTheory.SND] >>
  `(if lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type ce e = BaseT (StringT 0) then
      m = b /\ vv = StackValue (BaseT bt) (Lit 0w)
    else ?out. vv = StackValue (BaseT bt) out /\
      compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) m = (out,b))` by
    (IF_CASES_TAC >> fs[] >> metis_tac[]) >>
  `create_cut_code {} m b` by
    (qpat_assum `if _ then _ else ?out. _ /\ compile_type_convert _ _ m = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> metis_tac[compile_type_convert_cut_code,pairTheory.SND]) >>
  reverse conj_tac
  >- (irule create_convert_dynamic_visit >> rpt (first_assum (irule_at Any)) >> simp[] >>
      metis_tac[]) >>
  `fn_has_code a b f` by fs[expr_vv_sim_full_pre_def] >>
  `create_operand_at a s0` by simp[create_operand_at_def] >>
  drule_all blueprint_stage_scope_split >>
  disch_then (qspec_then `gas_explicit_sites C shC` strip_assume_tac) >>
  qpat_assum `!s. create_operand_at a s ==> _` (drule_then strip_assume_tac) >>
  drule_then assume_tac create_convert_dynamic_normalize_child >>
  simp[create_convert_dynamic_eval] >> irule scoped_operand_bind_all_mixed >>
  first_assum (irule_at Any) >> simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_def]
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_value >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      first_assum (ACCEPT_TAC o BETA_RULE o REWRITE_RULE [ignore_bind_def]))
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!H. _ ==> (_ /\ mid.gas_obs = []) /\ _`
        (fn th =>
          `mid.gas_obs = []` by metis_tac[th,vyperStorageFootprintTheory.storage_trace_domain_def] >>
          assume_tac (SIMP_RULE bool_ss [CONJ_ASSOC] th)) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
          create_force_read_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,x,G0,tn0)
            H res mid G1 tn1 t /\
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG)
            (s0,G0,tn0) marks (OK t,G1,tn1)` by metis_tac[] >>
      `!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)` by
        (rpt gen_tac >> disch_tac >>
         qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
         first_assum ACCEPT_TAC) >>
      drule_all create_convert_dynamic_selected_suffix >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `create_operand_full_scope a m _ _ _ _ _ (OK _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
  qpat_assum `!left u. create_expr_prefix a m _ _ _ s0 left u ==> _`
    (drule_then assume_tac) >>
  first_assum irule >> simp[create_operand_at_def] >>
  goal_assum (drule_at Any) >> simp[]
QED
