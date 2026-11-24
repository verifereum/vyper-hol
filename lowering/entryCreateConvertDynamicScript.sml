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
