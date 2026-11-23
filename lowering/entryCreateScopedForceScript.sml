(* A forced value evaluates its VV child and then executes the read suffix.
   The suffix interface chooses one endpoint and ghost pair before H. *)
Theory entryCreateScopedForce
Ancestors
  entryCreateCompositeFocus entryCreatePendingScope entryCreateStmtCases
  entryCreateFocusSpec entryCreateCompletedCut createSizeLocationCode bodyFullOfVV bodyFullUnwrap
  vyperEvalExprPreservesScopesDom gasShadowCompile exprOperandVar exprSimUnwrap
  exprSimMemorySource vyperStorageTrace vyperStorageFootprint
  exprSimFullBundleProps exprLoweringProps bodySimFull s1PrefixDefs
  loweringPosts exprSimDefs fragExec fragGasOriginPtr gasExemptCert
  gasSummary gasOutcomeFull compileEnv exprLowering vyperState
  entryCreatePathScope entryCreateOperandReplay createSizePrefixReplay
  createSizeCutRegion abiEncoderProps list relation entryCreateBodyCut

Definition create_force_read_post_def:
  create_force_read_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,op,G0,tn0)
    H res ee G tn t <=>
    expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,op,G0,tn0)
      H res ee G tn t /\
    (~is_word_type (post_value_type ce e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
              eval_operand op t = SOME w ==>
              type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)
End

Definition create_force_read_vv_site_def:
  create_force_read_vv_site vv <=>
    !DF lo D C f PG E ce cx ty e es st0 a m b s0 op G0 tn0 tv ee G tn s rty.
      compile_expr ce ty e a = (vv,m) /\ unwrap_value ce vv m = (op,b) /\
      fn_has_code m b f /\ fn_inst_ids_distinct f /\ local_ptrs_reserved ce a /\
      (!H. dead_lo_ok H (DF H) lo ce cx) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            ~is_word_type (post_value_type ce e) ==>
            type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
            type_memory_size rt < 2 ** 64) /\
      evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
      (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\ storage_trace_domain cx st0 ee.storage_trace /\
      create_operand_at m s /\ ~s.vs_halted /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        create_operand_vv_post (DF,lo,D,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
          H (INL tv : eval_result + vyperState$exception) ee G tn s) ==>
      ?v z G' tn'. read_result cx tv ee = (INL v,ee) /\
        create_operand_full_scope m b E C f s [] (OK z) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK z,G',tn') /\
          create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,b,s0,op,G0,tn0)
            H (INL v : value + vyperState$exception) ee G' tn' z)
End

Definition create_force_read_site_def:
  create_force_read_site allowed <=> !vv. allowed vv ==> create_force_read_vv_site vv
End

Definition create_force_slot_copy_def:
  create_force_slot_copy vv <=>
    ?ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
            (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)
End

Definition create_force_code_copy_def:
  create_force_code_copy vv <=>
    ?ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\ p.ptr_location = LocCode
End

Theorem create_force_read_cases:
  create_force_read_site (\vv. ~create_force_slot_copy vv /\ ~create_force_code_copy vv) /\
  create_force_read_site create_force_slot_copy /\ create_force_read_site create_force_code_copy ==>
  create_force_read_site (\vv. T)
Proof
  simp[create_force_read_site_def] >> metis_tac[]
QED

(* The paired compile equations share the same intermediate VV. *)
Theorem create_force_lower_value_split[local]:
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,op,s0,G0,tn0) ==>
  ?vv m shm.
    expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
      (st0,a,m,sha,shm,vv,s0,G0,tn0) /\
    unwrap_value ce vv m = (op,b) /\ fn_has_code m b f
Proof
  simp[expr_sim_full_pre_def, expr_vv_sim_full_pre_def, lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr ce ty e a` >> rename1 `_ = (vv,m)` >> simp[] >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  rename1 `_ = (shvv,shm)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `shvv = vv /\ gas_shadow_state m shm` by
    (`gas_shadow_compiles (compile_expr ce ty e)
       (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`a`,`sha`] mp_tac o
        REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[]) >>
  gvs[] >>
  `fn_has_code a m f /\ fn_has_code m b f` by
    (irule fn_has_code_split >> metis_tac[compile_expr_extends, unwrap_value_extends]) >>
  `fn_has_code sha shm shf /\ fn_has_code shm shb shf` by
    (irule fn_has_code_split >> metis_tac[compile_expr_extends, unwrap_value_extends]) >>
  simp[] >> metis_tac[forced_expr_admissible_raw]
QED

Theorem create_force_read_success[local]:
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (?v z G' tn'. read_result cx tv ee = (INL v,ee) /\
    create_operand_full_scope m b E C f s [] (OK z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK z,G',tn') /\
      Q H (INL v) ee G' tn' z)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (read_result cx tv) (ee,s,G,tn) Q R
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`ee`,`OK z`,`G'`,`tn'`] >>
  simp[gas_explicit_def] >> metis_tac[read_result_gas_obs]
QED

Theorem create_force_read_continuation[local]:
  create_force_read_site (\vv. T) /\
  compile_expr ce ty e a = (vv,m) /\ unwrap_value ce vv m = (op,b) /\
  fn_has_code m b f /\ fn_inst_ids_distinct f /\ local_ptrs_reserved ce a /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        ~is_word_type (post_value_type ce e) ==>
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
           (res, ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at m s /\
  ~s.vs_halted /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,D,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
      H res ee G tn s) ==>
  ?tv. res = INL tv /\
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 m b
      (read_result cx tv) (ee,s,G,tn)
      (create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,b,s0,op,G0,tn0))
      (create_operand_exit_post C cx)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def])) >> gvs[] >>
  qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` assume_tac) >>
  `ee with gas_obs := [] = ee` by
    fs[vyperStateTheory.evaluation_state_component_equality] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by metis_tac[] >>
  qpat_x_assum `create_force_read_site _`
    (strip_assume_tac o REWRITE_RULE [create_force_read_site_def]) >>
  first_x_assum (qspec_then `vv` mp_tac) >>
  simp[create_force_read_vv_site_def] >>
  disch_then (fn th => irule create_force_read_success >> simp[] >> irule th) >>
  simp[] >> qexists_tac `ty` >> simp[]
QED

(* The read succeeds at its own endpoint. Exceptional child results are
   propagated unchanged, even though forcing changes the success type. *)
Theorem create_force_child_post[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H (res : eval_result + vyperState$exception) ee G tn t.
       create_operand_vv_post (DF,lo,D,C,f) ce cx e
       (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. ?tv. res = INL tv /\
      create_operand_vv_post (DF,lo,D,C,f) ce cx e
        (es,a,m,s0,vv,G0,tn0) H (INL tv : eval_result + vyperState$exception) ee G tn t /\
      create_operand_at m t /\ ee.gas_obs = [] /\ ~t.vs_halted)
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value + vyperState$exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >>
  qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> res_tac >> fs[]
      >- (`~t.vs_halted` by metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase,
                                     fragGasPathTheory.gas_path_normal] >>
          `?tv. res = INL tv` by
            (qhdtm_assum `create_operand_vv_post`
               (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def]) >> metis_tac[]) >>
          gvs[exit_result_def] >>
          qpat_assum `!h. valid_horizon _ _ h _ ==> _` (qspec_then `H` mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
      Cases_on `res` >>
      fs[create_operand_exit_post_def, expr_exit_def, halt_exit_def,
         stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem create_force_scoped_bind[local]:
  create_force_read_site (\vv. T) /\
  expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,op,s0,G0,tn0) /\
  expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,m,sha,shm,vv,s0,G0,tn0) /\
  unwrap_value ce vv m = (op,b) /\ fn_has_code m b f /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        ~is_word_type (post_value_type ce e) ==>
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a m
    (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,D,C,f) ce cx e
       (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
    (create_operand_exit_post C cx) /\
  (!marks. create_operand_focus_scope a m E C f s0 marks ==>
           create_operand_focus_scope a b E C f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s0 marks r ==>
             create_operand_full_scope a b E C f s0 marks r) /\
  (!left t right. create_operand_full_scope a m E C f s0 left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s0 (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s0 left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s0 (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a b
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,b,s0,op,G0,tn0))
    (create_operand_exit_post C cx)
Proof
  strip_tac >>
  drule_then assume_tac create_force_child_post >>
  irule scoped_operand_bind >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_result >> simp[GSYM ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H (tv : eval_result) ee G tn t.
    create_operand_vv_post (DF,lo,D,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
       H (INL tv : eval_result + vyperState$exception) ee G tn t /\
    create_operand_at m t /\ ee.gas_obs = [] /\ ~t.vs_halted`, `m`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qx_genl_tac [`marks`,`v`,`mid`,`G`,`tn`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `create_operand_at m s /\ ~s.vs_halted` by metis_tac[] >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  mp_tac (Q.INST [`ee` |-> `mid with gas_obs := []`,
                  `res` |-> `INL v : eval_result + vyperState$exception`]
                 (SPEC_ALL create_force_read_continuation)) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* The right interval keeps the same exit. Widening its instruction band
   does not change any edge of its successful caller spine. *)
Theorem create_force_right_prefix[local]:
  a.cs_next_id <= m.cs_next_id /\
  create_expr_prefix m b E C f u marks t ==>
  create_expr_prefix a b E C f u marks t
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >>
  simp[create_prefix_step_def, frag_ids_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem create_force_full_append[local]:
  a.cs_next_id <= m.cs_next_id /\
  create_expr_prefix a b E C f s left u /\
  create_operand_full_scope m b E C f u right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac
  >- metis_tac[create_force_right_prefix, create_expr_prefix_append] >>
  rename1 `create_expr_prefix m b E C f u front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[create_force_right_prefix, create_expr_prefix_append] >>
  metis_tac[APPEND_ASSOC]
QED

(* A pending suffix may stop at any right-region caller cursor. Restrict
   a completing edge there using the installed right-hand code. *)
Theorem create_force_focus_append[local]:
  a.cs_next_id <= m.cs_next_id /\ body_inv tops C ce cx /\
  MEM f C.ctx_functions /\ create_cut_code {} m b /\ fn_has_code m b f /\
  create_operand_at m u /\ create_expr_prefix a b E C f s left u /\
  create_operand_focus_scope m b E C f u marks ==>
  create_operand_focus_scope a b E C f s (left ++ marks)
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix m b E C f u front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[create_force_right_prefix, create_expr_prefix_append] >>
  qexistsl_tac [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
  `create_cut_region m b u` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> rpt strip_tac >>
  qpat_assum `create_prefix_step a b E C f stop _ _`
    (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
  qpat_assum `!right v. create_prefix_step m b E C f stop right v ==> _` irule >>
  qexists_tac `v` >>
  irule (cj 1 operand_cut_region_edge) >>
  qpat_assum `gas_origin_edge F E C f stop right (OK v)` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* A native suffix visit is discharged by its instruction inventory; no
   return of the child or consumption of a CREATE oracle is required. *)
Theorem create_force_cut[local]:
  create_operand_cut a m E C f tops cx st0 (eval_expr cx e) (es,s0) /\
  (!p d k before hit after.
     create_interior_visit a b E C f (p,d,k) s0 (before,hit,after) ==>
     create_interior_visit a m E C f (p,d,k) s0 (before,hit,after) \/
     ?t d1 k1 front back. before = front ++ back /\ create_operand_at m t /\
       RTC (create_operand_native_step a m E C f p) (d,k,s0,[]) (d1,k1,t,front) /\
       create_expr_prefix a m E C f s0 (create_cut_marks E front) t /\
       create_interior_visit m b E C f (p,d1,k1) t (back,hit,after)) /\
  (!p d k t before key g i u after.
     create_interior_visit m b E C f (p,d,k) t (before,(key,g,i,u),after) ==>
     ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) ==>
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  simp[create_operand_cut_def] >> rpt strip_tac >>
  qpat_assum `!p d k before hit after. _ ==> _ \/ _`
    (drule_then strip_assume_tac)
  >- (irule create_cut_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >> metis_tac[]) >>
  PairCases_on `hit` >>
  qpat_assum `!p d k t before key g i u after. _ ==> _`
    (drule_then strip_assume_tac) >>
  fs[create_body_cut_def, venomRunBoundedTheory.inst_create_size_ok_def]
QED

(* The outer scope is an actual installed interval, not an unguarded
   simulation claim about all compile-state pairs.  L is supplied with
   the common subinterval and strict-stop laws of the installed layout. *)
Theorem create_value_of_vv_scoped_cut:
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
  body_inv tops C ce cx /\
  expr_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,op,s0,G0,tn0) /\ L a b /\
  (!m shm vv. expr_vv_sim_full_pre (DF,lo,D,C,shC,PG,f,shf) ce cx ty e es
      (st0,a,m,sha,shm,vv,s0,G0,tn0) /\ L a m ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a m
      (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,D,C,f) ce cx e
         (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
      (create_operand_exit_post C cx) /\
    create_operand_cut a m E C f tops cx st0 (eval_expr cx e) (es,s0)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a b
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (create_force_read_post (DF,lo,D,C,f) ce cx e (es,a,b,s0,op,G0,tn0))
    (create_operand_exit_post C cx) /\
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  strip_tac >> drule_then strip_assume_tac create_force_lower_value_split >>
  `compile_expr ce ty e a = (vv,m) /\ fn_has_code a m f /\ MEM f C.ctx_functions /\
   create_operand_at a s0` by fs[expr_vv_sim_full_pre_def,create_operand_at_def] >>
  drule_then strip_assume_tac compile_expr_extends >>
  drule_then strip_assume_tac unwrap_value_extends >>
  `L a m` by metis_tac[] >>
  qpat_assum `!m shm vv. _ ==> _ /\ _` (drule_then (strip_assume_tac o UNDISCH)) >>
  `create_cut_code {} a m` by metis_tac[operand_vv_cut_code] >>
  `create_cut_code {} m b` by metis_tac[create_unwrap_cut_code,pairTheory.SND] >>
  reverse conj_tac
  >- (irule create_force_cut >> qexists_tac `m` >> asm_simp_tac bool_ss [] >>
      conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `!ce' cx' tops' vv m op b E C f p d k t before key g i u after. _ ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  `create_cut_region a m s0` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[] >>
  `m.cs_next_id <= b.cs_next_id` by fs[createSizeCutCodeTheory.create_cut_code_def] >>
  qpat_assum `!a m b s. _ ==> _` (qspecl_then [`a`,`m`,`b`,`s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule create_force_scoped_bind >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
  qexists_tac `rty` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`create_operand_full_scope a b _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      qpat_x_assum `create_operand_full_scope _ _ _ _ _ s0 left (OK t)`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
      qpat_assum `!marks t. create_expr_prefix _ _ _ _ _ _ _ _ ==> _`
        (drule_then assume_tac) >>
      drule_all_then ACCEPT_TAC create_force_full_append) >>
  rpt strip_tac >>
  `create_operand_at m t /\ create_expr_prefix a m E C f s0 left t` by
    fs[create_operand_full_scope_def,create_operand_at_def] >>
  qpat_assum `!marks t. create_expr_prefix _ _ _ _ _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  drule_all_then ACCEPT_TAC create_force_focus_append
QED
