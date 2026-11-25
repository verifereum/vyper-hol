(* Scope the field-list simulation without re-running a normal field. The
   readiness relation and the two site laws are interpretations of the
   ordinary StructLit invariant and its observed continuation. *)
Theory entryCreateStructLitFields
Ancestors
  entryCreateCompositeFocus entryCreateCompletedCut
  entryCreateFocusSpec bodyFullStructLit gasStorage gasSummary fragGasOriginPtr
  exprSimMemorySource bodyPtrMakeArrayMemoryFrame typeLayoutProps valueEncodingDefs
  gasOutcomeFullCompose gasExemptCert vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState list

Definition structlit_fields_post_def:
  structlit_fields_post source_inv field_inv b fs tvs addr cells off H (res : value list + exception) ee G tn z <=>
    ?vs added. res = INL vs /\ source_inv ee /\ LIST_REL value_has_type tvs vs /\
      field_inv H ee b G tn z (cells ++ added) (off + type_memory_size_list tvs) /\
      (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP (MAP FST fs,vs)) (ZIP (MAP FST fs,tvs)) (addr+off) m)
End

Definition structlit_fields_exit_def:
  structlit_fields_exit ctx cx H (res : 'a + exception) ee gt r <=>
    ?exc. res = INR exc /\
      create_operand_exit_post ctx cx H (INR exc : eval_result + exception) ee gt r
End

Definition structlit_scope_split_def:
  structlit_scope_split a m b E C f s <=>
    (!marks. create_operand_focus_scope a m E C f s marks ==>
      create_operand_focus_scope a b E C f s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
      create_operand_full_scope a b E C f s marks r) /\
    (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
      create_operand_focus_scope m b E C f t right ==>
      create_operand_focus_scope a b E C f s (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
      create_operand_full_scope m b E C f t right r ==>
      create_operand_full_scope a b E C f s (left ++ right) r)
End

Theorem structlit_eval_fields_cons[local]:
  eval_exprs cx (e::MAP SND fs) =
    vyperState$bind (eval_expr cx e) (\tv. bind (read_result cx tv)
      (\v. bind (eval_exprs cx (MAP SND fs)) (\vs. return (v::vs))))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

(* Mapping a successful tail result does not alter the witnessed outcome,
   including the two focus branches. *)
Theorem structlit_scoped_source_map[local]:
  (!es. source' es = (map_result (FST (source es)), SND (source es))) /\
  (!ex. map_result (INR ex) = INR ex) /\ (!v. ISL (map_result (INL v))) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    source (es,s,G,tn) Q R ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    source' (es,s,G,tn)
    (\H raw ee G tn t. ?res. raw = map_result res /\ Q H res ee G tn t)
    (\H raw ee gt r. ?res. raw = map_result res /\ R H res ee gt r)
Proof
  strip_tac >>
  `ignore_bind source' (return ()) = ignore_bind source (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `source x` >> rename1 `source x = (res,st)` >>
     Cases_on `res` >> simp[] >> rename1 `map_result (INL v)` >>
     `ISL (map_result (INL v))` by simp[] >> Cases_on `map_result (INL v)` >> fs[]) >>
  `!x. SND (source' x) = SND (source x)` by simp[] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  asm_rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`map_result res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> res_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem structlit_scoped_post_mono[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn) Q R /\
  (!H res ee G tn z. Q H res ee G tn z ==> Q' H res ee G tn z) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn) Q' R'
Proof
  rw[scoped_operand_outcome_def] >> qexists_tac `marks` >> metis_tac[]
QED

Theorem structlit_fields_post_cons[local]:
  (!H ee b G tn z cells off. field_inv H ee b G tn z cells off ==>
     literal_prefix_ok cells tn z) /\
  value_has_type ftv v /\
  structlit_fields_post source_inv field_inv b fs tvs addr
    (cells ++ [(ftv,v,addr+off,type_memory_size ftv)])
    (off+type_memory_size ftv) H (INL vs) ee G tn z ==>
  structlit_fields_post source_inv field_inv b ((name,e)::fs) (ftv::tvs) addr cells off
    H (INL (v::vs)) ee G tn z
Proof
  rw[structlit_fields_post_def] >>
  qexists_tac `[(ftv,v,addr+off,type_memory_size ftv)] ++ added` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (simp_tac pure_ss [APPEND_ASSOC, type_memory_size_list_sum, MAP, SUM] >>
      fs[type_memory_size_list_sum, APPEND_ASSOC]) >>
  rpt strip_tac >>
  `literal_prefix_ok (cells ++ [(ftv,v,addr+off,type_memory_size ftv)] ++ added) tn z`
    by metis_tac[APPEND_ASSOC] >>
  `val_in_memory ftv v (addr+off) m` by
    (irule (cj 3 literal_prefix_lookup) >>
     qexistsl_tac [`cells ++ [(ftv,v,addr+off,type_memory_size ftv)] ++ added`,
                  `type_memory_size ftv`, `z`, `tn`] >> simp[]) >>
  pure_once_rewrite_tac[val_in_memory_def] >> simp[GSYM arithmeticTheory.ADD_ASSOC]
QED

(* This law is used with two different left result types. The final exit
   receives the same exception, not the left operand's success type. *)
Definition structlit_bind_all_law_def:
  structlit_bind_all_law (witness : 'a itself) <=>
    !DF lo E C f PG tops cx st0 a m b
      (source : evaluation_state -> 'a evaluation_result)
      (next : 'a -> evaluation_state -> value list evaluation_result)
      es s G tn Q1 Q R T.
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
      source (es,s,G,tn) Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    (!marks res mid G1 tn1 t.
      (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\
      create_operand_at m t /\
      create_operand_full_scope a m E C f s marks (OK t) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,E,C,f,PG)
          (s,G,tn) marks (OK t,G1,tn1)) ==>
      ?v. res = INL v /\ scoped_operand_outcome (DF,lo,E,C,f,PG)
        tops cx st0 m b (next v) (mid,t,G1,tn1) Q R) /\
    storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
    (!marks err ee leaf finish.
      gas_exempt_cert T tops (C,f) (ignore_bind source (return ()))
        (es,s) marks (err,ee) (leaf,finish) ==>
      gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
        (es,s) marks (err,ee) (leaf,finish)) /\
    (!left v mid t right err ee leaf finish.
      gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
      gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
        (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
      gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
        (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
    structlit_scope_split a m b E C f s ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
      (bind source next) (es,s,G,tn) Q R
End

Theorem structlit_scoped_admin_read[local]:
  structlit_bind_all_law (:value) /\
  read_result cx tv mid = (INL v,mid) /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  create_operand_full_scope m k E C f t [] (OK u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) [] (OK u,G2,tn2)) /\
  structlit_scope_split m k b E C f t /\
  (!v. storage_trace_frame ((next : value -> evaluation_state -> value list evaluation_result) v)) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 k b
    (next v) (mid,u,G2,tn2) Q (structlit_fields_exit C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (vyperState$bind (read_result cx tv) next) (mid,t,G1,tn1) Q (structlit_fields_exit C cx)
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `structlit_bind_all_law (:value)`
    (irule o REWRITE_RULE [structlit_bind_all_law_def]) >>
  simp[storage_trace_frame_read_result] >> conj_tac
  >- (qexists_tac `ARB` >> conj_tac
      >- (rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_error_value >> simp[]) >>
      rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_value >> qexistsl_tac [`mid'`,`t'`,`v'`] >> fs[ignore_bind_def]) >>
  qexistsl_tac [`\H res ee G tn z. res = INL v /\ ee = mid /\ G = G2 /\ tn = tn2 /\ z = u`,`k`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace`
        by fs[storage_trace_domain_def] >> res_tac >> gvs[] >> metis_tac[]) >>
  simp[scoped_operand_outcome_def, gas_explicit_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`mid`,`OK u`,`G2`,`tn2`] >>
  simp[read_result_gas_obs]
QED

Theorem structlit_scoped_eval_head[local]:
  structlit_bind_all_law (:eval_result) /\
  structlit_scope_split a m b E C f s /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e)
    (es,s,G,tn) Child (create_operand_exit_post C cx) /\
  (!marks res mid G1 tn1 t.
    (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
    create_operand_full_scope a m E C f s marks (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Child H res mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    ?tv. res = INL tv /\ scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (vyperState$bind (read_result cx tv) next) (mid,t,G1,tn1) Q (structlit_fields_exit C cx)) /\
  (!v. storage_trace_frame ((next : value -> evaluation_state -> value list evaluation_result) v)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (vyperState$bind (eval_expr cx e) (\tv. bind (read_result cx tv) next))
    (es,s,G,tn) Q (structlit_fields_exit C cx)
Proof
  strip_tac >>
  qpat_assum `structlit_bind_all_law (:eval_result)`
    (irule o REWRITE_RULE [structlit_bind_all_law_def]) >>
  simp[evaluate_storage_trace_frame] >> conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result]) >>
  conj_tac
  >- (qexists_tac `ARB` >> conj_tac
      >- (rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_error_result >> simp[]) >>
      rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >> qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def, bind_assoc]) >>
  qexistsl_tac [`Child`,`m`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_assum (drule_all_then strip_assume_tac) >> metis_tac[]) >>
  irule structlit_scoped_post_mono >> first_assum (irule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >>
  simp[structlit_fields_exit_def, create_operand_exit_post_def, exprSimDefsTheory.expr_exit_def]
QED

(* Abstract only the two implementation boundaries: layout supplies the
   actual child pre and split, and the successful continuation supplies the
   instantiated read/store witnesses and the recursive readiness invariant. *)
Theorem structlit_fields_scoped_intro:
  structlit_bind_all_law (:eval_result) /\ structlit_bind_all_law (:value) /\
  (!H ee b G tn z cells off. field_inv H ee b G tn z cells off ==>
     literal_prefix_ok cells tn z) /\
  (!tvs es a b s G tn cells off. ready [] tvs es a b s G tn cells off ==>
     tvs = [] /\ b = a /\ create_operand_at a s /\ ~s.vs_halted /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       source_inv (es with gas_obs := []) /\
       field_inv H (es with gas_obs := []) b G tn s cells off)) /\
  (!name e fs tvs es a b s G tn cells off.
    ready ((name,e)::fs) tvs es a b s G tn cells off ==>
    ?ftv rest_tvs vv m k sha shm.
      tvs = ftv::rest_tvs /\
      site name e fs ftv rest_tvs es a b s G tn cells off vv m k /\
      structlit_scope_split a m b (gas_explicit_sites C shctx) C f s /\
      expr_vv_sim_full_pre (DF,lo,d,C,shctx,PG,f,shfunc) ce cx (expr_type e) e es
        (st0,a,m,sha,shm,vv,s,G,tn) /\
      expr_vv_sim_scoped (DF,lo,d,C,shctx,PG,f,shfunc) ce cx (expr_type e) e es) /\
  (!name e fs ftv tvs es a b s G tn cells off vv m k marks res mid G1 tn1 t.
    site name e fs ftv tvs es a b s G tn cells off vv m k /\
    (!tail. eval_expr cx e
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
    create_operand_full_scope a m (gas_explicit_sites C shctx) C f s marks (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s,vv,G,tn) H res mid G1 tn1 t /\
       t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts) /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shctx,C,f,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    ?tv v u G2 tn2.
      res = INL tv /\ read_result cx tv mid = (INL v,mid) /\ mid.gas_obs = [] /\
      value_has_type ftv v /\
      structlit_scope_split m k b (gas_explicit_sites C shctx) C f t /\
      create_operand_full_scope m k (gas_explicit_sites C shctx) C f t [] (OK u) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shctx,C,f,PG)
          (t,G1,tn1) [] (OK u,G2,tn2)) /\
      ready fs tvs mid k b u G2 tn2 (cells ++ [(ftv,v,addr+off,type_memory_size ftv)])
        (off+type_memory_size ftv)) ==>
  !fs tvs es a b s G tn cells off.
    ready fs tvs es a b s G tn cells off ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shctx,C,f,PG) (cx_tops cx) cx st0 a b
      (eval_exprs cx (MAP SND fs)) (es,s,G,tn)
      (structlit_fields_post source_inv field_inv b fs tvs addr cells off)
      (structlit_fields_exit C cx)
Proof
  strip_tac >> Induct
  >- (rpt gen_tac >> strip_tac >> res_tac >> gvs[] >>
      irule scoped_operand_pure >> simp[] >> qexistsl_tac [`es`,`INL [] : value list + exception`] >>
      simp[Once evaluate_def, return_def] >> rpt strip_tac >>
      simp[structlit_fields_post_def, type_memory_size_list_sum, val_in_memory_def] >>
      qexists_tac `[]` >> simp[] >> res_tac >> simp[]) >>
  Cases >> rpt gen_tac >> strip_tac >>
  first_assum (drule_then strip_assume_tac) >> gvs[] >>
  drule_all (iffLR expr_vv_sim_scoped_def) >> strip_tac >>
  rewrite_tac[structlit_eval_fields_cons] >>
  irule structlit_scoped_eval_head >> simp[] >> conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ a m (eval_expr _ _) _ _ _`
    (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_assum (drule_all_then strip_assume_tac) >> gvs[] >>
  irule structlit_scoped_admin_read >> simp[] >>
  goal_assum (irule_at Any) >> simp[] >> conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qexistsl_tac [`G2`,`k`,`tn2`,`u`] >> simp[] >>
  qpat_assum `ready fs _ _ _ _ _ _ _ _ _`
    (fn th => first_assum (fn ih => mp_then Any assume_tac ih th)) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ k b (eval_exprs _ _) _ _ _`
    (mp_then Any (mp_tac o Q.ISPECL
      [`bind (eval_exprs cx (MAP SND (fs : (string # expr) list))) (\vs. return (v::vs))`,
       `\res : value list + exception. case res of INL vs => INL ((v:value)::vs) | INR ex => INR ex`])
      structlit_scoped_source_map) >>
  impl_tac
  >- (simp[bind_def, return_def] >> gen_tac >>
      Cases_on `eval_exprs cx (MAP SND fs) es'` >>
      rename1 `eval_exprs cx (MAP SND fs) es' = (rr,ee)` >> Cases_on `rr` >> simp[]) >>
  disch_then (mp_then Any irule structlit_scoped_post_mono) >>
  conj_tac
  >- (BETA_TAC >> rpt gen_tac >> disch_then (qx_choose_then `tail_res` strip_assume_tac) >>
      `?vs. tail_res = INL vs` by fs[structlit_fields_post_def] >> gvs[] >>
      irule structlit_fields_post_cons >> BETA_TAC >> conj_tac
      >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp_tac pure_ss [APPEND_ASSOC] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> simp[structlit_fields_exit_def, PULL_EXISTS]
QED
