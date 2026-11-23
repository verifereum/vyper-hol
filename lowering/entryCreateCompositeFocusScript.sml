(* Scoped composition for non-invoking fragments. *)
Theory entryCreateCompositeFocus
Ancestors
  entryCreateFocusSpec entryCreatePendingScope entryCreateStmtCases entryCreateBodyCut
  entryCreateNativeResume entryCreatePathScope createSizePrefixReplay
  venomExecSemantics fragExec entryCreateCompletedCut gasSummary gasOutcomeFull
  dftGasFromListTraceDefs compileEnv fragGasOriginPtr fragGasOrigin gasStorage
  vyperStorageTrace vyperStorageFootprint relation list pair
  gasSummaryCompose fragGasMode fragGasPath gasExemptCert vyperState
  bodyNameWordTypeMemory loweringSlice emitHelperProps abiEncoderProps emitHelper
  exprLoweringProps
  venomState venomInst vyperInterpreter vyperAST exprSimHypsDefs

(* A successful non-terminating administrative instruction leaves the
   caller at its next cursor regardless of the fuel in the origin edge. *)
Theorem create_admin_step_endpoint[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst k C i s = OK u /\
  create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,all) ==>
  v = u with vs_inst_idx := SUC s.vs_inst_idx
Proof
  simp[create_operand_native_step_def, LET_THM, create_prefix_step_def] >>
  strip_tac >> gvs[gas_origin_edge_def, step_inst_non_invoke, exit_result_def]
QED

(* The one-step region owns exactly its current instruction.  In particular
   a CREATE at the next cursor can be in the continuation's trace but cannot
   be in this region's selected visits. *)
Theorem create_admin_one_step_visit:
  create_operand_at a s /\ create_operand_fetch a b f s i /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~MEM i.inst_opcode [CREATE;CREATE2] /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  u.vs_current_bb = s.vs_current_bb /\
  t = u with vs_inst_idx := SUC s.vs_inst_idx /\ create_operand_at b t ==>
  (create_interior_visit a b E C f (p,d,k) s (before,hit,after) <=>
   before = [] /\ hit = ((p,d,i.inst_id),f,i,s) /\
   after = create_trace_from p d k C f t) /\
  create_body_cut E tops cx st0 source (es,s) ([],((p,d,i.inst_id),f,i,s))
Proof
  strip_tac >>
  `create_trace_from p d k C f s =
   ((p,d,i.inst_id),f,i,s)::create_trace_from p d k C f t` by
    (drule_all create_trace_from_next >> simp[trace_step_noninvoke]) >>
  reverse conj_tac
  >- (irule create_cut_noncreate_visit >> fs[]) >>
  eq_tac >> strip_tac
  >- (qpat_x_assum `create_interior_visit _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[create_interior_visit_def]) >>
      qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
      >- (gvs[create_operand_fetch_def, trace_step_noninvoke] >> metis_tac[]) >>
      rename1 `create_operand_native_step _ _ _ _ _ _ _ z` >>
      PairCases_on `z` >>
      drule_all create_admin_step_endpoint >> strip_tac >>
      `!w. ~create_operand_native_step a b E C f p (z0,z1,z2,z3) w` by
        (simp[FORALL_PROD, create_operand_native_step_def, create_operand_fetch_def] >>
         metis_tac[]) >>
      qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
      gvs[create_operand_fetch_def]) >>
  gvs[create_interior_visit_def] >>
  qexists_tac `k` >> simp[]
QED

(* Empty compiled leaves may still have a source storage-domain failure;
   its focus is the initial cursor, not an instruction of the continuation. *)
Theorem scoped_operand_pure:
  create_operand_at a s /\ ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G tn s) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a a
    source (es,s,G,tn) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`OK s`,`G`,`tn`] >>
      simp[gas_explicit_def, gas_origin_ptr_path_rules] >>
      metis_tac[create_operand_empty_scope]) >>
  disj1_tac >> simp[gas_bad_storage_at_def, gas_explicit_def] >>
  conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`, `f`, `PG`, `G`, `tn`, `s`] >>
  simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]
QED

Theorem scoped_operand_endpoint_horizon[local]:
  storage_trace_frame source /\
  (!tail. source (es with gas_obs := xs ++ tail) = (res, ee with gas_obs := tail)) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `!tail. source _ = _`
     (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule_all storage_trace_frame_prefix >> simp[] >>
  metis_tac[valid_horizon_append]
QED

Theorem scoped_operand_bind_right[local]:
  gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) left (OK t,G1,tn1)) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 b c
    (next v) (mid with gas_obs := [],t,G1,tn1) Q R /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  storage_trace_frame (next v) /\
  (!right. create_operand_focus_scope b c E C f t right ==>
           create_operand_focus_scope a c E C f s (left ++ right)) /\
  (!right r. create_operand_full_scope b c E C f t right r ==>
             create_operand_full_scope a c E C f s (left ++ right) r) /\
  (!right err ee leaf stop.
    gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,stop) ==>
    gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
      (es,s) (left ++ right) (err,ee) (leaf,stop)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a c
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `left ++ marks`
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- (disj1_tac >> conj_tac
      >- metis_tac[gas_bad_storage_at_bind_right] >>
      `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- metis_tac[] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
        (rpt strip_tac >> gvs[] >>
         drule_then (drule_then drule) scoped_operand_endpoint_horizon >> simp[]) >>
      fs[gas_marked_exec_def] >>
      `gas_path C f s (LENGTH left) (OK t)` by metis_tac[gas_marked_path_exec] >>
      drule gas_explicit_append_path >> disch_then (qspec_then `marks` assume_tac) >>
      conj_tac
      >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> qexistsl_tac [`mid`,`v`] >> fs[]) >>
      simp[] >> rpt strip_tac >> res_tac >> simp[] >>
      irule gas_origin_ptr_path_append >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `H` >> conj_tac >- metis_tac[] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

(* This is the sequencing rule for evaluated children.  The embeddings
   discharge the confined-path obligations, not the child's own simulation. *)
Theorem scoped_operand_bind:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!left v mid G1 tn1 t.
     (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
             (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          P H v (mid with gas_obs := []) G1 tn1 t) ==>
     scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 b c
       (next v) (mid with gas_obs := [],t,G1,tn1) Q R) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks. create_operand_focus_scope a b E C f s marks ==>
           create_operand_focus_scope a c E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a b E C f s marks r ==>
             create_operand_full_scope a c E C f s marks r) /\
  (!left t right. create_operand_full_scope a b E C f s left (OK t) /\
                  create_operand_focus_scope b c E C f t right ==>
                  create_operand_focus_scope a c E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a b E C f s left (OK t) /\
                    create_operand_full_scope b c E C f t right r ==>
                    create_operand_full_scope a c E C f s (left ++ right) r) /\
  (!marks err ee leaf stop.
     gas_exempt_cert T tops (C,f) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,stop) ==>
     gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
       (es,s) marks (err,ee) (leaf,stop)) /\
  (!left v mid t right err ee leaf stop.
     gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,stop) ==>
     gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
       (es,s) (left ++ right) (err,ee) (leaf,stop)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a c
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [scoped_operand_outcome_def])
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac >- metis_tac[gas_bad_storage_at_bind_left] >>
      metis_tac[])
  >- (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >>
      Cases_on `exit_result r`
      >- (`?exc. res = INR exc` by
            (qpat_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
               drule >> strip_tac >> gvs[exit_result_def] >> metis_tac[]) >>
          gvs[] >>
          rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
          disj2_tac >> disj1_tac >>
          qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
          conj_tac >- metis_tac[] >> conj_tac >- metis_tac[gas_source_bind_exception] >>
          simp[] >> rpt strip_tac >> res_tac >> fs[]) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        drule >> strip_tac >> gvs[] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G',tn') /\
           P H v (ee with gas_obs := []) G' tn' t` by (rpt strip_tac >> res_tac >> fs[]) >>
      `gas_marked_exec T (C,f) source (es,s) marks (INL v) ee (OK t)` by
        (rewrite_tac[gas_marked_exec_def] >>
         metis_tac[gas_origin_ptr_path_projections,gas_origin_path_erase]) >>
      irule scoped_operand_bind_right >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
      qexistsl_tac [`tn'`,`b`,`G'`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (metis_tac[]) >>
      rpt strip_tac >>
      drule_then (drule_then drule) scoped_operand_endpoint_horizon >> simp[]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The value form of a local word name emits MLOAD, even though the
   corresponding compile_expr can return a pointer without emitting it. *)
Theorem create_operand_cut_name_word:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr ce ty (Name ann id) a = (op,b) /\
  fn_has_code a b f /\ stmt_state_rel H C f ce cx es s /\
  create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx (Name ann id)) (read_result cx)) (es,s)
Proof
  strip_tac >> drule_all body_wordtype_name_region >> strip_tac >>
  drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
        fresh_id_def,fresh_var_def,emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction _ _ = SOME i` >>
  `i.inst_opcode = MLOAD /\ i.inst_id = a.cs_next_id` by simp[Abbr `i`,mk_inst_def] >>
  `create_operand_fetch a b f s i` by
    (fs[create_operand_fetch_def,create_operand_at_def,frag_ids_def] >> metis_tac[]) >>
  `?u. (!k. step_inst k C i s = OK u) /\ u.vs_current_bb = s.vs_current_bb` by
    (`eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
     simp[step_inst_non_invoke, Abbr `i`] >> drule step_MLOAD >>
     simp[update_var_def]) >>
  `create_operand_at b (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    fs[create_operand_at_def] >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  `?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by fs[create_operand_fetch_def] >>
  `i.inst_opcode <> INVOKE /\ ~MEM i.inst_opcode [CREATE;CREATE2] /\
   ~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `step_inst k C i s = OK u` by simp[] >>
  metis_tac[create_admin_one_step_visit]
QED

Theorem create_cut_exprs_cons:
  (create_body_cut E tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split E tops cx st0 (C,f)
       (bind (eval_expr cx e) (read_result cx))
       (\v. bind (eval_exprs cx xs) (\vs. return (v::vs)))
       (es,s) Q (left,right,hit)) ==>
  create_body_cut E tops cx st0 (eval_exprs cx (e::xs)) (es,s) (before,hit)
Proof
  `eval_exprs cx (e::xs) =
     bind (bind (eval_expr cx e) (read_result cx))
       (\v. bind (eval_exprs cx xs) (\vs. return (v::vs)))` by
    (simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
     gen_tac >> BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[] >> strip_tac
  >- (irule create_cut_bind_left >>
      simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  gvs[] >> drule_at Any create_cut_bind_right >>
  simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_return]
QED

Theorem create_cut_ifexp:
  (create_body_cut E tops cx st0 (eval_expr cx e) (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split E tops cx st0 (C,f) (eval_expr cx e)
       (\tv. bind (switch_BoolV cx tv (eval_expr cx yes) (eval_expr cx no))
                   (conditional_result cx)) (es,s) Q (left,right,hit)) ==>
  create_body_cut E tops cx st0 (eval_expr cx (IfExp ann e yes no)) (es,s) (before,hit)
Proof
  `eval_expr cx (IfExp ann e yes no) =
   bind (eval_expr cx e)
     (\tv. bind (switch_BoolV cx tv (eval_expr cx yes) (eval_expr cx no))
                 (conditional_result cx))` by
    simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
  simp[] >> strip_tac
  >- (irule create_cut_bind_left >>
      simp[storage_trace_frame_bind,storage_trace_frame_switch,
           evaluate_storage_trace_frame,storage_trace_frame_conditional_result]) >>
  gvs[] >> drule_at Any create_cut_bind_right >>
  simp[storage_trace_frame_bind,storage_trace_frame_switch,
       evaluate_storage_trace_frame,storage_trace_frame_conditional_result]
QED
