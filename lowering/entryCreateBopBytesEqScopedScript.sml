(* A scoped comparison composes the selected operand outcomes and the
   physical comparison run. The handoffs keep one ghost pair per exit. *)
Theory entryCreateBopBytesEqScoped
Ancestors
  entryCreateScopedBind entryCreateWordArgsGeometry entryCreateAdminSequence
  exprBopSimProps exprBopSimDefs exprSimFullBundleProps gasExemptCert fragGasPath
  entryCreateFocusSpec entryCreateCompletedCut entryCreateIntervalLayout
  abiEncoderProps bodySim exprSimDefs gasContext fragExec fragGasOriginPtr
  fragGasOrigin gasSummary vyperStorageTrace vyperStorageFootprint vyperAST
  vyperState vyperInterpreter venomInst venomState venomExecSemantics
  createSizeCutCode createSizePrefixReplay compileEnv arithmetic list

Theorem comparison_exit_post[local]:
  (\H (res : 'a + exception) ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post ctx cx H (INR exc : 'b + exception) ee gt r) =
  create_operand_exit_post ctx cx
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  Cases_on `res` >- simp[create_operand_exit_post_def] >>
  rename1 `INR ex` >> Cases_on `ex` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, halt_exit_def, expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem comparison_normal_source_state[local]:
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b source (es,s,G,tn) Q R ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b source (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\ ee.gas_obs = []) R
Proof
  rw[scoped_operand_outcome_def] >> qexists_tac `marks` >> simp[] >> metis_tac[]
QED

Theorem comparison_read_frame[local,simp]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]
QED

Theorem comparison_result_frame[local,simp]:
  storage_trace_frame (\s. (bop_result cx ann bop tys x y s,s))
Proof
  simp[storage_trace_frame_def, bop_result_def]
QED

(* The normal callback is handed the normalized source state and the same
   all-tail equation, path and post as the scoped left witness. *)
Theorem comparison_read_bind[local]:
  let read = bind (eval_expr cx e) (read_result cx) in
  let post = expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn) in
  body_inv (cx_tops cx) ctx ce cx /\ MEM f ctx.ctx_functions /\
  cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
  m.cs_next_id <= b.cs_next_id /\ create_layout a b /\ create_operand_at a s /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 a m
    read (es,s,G,tn) post (create_operand_exit_post ctx cx) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G1 tn1 t.
    mid.gas_obs = [] /\
    (!tail. read (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    create_operand_at m t /\ ~t.vs_halted /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       post H (INL v) mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 m b
      (next v) (mid,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 a b
    (bind read next) (es,s,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_word_args_scope_embeddings >>
  disch_then (qspec_then `E` strip_assume_tac) >>
  drule comparison_normal_source_state >> strip_tac >>
  irule scoped_operand_bind_all_mixed >>
  simp[comparison_read_frame] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_value >>
     simp[ignore_bind_def]) >>
  qexistsl_tac [`\H res ee G1 tn1 t.
      expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn)
        H res ee G1 tn1 t /\ ee.gas_obs = []`, `m`] >>
  simp[comparison_exit_post] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (rpt gen_tac >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      `?v. res = INL v` by fs[expr_sim_full_post_def] >> gvs[] >>
      `~t.vs_halted` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
           (drule_then strip_assume_tac) >>
         drule gas_origin_ptr_path_projections >>
         strip_tac >> drule gas_origin_path_erase >>
         metis_tac[fragGasModeTheory.gas_marked_path_exec, gas_path_normal]) >>
      first_x_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  pure_rewrite_tac[comparison_exit_post] >> first_assum ACCEPT_TAC
QED

Theorem comparison_scoped_suffix[local]:
  fn_has_code a b f /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts a b) /\
  create_operand_at a t /\ ~t.vs_halted /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (?raw G' tn' res.
    run_inst_seq (emitted_insts a b) t = OK raw /\
    (!tail. source (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    !H. valid_horizon cx st0 H fin.storage_trace ==>
      let u = raw with vs_inst_idx := LENGTH b.cs_current_insts in
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G,tn) [] (OK u,G',tn') /\
      Q H res (fin with gas_obs := []) G' tn' u) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b source (fin,t,G,tn) Q R
Proof
  simp_tac bool_ss[LET_THM] >> strip_tac >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`fin`,`OK (raw with vs_inst_idx := LENGTH b.cs_current_insts)`,
                `G'`,`tn'`] >>
  conj_tac >- (irule create_admin_sequence_scope >> fs[EVERY_MEM]) >>
  simp[NoAsms, gas_explicit_def, exit_result_def] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum drule >> simp[NoAsms]
QED

Theorem create_bop_bytes_eq_scoped_operands:
  let read1 = bind (eval_expr cx e1) (read_result cx) in
  let read2 = bind (eval_expr cx e2) (read_result cx) in
  let k = \v1 v2 ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee) in
  let parentQ = expr_sim_full_post (DF,lo,d,ctx,f) ce cx
       (Builtin ann (Bop bop) [e1;e2]) (es,a,b,s,op,G,tn) in
  let leftQ = expr_sim_full_post (DF,lo,d,ctx,f) ce cx e1 (es,a,m,s,x,G,tn) in
  let rightQ = \mid t G1 tn1.
       expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2 (mid,m,n,t,y,G1,tn1) in
  let left = \marks v1 mid G1 tn1 t.
       mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
       create_operand_at m t /\ ~t.vs_halted /\
       (!tail. read1 (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL v1,mid with gas_obs := tail)) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
         leftQ H (INL v1) mid G1 tn1 t /\
         gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) marks (OK t,G1,tn1)) in
  let right = \mid t G1 tn1 marks v2 fin G2 tn2 u.
       fin.gas_obs = [] /\ storage_trace_domain cx st0 fin.storage_trace /\
       create_operand_at n u /\ ~u.vs_halted /\
       (!tail. read2 (mid with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
          (INL v2,fin with gas_obs := tail)) /\
       (!H. valid_horizon cx st0 H fin.storage_trace ==>
         rightQ mid t G1 tn1 H (INL v2) fin G2 tn2 u /\
         gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G1,tn1) marks (OK u,G2,tn2)) in
  body_inv (cx_tops cx) ctx ce cx /\ MEM f ctx.ctx_functions /\ create_operand_at a s /\
  cs_extends a m /\ cs_extends m n /\ cs_extends n b /\
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= n.cs_next_id /\ n.cs_next_id <= b.cs_next_id /\
  create_layout a b /\ create_layout m b /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  create_cut_code {} m n /\ fn_has_code m n f /\
  create_cut_code {} n b /\ fn_has_code n b f /\
  b.cs_current_bb = n.cs_current_bb /\
  b.cs_current_insts = n.cs_current_insts ++ emitted_insts n b /\
  EVERY (\i. i.inst_id IN frag_ids n b /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts n b) /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 a m
    read1 (es,s,G,tn) leftQ (create_operand_exit_post ctx cx) /\
  (!marks v1 mid G1 tn1 t. left marks v1 mid G1 tn1 t ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 m n
      read2 (mid,t,G1,tn1) (rightQ mid t G1 tn1) (create_operand_exit_post ctx cx)) /\
  (!marks1 v1 mid G1 tn1 t marks2 v2 fin G2 tn2 u.
     left marks1 v1 mid G1 tn1 t /\ right mid t G1 tn1 marks2 v2 fin G2 tn2 u ==>
     ?raw G' tn' res.
       run_inst_seq (emitted_insts n b) u = OK raw /\
       (!tail. k v1 v2 (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
       !H. valid_horizon cx st0 H fin.storage_trace ==>
         let endstate = raw with vs_inst_idx := LENGTH b.cs_current_insts in
         gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (u,G2,tn2) [] (OK endstate,G',tn') /\
         parentQ H res (fin with gas_obs := []) G' tn' endstate) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 a b
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s,G,tn) parentQ (create_operand_exit_post ctx cx)
Proof
  simp_tac bool_ss[LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  `cs_extends m b /\ m.cs_next_id <= b.cs_next_id` by
    metis_tac[cs_extends_trans, LESS_EQ_TRANS] >>
  irule (SIMP_RULE bool_ss[LET_THM] comparison_read_bind) >>
  first_assum (irule_at Any) >> simp[] >>
  qexistsl_tac [`x`,`d`,`ce`] >> simp[storage_trace_frame_bind_all] >>
  rpt gen_tac >> strip_tac >>
  irule (SIMP_RULE bool_ss[LET_THM] comparison_read_bind) >>
  simp[] >> qexistsl_tac [`ce`,`d`,`n`,`y`] >> simp[] >>
  reverse conj_tac
  >- (first_x_assum irule >> simp[] >> qexistsl_tac [`marks`,`v`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule comparison_scoped_suffix >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  simp_tac bool_ss[LET_THM] >>
  qpat_assum `!ms v mid g tn t ms' v' fin g' tn' u. _ ==> ?raw. _` irule >>
  simp[] >> metis_tac[]
QED
