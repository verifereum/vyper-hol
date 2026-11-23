(* Ownership of a native ternary visit: follow its actual JNZ, without
   treating the two compiled arms as consecutive actions of that run. *)
Theory entryCreateIfExpVisit
Ancestors
  entryCreateFocusSpec entryCreateOperandReplay entryCreateBodyCut
  createSizeCutRegion createSizePrefixReplay fragGasOrigin
  dftGasFromListTraceDefs venomExecProofs venomExecSemantics venomRunBounded
  fragExec abiEncoderProps bodySim relation list pair venomInst venomState
  exprSimIfExp exprSimFullBundleProps vyperStorageTrace gasSummaryCompose
  entryCreateNativeFirstExit emitHelperProps loweringPosts entryCreateIfExpAdmin

(* After taking JNZ, discard the accumulated visits of the test and the JNZ
   itself, and restrict to the suffix beginning at the selected entry. *)
Triviality ifexp_suffix_native_rtc:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} se b /\ fn_has_code se b f ==>
  !x y. RTC (create_operand_native_step sc b E C f p) x y ==>
  !d k u front d' k' v all.
    x = (d,k,u,front) /\ y = (d',k',v,all) /\ create_operand_at se u ==>
    ?back. all = front ++ back /\
      create_trace_from p d k C f u = back ++ create_trace_from p d' k' C f v /\
      RTC (create_operand_native_step se b E C f p) (d,k,u,[]) (d',k',v,back) /\
      create_cut_region se b v
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (simp[create_operand_at_def] >>
      metis_tac[cj 1 create_cut_region_rules, APPEND]) >>
  simp_tac bool_ss [FORALL_PROD, create_operand_native_step_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `create_prefix_step sc b E C f m ms v` >>
  `gas_origin_edge F E C f m ms (OK v)` by fs[create_prefix_step_def] >>
  `~create_operand_at b m` by fs[create_operand_fetch_def] >>
  `create_prefix_step se b E C f m ms v /\ create_cut_region se b v` by
    (irule operand_cut_region_edge >> fs[create_operand_at_def] >> metis_tac[]) >>
  `create_operand_fetch se b f m inst` by
    (fs[create_operand_fetch_def, create_operand_at_def] >>
     metis_tac[cj 2 create_cut_region_rules]) >>
  qmatch_asmsub_rename_tac `RTC (create_operand_native_step se b E C f p)
      (d,k,u,[]) (dm,km,m,back)` >>
  simp[] >> irule (cj 2 RTC_RULES_RIGHT1) >> first_assum (irule_at Any) >>
  simp[create_operand_native_step_def] >> qexists_tac `inst` >> fs[Abbr `ms`]
QED

Triviality ifexp_jnz_native_step:
  create_operand_fetch sc b f u i /\ i.inst_opcode = JNZ /\
  step_inst_base i u = OK (jump_to l u) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_native_step sc b E C f p (d,k,u,[]) (d',k',v,front) ==>
  v = jump_to l u /\ front = [((p,d,i.inst_id),f,i,u)] /\
  create_trace_from p d k C f u = front ++ create_trace_from p d' k' C f v
Proof
  strip_tac >>
  fs[create_operand_native_step_def, LET_THM, create_operand_fetch_def] >>
  gvs[trace_step_noninvoke, create_prefix_step_def, gas_origin_edge_def,
      step_inst_non_invoke, is_terminator_def, exit_result_def, jump_to_def] >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  gvs[eval_phis_no_phi]
QED

Triviality ifexp_follow_jnz:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} se b /\ fn_has_code se b f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_fetch sc b f u i /\ i.inst_opcode = JNZ /\
  step_inst_base i u = OK (jump_to l u) /\ create_operand_at se (jump_to l u) /\
  create_interior_visit sc b E C f (p,d,k) u (before,hit,after) ==>
  before = [] /\ hit = ((p,d,i.inst_id),f,i,u) \/
  ?d1 k1 back. before = ((p,d,i.inst_id),f,i,u)::back /\
    create_interior_visit se b E C f (p,d1,k1) (jump_to l u) (back,hit,after)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `create_interior_visit _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE bool_ss [create_interior_visit_def, LET_THM]) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (qx_choosel_then [`df`,`kf`,`v`,`left`,`j`] mp_tac) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
  >- (gvs[create_operand_fetch_def, trace_step_noninvoke] >> metis_tac[]) >>
  rename1 `create_operand_native_step sc b E C f p (d,k,u,[]) z` >>
  PairCases_on `z` >> drule_all ifexp_jnz_native_step >> strip_tac >>
  `?back. left = z3 ++ back /\
     create_trace_from p z0 z1 C f z2 = back ++ create_trace_from p df kf C f v /\
     RTC (create_operand_native_step se b E C f p) (z0,z1,z2,[]) (df,kf,v,back) /\
     create_cut_region se b v` by metis_tac[ifexp_suffix_native_rtc] >>
  `create_operand_fetch se b f v j` by
    (fs[create_operand_fetch_def,create_operand_at_def] >>
     metis_tac[cj 2 create_cut_region_rules]) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac) >> disj2_tac >>
  qexistsl_tac [`z0`,`z1`] >> gvs[] >>
  simp[create_interior_visit_def] >>
  qexistsl_tac [`df`,`kf`,`v`,`back`,`j`] >> gvs[] >> metis_tac[]
QED

Triviality ifexp_visit_off_exit:
  create_interior_visit sc b E C f (p,d,k) u (before,hit,after) ==>
  ~create_operand_at b u
Proof
  rw[create_interior_visit_def] >>
  qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  fs[create_operand_native_step_def,create_operand_fetch_def] >>
  qmatch_asmsub_rename_tac `create_operand_native_step _ _ _ _ _ _ _ dest` >>
  PairCases_on `dest` >> fs[create_operand_native_step_def,create_operand_fetch_def]
QED

Triviality ifexp_forced_branch_frame:
  storage_trace_frame
    (if v = BoolV T then bind (eval_expr cx a) (conditional_result cx)
     else if v = BoolV F then bind (eval_expr cx b) (conditional_result cx)
     else raise (Error (TypeError "not BoolV")))
Proof
  rpt IF_CASES_TAC >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
       storage_trace_frame_conditional_result, storage_trace_frame_raise]
QED

(* Neither materialization nor ASSIGN/JMP owns an expression.  Their cut
   interfaces below are unconditional opcode exclusions, not statements about
   success of the selected arm or about its source result. *)
Triviality ifexp_selected_cont_cut:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} se b /\ fn_has_code se b f /\
  create_cut_code {} se sm /\ fn_has_code se sm f /\
  create_cut_code {} sm b /\ fn_has_code sm b f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_fetch sc b f u i /\ i.inst_opcode = JNZ /\
  step_inst_base i u = OK (jump_to l u) /\ create_operand_at se (jump_to l u) /\
  create_operand_cut se sm E C f tops cx st0 (eval_expr cx e) (mid,jump_to l u) /\
  (!p d k t before hit after.
    create_interior_visit sm b E C f (p,d,k) t (before,hit,after) ==>
    case hit of (_,_,inst,s) => inst_create_size_ok inst s) ==>
  create_operand_cut sc b E C f tops cx st0
    (bind (eval_expr cx e) (conditional_result cx)) (mid,u)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all ifexp_follow_jnz >> strip_tac
  >- gvs[create_body_cut_def,inst_create_size_ok_def] >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (`create_body_cut E tops cx st0 (eval_expr cx e) (mid,jump_to l u) (back,hit)` by
        metis_tac[create_operand_cut_def] >>
      `create_body_cut E tops cx st0 (bind (eval_expr cx e) (conditional_result cx))
         (mid,jump_to l u) (back,hit)` by
        (irule create_cut_bind_left >> simp[storage_trace_frame_conditional_result]) >>
      fs[create_body_cut_def,create_cut_marks_def,jump_to_def] >> metis_tac[]) >>
  `case hit of (_,_,inst,s) => inst_create_size_ok inst s` by metis_tac[] >>
  PairCases_on `hit` >> fs[create_body_cut_def]
QED

(* The replay premise is the common bind introduction, independent of the
   expression constructor.  The arm callback ranges over successful replays
   of the condition only, at the very cursor and ghosts supplied by replay. *)
Triviality ifexp_selected_vv_cut_at:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a sc /\ fn_has_code a sc f /\
  create_cut_code {} sc b /\ fn_has_code sc b f /\ ~s0.vs_halted /\
  expr_type c = BaseT BoolT /\
  gas_admissible (eval_expr cx (IfExp ann c yes no)) expr_vv_res_ok es /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn f /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  create_operand_cut a sc E C f tops cx st0
    (bind (eval_expr cx c) (read_result cx)) (es,s0) /\
  gas_completed_operand (DF,lo,E,C,f,PG) tops cx st0 a sc
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0) CondQ /\
  (!H res mid G tn u. CondQ H res mid G tn u ==>
    expr_sim_full_post (DF,lo,d,C,f) ce cx c (es,a,sc,s0,cop,G0,tn0) H res mid G tn u) ==>
  (! (source : evaluation_state -> value evaluation_result)
      (next : value -> evaluation_state -> eval_result evaluation_result) Q.
    (!v. storage_trace_frame (next v)) /\
    (!p depth k before hit after.
      create_interior_visit a b E C f (p,depth,k) s0 (before,hit,after) ==>
      create_interior_visit a sc E C f (p,depth,k) s0 (before,hit,after) \/
      ?u d1 k1 front back. before = front ++ back /\ create_operand_at sc u /\
        create_expr_prefix a sc E C f s0 (create_cut_marks E front) u /\
        create_interior_visit sc b E C f (p,d1,k1) u (back,hit,after)) /\
    create_operand_cut a sc E C f tops cx st0 source (es,s0) /\
    gas_completed_operand (DF,lo,E,C,f,PG) tops cx st0 a sc source (es,s0,G0,tn0) Q /\
    (!H marks v mid G tn u tail.
      create_expr_prefix a sc E C f s0 marks u /\ create_operand_at sc u /\
      source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid) /\ valid_horizon cx st0 H mid.storage_trace /\
      (!H'. valid_horizon cx st0 H' mid.storage_trace ==>
        gas_origin_ptr_path (DF H',lo,E,C,f,PG) (s0,G0,tn0) marks (OK u,G,tn) /\
        Q H' (INL v) (mid with gas_obs := []) G tn u) ==>
      create_operand_cut sc b E C f tops cx st0 (next v) (mid with gas_obs := [],u)) ==>
    create_operand_cut a b E C f tops cx st0 (bind source next) (es,s0)) /\
  (!sel. ?se sm sx.
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    create_cut_code {} se b /\ fn_has_code se b f /\
    create_cut_code {} se sm /\ fn_has_code se sm f /\
    create_cut_code {} sm b /\ fn_has_code sm b f /\
    create_cut_code {} sm sx /\ fn_has_code sm sx f /\
    create_cut_code {} sx b /\ fn_has_code sx b f /\
    (!p depth k t before hit after.
      create_interior_visit sm sx E C f (p,depth,k) t (before,hit,after) ==>
      case hit of (_,_,inst,s) => inst_create_size_ok inst s) /\
    (!p depth k t before hit after.
      create_interior_visit sx b E C f (p,depth,k) t (before,hit,after) ==>
      case hit of (_,_,inst,s) => inst_create_size_ok inst s) /\
    (!H marks mid G tn u tail.
      bind (eval_expr cx c) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL (BoolV sel),mid) /\ valid_horizon cx st0 H mid.storage_trace /\
      (!H'. valid_horizon cx st0 H' mid.storage_trace ==>
        gas_origin_ptr_path (DF H',lo,E,C,f,PG) (s0,G0,tn0) marks (OK u,G,tn) /\
        CondQ H' (INL (BoolV sel) : value + exception) (mid with gas_obs := []) G tn u) ==>
      create_operand_cut se sm E C f tops cx st0 (eval_expr cx (if sel then yes else no))
        (mid with gas_obs := [], jump_to (if sel then tl else el) u))) ==>
  create_operand_cut a b E C f tops cx st0 (eval_expr cx (IfExp ann c yes no)) (es,s0)
Proof
  ntac 2 strip_tac >> rewrite_tac[ifexp_root_eval_forced] >>
  qpat_x_assum `!source next Q. _` irule >>
  first_assum (irule_at Any) >> simp[ifexp_forced_branch_frame] >> conj_tac
  >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all ifexp_root_condition_bool >> strip_tac >> gvs[] >>
  qpat_x_assum `!sel. ?se sm sx. _` (qspec_then `sel` strip_assume_tac) >>
  `!p depth k t before hit after.
    create_interior_visit sm b E C f (p,depth,k) t (before,hit,after) ==>
    case hit of (_,_,inst,s) => inst_create_size_ok inst s` by
    (rpt gen_tac >> strip_tac >> drule_all create_interior_visit_first_exit >>
     metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `create_operand_cut _ _ _ _ _ _ _ _ src _` >>
  `src = bind (eval_expr cx (if sel then yes else no)) (conditional_result cx)` by
    (Cases_on `sel` >> simp[Abbr `src`]) >>
  gvs[] >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  `~create_operand_at b u` by metis_tac[ifexp_visit_off_exit] >>
  `CondQ H (INL (BoolV sel) : value + exception) (mid with gas_obs := []) G tn u` by
    metis_tac[] >>
  qpat_assum `!h r m g n t. CondQ h r m g n t ==> _`
    (drule_then assume_tac) >>
  `expr_post H C f ce cx c es a sc s0 (mid with gas_obs := []) (BoolV sel) cop u` by
    fs[expr_sim_full_post_def] >>
  drule_all ifexp_selected_jnz_fetch >> strip_tac >>
  qabbrev_tac `i = mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] []` >>
  `create_operand_fetch sc b f u i` by
    (fs[create_operand_fetch_def, create_operand_at_def] >>
     metis_tac[cj 1 create_cut_region_rules,cj 2 create_cut_region_rules]) >>
  `create_operand_at se (jump_to (if sel then tl else el) u)` by
    simp[create_operand_at_def,jump_to_def] >>
  `create_operand_cut se sm E C f tops cx st0 (eval_expr cx (if sel then yes else no))
    (mid with gas_obs := [], jump_to (if sel then tl else el) u)` by
    (qpat_assum `!H marks mid G tn u tail. _` irule >>
     conj_tac >- (qexistsl_tac [`G`,`marks`,`tail`,`tn`] >>
                  reverse conj_tac >- first_assum ACCEPT_TAC >>
                  qx_gen_tac `h` >> strip_tac >>
                  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
                    (qspec_then `h` mp_tac) >>
                  (impl_tac >- first_assum ACCEPT_TAC) >>
                  disch_then ACCEPT_TAC) >>
     qexists_tac `H` >> simp[]) >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `i.inst_opcode = JNZ` by simp[Abbr `i`,mk_inst_def] >>
  drule_all ifexp_selected_cont_cut >> simp[create_operand_cut_def] >>
  disch_then (drule_then ACCEPT_TAC)
QED

(* Retain the source equation from the very same normal scoped witness. *)
Triviality scoped_test_carries_source:
  scoped_operand_outcome D tops cx st0 a b src (es,s0,G0,tn0) P R ==>
  scoped_operand_outcome D tops cx st0 a b src (es,s0,G0,tn0)
    (\H res ee G tn t. P H res ee G tn t /\
      (?xs. !rest. src (es with gas_obs := xs ++ rest) = (res,ee with gas_obs := rest))) R
Proof
  PairCases_on `D` >> simp[entryCreateCompletedCutTheory.scoped_operand_outcome_def] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> qx_gen_tac `H` >> strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> simp[] >>
      disj1_tac >> qexists_tac `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The interval supplier describes the relative layout L on the compiled
   diamond. Child rules are used only after checking their own guarded pre. *)
Theorem ifexp_selected_vv_cut_intro:
  E = gas_explicit_sites C shC /\
  body_inv (cx_tops cx) C ce cx /\ shadow_body_inv (cx_tops cx) C shC /\
  expr_body_pre ce cx env (IfExp ann c yes no) es /\
  (!a sc b st0 s0 G0 tn0
      (source : evaluation_state -> value evaluation_result)
      (next : value -> evaluation_state -> eval_result evaluation_result) Q.
    (!v. storage_trace_frame (next v)) /\
    (!p depth k before hit after.
      create_interior_visit a b E C f (p,depth,k) s0 (before,hit,after) ==>
      create_interior_visit a sc E C f (p,depth,k) s0 (before,hit,after) \/
      ?u d1 k1 front back. before = front ++ back /\ create_operand_at sc u /\
        create_expr_prefix a sc E C f s0 (create_cut_marks E front) u /\
        create_interior_visit sc b E C f (p,d1,k1) u (back,hit,after)) /\
    create_operand_cut a sc E C f (cx_tops cx) cx st0 source (es,s0) /\
    gas_completed_operand (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a sc
      source (es,s0,G0,tn0) Q /\
    (!H marks v mid G tn u tail.
      create_expr_prefix a sc E C f s0 marks u /\ create_operand_at sc u /\
      source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid) /\ valid_horizon cx st0 H mid.storage_trace /\
      (!H'. valid_horizon cx st0 H' mid.storage_trace ==>
        gas_origin_ptr_path (DF H',lo,E,C,f,PG) (s0,G0,tn0) marks (OK u,G,tn) /\
        Q H' (INL v) (mid with gas_obs := []) G tn u) ==>
      create_operand_cut sc b E C f (cx_tops cx) cx st0 (next v)
        (mid with gas_obs := [],u)) ==>
    create_operand_cut a b E C f (cx_tops cx) cx st0 (bind source next) (es,s0)) /\
  (!st0 a b sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty (IfExp ann c yes no)
      es (st0,a,b,sha,shb,vv,s0,G0,tn0) /\ L a b ==>
    ?cop sc shsc sj sn tl el.
      L a sc /\ create_cut_code {} a sc /\ fn_has_code a sc f /\
      create_cut_code {} sc b /\ fn_has_code sc b f /\
      expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (BaseT BoolT) c
        es (st0,a,sc,sha,shsc,cop,s0,G0,tn0) /\
      emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
      fn_has_code sj sn f /\ sj.cs_current_bb = sc.cs_current_bb /\
      sj.cs_current_insts = sc.cs_current_insts /\
      !sel. ?se sm sx shse shsm av aop.
        let e = if sel then yes else no in
        compile_expr ce ty e se = (av,sm) /\
        compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shse = (av,shsm) /\
        compile_ifexp_arm ce ann (lowered_value_type ce e) av sm = (aop,sx) /\
        se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
        L se sm /\ create_cut_code {} se b /\ fn_has_code se b f /\
        create_cut_code {} se sm /\ fn_has_code se sm f /\
        create_cut_code {} sm b /\ fn_has_code sm b f /\
        create_cut_code {} sm sx /\ fn_has_code sm sx f /\
        create_cut_code {} sx b /\ fn_has_code sx b f /\
        (!p depth k t before hit after.
          create_interior_visit sm sx E C f (p,depth,k) t (before,hit,after) ==>
          case hit of (_,_,inst,s) => inst_create_size_ok inst s) /\
        (!p depth k t before hit after.
          create_interior_visit sx b E C f (p,depth,k) t (before,hit,after) ==>
          case hit of (_,_,inst,s) => inst_create_size_ok inst s) /\
        (!H marks mid G tn u tail.
          bind (eval_expr cx c) (read_result cx)
            (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
            (INL (BoolV sel),mid) /\ valid_horizon cx st0 H mid.storage_trace /\
          (!H'. valid_horizon cx st0 H' mid.storage_trace ==>
            gas_origin_ptr_path (DF H',lo,E,C,f,PG) (s0,G0,tn0) marks (OK u,G,tn) /\
            expr_sim_full_post (DF,lo,d,C,f) ce cx c (es,a,sc,s0,cop,G0,tn0)
              H' (INL (BoolV sel) : value + exception) (mid with gas_obs := []) G tn u) /\
          (?xs. !rest. bind (eval_expr cx c) (read_result cx)
            (es with gas_obs := xs ++ rest) = (INL (BoolV sel),mid with gas_obs := rest)) ==>
          expr_body_pre ce cx env e (mid with gas_obs := []) /\
          expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e
            (mid with gas_obs := [])
            (st0,se,sm,shse,shsm,av,jump_to (if sel then tl else el) u,G,tn))) /\
  (!st0 a sc sha shsc cop s0 G0 tn0.
    expr_body_pre ce cx env c es /\ L a sc /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (BaseT BoolT) c es
      (st0,a,sc,sha,shsc,cop,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a sc
      (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,C,f) ce cx c (es,a,sc,s0,cop,G0,tn0))
      (create_operand_exit_post C cx) /\
    create_operand_cut a sc E C f (cx_tops cx) cx st0
      (bind (eval_expr cx c) (read_result cx)) (es,s0)) /\
  (!sel ee st0 se sm shse shsm av u G tn.
    expr_body_pre ce cx env (if sel then yes else no) ee /\ L se sm /\
    expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty
      (if sel then yes else no) ee (st0,se,sm,shse,shsm,av,u,G,tn) ==>
    create_operand_cut se sm E C f (cx_tops cx) cx st0
      (eval_expr cx (if sel then yes else no)) (ee,u)) ==>
  !st0 a b sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty (IfExp ann c yes no)
      es (st0,a,b,sha,shb,vv,s0,G0,tn0) /\ L a b ==>
    create_operand_cut a b E C f (cx_tops cx) cx st0
      (eval_expr cx (IfExp ann c yes no)) (es,s0)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `E = gas_explicit_sites C shC` SUBST_ALL_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!st a b sha shb v s G n. _ ==> ?cop. _`
    (drule_all_then strip_assume_tac) >>
  drule bodyFullIfExpPrepareTheory.ifexp_body_pre_children >> strip_tac >>
  qpat_x_assum `!st a b sha shb op s G n. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  `MEM f C.ctx_functions /\ ~s0.vs_halted /\
    gas_admissible (eval_expr cx (IfExp ann c yes no)) expr_vv_res_ok es` by
    fs[s1PrefixDefsTheory.expr_vv_sim_full_pre_def] >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  qmatch_asmsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ P
    (create_operand_exit_post C cx)` >>
  qabbrev_tac `E = gas_explicit_sites C shC` >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ P _`
    (assume_tac o MATCH_MP scoped_test_carries_source) >>
  qmatch_asmsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ CondQ
    (create_operand_exit_post C cx)` >>
  drule_all entryCreateCompletedCutTheory.scoped_outcome_completed_operand >> strip_tac >>
  irule ifexp_selected_vv_cut_at >> simp[] >>
  qexistsl_tac [`CondQ`,`DF`,`G0`,`PG`,`ce`,`cop`,`d`,`el`,`lo`,`sc`,`sj`,`sn`,`tl`,`tn0`] >>
  `!H res mid G tn u. CondQ H res mid G tn u ==> P H res mid G tn u` by
    simp[Abbr `CondQ`] >>
  simp[GSYM markerTheory.Abbrev_def] >> reverse conj_tac
  >- (qpat_assum `!a sc b st s G n source next Q. _`
        (qspecl_then [`a`,`sc`,`b`,`st0`,`s0`,`G0`,`tn0`] ACCEPT_TAC)) >>
  qx_gen_tac `sel` >>
  qpat_x_assum `!sel. ?se sm sx shse shsm av aop. _`
    (qspec_then `sel` strip_assume_tac) >>
  qexistsl_tac [`se`,`sm`,`sx`] >> simp[] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H'. valid_horizon _ _ H' mid.storage_trace ==>
                  gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[Abbr `CondQ`] >>
  qpat_x_assum `!h ms ee g n t r. _ ==> expr_body_pre _ _ _ _ _ /\ _`
    (qspecl_then [`H`,`marks`,`mid`,`G`,`tn`,`u`,`tail`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists `xs` >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_x_assum `!sel ee st0 se sm shse shsm av u G tn. _`
    irule >>
  simp[] >>
  map_every qexists_tac [`G`,`av`,`shse`,`shsm`,`tn`] >>
  first_assum ACCEPT_TAC
QED
