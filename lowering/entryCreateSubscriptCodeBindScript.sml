(* The runtime-code selection uses the installed run at the ordinary landing. *)
Theory entryCreateSubscriptCodeBind
Ancestors
  bodyFullFramedCodeSelectionSpec entryCreateSubscriptArrayRun
  entryCreateSubscriptUncopied entryCreateIntervalLayout entryCreateFocusSpec
  entryCreateCompletedCut entryCreatePathScope fragGasOriginPtrExec
  fragGasOriginPtr exprSimFullBundleProps exprSimDefs bodyFullEmptyLeafData
  context vyperStorageFootprint vyperStorageTrace vyperState
  compileEnv fragExec emitHelperProps exprLoweringProps venomExecSemantics
  venomInst venomState abiEncoderProps bodyFullSubscriptArrayCodeBounds list instIdxIndep gasSummary
  entryCreateImmSubscriptIntervals entryCreateStmtUpdateCode createSizeCutCode
  exprSimSubscriptArraySource exprSimArrayIndex exprSimTopLevelProps gasContext bodySim
  createSizeOperandCode exprSimDefs exprSimHypsDefs s1PrefixDefs entryCreateOperandReplay
  bodyFullPreds bodyFullShadowBodyInv

Definition framed_code_load_scope_def:
  framed_code_load_scope <=>
    !imm arg a b op f s u t E ctx.
      compile_imm_load_word F imm arg a = (op,b) /\ fn_has_code a b f /\
      create_operand_at a s /\ ~s.vs_halted /\
      run_inst_seq (emitted_insts a b) s = OK u /\
      t = (u with vs_inst_idx := LENGTH b.cs_current_insts) ==>
      create_operand_full_scope a b E ctx f s [] (OK t)
End

Definition framed_code_bounds_runs_def:
  framed_code_bounds_runs B <=>
    (!a b s t. B a b s (OK t) ==> array_bounds_native_run a b s T t) /\
    (!a b s t. B a b s (Abort Revert_abort t) ==> array_bounds_native_run a b s F t)
End

Theorem framed_code_post[local]:
  expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,b,s,vv,G0,tn0) H res ee G tn t <=>
  create_operand_vv_post (DF,lo,d,ctx,f) ce cx e (es,a,b,s,vv,G0,tn0) H res ee G tn t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  simp[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,create_operand_vv_post_def,
       GSYM RIGHT_EXISTS_AND_THM, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem code_load_selector_code[local]:
  compile_imm_load_word F imm arg a = (op,b) ==> array_selector_code a b
Proof
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule emit_op_extends >>
  simp[same_blocks_def,array_selector_code_def,mk_inst_def,frag_ids_def,is_terminator_def]
QED

(* Use the physical optional length step before interpreting the check. *)
Theorem framed_code_length_stage[local]:
  framed_code_load_scope /\ create_operand_at a s /\ ~s.vs_halted /\
  fn_has_code a h f /\
  (case bd of Fixed n => h = a /\ t = s /\ len = Lit (n2w n)
   | Dynamic _ => compile_imm_load_word F imm arg a = (len,h) /\ framed_code_run a h s t) ==>
  array_selector_code a h /\ create_operand_at h t /\ framed_code_run a h s t
Proof
  Cases_on `bd` >> simp[] >> strip_tac
  >- (gvs[framed_code_run_def,emitted_insts_def,run_inst_seq_def,create_operand_at_def] >>
      simp[venom_state_component_equality]) >>
  drule code_load_selector_code >> strip_tac >> simp[] >>
  `create_operand_full_scope a h E ctx f s [] (OK t)` by
    (fs[framed_code_load_scope_def,framed_code_run_def] >> metis_tac[]) >>
  fs[create_operand_full_scope_def,create_operand_at_def]
QED

(* Revert absorbs the unexecuted address continuation.  The index stored
   by the raw run is immaterial here: the origin path supplies the actual
   indexed Abort to array_selector_oob_scope. *)
Theorem framed_code_selector_abort[local]:
  array_selector_code a h /\ array_selector_code h m /\ array_selector_code m b /\
  fn_has_code a b f /\ create_operand_at a s /\
  framed_code_run a h s u /\ array_bounds_native_run h m u F t /\
  gas_origin_path T E ctx f s [] (Abort Revert_abort t) ==>
  create_operand_full_scope a b E ctx f s [] (Abort Revert_abort t)
Proof
  strip_tac >>
  `array_selector_code a m /\ array_selector_code a b` by
    metis_tac[array_selector_code_join] >>
  fs[framed_code_run_def,array_bounds_native_run_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts h m)` by
    fs[array_selector_code_def,EVERY_MEM] >>
  `?v. run_inst_seq (emitted_insts h m) u' = Abort Revert_abort v` by
    (qpat_x_assum `run_inst_seq (emitted_insts h m) _ = _` mp_tac >>
     simp[run_inst_seq_inst_idx] >> Cases_on `run_inst_seq (emitted_insts h m) u'` >>
     simp[exec_result_map_def]) >>
  `inst_extends a h /\ inst_extends h m /\ inst_extends a m /\ inst_extends m b` by
    fs[array_selector_code_def,inst_extends_def] >>
  `emitted_insts a m = emitted_insts a h ++ emitted_insts h m` by
    fs[inst_extends_def,emitted_insts_append] >>
  `?v. run_inst_seq (emitted_insts a m) s = Abort Revert_abort v` by
    metis_tac[run_inst_seq_append] >>
  irule array_selector_oob_scope >> metis_tac[run_inst_seq_abort_extends]
QED

Theorem framed_code_terminal[local]:
  framed_code_selection_rule B /\ framed_code_load_scope /\ framed_code_bounds_runs B /\
  create_operand_at st2 it /\ ~it.vs_halted /\ fn_has_code st2 sb f /\
  framed_code_selection_hypotheses
    (DF,lo,d,ctx,shctx,PG,f,shf) (tops,ce,cx,env,ty,ann,e1,e2,et,bd)
    (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0) (sm,bvv,marks,tv,mid,s,G1,tn1)
    (st2,iop,imarks,v,fin,it,Gi,tni) dst ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 st2 sb (select_result cx (expr_type e1) tv (ValueSubscript v))
    (fin,it,Gi,tni)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Subscript ann e1 e2)
      (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `fin.gas_obs = [] /\ storage_trace_domain cx st0 fin.storage_trace` by
    (qpat_assum `framed_code_selection_hypotheses _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [framed_code_selection_hypotheses_def]) >> simp[]) >>
  qpat_x_assum `framed_code_selection_rule _`
    (drule_then (qx_choosel_then [`sl`,`sc`,`len`,`il`,`checked`,`res`,`r`,`Gf`,`tnf`]
      (map_every assume_tac o CONJUNCTS)) o REWRITE_RULE [framed_code_selection_rule_def]) >>
  `array_selector_code st2 sl /\ create_operand_at sl il /\ framed_code_run st2 sl it il` by
    (irule framed_code_length_stage >>
     qpat_assum `case bd of Fixed _ => _ | Dynamic _ => _` (irule_at Any) >>
     metis_tac[]) >>
  `array_selector_code sl sc` by metis_tac[array_bounds_selector_code] >>
  `array_selector_code sc sb` by metis_tac[array_elem_selector_code] >>
  `create_operand_full_scope st2 sb (gas_explicit_sites ctx shctx) ctx f it [] r` by
    (qpat_x_assum `(?child ib sf. _) \/ (?sf. _)` strip_assume_tac >> gvs[]
     >- (`array_bounds_native_run sl sc il T ib` by fs[framed_code_bounds_runs_def] >>
         fs[framed_code_run_def,array_bounds_native_run_def] >>
         irule array_selector_ok_scope_itinerary >> metis_tac[])
     >> irule framed_code_selector_abort >>
        qpat_assum `framed_code_run st2 sl it il` (irule_at Any) >> simp[] >>
        `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
          fs[storage_trace_domain_def] >>
        qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ [] _`
          (drule_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
        fs[framed_code_bounds_runs_def] >> metis_tac[]) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`fin`,`r`,`Gf`,`tnf`] >> simp[gas_explicit_def] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  rpt strip_tac >> gvs[GSYM framed_code_post,create_operand_exit_post_def,exit_result_def] >>
  metis_tac[]
QED

(* The common no-read bind at two installed exits. The actual child
   handoffs belong under the continuation quantifiers, not at entry. *)
Definition framed_code_nocopy_bind_def:
  framed_code_nocopy_bind <=>
    !DF lo E ctx f PG tops cx st0 a m n b es s G tn ce ann obj idx P I Q.
      body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
      create_operand_at a s /\ ~s.vs_halted /\ ~subscript_reads_base cx obj idx /\
      create_layout a b /\
      create_cut_code {} a m /\ create_cut_code {} m n /\ create_cut_code {} n b /\
      fn_has_code a m f /\ fn_has_code m n f /\ fn_has_code n b f /\ fn_has_code a b f /\
      scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
        (eval_expr cx obj) (es,s,G,tn) (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
        (create_operand_exit_post ctx cx) /\
      (!left v mid t G1 tn1.
        immutable_subscript_return (DF,lo,E,ctx,f,PG) cx st0 a m (eval_expr cx obj)
          (es,s,G,tn) P left v (mid,t,G1,tn1) ==>
        scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 m n
          (bind (eval_expr cx idx) (read_result cx)) (mid,t,G1,tn1)
          (\H res ee Gi tni it. ?k. res = INL k /\ I mid t G1 tn1 H k ee Gi tni it)
          (create_operand_exit_post ctx cx) /\
        (!right k fin it Gi tni.
          immutable_subscript_return (DF,lo,E,ctx,f,PG) cx st0 m n
            (bind (eval_expr cx idx) (read_result cx)) (mid,t,G1,tn1)
            (I mid t G1 tn1) right k (fin,it,Gi,tni) ==>
          scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 n b
            (select_result cx (expr_type obj) v (ValueSubscript k)) (fin,it,Gi,tni)
            Q (create_operand_exit_post ctx cx))) ==>
      scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
        (eval_expr cx (Subscript ann obj idx)) (es,s,G,tn) Q (create_operand_exit_post ctx cx)
End

Theorem framed_code_base_post[local]:
  (\H res ee G tn t. ?v. res = INL v /\
      create_operand_vv_post args ce cx e init H (INL v) ee G tn t /\
      create_operand_at m t) =
  (\H res ee G tn t. create_operand_vv_post args ce cx e init H res ee G tn t /\
      t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts)
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[FUN_EQ_THM,create_operand_vv_post_def,create_operand_at_def,
       GSYM RIGHT_EXISTS_AND_THM, AC CONJ_ASSOC CONJ_COMM] >> metis_tac[]
QED

Theorem framed_code_idx_post[local]:
  (\H res ee G tn t. ?v. res = INL v /\
      expr_sim_full_post args ce cx e init H (INL v) ee G tn t) =
  expr_sim_full_post args ce cx e init
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[FUN_EQ_THM,expr_sim_full_post_def] >> metis_tac[]
QED

Theorem framed_code_clear_tail[local]:
  mid.gas_obs = [] /\
  (!tail. source (es with gas_obs := prefix ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  source (es with gas_obs := prefix) = (INL v,mid)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `[]` mp_tac)) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >> simp[]
QED

Theorem framed_code_pre_bundle[local]:
  expr_vv_sim_full_pre args ce cx ty e es init <=>
  expr_vv_sim_full_hypotheses args ce cx ty e es init
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[expr_vv_sim_full_pre_def,expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def,
       CONJ_ASSOC]
QED

Theorem framed_code_scoped_bind_at:
  framed_code_selection_rule B /\ framed_code_load_scope /\ framed_code_bounds_runs B /\
  framed_code_nocopy_bind /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base ce e1 e2 /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et bd /\
  place_type ce e1 = ValPT (ArrayT et bd) /\ post_value_type ce e1 = expr_type e1 /\
  (!t res t'. eval_expr cx e2 t = (INL res,t') ==>
     t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!t tr slot vt t'. eval_expr cx e1 t <> (INL (PlaceR (StoragePlace tr slot vt)),t')) /\
  ~ce.ce_is_ctor /\
  (!ty' st. vv_location (FST (compile_expr ce ty' e1 st)) = SOME LocCode) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Subscript ann e1 e2)
    es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ create_layout sa sb /\
  (!sm shm bvv.
    expr_body_pre ce cx env e1 es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e1
      es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\ create_layout sa sm ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx e1) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx e1
        (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (create_operand_exit_post ctx cx)) /\
  (!gs tv mid s G1 tn1 sm shm st2 sh2 iop.
    eval_expr cx e1 (es with gas_obs := gs) = (INL tv,mid) /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_body_pre ce cx env e2 mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e2
      mid (st0,sm,st2,shm,sh2,iop,s,G1,tn1) /\ create_layout sm st2 ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sm st2 (bind (eval_expr cx e2) (read_result cx)) (mid,s,G1,tn1)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2 (mid,sm,st2,s,iop,G1,tn1))
      (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx (Subscript ann e1 e2)) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Subscript ann e1 e2)
      (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `cx_tops cx = tops` by fs[body_inv_def,cx_tops_def] >>
  qpat_x_assum `cx_tops cx = tops` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ (Subscript _ _ _) _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  drule_all_then (qx_choosel_then [`bvv`,`sm`,`shm`,`iop`,`st2`,`sh2`,`dst`,`loc`] strip_assume_tac)
    subscript_nocopy_selected_layout >>
  `vv_location bvv = SOME LocCode` by metis_tac[pairTheory.FST] >> gvs[] >>
  `create_layout sa sm /\ create_layout sm st2` by
    metis_tac[create_layout_subinterval,cs_extends_refl,cs_extends_trans] >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  `~array_slot_base ce e1` by metis_tac[array_slot_base_compile_location,pairTheory.FST] >>
  drule_all_then strip_assume_tac subscript_nocopy_base_ready >>
  qpat_assum `!sm shm bvv. _ ==> _` (qspecl_then [`sm`,`shm`,`bvv`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ e1 _ _`
    (mp_then Any assume_tac operand_vv_cut_code) >>
  `create_cut_code {} sm st2` by
    metis_tac[create_operand_cut_code,pairTheory.SND] >>
  `create_cut_code {} st2 sb` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule update_array_subscript_cut >> simp[]) >>
  qpat_x_assum `framed_code_nocopy_bind`
    (irule o REWRITE_RULE [framed_code_nocopy_bind_def]) >> simp[] >>
  conj_tac >- (qexists_tac `ce` >> simp[]) >>
  qexistsl_tac [
    `\mid t G1 tn1 H key ee Gi tni it. expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2
      (mid,sm,st2,t,iop,G1,tn1) H (INL key : value + exception) ee Gi tni it`,
    `\H raw ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx e1
      (es,sa,sm,s0,bvv,G0,tn0) H (INL raw : eval_result + exception) ee G tn t /\ create_operand_at sm t`,
    `sm`,`st2`] >>
  simp[framed_code_base_post,framed_code_idx_post] >>
  qx_genl_tac [`marks`,`tv`,`mid`,`s`,`G1`,`tn1`] >>
  simp[immutable_subscript_return_def] >> strip_tac >>
  suspend "after_base"
QED

Resume framed_code_scoped_bind_at[after_base]:
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (irule framed_code_clear_tail >> simp[] >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,f) ce cx e1
      (es,sa,sm,s0,bvv,G0,tn0) H (INL tv : eval_result + exception) mid G1 tn1 s /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (s0,G0,tn0) marks (OK s,G1,tn1)` by simp[] >>
  drule_all_then strip_assume_tac subscript_nocopy_index_ready >>
  conj_tac
  >- (qpat_assum `!gs tv mid s G1 tn1 sm shm st2 sh2 iop. _ ==> _`
       (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`tv`,`mid`,`s`,`G1`,`tn1`,
                    `sm`,`shm`,`st2`,`sh2`,`iop`] mp_tac) >>
      simp[framed_code_idx_post]) >>
  qx_genl_tac [`imarks`,`v`,`fin`,`it`,`Gi`,`tni`] >>
  simp[immutable_subscript_return_def] >> strip_tac >>
  `compile_array_subscript (vv_operand bvv) iop
     (case bd of Fixed _ => F | Dynamic _ => T)
     (case bd of Fixed n => n | Dynamic n => n) (word_scale LocCode)
     (elem_size_in_location ce LocCode et) (is_signed_type (expr_type e2))
     (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode) st2 = (dst,sb)` by
    (Cases_on `bd` >> fs[compile_array_subscript_split]) >>
  `framed_code_selection_hypotheses
     (DF,lo,d,ctx,shctx,PG,f,shf) (cx_tops cx,ce,cx,env,ty,ann,e1,e2,et,bd)
     (st0,es,sa,sb,sha,shb,LocatedValue ann (mk_ptr dst LocCode),s0,G0,tn0)
     (sm,bvv,marks,tv,mid,s,G1,tn1) (st2,iop,imarks,v,fin,it,Gi,tni) dst` by
    (simp[framed_code_selection_hypotheses_def,GSYM framed_code_pre_bundle,framed_code_post] >>
     fs[create_operand_at_def]) >>
  qpat_assum `expr_type e1 = _` (SUBST1_TAC o SYM) >>
  irule framed_code_terminal >>
  qpat_assum `framed_code_selection_hypotheses _ _ _ _ _ _` (irule_at Any) >>
  qexists_tac `B` >> simp[]
QED

Finalise framed_code_scoped_bind_at
