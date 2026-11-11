(* Unread positional operands: source reachability and CPS composition. *)
Theory exprExtRequestUnreadCps
Ancestors
  exprExtRequestGasBind exprSimDefs gasContext gasSummary gasSummaryCompose
  gasExemptCert stmtSimForRounds vyperInterpreter vyperState list
  exprSimSource exprSimHypsDefs vyperTypeInvariants
  exprExtRequestStrongCapture exprExtRequestHistory exprExtRequestHistoryCompose
  exprExtRequestSourceFrame exprExtRequestReadProbe exprOperandVar
  exprSafeOperand exprLoweringProps loweringPosts context venomState
  exprSimProps freshWrites compileEnv exprExtRequestOperandSafety exprLowering exprSimWordArgs stmtSimDeclGas gasOutcome pair fragExec fragGasMode vyperCallOutcomeFrame
Libs
  monadsyntax

Theorem extrequest_results_cons:
  eval_expr_results cx (e::es) =
    bind (eval_expr cx e)
      (\r. bind (eval_expr_results cx es) (\rs. return (r::rs)))
Proof
  simp[Once evaluate_def]
QED

Theorem extrequest_results_cps_cons:
  bind (eval_expr_results cx (e::es)) k =
    bind (eval_expr cx e)
      (\r. bind (eval_expr_results cx es) (\rs. k (r::rs)))
Proof
  simp[extrequest_results_cons, bind_assoc, bind_return]
QED

(* Typing rules out HashMapRef successes; exceptions must propagate all
   the way to the bound computation's admissibility gate. *)
Theorem extrequest_results_head_admissible:
  expr_body_pre cenv cx env e start /\
  gas_admissible (bind (eval_expr_results cx (e::es)) k)
    expr_vv_res_ok start ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok start
Proof
  rewrite_tac[gas_admissible_def, extrequest_results_cps_cons] >>
  rpt strip_tac >> Cases_on `res`
  >- (`expr_body_pre cenv cx env e (start with gas_obs := gs)` by simp[] >>
      drule_all expr_body_pre_eval_result >> strip_tac >>
      rename1 `INL v` >> Cases_on `v` >>
      gvs[expr_vv_res_ok_def, eval_result_typed_def]) >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

(* Unlike an arbitrary one-shot success equation, a counted source equation
   retains all fresh observation tails and hence suffices for admissibility. *)
Theorem extrequest_results_tail_admissible:
  gas_admissible (bind (eval_expr_results cx (e::es)) k)
    expr_vv_res_ok start /\
  (!tail. eval_expr cx e (start with gas_obs := used ++ tail) =
     (INL r, mid with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr_results cx es) (\rs. k (r::rs)))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[extrequest_results_cps_cons] >>
  strip_tac >> drule_all gas_admissible_bind_tail >> simp[]
QED

Definition extrequest_results_reach_def:
  extrequest_results_reach cx xs start i ee <=>
    i <= LENGTH xs /\
    ?gs rs mid.
      eval_expr_results cx (TAKE i xs) (start with gas_obs := gs) =
        (INL rs,mid) /\ ee = mid with gas_obs := []
End

Theorem extrequest_results_reach_zero[simp]:
  extrequest_results_reach cx xs start 0 ee <=>
  ee = start with gas_obs := []
Proof
  simp[extrequest_results_reach_def, Once evaluate_def, return_def]
QED

(* A counted head execution can be replayed with the tail's chosen gas
   observations, which is exactly the induction's reachable-entry bridge. *)
Theorem extrequest_results_reach_cons:
  (!tail. eval_expr cx e (start with gas_obs := used ++ tail) =
     (INL r, mid with gas_obs := tail)) /\
  extrequest_results_reach cx xs (mid with gas_obs := []) i ee ==>
  extrequest_results_reach cx (e::xs) start (SUC i) ee
Proof
  simp[extrequest_results_reach_def] >> strip_tac >>
  qexistsl_tac [`used ++ gs`, `r::rs`, `mid'`] >>
  simp[extrequest_results_cons, bind_def, return_def]
QED

Definition extrequest_results_success_def:
  extrequest_results_success cx xs start rs ee <=>
    ?gs mid. eval_expr_results cx xs (start with gas_obs := gs) =
      (INL rs,mid) /\ ee = mid with gas_obs := []
End

Theorem extrequest_results_success_nil[simp]:
  extrequest_results_success cx [] start rs ee <=>
  rs = [] /\ ee = start with gas_obs := []
Proof
  simp[extrequest_results_success_def, Once evaluate_def, return_def] >>
  metis_tac[]
QED

Theorem extrequest_results_success_cons:
  (!tail. eval_expr cx e (start with gas_obs := used ++ tail) =
     (INL r, mid with gas_obs := tail)) /\
  extrequest_results_success cx xs (mid with gas_obs := []) rs ee ==>
  extrequest_results_success cx (e::xs) start (r::rs) ee
Proof
  simp[extrequest_results_success_def] >> strip_tac >>
  qexistsl_tac [`used ++ gs`, `mid'`] >>
  simp[extrequest_results_cons, bind_def, return_def]
QED

Theorem extrequest_results_body_pre_tail:
  (!i ee. i < LENGTH (e::xs) /\
     extrequest_results_reach cx (e::xs) start i ee ==>
     expr_body_pre cenv cx env (EL i (e::xs)) ee) /\
  (!tail. eval_expr cx e (start with gas_obs := used ++ tail) =
     (INL r, mid with gas_obs := tail)) ==>
  !i ee. i < LENGTH xs /\
    extrequest_results_reach cx xs (mid with gas_obs := []) i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee
Proof
  rpt strip_tac >>
  `extrequest_results_reach cx (e::xs) start (SUC i) ee` by
    (drule_all extrequest_results_reach_cons >> simp[]) >>
  qpat_x_assum `!i ee. _` (qspecl_then [`SUC i`, `ee`] mp_tac) >>
  simp[]
QED

Theorem extrequest_vv_wb_frame[local]:
  vv_post ctx func cenv cx e es sa sb s0 ee r vv t ==>
  wb_frame cenv es sa s0 t
Proof
  simp[vv_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem extrequest_path_nonhalting[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==> !t. r = OK t ==> ~t.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[exit_result_def]
QED

(* The two held post interfaces are explicit theorem parameters, never axioms. *)
Theorem extrequest_unread_cps:
  !xs es sa sb vvs s0 k old_es old_rs old_vvs.
  results_case nocalls ctx func cenv cx xs /\
  compile_multi_vvs compile_expr cenv xs sa = (vvs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\e. ~expr_has_effect e) xs /\
  EVERY (\e. nocalls ==> int_calls_expr e = []) xs /\
  (!i ee. i < LENGTH xs /\ extrequest_results_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee) /\
  gas_admissible (bind (eval_expr_results cx xs) k) expr_vv_res_ok es /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!rs ee t.
    extrequest_results_success cx xs es rs ee /\
    stmt_state_rel ctx func cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ wb_frame cenv es sa s0 t /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ee.gas_obs = [] /\
    extrequest_strong_captures ctx func cenv cx xs rs vvs ee sb t /\
    extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sb t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k rs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr_results cx xs) k) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  Induct_on `xs` >> rpt gen_tac
  >- (simp[compile_multi_vvs_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops cx) (ctx,func) (k [])
         (es with gas_obs := [],s0) Q (\res ee r. expr_exit res r)` by
        (first_x_assum irule >> simp[wb_frame_refl]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[results_case_def, Once compile_multi_vvs_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  rename1 `compile_expr cenv (expr_type h) h sa = (head_vv,sm)` >>
  `expr_body_pre cenv cx env h es` by
    (qpat_x_assum `!i ee. _` (qspecl_then [`0`, `es with gas_obs := []`] mp_tac) >>
     simp[]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    (drule_all extrequest_results_head_admissible >> simp[]) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`, `expr_type h`, `h`, `sa`]
       (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sb` by
    (qpat_x_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
     mp_tac (Q.ISPEC `compile_expr` ci_mono_compile_multi_vvs) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (drule_all compiler_ci_mono_reserved >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type h) h es` by
    (gvs[expr_vv_case_def] >> first_x_assum irule >>
     qexists `env` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx h) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func cenv cx h es sa sm s0 ee r head_vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_vv_sim_def] >> first_x_assum irule >> simp[]) >>
  rewrite_tac[extrequest_results_cps_cons] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``]
    extrequest_outcome_bind_result) >>
  disch_then (qspecl_then
    [`\r. bind (eval_expr_results cx xs) (\rs. k (r::rs))`,
     `\res ee r. expr_exit res r`, `Q`] mp_tac) >>
  disch_then irule >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!tail. eval_expr cx h
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL r, mid with gas_obs := tail)` by gvs[gas_marked_exec_def] >>
  `gas_admissible (bind (eval_expr_results cx xs) (\rs. k (r::rs)))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (drule_all extrequest_results_tail_admissible >> simp[]) >>
  `!i ee. i < LENGTH xs /\
    extrequest_results_reach cx xs (mid with gas_obs := []) i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee` by
    (rpt strip_tac >>
     `extrequest_results_reach cx (h::xs) es (SUC i) ee` by
       (drule_all extrequest_results_reach_cons >> simp[]) >>
     qpat_x_assum `!i ee. i < SUC _ /\ _ ==> _`
       (qspecl_then [`SUC i`, `ee`] mp_tac) >> simp[]) >>
  `results_case nocalls ctx func cenv cx xs` by
    (first_x_assum irule >>
     qexistsl_tac [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `r`, `mid with gas_obs := []`] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `!l. vv_operand head_vv <> Label l` by
    (irule (cj 1 extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_x_assum `expr_body_pre _ _ _ h es` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand head_vv = Var x ==> not_fresh_at sm x` by
    (metis_tac[CONJUNCT1 compiler_compile_var]) >>
  `safe_operand sm (vv_operand head_vv)` by simp[safe_operand_def] >>
  `extrequest_strong_capture ctx func cenv cx h r head_vv
    (mid with gas_obs := []) sm t` by
    (`(case head_vv of StackValue ty op => safe_operand sm op
        | LocatedValue ty p => safe_operand sm p.ptr_operand)` by
       (Cases_on `head_vv` >> gvs[vv_operand_def]) >>
     `post_value_type cenv h = expr_type h` by
       (irule post_value_type_not_int_call >>
        metis_tac[expr_has_effect_thm]) >>
     irule extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ h _ _ _ _ _ _ _ _` (irule_at Any) >>
     fs[ci_mono_def] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `!e ee sm sn t ef r u ty p w tv. _`
       (drule_all_then mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[extrequest_path_nonhalting]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_x_assum `vv_post _ _ _ _ h _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def]) >>
  `extrequest_read_frame cx (es with gas_obs := [])
     (mid with gas_obs := [])` by
    (drule extrequest_pure_expr_read_frame >>
     rewrite_tac[state_rel_frame_result] >>
     disch_then (qspecl_then
       [`cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
        `INL r`, `mid with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     fs[extrequest_read_frame_def]) >>
  `vv_post ctx func cenv cx h (es with gas_obs := []) sa sm s0
     (mid with gas_obs := []) r head_vv t` by simp[vv_post_initial_gas] >>
  `wb_frame cenv es sa s0 t` by
    (irule extrequest_vv_wb_frame >>
     qpat_assum `vv_post _ _ _ _ h es _ _ _ _ _ _ _` (irule_at Any)) >>
  `extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
     (mid with gas_obs := []) sm t` by
    (irule extrequest_strong_captures_extend >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0`
       (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ h (es with gas_obs := []) _ _ _ _ _ _ _`
       (irule_at Any) >>
     simp[] >>
     qpat_x_assum `!e ee sm sn t ef r vv u. _` (drule_all_then mp_tac) >>
     fs[ci_mono_def]) >>
  qpat_x_assum `!es' sa' sb' vvs' s0' k' old_es' old_rs' old_vvs'. _` irule >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`h::old_es`, `r::old_rs`, `head_vv::old_vvs`] >>
  qpat_assum `compile_multi_vvs _ _ _ sm = _` (irule_at Any) >>
  simp[extrequest_strong_captures_cons] >>
  rpt gen_tac >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (fs[extrequest_read_frame_def]) >>
  `wb_frame cenv es sa s0 t'` by
    (`local_ptrs_rel func cenv es.scopes s0` by
       (qpat_assum `stmt_state_rel _ _ _ _ es s0` mp_tac >>
        simp[NoAsms, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
        metis_tac[]) >>
     qpat_assum `wb_frame _ es sa s0 t` mp_tac >>
     qpat_assum `wb_frame _ _ sm t t'` mp_tac >>
     simp[NoAsms, wb_frame_def] >> strip_tac >> strip_tac >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by
           (irule freshWritesTheory.not_fresh_at_mono >>
            qexists `sa` >> fs[ci_mono_def]) >> metis_tac[]) >>
     conj_tac
     >- (rpt strip_tac >>
         `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
         `aid < sm.cs_next_id` by fs[ci_mono_def] >>
         `!n b sz'. local_region cenv mid.scopes t n b sz' ==>
                     off + sz <= b \/ b + sz' <= off` by
           (rpt strip_tac >>
            `local_region cenv es.scopes s0 n b sz'` by
              (irule local_region_frame >>
               conj_tac >- (qexists `func` >> simp[]) >>
               qexistsl_tac [`sa`, `mid.scopes`, `t`] >> simp[]) >> metis_tac[]) >>
         metis_tac[]) >>
     fs[locals_kept_def] >> rpt strip_tac >>
     `local_region cenv mid.scopes t n b sz` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >> metis_tac[]) >>
  `extrequest_results_success cx (h::xs) es (r::rs) ee` by
    (irule extrequest_results_success_cons >>
     qexistsl_tac [`mid`, `gas_explicit marks s0.vs_gas_readings`] >> simp[]) >>
  qpat_x_assum `!rs ee t. extrequest_results_success cx (h::xs) _ _ _ /\ _ ==> _`
    irule >>
  simp[extrequest_strong_captures_cons]
QED
