(* Selection interface for the source-ordered external-call keyword fold. *)
Theory exprExtRequestKwargs
Ancestors
  exprExtRequestKwargCps exprExtRequestKwargSuffix exprExtRequestRetained
  exprExtRequestHistory exprExtRequestHistoryCompose exprExtRequestStrongCapture exprLowering
  exprSimWordArgs exprSimSource exprLoweringProps freshWrites exprSafeOperand
  exprSimHypsDefs exprSimDefs exprSimProps gasSummary gasOutcome
  stmtSimForRounds stmtSimDeclGas gasExemptCert compileEnv fragExec
  vyperInterpreter vyperState list option pair

Definition extrequest_kwarg_selection_def:
  extrequest_kwarg_selection cenv cx ret kw selected compiled ee sb t <=>
    (selected = NONE <=> compiled = NONE) /\
    !v. selected = SOME v ==>
      ?op ty. compiled = SOME (op,ty) /\
        extrequest_retained_value cenv cx
          (if kw = EKDefault then ty else BaseT (UintT 256)) v op ee sb t /\
        (kw = EKDefault ==>
          (ty = ret \/ is_bytestring_type ty /\ is_bytestring_type ret) /\
          ?rtv. evaluate_type (get_tenv cx) ret = SOME rtv /\
            value_has_type rtv v /\ val_wf rtv v)
End

Theorem extrequest_kwarg_selection_none[simp]:
  extrequest_kwarg_selection cenv cx ret kw NONE NONE ee sb t
Proof
  simp[extrequest_kwarg_selection_def]
QED

Theorem extrequest_kwarg_selection_head:
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
    old_es old_rs old_vvs v ee t /\
  extrequest_retained_value cenv cx
    (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb t ==>
  extrequest_kwarg_selection cenv cx ret kw (SOME v) (SOME (op,dty)) ee sb t
Proof
  strip_tac >> fs[extrequest_kwarg_post_def] >>
  Cases_on `kw = EKDefault` >> gvs[extrequest_kwarg_selection_def]
QED

Theorem extrequest_kwarg_selection_transport:
  extrequest_kwarg_selection cenv cx ret kw selected compiled ec sc tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee t ==>
  extrequest_kwarg_selection cenv cx ret kw selected compiled ee sn t
Proof
  simp[extrequest_kwarg_selection_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule extrequest_retained_value_transport >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extrequest_kwarg_selection_singleton:
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
    old_es old_rs old_vvs v ee t /\
  extrequest_retained_value cenv cx
    (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb t ==>
  extrequest_kwarg_selection cenv cx ret query
    (ext_call_kwarg query [kw] [v])
    (if kw = query then SOME (op,dty) else NONE) ee sb t
Proof
  strip_tac >> Cases_on `kw = query`
  >- (gvs[ext_call_kwarg_def] >> drule_all extrequest_kwarg_selection_head >> simp[]) >>
  simp[ext_call_kwarg_def]
QED

(* The singleton default exposes precisely the footprint, not its type's
   maximum allocation size, while retaining runtime typing at both types. *)
Theorem extrequest_selected_default_footprint:
  extrequest_kwarg_selection cenv cx ret EKDefault (SOME v)
    (SOME (op,dty)) ee sb t ==>
  (dty = ret \/ is_bytestring_type dty /\ is_bytestring_type ret) /\
  expr_val_rel cx dty v op t /\
  ?tv rtv. evaluate_type (get_tenv cx) dty = SOME tv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    value_has_type tv v /\ val_wf tv v /\
    value_has_type rtv v /\ val_wf rtv v /\
    (!w. ~is_word_type dty /\ eval_operand op t = SOME w ==>
       w2n w + val_footprint tv v <= t.vs_alloca_next)
Proof
  simp[extrequest_kwarg_selection_def, extrequest_retained_value_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[optionTheory.SOME_11]
QED

Definition extrequest_kwargs_post_def:
  extrequest_kwargs_post ctx func cenv cx ret ks xs es sa s0 sb
      value_op gas_op default_op old_es old_rs old_vvs vs ee t <=>
    (?obs. eval_exprs cx xs (es with gas_obs := obs) = (INL vs,ee)) /\
    (?used. !tail. eval_exprs cx xs (es with gas_obs := used ++ tail) =
      (INL vs, ee with gas_obs := tail)) /\
    ee.gas_obs = [] /\ LENGTH vs = LENGTH ks /\
    stmt_state_rel ctx func cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    wb_frame cenv es sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sb t /\
    extrequest_history_frame cenv cx (es with gas_obs := []) sa s0 ee sb t /\
    extrequest_kwarg_selection cenv cx ret EKValue
      (ext_call_kwarg EKValue ks vs) (OPTION_MAP (\op. (op,ret)) value_op) ee sb t /\
    extrequest_kwarg_selection cenv cx ret EKGas
      (ext_call_kwarg EKGas ks vs) (OPTION_MAP (\op. (op,ret)) gas_op) ee sb t /\
    extrequest_kwarg_selection cenv cx ret EKDefault
      (ext_call_kwarg EKDefault ks vs) default_op ee sb t
End

Theorem extrequest_kwargs_post_nil:
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 ==>
  extrequest_kwargs_post ctx func cenv cx ret [] [] es sa s0 sa
    NONE NONE NONE old_es old_rs old_vvs [] (es with gas_obs := []) s0
Proof
  simp[extrequest_kwargs_post_def, Once evaluate_def, return_def,
       wb_frame_refl, extrequest_history_frame_refl, ext_call_kwarg_def] >>
  strip_tac >> conj_tac
  >- (qexists `[]` >> simp[]) >>
  qexists `[]` >> simp[Once evaluate_def, return_def]
QED

Theorem extrequest_kwargs_source_cons:
  eval_exprs cx (e::xs) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx xs) (\vs. return (v::vs)))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem extrequest_kwargs_counted_cons:
  (!tail. (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := used ++ tail) = (INL v, mid with gas_obs := tail)) /\
  (!tail. eval_exprs cx xs (mid with gas_obs := more ++ tail) =
     (INL vs, ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx (e::xs) (es with gas_obs := (used ++ more) ++ tail) =
     (INL (v::vs), ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  rewrite_tac[extrequest_kwargs_source_cons, GSYM APPEND_ASSOC] >>
  once_rewrite_tac[bind_def] >> simp[] >> simp[bind_def, return_def]
QED

Definition extrequest_kwargs_reach_def:
  extrequest_kwargs_reach cx xs start i ee <=>
    i <= LENGTH xs /\
    ?gs vs mid. eval_exprs cx (TAKE i xs) (start with gas_obs := gs) =
      (INL vs,mid) /\ ee = mid with gas_obs := []
End

Theorem extrequest_kwargs_reach_zero[simp]:
  extrequest_kwargs_reach cx xs start 0 ee <=>
    ee = start with gas_obs := []
Proof
  simp[extrequest_kwargs_reach_def, Once evaluate_def, return_def]
QED

Theorem extrequest_kwargs_reach_cons:
  (!tail. (bind (eval_expr cx e) (read_result cx))
     (start with gas_obs := used ++ tail) = (INL v, mid with gas_obs := tail)) /\
  extrequest_kwargs_reach cx xs (mid with gas_obs := []) i ee ==>
  extrequest_kwargs_reach cx (e::xs) start (SUC i) ee
Proof
  simp[extrequest_kwargs_reach_def] >> strip_tac >>
  qexistsl_tac [`used ++ gs`, `v::vs`, `mid'`] >>
  rewrite_tac[extrequest_kwargs_source_cons] >>
  once_rewrite_tac[bind_def] >> simp[] >> simp[bind_def, return_def]
QED

Theorem extrequest_kwargs_body_pre_tail:
  (!i ee. i < LENGTH (e::xs) /\
     extrequest_kwargs_reach cx (e::xs) start i ee ==>
     expr_body_pre cenv cx env (EL i (e::xs)) ee) /\
  (!tail. (bind (eval_expr cx e) (read_result cx))
     (start with gas_obs := used ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  !i ee. i < LENGTH xs /\
    extrequest_kwargs_reach cx xs (mid with gas_obs := []) i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee
Proof
  rpt strip_tac >>
  `extrequest_kwargs_reach cx (e::xs) start (SUC i) ee` by
    (drule_all extrequest_kwargs_reach_cons >> simp[]) >>
  qpat_x_assum `!i ee. _` (qspecl_then [`SUC i`, `ee`] mp_tac) >> simp[]
QED

Theorem extrequest_kwarg_selection_cons:
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sm op dty
    old_es old_rs old_vvs v mid tm /\
  extrequest_retained_value cenv cx
    (if kw = EKDefault then dty else BaseT (UintT 256)) v op mid sm tm /\
  extrequest_history_frame cenv cx mid sm tm ee sb t /\
  stmt_state_rel ctx func cenv cx ee t /\
  extrequest_kwarg_selection cenv cx ret query
    (ext_call_kwarg query ks vs) compiled ee sb t ==>
  extrequest_kwarg_selection cenv cx ret query
    (ext_call_kwarg query (kw::ks) (v::vs))
    (if kw = query then SOME (op,dty) else compiled) ee sb t
Proof
  strip_tac >> Cases_on `kw = query`
  >- (gvs[ext_call_kwarg_def] >>
      irule extrequest_kwarg_selection_transport >>
      qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl_tac [`func`, `ctx`] >> simp[] >>
      conj_tac >- fs[extrequest_kwarg_post_def] >>
      irule extrequest_kwarg_selection_head >> metis_tac[]) >>
  simp[ext_call_kwarg_def]
QED

Theorem extrequest_kwargs_post_cons:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sm op dty
    old_es old_rs old_vvs v mid tm /\
  extrequest_retained_value cenv cx
    (if kw = EKDefault then dty else BaseT (UintT 256)) v op mid sm tm /\
  extrequest_history_frame cenv cx (es with gas_obs := []) sa s0 mid sm tm /\
  (!tail. (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := used ++ tail) = (INL v, mid with gas_obs := tail)) /\
  extrequest_kwargs_post ctx func cenv cx ret ks xs mid sm tm sb
    value_op gas_op default_op old_es old_rs old_vvs vs ee t ==>
  extrequest_kwargs_post ctx func cenv cx ret (kw::ks) (e::xs) es sa s0 sb
    (if kw = EKValue then SOME op else value_op)
    (if kw = EKGas then SOME op else gas_op)
    (if kw = EKDefault then SOME (op,dty) else default_op)
    old_es old_rs old_vvs (v::vs) ee t
Proof
  strip_tac >>
  `mid.gas_obs = []` by fs[extrequest_kwarg_post_def] >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx mid tm /\
   sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\ wb_frame cenv es sa s0 tm` by
    fs[extrequest_kwarg_post_def] >>
  `extrequest_history_frame cenv cx mid sm tm ee sb t /\
   stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv mid sm tm t` by
    fs[extrequest_kwargs_post_def] >>
  `wb_frame cenv es sa s0 t` by (drule_all wb_frame_trans >> simp[]) >>
  `extrequest_history_frame cenv cx (es with gas_obs := []) sa s0 ee sb t` by
    (irule extrequest_history_frame_trans >> conj_tac
     >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `?more. !tail. eval_exprs cx xs (mid with gas_obs := more ++ tail) =
    (INL vs, ee with gas_obs := tail)` by
    (fs[extrequest_kwargs_post_def] >> metis_tac[]) >>
  `!tail. eval_exprs cx (e::xs) (es with gas_obs := (used ++ more) ++ tail) =
    (INL (v::vs), ee with gas_obs := tail)` by
    (drule_all extrequest_kwargs_counted_cons >> simp[]) >>
  `!query compiled.
    extrequest_kwarg_selection cenv cx ret query
      (ext_call_kwarg query ks vs) compiled ee sb t ==>
    extrequest_kwarg_selection cenv cx ret query
      (ext_call_kwarg query (kw::ks) (v::vs))
      (if kw = query then SOME (op,dty) else compiled) ee sb t` by
    (rpt strip_tac >> irule extrequest_kwarg_selection_cons >>
     qpat_assum `extrequest_kwarg_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >> simp[]) >>
  fs[extrequest_kwargs_post_def] >>
  rewrite_tac[extrequest_kwargs_post_def] >>
  conj_tac >- (qexists `used ++ more` >>
    qpat_x_assum `!tail. eval_exprs cx (e::xs) _ = _`
      (qspec_then `[]` mp_tac) >>
    simp[evaluation_state_component_equality]) >>
  conj_tac >- (qexists `used ++ more` >> simp[]) >>
  qpat_assum `!query compiled. _` (qspecl_then
    [`EKValue`, `OPTION_MAP (\op. (op,ret)) value_op`]
      (drule_all_then assume_tac)) >>
  qpat_assum `!query compiled. _` (qspecl_then
    [`EKGas`, `OPTION_MAP (\op. (op,ret)) gas_op`]
      (drule_all_then assume_tac)) >>
  qpat_assum `!query compiled. _` (qspecl_then
    [`EKDefault`, `default_op`] (drule_all_then assume_tac)) >>
  Cases_on `kw` >> gvs[extrequest_kwarg_post_def]
QED

(* The generic fold monotonicity theorem is local to exprLoweringProps. *)
Theorem extrequest_kwargs_mono:
  !ks xs cenv ret sa.
    ci_mono sa (SND (compile_ext_call_kwargs compile_expr cenv ret ks xs sa))
Proof
  Induct >> Cases_on `xs` >> rpt strip_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> irule ci_mono_compile_ext_call_kwarg >>
      simp[cj 1 compile_expr_ci_mono]) >>
  rpt strip_tac >> simp[pairTheory.UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule) >>
  simp[pairTheory.UNCURRY, ci_mono_comp_return]
QED

Theorem extrequest_kwargs_bind_cons:
  bind (eval_exprs cx (e::xs)) kont =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx xs) (\vs. kont (v::vs)))
Proof
  rewrite_tac[extrequest_kwargs_source_cons] >>
  CONV_TAC (LHS_CONV (REWR_CONV bind_assoc)) >> AP_TERM_TAC >> ABS_TAC >>
  simp[bind_assoc, bind_return]
QED

Theorem extrequest_kwargs_cps:
  !ks xs es sa sb value_op gas_op default_op s0 kont old_es old_rs old_vvs.
  LENGTH xs = LENGTH ks /\ exprs_case nocalls ctx func cenv cx xs /\
  EVERY2 (\kw e. expr_type e = ext_call_kw_type ret kw /\
    (kw = EKDefault ==> ret <> NoneT)) ks xs /\
  EVERY (\e. ~expr_has_effect e) xs /\
  EVERY (\e. nocalls ==> int_calls_expr e = []) xs /\
  (!i ee. i < LENGTH xs /\ extrequest_kwargs_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee) /\
  compile_ext_call_kwargs compile_expr cenv ret ks xs sa =
    ((value_op,gas_op,default_op),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_exprs cx xs) kont) expr_vv_res_ok es /\
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
  (!vs ee t.
    extrequest_kwargs_post ctx func cenv cx ret ks xs es sa s0 sb
      value_op gas_op default_op old_es old_rs old_vvs vs ee t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont vs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (bind (eval_exprs cx xs) kont)
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  Induct_on `ks` >> rpt gen_tac
  >- (Cases_on `xs` >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops cx) (ctx,func) (kont [])
        (es with gas_obs := [],s0) Q (\res ee r. expr_exit res r)` by
        (first_x_assum irule >> irule extrequest_kwargs_post_nil >> simp[]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `xs` >> simp[] >>
  simp[Once compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  rename1 `compile_ext_call_kwarg compile_expr cenv ret kw e sa = ((op,dty),sm)` >>
  rename1 `EVERY (\e. ~expr_has_effect e) xs` >>
  qpat_x_assum `comp_bind _ _ sm = _` mp_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def] >>
  rename1 `compile_ext_call_kwargs compile_expr cenv ret ks xs sm = ((vo,go,dopt),sb)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`compile_expr`, `cenv`, `ret`, `kw`, `e`, `sa`]
      ci_mono_compile_ext_call_kwarg) >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`ks`, `xs`, `cenv`, `ret`, `sm`] extrequest_kwargs_mono) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_x_assum `!i ee. _` (qspecl_then [`0`, `es with gas_obs := []`] mp_tac) >> simp[]) >>
  `expr_vv_case nocalls ctx func cenv cx e` by fs[exprs_case_def] >>
  rewrite_tac[extrequest_kwargs_bind_cons] >>
  irule extrequest_kwarg_retained_cps >>
  qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`nocalls`, `env`] >> simp[GSYM extrequest_kwargs_bind_cons] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  rename1 `extrequest_kwarg_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mid tm` >>
  `mid.gas_obs = [] /\ stmt_state_rel ctx func cenv cx mid tm /\
   ~tm.vs_halted /\ tm.vs_current_bb = sm.cs_current_bb /\
   tm.vs_inst_idx = LENGTH sm.cs_current_insts /\ local_ptrs_reserved cenv sm /\
   extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs mid sm tm` by
    fs[extrequest_kwarg_post_def] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `gas_admissible (bind (eval_exprs cx xs) (\vs. kont (v::vs))) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible _ _ es` mp_tac >>
     rewrite_tac[extrequest_kwargs_bind_cons] >> strip_tac >>
     drule_all gas_admissible_bind_tail >> simp[]) >>
  `!i ee. i < LENGTH xs /\ extrequest_kwargs_reach cx xs mid i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee` by
    (rpt strip_tac >>
     `extrequest_kwargs_reach cx (e::xs) es (SUC i) ee` by
       (irule extrequest_kwargs_reach_cons >> goal_assum (drule_at Any) >>
        simp[]) >>
     qpat_x_assum `!i ee. i < SUC _ /\ _ ==> _`
       (qspecl_then [`SUC i`, `ee`] mp_tac) >> simp[]) >>
  `exprs_case nocalls ctx func cenv cx xs` by
    (qpat_assum `exprs_case _ _ _ _ _ (e::xs)` mp_tac >>
     simp[NoAsms, exprs_case_def] >> strip_tac >> first_x_assum irule >>
     qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     goal_assum (drule_at Any) >> gvs[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `!xs' es' sa' sb' value_op' gas_op' default_op' s0' kont' old_es' old_rs' old_vvs'. _` irule >>
  qpat_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`old_vvs`, `old_rs`, `old_es`] >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vs ee t. _` irule >>
  `extrequest_kwargs_post ctx func cenv cx ret (kw::ks) (e::xs) es sa s0 sb
    (if kw = EKValue then SOME op else vo)
    (if kw = EKGas then SOME op else go)
    (if kw = EKDefault then SOME (op,dty) else dopt)
    old_es old_rs old_vvs (v::vs) ee t` by
    (irule (INST_TYPE [alpha |-> ``:typing_env``] extrequest_kwargs_post_cons) >> simp[] >>
     qexistsl_tac [`env`, `mid`, `sm`, `tm`, `used`] >> simp[]) >>
  Cases_on `kw` >> gvs[]
QED
