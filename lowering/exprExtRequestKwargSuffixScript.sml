(* Shared composition for the two keyword read suffixes. *)
Theory exprExtRequestKwargSuffix
Ancestors
  exprExtRequestHistory exprExtRequestHistoryCompose exprExtRequestReadProbe
  exprSimProps exprSimDefs loweringPosts compileEnv loweringStateRelDefs freshWrites
  exprLoweringProps valueEncodingProofs
  gasSummary gasSummaryCompose gasOutcome gasExemptCert exprExtRequestGasBind
  exprExtRequestStrongCapture exprLowering vyperInterpreter vyperState
Libs
  monadsyntax

Definition extrequest_kwarg_post_def:
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
      old_es old_rs old_vvs v ee t <=>
    (?obs. (bind (eval_expr cx e) (read_result cx))
       (es with gas_obs := obs) = (INL v,ee)) /\ ee.gas_obs = [] /\
    dty = (if kw = EKDefault /\ ~is_word_type ret
           then lowered_value_type cenv e else ret) /\
    stmt_state_rel ctx func cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\ wb_frame cenv es ee sa s0 t /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sb t /\
    safe_operand sb op /\
    expr_val_rel cx (if kw = EKDefault then dty else BaseT (UintT 256)) v op t /\
    (?tv. evaluate_type (get_tenv cx)
             (if kw = EKDefault then dty else BaseT (UintT 256)) = SOME tv /\
       value_has_type tv v /\ val_wf tv v /\
       (!w. ~is_word_type (if kw = EKDefault then dty else BaseT (UintT 256)) /\
            eval_operand op t = SOME w ==>
            w2n w + val_footprint tv v <= t.vs_alloca_next)) /\
    (kw = EKDefault ==>
       (dty = ret \/ is_bytestring_type dty /\ is_bytestring_type ret) /\
       ?rtv. evaluate_type (get_tenv cx) ret = SOME rtv /\
          value_has_type rtv v /\ val_wf rtv v)
End

Theorem extrequest_kwarg_history_writeback:
  vv_post ctx func cenv cx e es sa sm s0 ee r vv t /\
  stmt_state_rel ctx func cenv cx es s0 /\
  extrequest_read_frame cx es ee /\ ci_mono sa sm /\
  local_ptrs_reserved cenv sa /\
  extrequest_history_frame cenv cx ee sm t ee sb z ==>
  wb_frame cenv es ee sa s0 z
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ es s0` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[extrequest_read_frame_def] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, vv_post_def, extrequest_history_frame_def] >>
  strip_tac >> strip_tac >> rewrite_tac[wb_frame_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists `sa` >> fs[ci_mono_def]) >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `aid < sm.cs_next_id` by fs[ci_mono_def] >>
      `!n b sz'. local_region cenv ee.scopes t n b sz' ==>
                  off + sz <= b \/ b + sz' <= off` by
        (rpt strip_tac >>
         `local_region cenv es.scopes s0 n b sz'` by
           (irule local_region_frame >>
            conj_tac >- (qexists `func` >> simp[]) >>
            qexistsl_tac [`sa`, `ee.scopes`, `t`] >> simp[]) >> metis_tac[]) >>
      fs[regions_disjoint_def] >> metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists `t` >> simp[] >>
  rpt strip_tac >>
  `local_region cenv ee.scopes t n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem extrequest_kwarg_suffix_post:
  (!tail. eval_expr cx e (es with gas_obs := used ++ tail) =
     (INL r, ee with gas_obs := tail)) /\ ee.gas_obs = [] /\
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,t) [] (INL v) ee (OK z) /\
  vv_post ctx func cenv cx e es sa sm s0 ee r vv t /\
  stmt_state_rel ctx func cenv cx es s0 /\
  extrequest_read_frame cx es ee /\ ci_mono sa sm /\ ci_mono sm sb /\
  local_ptrs_reserved cenv sa /\
  extrequest_history_frame cenv cx ee sm t ee sb z /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sm t /\
  dty = (if kw = EKDefault /\ ~is_word_type ret
         then lowered_value_type cenv e else ret) /\
  stmt_state_rel ctx func cenv cx ee z /\ ~z.vs_halted /\
  z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  safe_operand sb op /\
  expr_val_rel cx (if kw = EKDefault then dty else BaseT (UintT 256)) v op z /\
  (?tv. evaluate_type (get_tenv cx)
           (if kw = EKDefault then dty else BaseT (UintT 256)) = SOME tv /\
     value_has_type tv v /\ val_wf tv v /\
     (!w. ~is_word_type (if kw = EKDefault then dty else BaseT (UintT 256)) /\
          eval_operand op z = SOME w ==>
          w2n w + val_footprint tv v <= z.vs_alloca_next)) /\
  (kw = EKDefault ==>
     (dty = ret \/ is_bytestring_type dty /\ is_bytestring_type ret) /\
     ?rtv. evaluate_type (get_tenv cx) ret = SOME rtv /\
        value_has_type rtv v /\ val_wf rtv v) ==>
  extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
    old_es old_rs old_vvs v ee z
Proof
  strip_tac >>
  `wb_frame cenv es ee sa s0 z` by
    (drule_all extrequest_kwarg_history_writeback >> simp[]) >>
  `extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sb z` by
    (drule_all extrequest_strong_captures_history >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx r ee = (INL v,ee)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  rewrite_tac[extrequest_kwarg_post_def] >>
  conj_tac
  >- (qexists `used` >>
      qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
      fs[bind_def]) >>
  fs[ci_mono_def, extrequest_history_frame_def, extrequest_read_frame_def]
QED

(* Both operational branches feed the same read/continuation composition. *)
Theorem extrequest_kwarg_suffix_cps:
  gas_marked_exec F (ctx,func) (read_result cx r) (ee,t) [] (INL v) ee (OK z) /\
  ee.gas_obs = [] /\
  gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,z) Q
    (\res ef result. expr_exit res result) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (bind (read_result cx r) kont) (ee,t) Q
    (\res ef result. expr_exit res result)
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (`gas_marked_exec F (ctx,func) (bind (read_result cx r) kont)
         (ee,t) marks res es_end (OK t')` by
        metis_tac[gas_marked_exec_bind_normal, listTheory.APPEND] >>
      qexists `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `OK t'`] >> simp[])
  >- (`gas_marked_exec F (ctx,func) (bind (read_result cx r) kont)
         (ee,t) marks res es_end r'` by
        metis_tac[gas_marked_exec_bind_normal, listTheory.APPEND] >>
      qexists `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r'`] >> simp[]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee'`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
  simp[ignore_bind_def] >> strip_tac >>
  drule gas_exempt_cert_bind_value >> simp[]
QED

val _ = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail "Unclosed keyword suffix helper"
  end)
  [extrequest_kwarg_history_writeback, extrequest_kwarg_suffix_post,
   extrequest_kwarg_suffix_cps];

(* A zero-mark read consumes no additional gas observations. *)
Theorem extrequest_kwarg_counted_read:
  (!tail. eval_expr cx e (es with gas_obs := used ++ tail) =
    (INL r, ee with gas_obs := tail)) /\
  gas_marked_exec F (ctx,func) (read_result cx r) (ee with gas_obs := [],t) []
    (INL v) (ee with gas_obs := []) (OK z) ==>
  !tail. (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := used ++ tail) = (INL v, ee with gas_obs := tail)
Proof
  simp[gas_marked_exec_def] >> rpt strip_tac >> simp[bind_def]
QED
