(* Marked operand execution is the boundary needed to recover source typing. *)
Theory bodyPtrHashBuiltinsSuffix
Ancestors
  bodyPtrDefs gasSummaryComposePtr fragGasSeqPtr gasExemptCert
  exprSimHash exprSimDefs fragGasPathPtr vyperState list

Theorem hash_marked_ptr_normal:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0)
    marks res ee G tn (OK t) ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (res, ee with gas_obs := []) /\ ~t.vs_halted
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_ok_not_halted]
QED

(* General value-result bind boundary: normal callbacks see the actual
   source run, whereas exceptional/exempt operands need no continuation. *)
Theorem hash_value_outcome_ptr_suffix:
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0)
    (\res ee G tn t. ?v:value. res = INL v /\ P v ee G tn t)
    (\res ee gt r. expr_exit res r) /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee gt r) /\
  (!gs v ee G tn t.
     source (es with gas_obs := gs) = (INL v, ee) /\
     ee.gas_obs = [] /\ P v ee G tn t /\ ~t.vs_halted ==>
     ?right. gas_summary_ptr_at D (ctx, func) PG right (k v)
       (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr D tops (ctx, func) PG (bind source k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >>
      gvs[]
      >- (drule hash_marked_ptr_normal >> strip_tac >>
          qpat_x_assum `!gs v ee G tn t. _` drule >>
          simp[] >> disch_then drule_all >> strip_tac >>
          rewrite_tac[gas_outcome_ptr_def] >>
          qexists_tac `marks ++ right` >> disj1_tac >>
          irule gas_summary_ptr_at_bind_normal >> metis_tac[]) >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
      metis_tac[gas_marked_exec_ptr_bind_exception]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  simp[ignore_bind_def, bind_assoc] >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem hash_expr_sim_ptr_suffix:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee gt r) /\
  (!gs v ee G tn t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     expr_post ctx func cenv cx e es sa sm s0 ee v op t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\
     ghost_inv d cenv cx ee G tn t /\
     ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
     ghost_kept cenv es sa G0 tn0 s0 G tn ==>
     ?right. gas_summary_ptr_at (cx_dead cx) (ctx, func) PG right (k v)
       (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule hash_value_outcome_ptr_suffix >>
  conj_tac >- metis_tac[] >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  simp[] >> metis_tac[]
QED
