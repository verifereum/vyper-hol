Theory entryCreateBopWordSuffixScope
Ancestors
  entryCreateAdminSequence entryCreateAdminAbortScope entryCreateFocusSpec
  bodyFullBopWordExtract bodyFullHashKeccakFixed exprSimFullBundleProps
  loweringPosts exprSimDefs exprSimWordArgs valueEncoding vyperStorageFootprint
  gasSummary fragGasOriginPtr fragExec s1PrefixDefs exprSimProps list
  entryCreateCompletedCut

(* The row supplier is conditional on the facts extracted from these two
   completed operands. Its raw run and indexed result belong to one row. *)
Theorem create_bop_word_suffix_scoped:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
    (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
    (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= sb.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
  cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
  cs_extends shadow_s2 shadow_sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_has_code shadow_s2 shadow_sb shadow_func /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    (INL v1, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
    expr_store_bound cx (expr_type e1) v1 x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
    (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted /\ mid.gas_obs = []) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL v2, fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
    expr_store_bound cx (expr_type e2) v2 y u /\
    u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
    (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 u) /\
    ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = []) /\
  sb.cs_current_bb = s2.cs_current_bb /\
  sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
  EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts s2 sb) /\
  (well_typed_binop ann bop (expr_type e1) (expr_type e2) /\ is_word_type ann /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
   (?B. bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
      (emitted_insts s2 sb) B /\ op IN B) /\
   ((?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
           run_inst_seq (emitted_insts s2 sb) u = OK r /\ expr_val_rel cx ann v op r) \/
    (?m r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin =
             INR (Error (RuntimeError m)) /\
           run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort r)) ==>
   ?res r G' tn'.
     ((?v raw. res = INL v /\ run_inst_seq (emitted_insts s2 sb) u = OK raw /\
         r = OK (raw with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb))) \/
      (?msg raw j. res = INR (Error (RuntimeError msg)) /\
         run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort raw /\
         r = Abort Revert_abort (raw with vs_inst_idx := j))) /\
     (!tail. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2
               (fin with gas_obs := tail) = res) /\
     storage_trace_domain cx st0 fin.storage_trace /\
     !H. valid_horizon cx st0 H fin.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (u,G2,tn2) [] (r,G',tn') /\
       ((?v q. r = OK q /\ res = INL v /\
          expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0
            (fin with gas_obs := []) v op q /\
          expr_store_bound cx (expr_type (Builtin ann (Bop bop) [e1;e2])) v op q /\
          q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx (fin with gas_obs := []) G' tn' q /\
          ptr_val_ok cx (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) v op G' tn' q /\
          (~is_word_type (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) ==>
            ptr_buf_ok cenv (Builtin ann (Bop bop) [e1;e2]) op G' q) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
        (exit_result r /\ expr_exit res r /\ halt_exit H cx (fin with gas_obs := []) res r))) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 s2 sb
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee)) (fin,u,G2,tn2)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin ann (Bop bop) [e1;e2])
      (es,sa,sb,s0,op,G0,tn0)) (create_operand_exit_post ctx cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_def]) >>
  mp_tac (SRULE [LET_THM] bop_word_suffix_extract) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN
    `((?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
        run_inst_seq (emitted_insts s2 sb) u = OK r /\ expr_val_rel cx ann v op r) \/
      (?m r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin =
        INR (Error (RuntimeError m)) /\ run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort r))`
    assume_tac
  >- (qpat_x_assum `(?v r. _) \/ _` strip_assume_tac
      >- (disj1_tac >> qexistsl_tac [`v`,`r`] >>
          simp[expr_val_rel_def, typed_val_to_w256_word_value]) >>
      disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `(well_typed_binop _ _ _ _ /\ _) ==> _` mp_tac >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`res`,`r`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  `create_operand_at s2 u /\ ~u.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[create_operand_at_def]) >>
  `EVERY (\i. i.inst_id IN frag_ids s2 sb /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts s2 sb)` by
    fs[EVERY_MEM] >>
  `LENGTH sb.cs_current_insts = u.vs_inst_idx + LENGTH (emitted_insts s2 sb)` by
    fs[create_operand_at_def] >>
  `create_operand_full_scope s2 sb (gas_explicit_sites ctx shadow_ctx) ctx func u [] r` by
    (qpat_assum `(?v raw. res = INL v /\ _) \/ _` strip_assume_tac >>
     gvs[]
     >- (drule_all create_admin_sequence_scope >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o CONJUNCT1)) >>
     drule_then (strip_assume_tac o CONJUNCT1) gas_origin_ptr_path_projections >>
     drule_all create_admin_sequence_abort_scope >> simp[]) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`fin`,`r`,`Gf`,`tnf`] >> simp[gas_explicit_def] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[] >>
  qpat_x_assum `(?v q. r = OK q /\ _) \/ (exit_result r /\ _)` strip_assume_tac
  >- (disj1_tac >> simp[expr_sim_full_post_def, expr_sim_full_endpoint_def,
                        vyperASTTheory.expr_type_def] >>
      drule_then (assume_tac o CONJUNCT1) (iffLR expr_post_def) >>
      drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
      fs[vyperASTTheory.expr_type_def]) >>
  disj2_tac >> qpat_x_assum `(?v raw. res = INL v /\ _) \/ _` strip_assume_tac >>
  gvs[exit_result_def, create_operand_exit_post_def]
QED
