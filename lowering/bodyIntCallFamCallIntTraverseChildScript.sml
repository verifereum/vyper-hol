(* Counted child runs retain their path while extending the deferred prefix. *)
Theory bodyIntCallFamCallIntTraverseChild
Ancestors
  bodyIntCallFamCallIntTraversePost bodyIntCallFamCallIntTraverseInterfaces
  bodyIntCallFamCallIntCertificateIntro bodyIntCallJointContract
  bodyIntCallJointCallCore gasOutcome gasSummary exprSimMemDefs exprSimProps

val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

Theorem intcall_expr_cont_initial_gas:
  intcall_expr_cont fp ce env (es with gas_obs := gs) a s ee b u <=>
  intcall_expr_cont fp ce env es a s ee b u
Proof
  simp[intcall_expr_cont_def, loweringPostsTheory.locals_kept_def]
QED

Theorem intcall_expr_cont_final_gas:
  intcall_expr_cont fp ce env es a s (ee with gas_obs := gs) b u <=>
  intcall_expr_cont fp ce env es a s ee b u
Proof
  simp[intcall_expr_cont_def, intcall_expr_res_def, compileEnvTheory.local_region_def,
       loweringPostsTheory.locals_kept_def]
QED

Theorem intcall_marked_prefix_step:
  ^deferred_list fp ce ds vs rs b ee t /\
  ^deferred fp ce child vv child_r d (mid with gas_obs := []) u /\
  intcall_expr_res fp ce env es a s /\
  intcall_expr_cont fp ce env es a s ee b t /\
  intcall_expr_cont fp ce env ee b t (mid with gas_obs := []) d u /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  b.cs_next_id <= d.cs_next_id /\ b.cs_next_var <= d.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  supported_pure_expr fp.jc_tops child /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child ee b d t
    (mid with gas_obs := []) child_r vv u /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx child)
    (ee,t) marks (INL child_r) mid (OK u) ==>
  ^deferred_list fp ce (ds ++ [child]) (vs ++ [vv]) (rs ++ [child_r])
    d (mid with gas_obs := []) u /\
  intcall_expr_cont fp ce env es a s (mid with gas_obs := []) d u /\
  MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  qmatch_asmsub_abbrev_tac `ee with gas_obs := gs` >>
  `^deferred_list fp ce ds vs rs b (ee with gas_obs := gs) t` by
    (BETA_TAC >> pure_rewrite_tac[BETA_RULE intcall_deferred_list_gas_obs] >>
     first_assum ACCEPT_TAC) >>
  `intcall_expr_cont fp ce env es a s (ee with gas_obs := gs) b t` by
    simp[intcall_expr_cont_final_gas] >>
  `intcall_expr_cont fp ce env (ee with gas_obs := gs) b t
     (mid with gas_obs := []) d u` by
    simp[intcall_expr_cont_initial_gas] >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child
     (ee with gas_obs := gs) b d t (mid with gas_obs := []) child_r vv u` by
    simp[vv_post_initial_gas] >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := gs).scopes` by simp[] >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `LENGTH _ = _ /\ _` strip_assume_tac >>
  drule_all (BETA_RULE intcall_deferred_prefix_step) >>
  disch_then ACCEPT_TAC
QED

Theorem intcall_counted_prefix_child:
  ^deferred_list fp ce ds vs rs b ee t /\
  intcall_expr_res fp ce env es a s /\
  intcall_expr_cont fp ce env es a s ee b t /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  b.cs_next_id <= d.cs_next_id /\ b.cs_next_var <= d.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  supported_pure_expr fp.jc_tops child /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx child) (ee,t)
    (\res ef u. ?r. res = INL r /\
      ^deferred fp ce child vv r d ef u /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child ee b d t ef r vv u /\
      intcall_expr_cont fp ce env ee b t ef d u)
    (\res ef r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx child) (ee,t)
    (\res ef u. ?r. res = INL r /\
      ^deferred_list fp ce (ds ++ [child]) (vs ++ [vv]) (rs ++ [r]) d ef u /\
      intcall_expr_cont fp ce env es a s ef d u /\
      MAP FDOM es.scopes = MAP FDOM ef.scopes)
    (\res ef r. expr_exit res r)
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `result` strip_assume_tac)))
      >- (qpat_x_assum `(\res ef u. _) _ _ _`
            (qx_choose_then `child_r` (CONJUNCTS_THEN2 assume_tac
              (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) o BETA_RULE) >>
          rpt BasicProvers.VAR_EQ_TAC >>
          rename1 `gas_marked_exec _ _ _ _ marks (INL child_r) mid (OK out)` >>
          qexists `marks` >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl [`INL child_r`, `mid`, `OK out`] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          disj1_tac >> qexists `out` >> conj_tac >- simp[] >>
          BETA_TAC >> qexists `child_r` >>
          conj_tac >- simp[] >>
          drule_all (BETA_RULE intcall_marked_prefix_step) >>
          disch_then ACCEPT_TAC) >>
      qexists `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`res`, `mid`, `result`] >> simp[]) >>
  strip_tac >> qexists `marks` >> disj2_tac >>
  goal_assum (drule_at Any)
QED
