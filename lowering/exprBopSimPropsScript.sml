(* Shared pure operator simulation facts. *)
Theory exprBopSimProps
Ancestors
  exprBopSimDefs gasContext gasNormalPrefix gasSummary gasExemptCert gasSummaryCompose fragGasMode fragGasPath
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib


(* Source boundary for counted composition and concrete certificates. *)
Theorem eval_expr_bop_bind:
  (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
      read_result cx result od) =
  (do v1 <- (do result <- eval_expr cx e1; read_result cx result od);
      v2 <- (do result <- eval_expr cx e2; read_result cx result od);
      (\es2. (bop_result cx ann bop [expr_type e1; expr_type e2]
                v1 v2 es2, es2)) od)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bop = In \/ bop = NotIn` >>
  (simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def,
       COND_RATOR] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e1 x` >> rename1 `_ = (raw1, st1)` >>
  reverse (Cases_on `raw1`) >- simp[] >>
  rename1 `eval_expr cx e1 x = (INL r1, st1)` >>
  Cases_on `read_result cx r1 st1` >> rename1 `_ = (res1, es1)` >>
  reverse (Cases_on `res1`) >- simp[] >>
  rename1 `read_result cx r1 st1 = (INL v1, es1)` >>
  simp[] >> simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e2 es1` >> rename1 `_ = (raw2, st2)` >>
  reverse (Cases_on `raw2`) >- simp[] >>
  rename1 `eval_expr cx e2 es1 = (INL r2, st2)` >>
  Cases_on `read_result cx r2 st2` >> rename1 `_ = (res2, es2)` >>
  reverse (Cases_on `res2`) >- simp[] >>
  rename1 `read_result cx r2 st2 = (INL v2, es2)` >>
  simp[Once evaluate_def, bind_def, return_def, get_accounts_def,
       lift_sum_def, bop_result_def, ignore_bind_def, type_check_def,
       assert_def, raise_def, lift_option_type_def, COND_RATOR,
       precompile_call_success_def, precompile_builtin_def] >>
  BasicProvers.every_case_tac >>
  gvs[read_result_def, return_def, raise_def, bind_def])
QED

Theorem eval_expr_bop_cases:
  !cx ann bop e1 e2 es res es'.
    (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx result od) es = (res, es') ==>
    (?exc. (do result <- eval_expr cx e1; read_result cx result od) es =
             (INR exc, es') /\ res = INR exc) \/
    ?v1 es1.
      (do result <- eval_expr cx e1; read_result cx result od) es =
        (INL v1, es1) /\
      ((?exc. (do result <- eval_expr cx e2; read_result cx result od) es1 =
                (INR exc, es') /\ res = INR exc) \/
       ?v2. (do result <- eval_expr cx e2; read_result cx result od) es1 =
              (INL v2, es') /\
            res = bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es')
Proof
  rpt gen_tac >> rewrite_tac[eval_expr_bop_bind] >>
  strip_tac >> gvs[bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem eval_operand_frame:
  !x st t u w.
    (!z. x = Var z ==> not_fresh_at st z) /\ (!l. x <> Label l) /\
    eval_operand x t = SOME w /\
    (!z w'. not_fresh_at st z /\ lookup_var z t = SOME w' ==>
            lookup_var z u = SOME w') ==>
    eval_operand x u = SOME w
Proof
  Cases >> rw[eval_operand_def] >> metis_tac[]
QED

Theorem expr_val_rel_word:
  !cx t v op s.
    expr_val_rel cx t v op s /\ is_word_type t /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ word_value v ==>
    eval_operand op s = SOME (val_to_w256 v)
Proof
  rw[expr_val_rel_def, optionTheory.IS_SOME_EXISTS] >> first_x_assum drule >>
  simp[typed_val_to_w256_word_value]
QED

Theorem expr_val_rel_typed:
  !cx t tv v op s.
    expr_val_rel cx t v op s /\ is_word_type t /\
    evaluate_type (get_tenv cx) t = SOME tv ==>
    eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  rw[expr_val_rel_def] >> first_x_assum drule >> simp[]
QED

Theorem local_regions_memory_tail:
  !cenv sa scopes scopes' sm s t.
  local_ptrs_reserved cenv sa /\
  MAP FDOM scopes = MAP FDOM scopes' /\
  (!x. not_fresh_at sa x ==> lookup_var x sm = lookup_var x s) /\
  (!n b sz. local_region cenv scopes s n b sz ==>
    mem_bytes_at b sz sm.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!n b sz. local_region cenv scopes' sm n b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz sm.vs_memory) ==>
  (!n b sz. local_region cenv scopes s n b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  rpt strip_tac >>
  `local_region cenv scopes' sm n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem locals_kept_trans:
  !cenv es es1 sa s0 t u.
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    locals_kept cenv es s0 t /\ locals_kept cenv es1 t u ==>
    locals_kept cenv es s0 u
Proof
  rw[locals_kept_def] >>
  `local_region cenv es1.scopes t n b sz` by
    metis_tac[local_region_frame_fwd] >>
  metis_tac[]
QED

Theorem expr_post_bop:
  !func cenv cx ann bop e1 e2 es es1 es' sa s1 s2 sb s0 t u ss x y op v1 v2 v ctx.
    expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    stmt_state_rel ctx func cenv cx es' ss /\
    eval_operand op ss = SOME (val_to_w256 v) /\ word_value v /\
    (!z w. not_fresh_at s2 z /\ lookup_var z u = SOME w ==>
           lookup_var z ss = SOME w) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==>
             FLOOKUP ss.vs_allocas aid = SOME b) /\
    ss.vs_memory = u.vs_memory /\
    is_word_type ann /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id ==>
    expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1; e2]) es sa sb s0 es'
      v op ss
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  simp[expr_val_rel_def, expr_val_at_def, vyperASTTheory.expr_type_def,
       typed_val_to_w256_word_value] >>
  conj_tac
  >- ((* the variables handed out before sa *)
      rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      `not_fresh_at s2 z` by
        (irule not_fresh_at_mono >> qexists_tac `s1` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s2 z /\ lookup_var z u = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at s1 x /\ lookup_var x t = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  conj_tac
  >- ((* the memory of the allocations before sa: kept by e1, then by e2 *)
      rpt strip_tac >>
      qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      disch_then irule >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
          qexists_tac `n` >>
          irule local_region_frame >>
          conj_tac >- (qexists_tac `func` >>
            gvs[stmt_state_rel_def, state_rel_def]) >>
          qexistsl_tac [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[])
      >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
          qexists_tac `sa.cs_next_id` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  (* the locals' memory: kept by e1, then by e2 *)
  irule locals_kept_mem_tail >> qexists_tac `u` >> simp[] >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem bop_result_gas_obs[simp]:
  bop_result cx ann bop ts v1 v2 (es with gas_obs := gs) =
  bop_result cx ann bop ts v1 v2 es
Proof
  simp[bop_result_def]
QED

Theorem eval_expr_bop_ignore_bind:
  ignore_bind
    (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx result od) (return ()) =
  (do v1 <- (do result <- eval_expr cx e1; read_result cx result od);
      v2 <- (do result <- eval_expr cx e2; read_result cx result od);
      ignore_bind (\es2. (bop_result cx ann bop
        [expr_type e1; expr_type e2] v1 v2 es2, es2)) (return ()) od)
Proof
  pure_once_rewrite_tac[eval_expr_bop_bind] >>
  simp[ignore_bind_def, vyperStateTheory.bind_assoc]
QED

Theorem bop_first_admissible:
  gas_admissible
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) expr_res_ok es ==>
  gas_admissible
    (do r <- eval_expr cx e1; read_result cx r od) expr_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_bop_bind] >>
  simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> gvs[bind_def]
QED

Theorem bop_second_admissible:
  gas_admissible
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) expr_res_ok es /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e1; read_result cx r od)
    (es, s0) marks (INL v1) mid (OK t) ==>
  gas_admissible
    (do r <- eval_expr cx e2; read_result cx r od)
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_bop_bind] >>
  simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> gvs[bind_def]
QED

Theorem bop_result_admissible:
  gas_admissible
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) expr_res_ok es /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e1; read_result cx r od)
    (es, s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e2; read_result cx r od)
    (mid with gas_obs := [], t) right (INL v2) fin (OK u) ==>
  expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2]
    v1 v2 (fin with gas_obs := []))
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit left s0.vs_gas_readings ++
                  (gas_explicit right t.vs_gas_readings ++ [])` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_bop_bind] >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  gvs[bind_def]
QED

Theorem bop_prefix_continuation:
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e1; read_result cx r od)
    (es, s0) marks (INL v1) mid (OK t) /\
  (!gs v ee. (do r <- eval_expr cx e1; read_result cx r od)
      (es with gas_obs := gs) = (INL v, ee) ==> P v ee) ==>
  P v1 (mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem bop_value_scopes_dom:
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, ee) ==>
  MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[eval_expr_preserves_scopes_dom]
QED

Theorem bop_first_exempt_cert:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (do r <- eval_expr cx e1; read_result cx r od) (return ()))
    (es, s0) marks (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
                    read_result cx r od) (return ()))
    (es, s0) marks (err, ee) (leaf, sf)
Proof
  strip_tac >> rewrite_tac[eval_expr_bop_ignore_bind] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED

Theorem bop_second_exempt_cert:
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e1; read_result cx r od)
    (es, s0) left (INL v1) mid (OK t) /\
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (do r <- eval_expr cx e2; read_result cx r od) (return ()))
    (mid with gas_obs := [], t) right (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
                    read_result cx r od) (return ()))
    (es, s0) (left ++ right) (err, ee) (leaf, sf)
Proof
  strip_tac >> rewrite_tac[eval_expr_bop_ignore_bind] >>
  irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> simp[] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED

Theorem bop_marked_exec_normal:
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e1; read_result cx r od)
    (es, s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e2; read_result cx r od)
    (mid with gas_obs := [], t) right (INL v2) fin (OK u) /\
  gas_marked_path memory ctx func u 0 r ==>
  gas_marked_exec memory (ctx, func)
    (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx result od)
    (es, s0) (left ++ right)
    (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin) fin r
Proof
  strip_tac >> rewrite_tac[eval_expr_bop_bind] >>
  `gas_marked_exec memory (ctx, func)
     (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee, ee))
     (fin with gas_obs := [], u) []
     (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin) fin r` by
    simp[gas_marked_exec_def] >>
  `gas_marked_exec memory (ctx, func)
     (do v2 <- (do result <- eval_expr cx e2; read_result cx result od);
         (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee, ee)) od)
     (mid with gas_obs := [], t) (right ++ [])
     (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin) fin r` by
    (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem bop_marked_scopes_dom:
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx e; read_result cx r od)
    (es, s0) marks (INL v) mid (OK t) ==>
  MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  disch_then (mp_tac o MATCH_MP bop_value_scopes_dom) >> simp[]
QED

Theorem bop_normal_prefix_summary:
  gas_value_prefix F (ctx, func, cenv, cx) (expr_type e1, e1)
    (sa, s1, x) (es, s0) left (v1, mid, t) /\
  gas_value_prefix F (ctx, func, cenv, cx) (expr_type e1, e2)
    (s1, s2, y) (mid with gas_obs := [], t) right (v2, fin, u) /\
  gas_admissible
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) expr_res_ok es /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op, sb) /\
  fn_has_code s2 sb func /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  binop_frag_words ctx func cenv cx bop (expr_type e1) ann bl el
    [expr_type e1; expr_type e2] v1 v2
    (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2)
    (fin with gas_obs := []) ==>
  gas_summary_at F (ctx, func) (left ++ right)
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) (es, s0)
    (\res ee ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
        es sa sb s0 ee v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_value_prefix _ _ _ (sa, s1, x) _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_value_prefix_def]) >>
  qpat_x_assum `gas_value_prefix _ _ _ (s1, s2, y) _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_value_prefix_def]) >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2]
     v1 v2 (fin with gas_obs := []))` by
    metis_tac[bop_result_admissible] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv1 v1) /\
   eval_operand y u = SOME (typed_val_to_w256 tv2 v2)` by
    (conj_tac >> irule expr_val_rel_typed >>
     gvs[expr_post_def] >> metis_tac[]) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv1 v1)` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`s1`, `t`] >>
     gvs[expr_post_def]) >>
  `(!z. x = Var z ==> not_fresh_at s2 z) /\
   local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (fin with gas_obs := []) u` by
    gvs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_words _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `sb`, `x`, `y`, `op`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `gas_marked_exec F (ctx, func)
     (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
         read_result cx result od)
     (es, s0) (left ++ right)
     (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin) fin r` by
    metis_tac[bop_marked_exec_normal] >>
  simp[gas_summary_at_def] >>
  goal_assum (drule_at Any) >> simp[]
  >- (disj1_tac >> simp[] >>
      `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
        metis_tac[bop_marked_scopes_dom] >>
      qexists_tac `v` >> gvs[] >>
      irule expr_post_bop >>
      qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[]) >>
  metis_tac[bop_result_gas_obs]
QED
