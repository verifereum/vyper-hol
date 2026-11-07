(* Counted simulation of dynamic bytestring equality and inequality. *)

Theory exprSimBopBytestring
Ancestors
  exprBopDigestProps
  exprSimHashBoundary bytestringHashProps gasSummary fragGasMode fragGasPath
  gasOutcome gasSummaryCompose gasExemptCert
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomInst venomState
  valueEncoding ASCIInumbers words vyperTypeBytesCrypto venomMemProps
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprBopSimProps exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

Theorem comparison_hash_counted[local]:
  compile_bytestring_hash ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all (SIMP_RULE std_ss [byteTheory.word_of_bytes_be_def] compile_bytestring_hash_run_nofresh) >> strip_tac >>
  drule (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >> strip_tac >>
  drule_all hash_run_path >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, stmt_state_rel_inst_idx] >>
  qpat_x_assum `_ with vs_vars := _ = _`
    (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]
QED

Theorem comparison_hash_dynamic[local]:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) ptr_op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  compile_bytestring_hash ptr_op sm = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  irule comparison_hash_counted >> goal_assum drule >>
  gvs[loweringPostsTheory.expr_post_def] >> metis_tac[]
QED

Theorem comparison_hash_string[local]:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) ptr_op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  compile_bytestring_hash ptr_op sm = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (MAP (n2w o ORD) str))) /\
    stmt_state_rel ctx func cenv cx es' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all hash_string_post_view >> strip_tac >>
  irule comparison_hash_counted >> goal_assum drule >>
  gvs[loweringPostsTheory.expr_post_def] >> metis_tac[]
QED

Theorem comparison_hash_typed[local]:
  expr_post ctx func cenv cx e es sa sm s0 ee v p t /\
  (?cap. expr_type e = BaseT (BytesT (Dynamic cap)) \/
         expr_type e = BaseT (StringT cap)) /\
  (?tv. evaluate_type tenv (expr_type e) = SOME tv /\ value_has_type tv v) /\
  compile_bytestring_hash p sm = (h, sh) /\
  (!x. p = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sh func /\ local_ptrs_reserved cenv sm /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?d u.
    ((?bs. v = BytesV bs /\
       d = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
     (?str. v = StringV str /\
       d = word_of_bytes T (0w:bytes32) (Keccak_256_w64 (MAP (n2w o ORD) str)))) /\
    gas_marked_path F ctx func t 0 (OK u) /\ eval_operand h u = SOME d /\
    stmt_state_rel ctx func cenv cx ee u /\ ~u.vs_halted /\
    u.vs_current_bb = sh.cs_current_bb /\
    u.vs_inst_idx = LENGTH sh.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
    u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap))) \/
   evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (StringT cap))` by
    simp[vyperValueTheory.evaluate_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def]
  >- (irule comparison_hash_dynamic >>
      qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[vyperValueTheory.evaluate_type_def]) >>
  irule comparison_hash_string >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[vyperValueTheory.evaluate_type_def]
QED

Theorem comparison_hash_literal[local]:
  bytestring_literal_hash e = SOME h ==>
  ?v. (!es. bind (eval_expr cx e) (read_result cx) es = (INL v, es)) /\
    ((?bs. v = BytesV bs /\
       h = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
     (?str. v = StringV str /\
       h = word_of_bytes T (0w:bytes32)
         (Keccak_256_w64 (MAP (n2w o ORD) str))))
Proof
  Cases_on `e` >> simp[bytestring_literal_hash_def] >>
  rename1 `Literal ann lit` >> Cases_on `lit` >>
  simp[bytestring_literal_hash_bytes, bytestring_literal_hash_string,
       bytestring_literal_hash_def] >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem comparison_digest_counted[local]:
  (bop = Eq \/ bop = NotEq) /\
  (if bop = Eq then emit_op EQ [h1; h2] sa = (op, sb)
   else ?q sq. emit_op EQ [h1; h2] sa = (q, sq) /\
               emit_op ISZERO [q] sq = (op, sb)) /\
  eval_operand h1 s = SOME d1 /\ eval_operand h2 s = SOME d2 /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME
      (val_to_w256 (BoolV (if bop = Eq then d1 = d2 else d1 <> d2))) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(if bop = Eq then emit_op EQ [h1; h2] sa
    else let (q, sm) = emit_op EQ [h1; h2] sa in emit_op ISZERO [q] sm) =
      (op, sb)` by (Cases_on `bop = Eq` >> gvs[]) >>
  drule_all comparison_digest_run >> strip_tac >>
  drule_all (SIMP_RULE std_ss [ci_mono_def] comparison_digest_shape) >> strip_tac >>
  drule_all hash_run_path >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, stmt_state_rel_inst_idx,
      val_to_w256_def, bool_to_word_def] >>
  qpat_x_assum `_ with vs_vars := _ = _`
    (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >>
  Cases_on `d1 = d2` >> simp[bool_to_word_def]
QED

Theorem comparison_finish_post[local]:
  (bop = Eq \/ bop = NotEq) /\
  (if bop = Eq then emit_op EQ [h1; h2] sh = (op, sb)
   else ?q sq. emit_op EQ [h1; h2] sh = (q, sq) /\
               emit_op ISZERO [q] sq = (op, sb)) /\
  eval_operand h1 u = SOME d1 /\ eval_operand h2 u = SOME d2 /\
  fn_has_code sh sb func /\
  stmt_state_rel ctx func cenv cx ee u /\ local_ptrs_reserved cenv sh /\
  ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
  u.vs_inst_idx = LENGTH sh.cs_current_insts /\
  wb_frame cenv es sa s0 u /\ sa.cs_next_var <= sh.cs_next_var ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    expr_post ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
      es sa sb s0 ee (BoolV (if bop = Eq then d1 = d2 else d1 <> d2)) op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all comparison_digest_counted >> strip_tac >>
  rename1 `eval_operand op z = SOME _` >>
  `wb_frame cenv es sa s0 z` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`sh`, `u`] >> simp[]) >>
  qexists_tac `z` >> simp[] >>
  simp[loweringPostsTheory.expr_post_def, expr_type_def] >>
  qpat_x_assum `wb_frame cenv es sa s0 z` mp_tac >>
  simp[loweringPostsTheory.wb_frame_def,
       loweringPostsTheory.expr_val_at_def,
       loweringPostsTheory.expr_val_rel_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.typed_val_to_w256_def] >>
  rpt strip_tac >> simp[]
QED

Theorem comparison_terminal_summary[local]:
  (!ss. bop_result cx (BaseT BoolT) bop [ty;ty] v1 v2 ss = INL bv) /\
  ee.gas_obs = [] /\
  gas_marked_path F ctx func t 0 (OK z) /\
  expr_post ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee bv op z /\
  z.vs_current_bb = sh.cs_current_bb /\
  z.vs_inst_idx = LENGTH sh.cs_current_insts + LENGTH (emitted_insts sh sb) ==>
  ?marks. gas_summary_at F (ctx,func) marks
    (\ss. (bop_result cx (BaseT BoolT) bop [ty;ty] v1 v2 ss,ss)) (ee,t)
    (\res ee z. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
        es sa sb s0 ee v op z /\
      z.vs_current_bb = sh.cs_current_bb /\
      z.vs_inst_idx = LENGTH sh.cs_current_insts + LENGTH (emitted_insts sh sb))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists_tac `[]` >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def] >>
  qexistsl_tac [`INL bv`, `ee`, `OK z`] >> simp[]
QED

Theorem comparison_operand_outcome_suffix[local]:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gs v ee t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     expr_post ctx func cenv cx e es sa sm s0 ee v op t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     ?u. gas_marked_path F ctx func t 0 (OK u) /\
       gas_outcome F (cx_tops cx) (ctx,func) (k v) (ee,u) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`op`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume comparison_operand_outcome_suffix[normal]:
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!gs v ee t. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                  `es_end with gas_obs := []`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) es_end (OK u)` by
    (gvs[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rename1 `gas_summary_at F _ right _ _ _ _` >>
      qexists_tac `marks ++ right` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`res`,`es_end'`,`r`] >> simp[] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`,`u`,`v`] >> gvs[]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ right _ _` >>
  qexists_tac `marks ++ right` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  gvs[ignore_bind_def]
QED

Resume comparison_operand_outcome_suffix[exit]:
  Cases_on `res` >> gvs[] >>
  rename1 `expr_exit (INR exc) r` >>
  qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

Resume comparison_operand_outcome_suffix[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED
Finalise comparison_operand_outcome_suffix

Theorem compile_bop_bytestring_eqne_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) ==>
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  strip_tac >>
  pure_rewrite_tac[expr_sim_case_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    metis_tac[well_typed_binop_def] >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     (conj_tac >- gvs[expr_body_pre_def]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!es'. expr_sim_inv cenv cx env es' ==>
     expr_body_pre cenv cx env e2 es'` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     (conj_tac >- simp[]) >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ e1`
       (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
     disch_then irule >>
     (conj_tac >- gvs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  `bop <> In /\ bop <> NotIn` by
    (qpat_x_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >> simp[]) >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all comparison_compile_cut >> strip_tac >>
  `(if bop = Eq then emit_op EQ [h1; h2] sh2
    else let (q, sm) = emit_op EQ [h1; h2] sh2 in emit_op ISZERO [q] sm) =
      (op, sb)` by (Cases_on `bop = Eq` >> gvs[]) >>
  drule_all (SIMP_RULE std_ss [ci_mono_def] comparison_digest_shape) >> strip_tac >>
  `cs_extends sa sh1 /\ cs_extends sh1 sh2` by
    (conj_tac
     >- (qpat_x_assum `case bytestring_literal_hash e1 of NONE => ?p sm. lower_value _ _ _ e1 sa = _ /\ _ | SOME h => _` mp_tac >>
         Cases_on `bytestring_literal_hash e1` >> simp_tac (srw_ss()) [] >>
         strip_tac >> imp_res_tac (cj 2 compile_expr_grows) >>
         imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
         metis_tac[cs_extends_trans, cs_extends_refl]) >>
     qpat_x_assum `case bytestring_literal_hash e2 of NONE => ?p sm. lower_value _ _ _ e2 sh1 = _ /\ _ | SOME h => _` mp_tac >>
     Cases_on `bytestring_literal_hash e2` >> simp_tac (srw_ss()) [] >>
     strip_tac >> imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  `fn_has_code sa sh1 func /\ fn_has_code sh1 sh2 func /\
   fn_has_code sh2 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `sa.cs_next_var <= sh1.cs_next_var /\ sh1.cs_next_var <= sh2.cs_next_var` by
    (conj_tac >>
     Cases_on `bytestring_literal_hash e1` >>
     Cases_on `bytestring_literal_hash e2` >> gvs[] >>
     imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >> decide_tac) >>
  `local_ptrs_reserved cenv sh1 /\ local_ptrs_reserved cenv sh2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] exprBopSimPropsTheory.eval_expr_bop_bind] >>
  Cases_on `bytestring_literal_hash e1`
  >- (gnvs[] >>
      qpat_x_assum `?p sm. lower_value _ _ _ e1 sa = _ /\ _` strip_assume_tac >>
      `fn_has_code sa sm func /\ fn_has_code sm sh1 func` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
         metis_tac[fn_has_code_mid, cs_extends_refl]) >>
      irule comparison_operand_outcome_suffix >>
      qpat_assum `expr_sim _ _ _ _ _ e1 _` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ e1 _ = _` (irule_at Any) >>
      simp[] >>
      (conj_tac >- metis_tac[exprBopSimPropsTheory.bop_first_admissible]) >>
      rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by
        simp[expr_body_pre_gas_obs] >>
      drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
      `expr_sim_case nocalls ctx func cenv cx e2 /\
       expr_vv_case nocalls ctx func cenv cx e2` by
        (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
         qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
         metis_tac[]) >>
      `expr_sim ctx func cenv cx (expr_type e1) e2 ee` by
        (qpat_x_assum `expr_sim_case _ _ _ _ _ e2`
           (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
         disch_then irule >>
         (conj_tac >- gvs[int_calls_expr_def]) >>
         qexists_tac `env` >> simp[]) >>
      `?tv. evaluate_type env.type_defs (expr_type e1) = SOME tv /\
            value_has_type tv v` by
        (qpat_x_assum `!v'. INL v = _ ==> _` (qspec_then `v` mp_tac) >>
         simp[expr_result_typed_def, expr_runtime_typed_def,
              value_result_typed_def]) >>
      `!x. p = Var x ==> not_fresh_at sm x` by
        (qpat_assum `lower_value _ _ _ e1 _ = _`
           (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >>
         simp[]) >>
      `local_ptrs_reserved cenv sm` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         metis_tac[local_ptrs_reserved_next_var]) >>
      Q.SUBGOAL_THEN
        `?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
               expr_type e1 = BaseT (StringT cap)` assume_tac
      >- (Cases_on `expr_type e1` >> gvs[is_bytestring_type_def] >>
          rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
          gvs[is_bytestring_type_def] >> Cases_on `b` >>
          gvs[is_bytestring_type_def]) >>
      drule comparison_hash_typed >>
      disch_then (qspecl_then [`env.type_defs`, `sh1`, `h1`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >>
      disch_then (qx_choose_then `d1` (qx_choose_then `t'`
        (map_every assume_tac o CONJUNCTS))) >>
      `wb_frame cenv es sa s0 t'` by
        (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
         qexistsl_tac [`sm`, `t`] >>
         imp_res_tac (cj 2 compile_expr_grows) >>
         simp[] >> metis_tac[exprSimWordArgsTheory.expr_post_frame]) >>
      `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
        (qpat_assum `monad_bind _ _ (es with gas_obs := gs) = _`
           (mp_then Any mp_tac (REWRITE_RULE [ETA_AX]
              exprBopSimPropsTheory.bop_value_scopes_dom)) >> simp[]) >>
      qexists_tac `t'` >> simp[] >>
      Cases_on `bytestring_literal_hash e2`
      >- (gnvs[] >>
          qpat_x_assum `?p sm. lower_value _ _ _ e2 sh1 = _ /\ _` strip_assume_tac >>
          `fn_has_code sh1 sm' func /\ fn_has_code sm' sh2 func` by
            (imp_res_tac (cj 2 compile_expr_grows) >>
             imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
             metis_tac[fn_has_code_mid, cs_extends_refl]) >>
          irule expr_sim_suffix >>
          qpat_assum `expr_sim _ _ _ _ _ e2 _` (irule_at Any) >>
          qpat_assum `lower_value _ _ _ e2 _ = _` (irule_at Any) >>
          simp[] >>
          (conj_tac >- (irule expr_body_pre_gas_admissible >>
             qexistsl_tac [`cenv`, `env`] >> simp[])) >>
          map_every qx_gen_tac [`gs2`, `v2`, `ee2`, `t2`] >> strip_tac >>
          `expr_body_pre cenv cx env e2 (ee with gas_obs := gs2)` by
            simp[expr_body_pre_gas_obs] >>
          drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
          `?tv. evaluate_type env.type_defs (expr_type e2) = SOME tv /\
                value_has_type tv v2` by
            (qpat_x_assum `!v'. INL v2 = _ ==> _` (qspec_then `v2` mp_tac) >>
             simp[expr_result_typed_def, expr_runtime_typed_def,
                  value_result_typed_def]) >>
          `!x. p' = Var x ==> not_fresh_at sm' x` by
            (qpat_assum `lower_value _ _ _ e2 _ = _`
               (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
          `local_ptrs_reserved cenv sm'` by
            (imp_res_tac (cj 2 compile_expr_grows) >>
             metis_tac[local_ptrs_reserved_next_var]) >>
          drule comparison_hash_typed >>
          disch_then (qspecl_then [`env.type_defs`, `sh2`, `h2`] mp_tac) >>
          (impl_tac >- (simp[] >> metis_tac[])) >>
          disch_then (qx_choose_then `d2` (qx_choose_then `u`
            (map_every assume_tac o CONJUNCTS))) >>
          `!x. h1 = Var x ==> not_fresh_at sh1 x` by
            metis_tac[(SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape)] >>
          `!x. h1 = Var x ==> not_fresh_at sm' x` by
            (imp_res_tac (cj 2 compile_expr_grows) >>
             metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
          `eval_operand h1 u = SOME d1` by
            (`?x. h1 = Var x` by
               (qpat_x_assum `compile_bytestring_hash p sm = _` mp_tac >>
                simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
                     comp_ignore_bind_def, comp_return_def, fresh_id_def,
                     fresh_var_def, emit_def] >> metis_tac[]) >>
             gnvs[eval_operand_def] >>
             qpat_x_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
             simp[loweringPostsTheory.expr_post_def] >> strip_tac >>
             first_x_assum irule >> simp[]) >>
          `wb_frame cenv es sa s0 t2` by
            (irule exprSimWordArgsTheory.wb_frame_trans >>
             goal_assum (drule_at Any) >>
             reverse conj_tac >- (goal_assum (drule_at Any)) >>
             qexistsl_tac [`ee`, `sh1`, `t'`] >>
             simp[] >> imp_res_tac (cj 2 compile_expr_grows) >>
             imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
             metis_tac[exprSimWordArgsTheory.expr_post_frame,
                       arithmeticTheory.LESS_EQ_TRANS]) >>
          `wb_frame cenv es sa s0 u` by
            (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
             qexistsl_tac [`sm'`, `t2`] >>
             imp_res_tac (cj 2 compile_expr_grows) >>
             simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
          `sa.cs_next_var <= sh2.cs_next_var` by
            metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
          drule_all comparison_finish_post >>
          disch_then (qspecl_then [`e2`, `e1`] strip_assume_tac) >>
          `!ss. bop_result cx (BaseT BoolT) bop
             [expr_type e1; expr_type e1] v v2 ss =
             INL (BoolV (if bop = Eq then d1 = d2 else d1 <> d2))` by
            (irule comparison_source_result >> simp[] >>
             qexistsl_tac [`env.type_defs`, `tv`] >> simp[] >>
             metis_tac[optionTheory.SOME_11]) >>
          `gas_marked_path F ctx func t2 0 (OK z)` by
            metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
          irule comparison_terminal_summary >>
          goal_assum (drule_at Any) >> simp[] >>
          qexists_tac `z` >> simp[]) >>
      gnvs[] >>
      drule comparison_hash_literal >>
      disch_then (qspec_then `cx`
        (qx_choose_then `v2` (map_every assume_tac o CONJUNCTS))) >>
      `expr_body_pre cenv cx env e2 ee` by simp[] >>
      `bind (eval_expr cx e2) (read_result cx) ee = (INL v2,ee)` by simp[] >>
      `expr_result_typed env e2 (Value v2)` by
        (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
      `value_has_type tv v2` by
        (gnvs[expr_result_typed_def, expr_runtime_typed_def,
              value_result_typed_def] >> metis_tac[optionTheory.SOME_11]) >>
      `eval_operand (Lit x) t' = SOME x` by simp[eval_operand_def] >>
      drule_all comparison_finish_post >>
      disch_then (qspecl_then [`e2`, `e1`] strip_assume_tac) >>
      `!ss. bop_result cx (BaseT BoolT) bop
         [expr_type e1; expr_type e1] v v2 ss =
         INL (BoolV (if bop = Eq then d1 = x else d1 <> x))` by
        (irule comparison_source_result >> simp[] >>
         qexistsl_tac [`env.type_defs`, `tv`] >> simp[]) >>
      `bind (bind (eval_expr cx e2) (read_result cx))
         (\v2 ss. (bop_result cx (BaseT BoolT) bop
           [expr_type e1;expr_type e1] v v2 ss,ss)) =
       (\ss. (bop_result cx (BaseT BoolT) bop
           [expr_type e1;expr_type e1] v v2 ss,ss))` by
        simp[FUN_EQ_THM, vyperStateTheory.bind_def] >>
      qpat_x_assum `bind (bind _ _) _ = _` (fn th => pure_once_rewrite_tac[th]) >>
      rewrite_tac[gas_outcome_def] >>
      irule_at Any OR_INTRO_THM1 >>
      irule comparison_terminal_summary >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `z` >> simp[]) >>
  gnvs[] >>
  drule comparison_hash_literal >>
  disch_then (qspec_then `cx`
    (qx_choose_then `v1` (map_every assume_tac o CONJUNCTS))) >>
  `bind (eval_expr cx e1) (read_result cx) es = (INL v1,es)` by simp[] >>
  `expr_sim_inv cenv cx env es /\ expr_result_typed env e1 (Value v1)` by
    (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx e2 /\
   expr_vv_case nocalls ctx func cenv cx e2` by
    (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
     qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2 es` by simp[] >>
  `expr_sim ctx func cenv cx (expr_type e1) e2 es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ e2`
       (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
     disch_then irule >>
     (conj_tac >- gvs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  `?tv. evaluate_type env.type_defs (expr_type e1) = SOME tv /\
        value_has_type tv v1` by
    gnvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  Q.SUBGOAL_THEN
    `?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
           expr_type e1 = BaseT (StringT cap)` assume_tac
  >- (Cases_on `expr_type e1` >> gvs[is_bytestring_type_def] >>
      rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def] >> Cases_on `b` >> gvs[is_bytestring_type_def]) >>
  `bind (bind (eval_expr cx e1) (read_result cx))
     (\v1. bind (bind (eval_expr cx e2) (read_result cx))
       (\v2 ss. (bop_result cx (BaseT BoolT) bop
         [expr_type e1;expr_type e1] v1 v2 ss,ss))) =
   bind (bind (eval_expr cx e2) (read_result cx))
       (\v2 ss. (bop_result cx (BaseT BoolT) bop
         [expr_type e1;expr_type e1] v1 v2 ss,ss))` by
    simp[FUN_EQ_THM, vyperStateTheory.bind_def] >>
  qpat_x_assum `bind (bind _ _) _ = _` (fn th => pure_once_rewrite_tac[th]) >>
  Cases_on `bytestring_literal_hash e2`
  >- (gnvs[] >>
      qpat_x_assum `?p sm. lower_value _ _ _ e2 sa = _ /\ _` strip_assume_tac >>
      `fn_has_code sa sm func /\ fn_has_code sm sh2 func` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         imp_res_tac (SIMP_RULE std_ss [ci_mono_def] compile_bytestring_hash_shape) >>
         metis_tac[fn_has_code_mid, cs_extends_refl]) >>
      irule expr_sim_suffix >>
      qpat_assum `expr_sim _ _ _ _ _ e2 _` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ e2 _ = _` (irule_at Any) >>
      simp[] >>
      (conj_tac >- (irule expr_body_pre_gas_admissible >>
         qexistsl_tac [`cenv`, `env`] >> simp[])) >>
      map_every qx_gen_tac [`gs2`, `v2`, `ee2`, `t2`] >> strip_tac >>
      `expr_body_pre cenv cx env e2 (es with gas_obs := gs2)` by
        simp[expr_body_pre_gas_obs] >>
      drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
      `value_has_type tv v2` by
        (qpat_x_assum `!v'. INL v2 = _ ==> _` (qspec_then `v2` mp_tac) >>
         simp[expr_result_typed_def, expr_runtime_typed_def,
              value_result_typed_def] >> metis_tac[optionTheory.SOME_11]) >>
      `!x. p = Var x ==> not_fresh_at sm x` by
        (qpat_assum `lower_value _ _ _ e2 _ = _`
           (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
      `local_ptrs_reserved cenv sm` by
        (imp_res_tac (cj 2 compile_expr_grows) >>
         metis_tac[local_ptrs_reserved_next_var]) >>
      drule comparison_hash_typed >>
      disch_then (qspecl_then [`env.type_defs`, `sh2`, `h2`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >>
      disch_then (qx_choose_then `d2` (qx_choose_then `u`
        (map_every assume_tac o CONJUNCTS))) >>
      `eval_operand (Lit x) u = SOME x` by simp[eval_operand_def] >>
      `wb_frame cenv es sa s0 u` by
        (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
         qexistsl_tac [`sm`, `t2`] >>
         imp_res_tac (cj 2 compile_expr_grows) >> simp[] >>
         metis_tac[exprSimWordArgsTheory.expr_post_frame]) >>
      drule_all comparison_finish_post >>
      disch_then (qspecl_then [`e2`, `e1`] strip_assume_tac) >>
      `!ss. bop_result cx (BaseT BoolT) bop
         [expr_type e1;expr_type e1] v1 v2 ss =
         INL (BoolV (if bop = Eq then x = d2 else x <> d2))` by
        (irule comparison_source_result >> simp[] >>
         qexistsl_tac [`env.type_defs`, `tv`] >> simp[]) >>
      `gas_marked_path F ctx func t2 0 (OK z)` by
        metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
      qpat_assum `sb.cs_current_bb = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `sb.cs_current_insts = _` (fn th => pure_rewrite_tac[th, LENGTH_APPEND]) >>
      irule comparison_terminal_summary >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `z` >> simp[]) >>
  gnvs[] >>
  qpat_assum `bytestring_literal_hash e2 = SOME x'`
    (mp_then Any mp_tac comparison_hash_literal) >>
  disch_then (qspec_then `cx`
    (qx_choose_then `v2` (map_every assume_tac o CONJUNCTS))) >>
  `expr_body_pre cenv cx env e2 es` by simp[] >>
  `bind (eval_expr cx e2) (read_result cx) es = (INL v2,es)` by simp[] >>
  `expr_result_typed env e2 (Value v2)` by
    (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
  `value_has_type tv v2` by
    (gnvs[expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def] >> metis_tac[optionTheory.SOME_11]) >>
  `eval_operand (Lit x) s0 = SOME x /\ eval_operand (Lit x') s0 = SOME x'` by
    simp[eval_operand_def] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by simp[] >>
  `wb_frame cenv es sa s0 s0` by simp[exprSimWordArgsTheory.wb_frame_refl] >>
  `?z. gas_marked_path F ctx func s0 0 (OK z) /\
    expr_post ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
      es sa sb s0 (es with gas_obs := [])
      (BoolV (if bop = Eq then x = x' else x <> x')) op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule comparison_finish_post >> simp[] >>
     qexistsl_tac [`Lit x`, `Lit x'`, `sa`] >> simp[]) >>
  `!ss. bop_result cx (BaseT BoolT) bop
     [expr_type e1;expr_type e1] v1 v2 ss =
     INL (BoolV (if bop = Eq then x = x' else x <> x'))` by
    (irule comparison_source_result >> simp[] >>
     qexistsl_tac [`env.type_defs`, `tv`] >> simp[]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def] >>
  qexistsl_tac [`INL (BoolV (if bop = Eq then x = x' else x <> x'))`,
                `es`, `OK z`] >>
  simp[vyperStateTheory.bind_def]
QED
