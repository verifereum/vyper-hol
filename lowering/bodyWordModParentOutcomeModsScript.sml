(* Lift the silent modular suffix at the third reached cut to the parent post. *)
Theory bodyWordModParentOutcomeMods
Ancestors
  bodyFullBuiltinWordModPost bodyFullPostsMods gasOutcomeFullPostMods gasOutcomeFull
  wordArgsPtr exprSimWordArgs exprSimMemDefs exprSimDefs bodyPtrDefs
  loweringPosts loweringSlice valueEncoding compileEnv builtinMath
  vyperAST vyperState vyperInterpreter vyperStorageTrace vyperStorageFootprint
  integer_word words list
Libs monadsyntax

Theorem modular_first_horizon[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
     (INL v,mid with gas_obs := []) /\
  storage_trace_domain cx st0 mid.storage_trace ==>
  valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace
Proof
  strip_tac >>
  `?delta. mid.storage_trace = es.storage_trace ++ delta` by
    (drule_at (Pat `_ = _`) storage_trace_frame_prefix >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  irule valid_horizon_append >> qexists_tac `delta` >> fs[storage_trace_domain_def]
QED

Theorem modular_word_kept_step[local]:
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es mid sa s0 t /\ wb_frame cenv mid fin sm t u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 ==>
  wb_frame cenv es fin sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
      >- (qexistsl_tac [`mid`,`sm`,`t`] >> simp[]) >>
      qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac ghost_kept_at_wb_trans) >>
  disch_then irule >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`mid`,`t`,`sm`,`tn1`] >> simp[]
QED

val u256 = ``BaseT (UintT 256)``;
val parent = ``Builtin ^u256 bt [e1;e2;e3]``;
val words = [``val_to_w256 v1``, ``val_to_w256 v2``, ``val_to_w256 v3``];
val [wa,wb,wc] = words;
val suffix_result = ``builtin_result cx (fin:evaluation_state).accounts ^u256 bt [^u256;^u256;^u256]
  [IntV (&w2n ^wa);IntV (&w2n ^wb);IntV (&w2n ^wc)]``;
val word_result = ``(if bt = AddMod then addmod else mulmod) ^wa ^wb ^wc``;
val value_result = ``IntV (&w2n ^word_result)``;
val div_error = ``Error (RuntimeError (if bt = AddMod then
      "AddMod division by zero" else "MulMod division by zero"))``;

Theorem modular_suffix_parent_outcome_mods:
  expr_type e1 = ^u256 /\ expr_type e2 = ^u256 /\ expr_type e3 = ^u256 /\
  v1 = IntV (&w2n ^wa) /\ v2 = IntV (&w2n ^wb) /\ v3 = IntV (&w2n ^wc) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  s1.cs_next_var <= s2.cs_next_var /\ s1.cs_next_id <= s2.cs_next_id /\
  s2.cs_next_var <= s3.cs_next_var /\ s2.cs_next_id <= s3.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v1,mid1 with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid1.storage_trace /\
  storage_trace_domain cx st0 mid2.storage_trace /\
  (!H. valid_horizon cx st0 H mid1.storage_trace ==>
    expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid1 v1 x t1 /\
    s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 mid1 s1 s2 t1 mid2 v2 y t2 /\
    t1.vs_alloca_next <= t2.vs_alloca_next /\
    ghost_kept_at lo cenv mid1 s1 G1 tn1 t1 G2 tn2) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx func cenv cx e3 mid2 s2 s3 t2 fin v3 z t3 /\
    t2.vs_alloca_next <= t3.vs_alloca_next /\
    ghost_kept_at lo cenv mid2 s2 G2 tn2 t2 G3 tn3 /\
    ~t3.vs_halted /\ fin.gas_obs = []) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (?r u Gf tnf.
    (^wc = 0w ==>
      r = Abort Revert_abort u /\ Gf = G3 /\ tnf = tn3 /\
      ^suffix_result = INR ^div_error /\
      exit_result r /\ expr_exit ^suffix_result r) /\
    (^wc <> 0w ==>
      r = OK u /\ ^suffix_result = INL ^value_result /\
      eval_operand op u = SOME ^word_result /\
      op_taint tnf op = {} /\ op_prov Gf op = NONE /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
      u.vs_alloca_next = t3.vs_alloca_next /\ u.vs_allocas = t3.vs_allocas /\
      u.vs_memory = t3.vs_memory /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      (!q. not_fresh_at s3 q ==> lookup_var q u = lookup_var q t3) /\
      ghost_kept_at lo cenv fin s3 G3 tn3 t3 Gf tnf) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t3,G3,tn3) [] (r,Gf,tnf) /\
      (^wc <> 0w ==> stmt_state_rel H ctx func cenv cx fin u /\
         immutable_frame_mods func cenv cx fin u /\
         ghost_inv_at_mods (DF H) lo d cenv cx fin Gf tnf u))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (\ee. (builtin_result cx ee.accounts ^u256 bt (MAP expr_type [e1;e2;e3]) [v1;v2;v3],ee))
    (fin,t3,G3,tn3)
    (\H res ee G tn t. ?v. res = INL v /\
       expr_post_mods H ctx func cenv cx ^parent es sa sb s0 ee v op t /\
       expr_store_bound cx (post_value_type cenv ^parent) v op t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
       ptr_val_ok cx (post_value_type cenv ^parent) v op G tn t /\
       (~is_word_type (post_value_type cenv ^parent) ==> ptr_buf_ok cenv ^parent op G t) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace`
    by fs[storage_trace_domain_def] >>
  `~t3.vs_halted /\ fin.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `builtin_result cx fin.accounts ^u256 bt [^u256;^u256;^u256] [v1;v2;v3] = ^suffix_result` by
    (qpat_assum `v1 = IntV _` (fn a => qpat_assum `v2 = IntV _` (fn b =>
       qpat_assum `v3 = IntV _` (fn c => simp[NoAsms, SimpRHS, GSYM a, GSYM b, GSYM c]))) >>
     simp[]) >>
  Cases_on `^wc = 0w`
  >- suspend "zero" >>
  suspend "nonzero"
QED

Resume modular_suffix_parent_outcome_mods[zero]:
  qpat_x_assum `^wc = 0w ==> _` (drule_then strip_assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  qexistsl_tac [`G3`,`fin`,`INR ^div_error`,`tn3`,`u`] >>
  simp[halt_exit_def, fragExecTheory.exit_result_def, expr_exit_def] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> fs[]
QED

Resume modular_suffix_parent_outcome_mods[nonzero]:
  qpat_x_assum `^wc <> 0w ==> _` (drule_then strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`fin`,`INL ^value_result`,`u`,`tnf`] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  conj_tac >- fs[] >>
  qpat_x_assum `^wc <> 0w ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) es.storage_trace` by
    (irule modular_first_horizon >>
     qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (irule_at Any) o REWRITE_RULE [APPEND_NIL]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  suspend "post"
QED

Resume modular_suffix_parent_outcome_mods[post]:
  qmatch_goalsub_abbrev_tac `IntV (&w2n w)` >>
  fs[expr_type_def, post_value_type_word, is_word_type_def,
     expr_store_bound_word, ptr_val_ok_def] >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
   sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
   s0.vs_alloca_next <= t3.vs_alloca_next` by decide_tac >>
  fs[expr_post_mods_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes /\
   MAP FDOM es.scopes = MAP FDOM mid2.scopes /\
   MAP FDOM es.scopes = MAP FDOM fin.scopes /\
   storage_well_formed_on cx fin (FST H)` by
    fs[expr_post_def, locals_kept_def] >>
  conj_tac >- suspend "ordinary" >>
  suspend "ghost"
QED

Resume modular_suffix_parent_outcome_mods[ordinary]:
  irule (INST_TYPE (map (fn ty => ty |-> ``:256``)
           (type_vars_in_term (concl modular_parent_post))) modular_parent_post) >>
  simp[is_word_type_def, word_value_def, val_to_w256_def, i2w_pos] >>
  conj_tac >- (qexists_tac `storage_trace_horizon mid1.storage_trace` >> simp[]) >>
  qpat_assum `expr_post _ _ _ _ _ e1 es _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ _ e2 mid1 _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post H _ _ _ _ e3 mid2 _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `MAP FDOM es.scopes = MAP FDOM fin.scopes`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  qpat_x_assum `MAP FDOM es.scopes = MAP FDOM mid2.scopes`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[]
QED

Resume modular_suffix_parent_outcome_mods[ghost]:
  `wb_frame cenv es mid1 sa s0 t1 /\ wb_frame cenv mid1 mid2 s1 t1 t2 /\
   wb_frame cenv mid2 fin s2 t2 t3` by
    (rpt conj_tac >> first_assum (ACCEPT_TAC o MATCH_MP expr_post_frame)) >>
  `wb_frame cenv es mid2 sa s0 t2 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule modular_word_kept_step >> simp[] >> conj_tac
     >- (qexistsl_tac [`storage_trace_horizon mid1.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`G1`,`mid1`,`s1`,`t1`,`tn1`] >>
     qpat_x_assum `MAP FDOM es.scopes = MAP FDOM fin.scopes`
       (fn th => PURE_REWRITE_TAC[GSYM th]) >>
     qpat_x_assum `MAP FDOM es.scopes = MAP FDOM mid1.scopes`
       (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[]) >>
  `wb_frame cenv es fin sa s0 t3 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G3 tn3` by
    (irule modular_word_kept_step >> simp[] >> conj_tac
     >- (qexistsl_tac [`storage_trace_horizon mid1.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`G2`,`mid2`,`s2`,`t2`,`tn2`] >>
     qpat_x_assum `MAP FDOM es.scopes = MAP FDOM fin.scopes`
       (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[]) >>
  irule (Q.ISPEC `storage_trace_horizon mid1.storage_trace`
    (Q.GEN `H` (SPEC_ALL ghost_kept_at_wb_trans))) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`ctx`,`cx`,`func`,`mid1`] >> simp[]) >>
  qexistsl_tac [`G3`,`fin`,`fin`,`t3`,`s3`,`tn3`] >> simp[]
QED

Finalise modular_suffix_parent_outcome_mods
