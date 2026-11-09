(* Counted composition for typed word operands. *)
Theory bodyMemBiWordCompose
Ancestors
  bodyMemBiWordFrag bodyArgsMemory exprSimPrecompiles exprSimWordArgs
  exprSimSource exprSimProps exprSimWordBuiltins list rich_list
  exprSimDefs gasSummary gasOutcome gasSummaryCompose fragGasMode
  vyperState venomState exprSimMemDefs exprSimHypsDefs
  freshWrites compileEnv fragExec exprLoweringProps fragGasPath gasContext

Theorem typed_args_operands_word[local]:
  !cx t args vs xs.
    EVERY (\e. word_value_type (expr_type e)) args /\
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs /\
    LENGTH args = LENGTH vs /\
    LIST_REL (\x ev. eval_operand x t = SOME
      (typed_val_to_w256
        (THE (evaluate_type (get_tenv cx) (expr_type (FST ev))))
        (SND ev))) xs (ZIP (args,vs)) ==>
    LIST_REL (\x v. eval_operand x t = SOME (val_to_w256 v)) xs vs
Proof
  ntac 2 gen_tac >>
  Induct >> Cases_on `vs` >> Cases_on `xs` >> simp[] >> rpt strip_tac >>
  gvs[]
  >- metis_tac[word_value_type_typed, typed_val_to_w256_word_value] >>
  first_x_assum (drule_at Any) >> simp[]
QED

Theorem typed_args_post_word:
  !args vs xs.
    EVERY (\e. word_value_type (expr_type e)) args /\
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs /\
    typed_args_post ctx func cenv cx es sa s0 ee args xs vs t ==>
    wb_args_post ctx func cenv cx es sa s0 ee xs vs t /\
    (~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 t)
Proof
  rpt gen_tac >> simp[typed_args_post_def, wb_args_post_def] >> strip_tac >>
  simp[] >> match_mp_tac typed_args_operands_word >>
  qexistsl_tac [`cx`, `args`] >> simp[]
QED

Theorem word_builtin_continuation_summary_mem:
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) xs vs t0 /\
  (~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 t0) /\
  t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t0.vs_halted /\
  alloca_history func t0 /\ s0.vs_alloca_next <= t0.vs_alloca_next /\
  (!sa sb xs op s0.
    code xs sa = (op,sb) /\ expr_res_ok
      (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) /\
    EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx (ee with gas_obs := []) s0 /\
    alloca_history func s0 /\
    LIST_REL (\x v. eval_operand x s0 = SOME (val_to_w256 v)) xs vs /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?r. gas_marked_path T ctx func s0 0 r /\
      ((?s v. r = OK s /\
        builtin_result cx ee.accounts ann bt (MAP expr_type args) vs = INL v /\
        word_value v /\ stmt_state_rel ctx func cenv cx (ee with gas_obs := []) s /\
        eval_operand op s = SOME (val_to_w256 v) /\
        (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
        s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) \/
       (exit_result r /\ expr_exit
         (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) r))) /\
  expr_res_ok (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) /\
  code xs sm = (op,sb) /\
  EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ is_word_type ann /\
  sa.cs_next_var <= sm.cs_next_var ==>
  gas_summary_at T (ctx,func) []
    (\st. (builtin_result cx st.accounts ann bt (MAP expr_type args) vs,st))
    (ee with gas_obs := [],t0)
    (\res fin t. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann bt args) es sa sb s0 fin v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   LIST_REL (\x v. eval_operand x t0 = SOME (val_to_w256 v)) xs vs` by
    gvs[wb_args_post_def] >>
  qpat_x_assum `!sa sb xs op s0. _`
    (qspecl_then [`sm`,`sb`,`xs`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`builtin_result cx ee.accounts ann bt (MAP expr_type args) vs`,
                    `ee`, `r`] >> conj_tac
      >- (simp[gas_marked_exec_def] >> metis_tac[]) >>
      gvs[] >>
      irule expr_post_word_builtin >> simp[] >>
      qexistsl_tac [`sm`,`t0`,`vs`,`xs`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`builtin_result cx ee.accounts ann bt (MAP expr_type args) vs`,
                `ee`, `r`] >> simp[gas_marked_exec_def]
QED

Theorem compile_typed_word_builtin_sim_mem:
  !ctx func cenv cx env ty ann bt args es arg_ty code.
    expr_body_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e)) args /\
    typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args /\
    bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
    builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
    (!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
      ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
    (!xs. straight_fresh (code xs)) /\
    (!vs ee. LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                                value_has_type tv v) args vs ==>
      !sa sb xs op s0.
        code xs sa = (op,sb) /\ expr_res_ok
          (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) /\
        EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx ee s0 /\
        alloca_history func s0 /\
        LIST_REL (\x v. eval_operand x s0 = SOME (val_to_w256 v)) xs vs /\
        ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        ?r. gas_marked_path T ctx func s0 0 r /\
          ((?s v. r = OK s /\
            builtin_result cx ee.accounts ann bt (MAP expr_type args) vs = INL v /\
            word_value v /\ stmt_state_rel ctx func cenv cx ee s /\
            eval_operand op s = SOME (val_to_w256 v) /\
            (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
            (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
            s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
            s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) \/
           (exit_result r /\ expr_exit
             (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) r))) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann bt args) es
Proof
  rpt gen_tac >> strip_tac >>
  `wb_args_shape cenv arg_ty args` by metis_tac[typed_word_args_shape] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  rewrite_tac[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  (conj_tac >- simp[vyperASTTheory.expr_type_def]) >>
  qpat_x_assum `!sa sb op. _ ==> _` drule >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by
    (qpat_x_assum `!xs. straight_fresh _` (qspec_then `xs` mp_tac) >>
     simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
     expr_sim_inv cenv cx env (ee with gas_obs := gs)` by
    simp[] >>
  drule_all lower_typed_args_sim_mem >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume compile_typed_word_builtin_sim_mem[normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_res_ok (builtin_result cx es_end.accounts ann bt (MAP expr_type args) vs)` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     gvs[bind_def]) >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (irule word_args_values_typed >> goal_assum (drule_at Any) >>
     qexistsl_tac [`cenv`,`env`] >> conj_tac
     >- (rpt gen_tac >> strip_tac >> conj_tac
         >- (irule expr_body_pre_builtin_typed_arg >> simp[] >> conj_tac
             >- (strip_tac >> gvs[EVERY_MEM] >> first_x_assum drule >>
                 simp[word_value_type_def]) >>
             qexistsl_tac [`ann`,`args`,`bt`,`es`] >> simp[]) >>
         gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >> simp[]) >>
  drule_all typed_args_post_word >> strip_tac >>
  qpat_x_assum `!vs ee. _` drule >>
  disch_then (qspec_then `es_end with gas_obs := []`
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `gas_summary_at T (ctx,func) []
     (\st. (builtin_result cx st.accounts ann bt (MAP expr_type args) vs,st))
     (es_end with gas_obs := [],t)
     (\res fin u. ?v. res = INL v /\
       expr_post ctx func cenv cx (Builtin ann bt args) es sa sb s0 fin v op u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
     (\res fin r. expr_exit res r)` by
    (irule word_builtin_continuation_summary_mem >> simp[] >>
     qexistsl_tac [`code`,`sm`,`xs`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  qexists_tac `marks` >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_summary_at_def] >>
  qexistsl_tac [`res`,`es_end'`,`r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                |> REWRITE_RULE [APPEND_NIL]) >>
       qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _` (irule_at Any) >>
       gvs[]) >> gvs[])
QED
Resume compile_typed_word_builtin_sim_mem[exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_summary_at_def] >>
  qexistsl_tac [`INR y`,`es_end`,`r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume compile_typed_word_builtin_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any word_builtin_exempt_cert >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise compile_typed_word_builtin_sim_mem
