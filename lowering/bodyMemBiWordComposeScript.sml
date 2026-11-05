(* Counted composition for typed word operands. *)
Theory bodyMemBiWordCompose
Ancestors
  bodyMemBiWordFrag bodyArgsMemory exprSimPrecompiles exprSimWordArgs
  exprSimSource exprSimProps list rich_list
  exprSimDefs gasSummary gasOutcome gasSummaryCompose fragGasMode
  vyperState venomState

Theorem typed_args_post_word:
  !args vs xs.
    EVERY (\e. word_value_type (expr_type e)) args /\
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs /\
    typed_args_post ctx func cenv cx es sa s0 ee args xs vs t ==>
    wb_args_post ctx func cenv cx es sa s0 ee xs vs t
Proof
  Induct >> Cases_on `vs` >> Cases_on `xs` >>
  simp[typed_args_post_def, wb_args_post_def] >> rpt strip_tac >>
  gvs[]
  >- metis_tac[word_value_type_typed, typed_val_to_w256_word_value] >>
  first_x_assum (drule_at Any) >>
  simp[typed_args_post_def, wb_args_post_def]
QED

Theorem word_builtin_continuation_summary_mem:
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) xs vs t0 /\
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
