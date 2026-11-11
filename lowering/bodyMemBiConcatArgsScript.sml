(* Memory-labelled operand-list simulation for concat. *)
Theory bodyMemBiConcatArgs
Ancestors
  bodyMemBiConcatHead bodyMemoryPreds exprSimConcatArgs gasSummaryCompose
  fragGasPathMem exprSimHyps exprSimMemDefs exprLowering exprLoweringProps
  compileEnv gasOutcome gasSummary gasExemptCert fragGasMode fragGasPath
  exprSimProps exprSimDefs loweringPosts exprSimConcatPath exprSimConcatStore
  vyperInterpreter vyperState venomState words arithmetic list rich_list
  exprSimWordArgs fragExec exprSimSource freshWrites
Libs
  monadsyntax

Theorem concat_args_sim_mem:
  !args P k tops ctx func cenv cx env es sa sb s0 dv ov ow
   binst B bsz oinst.
    compile_concat compile_expr cenv args (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) args)
      (Var ov) sa = ((), sb) /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
               ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    expr_sim_inv cenv cx env es /\
    (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env e st) /\
    body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var dv s0 = SOME (n2w (B + 32)) /\ lookup_var ov s0 = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\
    B + bsz < dimword (:256) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32 + P + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    32 + concat_data_bound P (MAP expr_type args) <= bsz /\
    alloca_history func s0 ==>
    gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee t /\
         LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                              value_has_type tv v) args vs /\
         mem_bytes_at (B + 32) (k + LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) t.vs_memory =
           mem_bytes_at (B + 32) k s0.vs_memory ++ FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs) /\
         mload (w2n ow) t = n2w (k + LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                lookup_var z t = SOME w) /\
         (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
                  FLOOKUP t.vs_allocas aid = SOME a) /\
         (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
            aid < sa.cs_next_id /\
            (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
            (!name lo sz. local_region cenv es.scopes s0 name lo sz ==>
                          p + n <= lo \/ lo + sz <= p) ==>
            mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         locals_kept cenv es ee s0 t /\ alloca_history func t /\
         s0.vs_alloca_next <= t.vs_alloca_next)
      (\rr ee r. ?exc. rr = INR exc /\
         expr_exit (INR exc : eval_result + exception) r)
Proof
  Induct
  >- (rpt strip_tac >>
      qpat_x_assum `compile_concat _ _ [] _ _ _ _ = _`
        (mp_tac o REWRITE_RULE [compile_concat_def, comp_return_def]) >>
      simp[] >> disch_then SUBST_ALL_TAC >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def,
           eval_exprs_nil, gas_marked_path_def] >>
      qexistsl_tac [`INL []`, `es`, `OK s0`] >>
      simp[cj 1 gas_path_mem_rules, locals_kept_refl]) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `body_exprs_mem_ok cx (e::args)` >>
  qpat_x_assum `body_exprs_mem_ok _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [body_exprs_mem_ok_def]) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `!e st. MEM _ _ /\ _ ==> _` (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_mem_ok _ _`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then drule >> disch_then drule >> simp[]) >>
  qpat_assum `EVERY _ (e::args)`
    (CONJUNCTS_THEN assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ sa = (op, s1)` >>
  `ci_mono sa s1` by
    (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono s1 sb` by (drule_all concat_cons_mono >> simp[]) >>
  `fn_has_code sa s1 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume concat_args_sim_mem[head_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    asm_simp_tac (srw_ss()) [expr_body_pre_gas_obs] >>
  drule_all concat_head_typed >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
    (qpat_x_assum `MAP FDOM _ = _` mp_tac >> simp[]) >>
  drule_all concat_head_arm_mem >> strip_tac >>
  suspend "recurse"
QED
Resume concat_args_sim_mem[head_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\res ee r. expr_exit res r) _ _ _` mp_tac >>
      simp[expr_exit_def]) >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  qpat_x_assum `(\res ee r. expr_exit res r) _ _ _` mp_tac >>
  qpat_x_assum `exit_result r` mp_tac >> simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_exit _ r` mp_tac >>
  Cases_on `y` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED
Resume concat_args_sim_mem[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED
Resume concat_args_sim_mem[recurse]:
  `body_exprs_mem_ok cx args` by
    (qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `!e' st. MEM e' args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e' st` by
    (rpt strip_tac >> qpat_x_assum `!e st. MEM _ _ /\ _ ==> _` irule >> simp[]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   sa.cs_next_id <= s2.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `not_fresh_at s2 dv /\ not_fresh_at s2 ov` by
    (conj_tac >>
     (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> decide_tac)) >>
  `binst.inst_id < s2.cs_next_id /\ oinst.inst_id < s2.cs_next_id` by decide_tac >>
  `32 + (P + concat_payload_capacity (expr_type e)) +
     SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz` by
    (qpat_x_assum `32 + P + SUM _ <= bsz` mp_tac >> simp[] >> decide_tac) >>
  `32 + concat_data_bound (P + concat_payload_capacity (expr_type e))
     (MAP expr_type args) <= bsz` by
    (qpat_x_assum `32 + concat_data_bound P _ <= bsz` mp_tac >>
     simp[concat_data_bound_def, LET_THM] >> rw[MAX_DEF]) >>
  qpat_x_assum `!P k tops ctx func cenv cx env es sa sb s0 dv ov ow binst B bsz oinst. _`
    (qspecl_then [`P + concat_payload_capacity (expr_type e)`,
      `k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])`,
      `tops`] mp_tac) >>
  disch_then drule_all >> strip_tac >>
  `gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) es_end (OK t2)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ (OK t)` mp_tac >>
     qpat_assum `gas_path_mem _ _ t 0 (OK t2)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[gas_marked_exec_def] >> rpt strip_tac >>
     metis_tac[gas_marked_path_then, gas_marked_path_from_mem, ADD_0]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ (OK t)` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume concat_args_sim_mem[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `gas_marked_exec _ _ (eval_exprs cx args) _ _ (INL vs) es_end' (OK tu)` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK tu`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >>
  drule_all concat_args_glue >> strip_tac >>
  suspend "post"
QED
Resume concat_args_sim_mem[tail_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\rr ee r. _) _ _ _` mp_tac >> simp[]) >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qpat_x_assum `(\rr ee r. _) _ _ _` mp_tac >>
  qpat_x_assum `exit_result r` mp_tac >> simp[]
QED
Resume concat_args_sim_mem[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume concat_args_sim_mem[post]:
  qexists_tac `tu` >> conj_tac >- REFL_TAC >>
  qexists_tac `v::vs` >> conj_tac >- REFL_TAC >>
  simp[] >> conj_tac
  >- (qpat_x_assum `expr_sim_inv _ _ _ (es_end' with gas_obs := [])` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (es_end' with gas_obs := []) tu` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `mem_bytes_at _ _ tu.vs_memory = mem_bytes_at _ _ s0.vs_memory ++ _` mp_tac >>
      simp_tac bool_ss [LENGTH_APPEND, APPEND_ASSOC, AC ADD_ASSOC ADD_COMM]) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ _ ==> _` irule >>
  simp[ADD_COMM] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `aid` >> simp[]
QED
Finalise concat_args_sim_mem
