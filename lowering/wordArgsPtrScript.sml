Theory wordArgsPtr
Ancestors
  bodyPtrDefs bodyPtrPreds exprSimWordArgs exprSimProps loweringPosts
  compileEnv loweringStateRelDefs ptrDiscipline venomState exprLoweringProps
  list finite_map freshWrites gasSummaryComposePtr fragGasPathPtr
  vyperInterpreter vyperState gasCount stmtSimLogArgs exprSimPrecompiles

Theorem ghost_kept_at_refl:
  ghost_kept_at lo cenv es sa G tn s G tn
Proof
  simp[ghost_kept_at_def]
QED

Theorem ghost_kept_refl:
  ghost_kept cenv es sa G tn s G tn
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_operand:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_taint tn op = op_taint tn0 op
Proof
  Cases_on `op` >> simp[op_taint_def, ghost_kept_def] >>
  metis_tac[op_taint_def]
QED

Theorem word_operand_frame:
  wb_frame cenv es es' sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w /\ op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> conj_tac
  >- (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  irule ghost_kept_operand >> metis_tac[]
QED

Theorem word_operands_frame:
  wb_frame cenv es es' sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  eval_operands ops s0 = SOME ws /\
  EVERY (\op. op_taint tn0 op = {}) ops ==>
  eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops
Proof
  qid_spec_tac `ws` >> Induct_on `ops` >>
  simp[eval_operands_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all word_operand_frame >> strip_tac >>
  gvs[]
QED

Theorem ghost_kept_trans:
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
            local_region cenv es1.scopes s1 n b sz) ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_def] >> rpt strip_tac
  >- (`not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
      res_tac >> gvs[])
  >- (`not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
      res_tac >> gvs[])
  >- (`aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _`
          irule >> metis_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        irule >> metis_tac[]) >>
  metis_tac[]
QED

Theorem wb_frame_local_regions:
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es es' sa s0 s1 ==>
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv es1.scopes s1 n b sz)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s1 = SOME w` by metis_tac[wb_frame_vars] >>
  metis_tac[local_region_frame, local_region_frame_fwd]
QED

Theorem ghost_kept_wb_trans:
  stmt_state_rel H ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es0 es' sa s0 s1 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> drule_all wb_frame_local_regions >> strip_tac >>
  irule ghost_kept_trans >>
  gvs[wb_frame_def] >> metis_tac[]
QED

(* ghost_kept_trans at a low-memory bound lo. *)
Theorem ghost_kept_at_trans:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es1.scopes s1 n b sz <=>
            local_region cenv es.scopes s0 n b sz) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_at_def] >> rpt strip_tac
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> metis_tac[]) >> simp[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
           (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!n b sz i. local_region cenv es1.scopes s1 n b sz /\ _ ==> _` irule >>
      conj_tac >- simp[] >> qexistsl_tac [`b`,`n`,`sz`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_kept_at_wb_trans:
  !lo cenv es sa G0 tn0 s0 G1 tn1 es1 sm G2 tn2 s1 H ctx func cx es'.
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es' sa s0 s1 ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all wb_frame_local_regions >> strip_tac >>
  irule ghost_kept_at_trans >>
  qexistsl_tac [`G1`,`es1`,`s1`,`sm`,`tn1`] >> simp[] >>
  gvs[wb_frame_def] >> metis_tac[]
QED

Theorem eval_exprs_nil_marked_ptr:
  ~s.vs_halted ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx []) (es,s,G,tn)
    [] (INL []) es G tn (OK s)
Proof
  simp[gas_marked_exec_ptr_def, Once evaluate_def, return_def,
       gas_path_ptr_rules]
QED

Theorem eval_exprs_cons_marked_ptr:
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    left (INL v) mid G1 tn1 (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_exprs cx args) (\vs. return (v::vs)))
    (mid with gas_obs := [],t,G1,tn1) right res fin G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx (e::args))
    (es,s,G0,tn0) (left ++ right) res fin G tn r
Proof
  rewrite_tac[eval_exprs_cons_action] >> strip_tac >>
  irule gas_marked_exec_ptr_bind_normal >> metis_tac[]
QED

Theorem eval_exprs_cons_exception_ptr:
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    marks (INR exc) fin G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx (e::args))
    (es,s,G0,tn0) marks (INR exc) fin G tn r
Proof
  rewrite_tac[eval_exprs_cons_action] >>
  metis_tac[gas_marked_exec_ptr_bind_exception]
QED

Theorem body_exprs_ptr_ok_tail:
  body_exprs_ptr_ok cx (e::args) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
  body_exprs_ptr_ok cx args
Proof
  simp[body_exprs_ptr_ok_def, bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem saved_value_footprint_taint_kept:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
  i IN tn0.t_mem
Proof
  simp[expr_val_at_def] >> strip_tac >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (fs[ghost_kept_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[])
  >> fs[ghost_kept_def, log_arg_clear_def] >>
  qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
  simp[] >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!tv n j k. _` drule_all >> strip_tac >> decide_tac
QED

Theorem saved_value_footprint_clean:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn0.t_mem) ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn.t_mem
Proof
  metis_tac[saved_value_footprint_taint_kept]
QED

Theorem saved_dynamic_bytes_across_word_args:
  typed_args_post H ctx func cenv cx es sb s es' args xs vs t /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sb es
    (BytesV bs) (Var x) s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  not_fresh_at sb x /\ eval_operand (Var x) s = SOME (n2w b) /\
  (b:num) < dimword (:256) /\ FLOOKUP G0 x = SOME (region_base,sz) /\
  (region_base:num) <= b /\ b+32+LENGTH bs <= region_base+(sz:num) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn0.t_mem) ==>
  eval_operand (Var x) t = SOME (n2w b) /\
  FLOOKUP G x = SOME (region_base,sz) /\ op_taint tn (Var x) = op_taint tn0 (Var x) /\
  mem_bytes_at b (32+LENGTH bs) t.vs_memory =
    mem_bytes_at b (32+LENGTH bs) s.vs_memory /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `wb_frame cenv es es' sb s t` by
    fs[exprSimPrecompilesTheory.typed_args_post_def] >>
  `log_arg_clear cenv cx (BaseT (BytesT (Dynamic n))) (BytesV bs)` by
    metis_tac[log_arg_clear_base] >>
  conj_tac >- (irule log_frame_operand >> simp[] >> metis_tac[]) >>
  `FLOOKUP G x = FLOOKUP G0 x /\
   op_taint tn (Var x) = op_taint tn0 (Var x)` by fs[ghost_kept_def] >>
  simp[] >> conj_tac
  >- (`~is_word_type (BaseT (BytesT (Dynamic n)))` by
        simp[compileEnvTheory.is_word_type_def] >>
      drule_all log_argument_footprint_kept >>
      simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
        wordsTheory.w2n_n2w]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `i IN tn0.t_mem` suffices_by (gvs[] >> metis_tac[]) >>
  irule saved_value_footprint_taint_kept >>
  first_assum (irule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`n2w b`, `BaseTV (BytesT (Dynamic n))`, `tn`, `G0`, `G`] >>
  simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
    wordsTheory.w2n_n2w]
QED
