Theory wordArgsPtr
Ancestors
  bodyPtrDefs bodyPtrPreds exprSimWordArgs exprSimProps loweringPosts
  compileEnv loweringStateRelDefs ptrDiscipline venomState exprLoweringProps
  list finite_map freshWrites gasSummaryComposePtr fragGasPathPtr
  vyperInterpreter vyperState gasCount

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
  wb_frame cenv es sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w /\ op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> conj_tac
  >- (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  irule ghost_kept_operand >> metis_tac[]
QED

Theorem word_operands_frame:
  wb_frame cenv es sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
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
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es sa s0 s1 ==>
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
  stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es0 sa s0 s1 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> drule_all wb_frame_local_regions >> strip_tac >>
  irule ghost_kept_trans >>
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
