Theory bodyPtrIfExpRuntimeCopy
Ancestors bodyPtrIfExpRuntimeOneFrame bodyPtrIfExpRuntimeOne
  immutableCopyExecution exprSimCopy exprLoweringProps context compileEnv loweringStateRelDefs
  fragExec emitHelperProps fragGasPathPtr words arithmetic pred_set
  bodyPtrDefs ptrDiscipline venomState finite_map rich_list venomInst

Theorem ifexp_runtime_copy_nonterm:
  compile_imm_copy_to_memory F imm src dst n off ca = ((),cb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca cb)
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  simp[emitted_insts_def, DROP_PREFIX] >>
  irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem ifexp_runtime_copy_parts:
  compile_imm_copy_to_memory F imm src dst (SUC n) off ca = ((),cb) /\
  fn_has_code ca cb fn ==>
  ?cm. immutable_copy_one F imm src dst off ca = ((),cm) /\
    compile_imm_copy_to_memory F imm src dst n (off+32) cm = ((),cb) /\
    fn_has_code ca cm fn /\ fn_has_code cm cb fn /\ ci_mono ca cm /\ ci_mono cm cb
Proof
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >>
  `compile_imm_copy_to_memory F imm src dst (SUC 0) off ca = ((),st1)` by
    simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases,
         compile_imm_copy_zero] >>
  `ci_mono ca st1 /\ ci_mono st1 cb` by
    (mp_tac ci_mono_compile_imm_copy_to_memory >> metis_tac[pairTheory.SND]) >>
  `cs_extends ca st1 /\ cs_extends st1 cb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qexists_tac `st1` >> simp[]
QED

Theorem ifexp_runtime_copy_ptr:
  !n off ca cb s G tn.
  compile_imm_copy_to_memory F imm src (Var root) n off ca = ((),cb) /\
  fn_has_code ca cb fn /\ copy_old_operand ca src /\
  copy_old_operand ca (Var root) /\ eval_operand src s = SOME a /\
  lookup_var root s = SOME d /\ op_taint tn src = {} /\
  ptr_covers G tn root s capacity /\ off+32*n <= capacity /\
  w2n d+capacity < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa0 G0 tn0 s0 G tn /\
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at ca x) /\
  (!name entry p sz v. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v+type_memory_size entry.type <= w2n d \/ w2n d+capacity <= w2n v)) ==>
  ?t H tt.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_memory = (immutable_transfers F F a d n off s).vs_memory /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers H tt root t capacity /\ eval_operand src t = SOME a /\
    lookup_var root t = SOME d /\ op_taint tt src = {} /\
    tt.t_mem = tn.t_mem DIFF {i | w2n d+off <= i /\ i < w2n d+off+32*n} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    ghost_inv rty ce cx ee H tt t /\ ghost_kept ce es sa0 G0 tn0 s0 H tt
Proof
  Induct >- suspend "zero" >> rpt gen_tac >> strip_tac >>
  drule_all ifexp_runtime_copy_parts >> strip_tac >>
  `off+32 <= capacity` by (gvs[MULT_SUC] >> decide_tac) >>
  drule_all ifexp_runtime_one_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 J tr (OK r)` >>
  suspend "step_premises"
QED

Resume ifexp_runtime_copy_ptr[zero]:
  simp[compile_imm_copy_zero] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[gas_path_ptr_rules, immutable_transfers_def] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[copy_runtime_frame_refl]
QED

Resume ifexp_runtime_copy_ptr[step_premises]:
  `ca.cs_next_var <= cm.cs_next_var` by gvs[ci_mono_def] >>
  `!x. not_fresh_at ca x ==> not_fresh_at cm x` by
    (rpt strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `not_fresh_at ca x` mp_tac >> simp[not_fresh_at_def] >>
     disch_then (qspec_then `n'` mp_tac) >> simp[]) >>
  `copy_old_operand cm src /\ copy_old_operand cm (Var root)` by
    metis_tac[copy_old_operand_mono] >>
  `lookup_var root r = SOME d` by (gvs[copy_old_operand_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce cm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cm x) /\
   (!x. not_fresh_at sa0 x ==> not_fresh_at cm x)` by metis_tac[] >>
  `!name entry p sz v. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p r = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v+type_memory_size entry.type <= w2n d \/ w2n d+capacity <= w2n v)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at ca p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var p s = SOME v` by metis_tac[] >> metis_tac[]) >>
  `off+32+32*n <= capacity` by (gvs[MULT_SUC] >> decide_tac) >>
  qpat_x_assum `!off ca cb s G tn. _` drule_all >> strip_tac >>
  suspend "step_finish"
QED

Resume ifexp_runtime_copy_ptr[step_finish]:
  rename1 `gas_path_ptr D 0 ctx fn PG J tr r 0 H tt (OK t)` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cm cb)` by
    metis_tac[ifexp_runtime_copy_nonterm] >>
  `copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule ifexp_runtime_frame_then >> qexistsl_tac [`cm`, `r`] >> simp[]) >>
  `t.vs_memory = (immutable_transfers F F a d (SUC n) off s).vs_memory` by
    (`eval_operand (Var root) s = SOME d` by simp[eval_operand_def] >>
     qpat_assum `compile_imm_copy_to_memory F imm src (Var root) (SUC n) off ca = _`
       (mp_then Any mp_tac copy_runtime_run) >>
     disch_then (qspecl_then [`s`, `a`, `d`] mp_tac) >>
     simp[] >> strip_tac >> gvs[copy_runtime_frame_def]) >>
  qexistsl_tac [`t`, `H`, `tt`] >> simp[] >>
  suspend "step_post"
QED

Resume ifexp_runtime_copy_ptr[step_post]:
  simp[EXTENSION, MULT_SUC] >> gen_tac >>
  Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac
QED

Finalise ifexp_runtime_copy_ptr
