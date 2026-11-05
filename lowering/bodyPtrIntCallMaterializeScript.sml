Theory bodyPtrIntCallMaterialize
Ancestors
  bodyPtrIntCallScalarStore allocationPtr fragGasSeqPtr fragExecPtr
  loweringHalt ptrDiscipline venomExecSemantics venomInst venomState
  finite_map list words bodyPtrDefs arithmetic typedCopyPtr fragExec exprLoweringProps robustCopyTransportPtr pred_set
  bodyPtrIntCallAuxEntry

Theorem intcall_alloca_scalar_operand:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  v <> Var out ==>
  eval_operand v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand v s /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) v =
    op_taint tn v
Proof
  rpt strip_tac >> drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  drule_all step_alloca_fresh >> strip_tac >> gvs[] >>
  Cases_on `v` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE]
QED

Theorem intcall_scalar_materialize_path:
  FLOOKUP s.vs_allocas id = NONE /\
  s.vs_alloca_next + n < dimword (:256) /\ 32 <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  v <> Var out /\ eval_operand v s = SOME word /\ op_taint tn v = {} /\
  (!b m. mem_word_at b m = word ==> val_in_memory ty value b m) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out];
            mk_inst (id+1) MSTORE [Var out;v] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := s.vs_inst_idx + 2) /\
    G' = G |+ (out,(s.vs_alloca_next,n)) /\
    tn'.t_var = tn.t_var |+ (out,{}) /\
    tn'.t_mem = (tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n})
      DIFF {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ptr_covers G' tn' out t n /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
         val_in_memory ty value s.vs_alloca_next m)
Proof
  rpt strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  drule_all intcall_alloca_scalar_operand >>
  disch_then (qspec_then `tn` mp_tac) >> simp[] >> strip_tac >>
  drule_all fresh_alloca_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `out`, `n`] strip_assume_tac) >>
  qpat_x_assum `out <> out /\ _ ==> _` kall_tac >>
  qabbrev_tac `ai = mk_inst id ALLOCA [Lit (n2w n)] [out]` >>
  qabbrev_tac `si = mk_inst (id+1) MSTORE [Var out;v] []` >>
  qabbrev_tac `G1 = step_prov PG G ai s1` >>
  qabbrev_tac `tn1 = step_taint ai s s1 tn` >>
  `lookup_var out s1 = SOME (n2w s.vs_alloca_next)` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     fs[Abbr `ai`] >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  qabbrev_tac `s2 = mstore s.vs_alloca_next word s1` >>
  `step_inst_base si s1 = OK s2` by
    (simp[Abbr `si`] >> pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `s2`, w2n_n2w]) >>
  `ptr_covers G1 tn1 out s1 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qabbrev_tac `u = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `z = mstore s.vs_alloca_next word u` >>
  qabbrev_tac `G2 = step_prov PG G1 si z` >>
  qabbrev_tac `tn2 = step_taint si u z tn1` >>
  `step_inst_base si u = OK z` by
    (simp[Abbr `si`] >> pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `z`, Abbr `u`, w2n_n2w]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn [ai;si] s G2 tn2` by
    (fs[Abbr `u`, Abbr `G1`, Abbr `tn1`] >>
     simp[inst_seq_ptr_def] >>
     conj_tac >- (simp[Abbr `ai`] >> irule ptr_inst_ok_alloca >> simp[]) >>
     simp[Abbr `si`] >> irule ptr_inst_ok_mstore >>
     fs[ptr_covers_def, lookup_var_def]) >>
  suspend "endpoint"
QED

Resume intcall_scalar_materialize_path[endpoint]:
  `run_inst_seq [ai;si] s = OK s2` by simp[run_inst_seq_def] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
     (OK (s2 with vs_inst_idx := s.vs_inst_idx + 2))` by
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [ai;si]` by
       simp[Abbr `ai`, Abbr `si`, mk_inst_def, is_terminator_def] >>
     drule_all run_inst_seq_gas_path_ptr >>
     simp[Abbr `ai`, Abbr `si`, mk_inst_def]) >>

  `eval_operand v u = SOME word /\ lookup_var out u = SOME (n2w s.vs_alloca_next)` by
    fs[Abbr `u`, lookup_var_def] >>
  `G2 = G1 /\ tn2.t_var = tn1.t_var /\
   tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
   tn2.t_mem = tn1.t_mem DIFF {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `G1`, `id+1`] mp_tac) >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `si`, Abbr `z`, w2n_n2w]) >>
  `G1 = G |+ (out,(s.vs_alloca_next,n)) /\
   tn1 = tn with <|t_var := tn.t_var |+ (out,{});
     t_mem := tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}|>` by
    (fs[Abbr `ai`, Abbr `G1`, Abbr `tn1`] >>
     drule_all fresh_alloca_ghost >>
     disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]) >>
  `tn2.t_imm = tn.t_imm` by
    simp[Abbr `tn2`, Abbr `si`, step_taint_def, set_var_taint_def,
         store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  qexists_tac `tn2` >>
  fs[] >>
  conj_tac >-
    (simp[ptr_covers_def, Abbr `s2`, mstore_def, lookup_var_def,
          op_taint_def, FLOOKUP_UPDATE, w2n_n2w] >> fs[lookup_var_def]) >>
  `!m. mem_agree_outside tn2.t_mem z.vs_memory m ==>
       val_in_memory ty value s.vs_alloca_next m` by
    (`eval_operand (Var out) u = SOME (n2w s.vs_alloca_next)` by simp[eval_operand_def] >>
     qpat_assum `eval_operand (Var out) u = _` (mp_then Any mp_tac intcall_scalar_mstore_robust) >>
     simp[w2n_n2w] >> strip_tac >>
     fs[Abbr `tn2`, Abbr `z`, Abbr `si`] >> metis_tac[]) >>
  fs[Abbr `z`, Abbr `s2`, Abbr `u`, mstore_def]
QED
Finalise intcall_scalar_materialize_path

(* The list materialization invariant keeps every earlier footprint below
   the allocation frontier. The new block can change neither those bytes
   nor their taint; this transports their robust representations. *)
Theorem intcall_materialize_old_robust:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\ 32 <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := j) /\
  tn'.t_mem = (tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n})
    DIFF {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32} /\
  val_wf ty value /\ p + val_footprint ty value <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ty value p m) ==>
  !m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ty value p m
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`,
    `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`] >> simp[] >>
  `s1.vs_memory = s.vs_memory` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     gvs[update_var_def]) >>
  mp_tac (Q.SPECL [`s1`, `s.vs_alloca_next`, `word`] mstore_memory_frame) >>
  simp[mem_agree_outside_def] >> strip_tac >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem intcall_materialize_old_vars:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := j) /\
  G' = G |+ (out,(s.vs_alloca_next,n)) /\ tn'.t_var = tn.t_var |+ (out,{}) ==>
  !x. x <> out ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
  rpt strip_tac >> gvs[lookup_var_def, update_var_def, mstore_def,
                         FLOOKUP_UPDATE, op_taint_def]
QED

Theorem intcall_materialize_metadata:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := j) /\
  G' = G |+ (out,(s.vs_alloca_next,n)) /\ tn'.t_var = tn.t_var |+ (out,{}) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!k. cenv.ce_return_buf <> SOME (PtrVar (Var out) k)) /\
  (!k. cenv.ce_return_pc <> SOME (PtrVar (Var out) k)) /\
  return_buf_ptr d cenv G tn s /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  return_buf_ptr d cenv G' tn' t /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn' (Var x) = {}) /\
  stor_taint_ok cx tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `!x. x <> out ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (match_mp_tac intcall_materialize_old_vars >> metis_tac[]) >>
  conj_tac >-
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
  gvs[stor_taint_ok_def, update_var_def, mstore_def]
QED

Theorem intcall_materialize_lookup[local]:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := j) ==>
  lookup_var out t = SOME (n2w s.vs_alloca_next)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
  strip_tac >> gvs[lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE]
QED

Theorem intcall_scalar_materialize_singleton:
  FLOOKUP s.vs_allocas id = NONE /\
  s.vs_alloca_next + n < dimword (:256) /\ 32 <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  v <> Var out /\ eval_operand v s = SOME word /\ op_taint tn v = {} /\
  (!b m. mem_word_at b m = word ==> val_in_memory entry.type entry.value b m) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out];
            mk_inst (id+1) MSTORE [Var out;v] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!k. cenv.ce_return_buf <> SOME (PtrVar (Var out) k)) /\
  (!k. cenv.ce_return_pc <> SOME (PtrVar (Var out) k)) /\
  return_buf_ptr d cenv G tn s /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var out) n))
      cx (vs with scopes := [FEMPTY |+ (name,entry)]) G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_scalar_materialize_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  `n < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `return_buf_ptr d cenv G' tn' t /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn' (Var x) = {}) /\
   stor_taint_ok cx tn' t` by
    (irule intcall_materialize_metadata >> metis_tac[]) >>
  `lookup_var out t = SOME (n2w s.vs_alloca_next)` by
    (irule intcall_materialize_lookup >> metis_tac[]) >>
  irule intcall_singleton_ghost_inv >>
  gvs[ptr_covers_def, w2n_n2w, FLOOKUP_UPDATE] >>
  Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
  fs[return_buf_ptr_def]
QED
