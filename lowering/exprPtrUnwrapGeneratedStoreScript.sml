(* Concrete store and counter advance suffix; copied taint is not discarded. *)
Theory exprPtrUnwrapGeneratedStore
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges exprPtrUnwrapFrames
  typedCopyPtr decoderGhostFramePtr slotCopyExecution copyExecution
  fragGasSeqPtr fragExec bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map exprLoweringProps ghostPcTransportPtr

Theorem copy_generated_store_checks:
  ptr_covers G tn (slot_copy_var cs 5) s 32 /\
  eval_operand (Var (slot_copy_var cs 5)) s = SOME a /\
  eval_operand (Var (slot_copy_var cs 3)) s = SOME value /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = mstore (w2n a) value s /\ w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) s u tn /\
  v = update_var (slot_copy_var cs 6) (k+1w) w /\
  z = (v with vs_inst_idx := SUC w.vs_inst_idx) /\
  J = step_prov PG H (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) v /\
  tq = step_taint (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) w v tm /\
  Gf = step_prov PG J (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0])
    (update_var (slot_copy_var cs 0) (k+1w) z) /\
  tnf = step_taint (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) z
    (update_var (slot_copy_var cs 0) (k+1w) z) tq ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst (cs.cs_next_id+8) MSTORE
       [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] [];
     mk_inst (cs.cs_next_id+9) ADD [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6];
     mk_inst (cs.cs_next_id+10) ASSIGN [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]] s Gf tnf
Proof
  strip_tac >>
  `step_inst_base (mk_inst (cs.cs_next_id+8) MSTORE
     [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) s = OK u` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_write2_def]) >>
  `op_taint tm (Var (slot_copy_var cs 0)) = {}` by
    (gvs[] >> simp[step_taint_other_output, mk_inst_def]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+9) ADD
     [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) w = OK v` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
                  mstore_def, eval_operand_def]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+10) ASSIGN
     [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) z =
     OK (update_var (slot_copy_var cs 0) (k+1w) z)` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_pure1_def,
                  eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst (cs.cs_next_id+8) MSTORE
     [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) s` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx fn H tm (mk_inst (cs.cs_next_id+9) ADD
     [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) w` by
    (irule ptr_inst_ok_copy_arith >>
     gvs[op_taint_def, allocas_from_def, allocas_below_fmp_def, mstore_def] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx fn J tq (mk_inst (cs.cs_next_id+10) ASSIGN
     [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) z` by
    (irule ptr_inst_ok_copy_assign >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def, mstore_def] >> metis_tac[]) >>
  gvs[] >> simp[inst_seq_ptr_def]
QED

Theorem copy_generated_store_ghost:
  eval_operand (Var (slot_copy_var cs 5)) s = SOME a /\
  eval_operand (Var (slot_copy_var cs 3)) s = SOME value /\
  u = mstore (w2n a) value s /\ w = (u with vs_inst_idx := ix) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) s u tn /\
  v = update_var (slot_copy_var cs 6) (k+1w) w /\ z = (v with vs_inst_idx := iy) /\
  J = step_prov PG H (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) v /\
  tq = step_taint (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) w v tm /\
  t = update_var (slot_copy_var cs 0) (k+1w) z /\
  Gf = step_prov PG J (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) t /\
  tnf = step_taint (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) z t tq ==>
  op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
  tnf.t_mem =
    (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a+32}) UNION
    {w2n a+j | j IN op_taint tn (Var (slot_copy_var cs 3))} /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `tm.t_mem =
    (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a+32}) UNION
    {w2n a+j | j IN op_taint tn (Var (slot_copy_var cs 3))}` by
    (qpat_x_assum `tm = _` SUBST1_TAC >>
     qpat_x_assum `u = _` SUBST1_TAC >>
     irule mstore_transferred_taint >> simp[]) >>
  `tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    (gvs[] >> simp[step_taint_nonmemory_frame, copy_mk_immutable_taint, mk_inst_def]) >>
  `op_taint tq (Var (slot_copy_var cs 6)) = {} /\
   tq.t_mem = tm.t_mem /\ tq.t_stor = tm.t_stor /\
   tq.t_trans = tm.t_trans /\ tq.t_imm = tm.t_imm` by
    (qpat_x_assum `tq = _` SUBST1_TAC >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     simp[copy_len_binop_ghost_frame, copy_mk_immutable_taint]) >>
  `op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
   tnf.t_mem = tq.t_mem /\ tnf.t_stor = tq.t_stor /\
   tnf.t_trans = tq.t_trans /\ tnf.t_imm = tq.t_imm` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     qpat_x_assum `t = _` SUBST1_TAC >>
     simp[copy_assign_ghost_frame]) >>
  fs[] >> rpt strip_tac >> gvs[] >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem copy_generated_store_execution:
  eval_operand (Var (slot_copy_var cs 5)) s = SOME a /\
  eval_operand (Var (slot_copy_var cs 3)) s = SOME value /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k ==>
  run_inst_seq
    [mk_inst (cs.cs_next_id+8) MSTORE
       [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] [];
     mk_inst (cs.cs_next_id+9) ADD [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6];
     mk_inst (cs.cs_next_id+10) ASSIGN [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]] s =
  OK (update_var (slot_copy_var cs 0) (k+1w)
       (update_var (slot_copy_var cs 6) (k+1w) (mstore (w2n a) value s)))
Proof
  strip_tac >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_write2_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, mstore_def] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem copy_generated_store_segment:
  ptr_covers G tn (slot_copy_var cs 5) s 32 /\
  eval_operand (Var (slot_copy_var cs 5)) s = SOME a /\
  eval_operand (Var (slot_copy_var cs 3)) s = SOME value /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 0) (k+1w)
       (update_var (slot_copy_var cs 6) (k+1w) (mstore (w2n a) value s)) /\
    run_inst_seq
      [mk_inst (cs.cs_next_id+8) MSTORE
         [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] [];
       mk_inst (cs.cs_next_id+9) ADD [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6];
       mk_inst (cs.cs_next_id+10) ASSIGN [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]] s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst (cs.cs_next_id+8) MSTORE
         [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] [];
       mk_inst (cs.cs_next_id+9) ADD [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6];
       mk_inst (cs.cs_next_id+10) ASSIGN [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]]
      (s with vs_inst_idx := ix) Gf tnf) /\
    op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
    tnf.t_mem = (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a+32}) UNION
      {w2n a+j | j IN op_taint tn (Var (slot_copy_var cs 3))} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `u = mstore (w2n a) value s` >>
  qabbrev_tac `v = update_var (slot_copy_var cs 6) (k+1w) u` >>
  qabbrev_tac `t = update_var (slot_copy_var cs 0) (k+1w) v` >>
  qabbrev_tac `H = step_prov PG G (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) u` >>
  qabbrev_tac `tm = step_taint (mk_inst (cs.cs_next_id+8) MSTORE
    [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []) s u tn` >>
  qabbrev_tac `J = step_prov PG H (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) v` >>
  qabbrev_tac `tq = step_taint (mk_inst (cs.cs_next_id+9) ADD
    [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6]) u v tm` >>
  qabbrev_tac `Gf = step_prov PG J (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) t` >>
  qabbrev_tac `tnf = step_taint (mk_inst (cs.cs_next_id+10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) v t tq` >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  conj_tac >- simp[Abbr `t`, Abbr `v`, Abbr `u`] >>
  conj_tac >- (simp[Abbr `t`, Abbr `v`, Abbr `u`] >>
               irule copy_generated_store_execution >> simp[]) >>
  conj_tac
  >- (gen_tac >> irule copy_generated_store_checks >>
      simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, Abbr `v`, Abbr `u`, Abbr `J`,
           Abbr `tq`, Abbr `H`, Abbr `tm`]) >>
  rule_assum_tac (REWRITE_RULE[markerTheory.Abbrev_def]) >>
  `u = (u with vs_inst_idx := u.vs_inst_idx)` by simp[] >>
  `v = (v with vs_inst_idx := v.vs_inst_idx)` by simp[] >>
  drule_all copy_generated_store_ghost >> simp[]
QED
