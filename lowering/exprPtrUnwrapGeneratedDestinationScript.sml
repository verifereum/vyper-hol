(* Generated MUL/ADD address prefix, with concrete ghost endpoints. *)
Theory exprPtrUnwrapGeneratedDestination
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges exprPtrUnwrapFrames
  typedCopyPtr typedCopyLoopHeaderPtr decoderGhostFramePtr
  slotCopyExecution copyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  exprLoweringProps ghostPcTransportPtr

Theorem copy_generated_destination_covers:
  lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ root <> slot_copy_var cs 4 /\
  root <> slot_copy_var cs 5 /\ 
  off < capacity /\ off + 32 <= capacity /\ w2n a + off < dimword(:256) /\
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := ix) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  v = update_var (slot_copy_var cs 5) (a+n2w off) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w v tm ==>
  ptr_covers Gf tnf (slot_copy_var cs 5) v 32
Proof
  strip_tac >>
  `ptr_covers H tm root w capacity` by
    (gvs[ptr_covers_inst_idx] >> irule ptr_covers_step_frame >>
     fs[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var root w = SOME a /\
   eval_operand (Var (slot_copy_var cs 4)) w = SOME (n2w off) /\
   op_taint tm (Var (slot_copy_var cs 4)) = {}` by
    (gvs[] >> simp[copy_mul_ghost_frame] >>
     gvs[lookup_var_def, update_var_def, eval_operand_def, FLOOKUP_UPDATE]) >>
  qpat_x_assum `Gf = _` SUBST1_TAC >>
  qpat_x_assum `tnf = _` SUBST1_TAC >>
  qpat_x_assum `v = _` SUBST1_TAC >>
  irule typed_copy_loop_dynamic_offset_covers >> simp[] >>
  qexists `capacity` >> gvs[ptr_covers_inst_idx]
QED

Theorem copy_generated_destination_checks:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  root <> slot_copy_var cs 4 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5])
    (update_var (slot_copy_var cs 5) (a+n2w off) w) /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w
    (update_var (slot_copy_var cs 5) (a+n2w off) w) tm ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s Gf tnf
Proof
  strip_tac >>
  `op_taint tm (Var root) = {} /\
   op_taint tm (Var (slot_copy_var cs 4)) = {}` by
    (gvs[] >> simp[copy_mul_ghost_frame] >> fs[ptr_covers_def]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+6) MUL
     [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s = OK u` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+7) ADD
     [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w =
     OK (update_var (slot_copy_var cs 5) (a+n2w off) w)` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
                  eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst (cs.cs_next_id+6) MUL
     [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s` by
    (irule ptr_inst_ok_copy_arith >> simp[op_taint_def]) >>
  `ptr_inst_ok D lo 0 ctx fn H tm (mk_inst (cs.cs_next_id+7) ADD
     [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w` by
    (irule ptr_inst_ok_copy_arith >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  gvs[] >> simp[inst_seq_ptr_def]
QED

Theorem copy_generated_destination_ghost:
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := ix) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  v = update_var (slot_copy_var cs 5) (a+n2w off) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w v tm ==>
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 ==>
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    (gvs[] >> simp[copy_mul_ghost_frame]) >>
  `tnf.t_mem = tm.t_mem /\ tnf.t_stor = tm.t_stor /\
   tnf.t_trans = tm.t_trans /\ tnf.t_imm = tm.t_imm` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     simp[copy_len_binop_ghost_frame, copy_mk_immutable_taint]) >>
  fs[] >> rpt strip_tac >> gvs[] >>
  simp[copy_len_binop_ghost_frame, step_prov_other_output,
       step_taint_other_output, mk_inst_def]
QED

Theorem copy_generated_destination_execution:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ root <> slot_copy_var cs 4 ==>
  run_inst_seq
    [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s =
  OK (update_var (slot_copy_var cs 5) (a+n2w off)
        (update_var (slot_copy_var cs 4) (n2w off) s))
Proof
  strip_tac >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem copy_generated_destination_segment:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  off < capacity /\ off+32 <= capacity /\ w2n a+off < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 5) (a+n2w off)
          (update_var (slot_copy_var cs 4) (n2w off) s) /\
    run_inst_seq
      [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
       mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
       mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]]
      (s with vs_inst_idx := ix) Gf tnf) /\
    ptr_covers Gf tnf (slot_copy_var cs 5) t 32 /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var (slot_copy_var cs 4) (n2w off) s` >>
  qabbrev_tac `t = update_var (slot_copy_var cs 5) (a+n2w off) u` >>
  qabbrev_tac `H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u` >>
  qabbrev_tac `tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn` >>
  qabbrev_tac `Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) t` >>
  qabbrev_tac `tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) u t tm` >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  conj_tac >- simp[Abbr `t`, Abbr `u`] >>
  conj_tac >- (simp[Abbr `t`, Abbr `u`] >>
               irule copy_generated_destination_execution >> simp[]) >>
  conj_tac
  >- (gen_tac >> irule copy_generated_destination_checks >>
      simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, Abbr `u`, Abbr `H`, Abbr `tm`,
           copy_update_inst_idx, allocas_from_def, allocas_below_fmp_def] >>
      conj_tac
      >- (qexistsl [`a`, `off`] >> fs[lookup_var_def]) >>
      qexists `capacity` >> simp[]) >>
  rule_assum_tac (REWRITE_RULE[markerTheory.Abbrev_def]) >>
  `u = (u with vs_inst_idx := u.vs_inst_idx)` by simp[] >>
  conj_tac
  >- (drule_all copy_generated_destination_covers >> simp[]) >>
  drule_all copy_generated_destination_ghost >> simp[]
QED
