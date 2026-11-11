(* Concrete generated source prefix. Ghost endpoints remain explicit so
   consumers infer them from equations, rather than unpacking existentials. *)
Theory exprPtrUnwrapGeneratedSource
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapFrames exprPtrUnwrapCopyEdges typedCopyPtr
  slotCopyExecution copyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map exprLoweringProps decoderGhostFramePtr ghostPcTransportPtr

Theorem copy_generated_source_checks:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var (slot_copy_var cs 2) (a+k) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s u tn /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3])
    (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w) /\
  tnf = step_taint (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w
    (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w) tm ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s Gf tnf
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `op_taint tm (Var (slot_copy_var cs 2)) = {}` by
    (gvs[] >> simp[copy_len_binop_ghost_frame]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+4) ADD
     [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s = OK u` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
  `eval_operand (Var (slot_copy_var cs 2)) w = SOME (a+k)` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst (cs.cs_next_id+4) ADD
     [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s` by
    (irule ptr_inst_ok_copy_arith >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx fn H tm (mk_inst (cs.cs_next_id+5) load
     [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w` by
    (irule ptr_inst_ok_slot_load >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >>
     metis_tac[]) >>
  `step_inst_base (mk_inst (cs.cs_next_id+5) load
     [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w =
     OK (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w)` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
                  slot_copy_word_def, update_var_def, sload_def, tload_def,
                  contract_storage_def, contract_transient_def]) >>
  gvs[] >> simp[inst_seq_ptr_def]
QED

Theorem copy_generated_source_ghost:
  (load = SLOAD \/ load = TLOAD) /\
  u = update_var (slot_copy_var cs 2) (a+k) s /\
  w = u /\ 
  H = step_prov PG G (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s u tn /\
  v = update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w v tm ==>
  op_taint tnf (Var (slot_copy_var cs 3)) =
    key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (a+k) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 ==>
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    (gvs[] >> simp[copy_len_binop_ghost_frame, copy_mk_immutable_taint]) >>
  `eval_operand (Var (slot_copy_var cs 2)) w = SOME (a+k)` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint tnf (Var (slot_copy_var cs 3)) =
    key_taint (if load=SLOAD then tm.t_stor else tm.t_trans) (a+k)` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     irule slot_load_output_taint >> simp[]) >>
  `tnf.t_mem = tm.t_mem /\ tnf.t_stor = tm.t_stor /\
   tnf.t_trans = tm.t_trans /\ tnf.t_imm = tm.t_imm` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     irule slot_load_ghost_frame >> simp[]) >>
  fs[] >> rpt strip_tac >>
  gvs[] >> simp[step_prov_other_output, step_taint_other_output,
               copy_len_binop_ghost_frame, mk_inst_def]
QED

Theorem copy_generated_source_execution:
  (load=SLOAD \/ load=TLOAD) /\ eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k ==>
  run_inst_seq
    [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s =
  OK (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k))
       (update_var (slot_copy_var cs 2) (a+k) s))
Proof
  strip_tac >> gvs[] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
       slot_copy_word_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, sload_def, tload_def,
       contract_storage_def, contract_transient_def]
QED


Theorem copy_generated_source_segment:
  (load=SLOAD \/ load=TLOAD) /\ eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k))
       (update_var (slot_copy_var cs 2) (a+k) s) /\
    run_inst_seq
      [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
       mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
       mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]]
      (s with vs_inst_idx := ix) Gf tnf) /\
    op_taint tnf (Var (slot_copy_var cs 3)) =
      key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (a+k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qabbrev_tac `u = update_var (slot_copy_var cs 2) (a+k) s` >>
  qabbrev_tac `t = update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) u` >>
  qabbrev_tac `H = step_prov PG G (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) u` >>
  qabbrev_tac `tm = step_taint (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s u tn` >>
  qabbrev_tac `Gf = step_prov PG H (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) t` >>
  qabbrev_tac `tnf = step_taint (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) u t tm` >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  conj_tac >- simp[Abbr `t`, Abbr `u`] >>
  conj_tac >- (simp[Abbr `t`, Abbr `u`] >>
               irule copy_generated_source_execution >> simp[]) >>
  conj_tac
  >- (gen_tac >> irule copy_generated_source_checks >>
      simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, Abbr `u`, Abbr `H`, Abbr `tm`,
           copy_update_inst_idx, allocas_from_def, allocas_below_fmp_def,
           slot_copy_word_def, sload_def, tload_def,
           contract_storage_def, contract_transient_def]) >>
  rule_assum_tac (REWRITE_RULE[markerTheory.Abbrev_def]) >>
  irule copy_generated_source_ghost >> simp[] >>
  qexistsl [`PG`, `s`, `src`] >> simp[]
QED
