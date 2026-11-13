(* Instruction-level probes for the top-level copy interface. *)
Theory exprSimPtrTopLevelCopy
Ancestors
  decoderGhostFramePtr fragGasSeqPtr typedCopyPtr ptrDiscipline bodyPtrDefs contextCodegenRel contextCodegenRelProps codegenRel memLocDefs ptrSafeRun words
  venomExecSemantics venomInst venomState finite_map pred_set list

Theorem toplevel_storage_load_taint:
  eval_operand src s = SOME a ==>
  op_taint (step_taint (mk_inst id SLOAD [src] [tmp]) s t tn)
    (Var tmp) = key_taint tn.t_stor a
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem toplevel_code_load_taint:
  op_taint (step_taint (mk_inst id DLOAD [src] [tmp]) s t tn)
    (Var tmp) = {}
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand src s` >> simp[]
QED

Theorem toplevel_load_preserves_destination:
  tmp <> dst /\ ptr_covers G tn dst s n /\
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) ==>
  ptr_covers
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    dst (update_var tmp w s) n
Proof
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* The storage value may be tainted; a store only requires a clean address. *)
Theorem toplevel_store_taint_ok:
  op_taint tn dst = {} ==>
  taint_ok fn tn (mk_inst id MSTORE [dst; value] []) s
Proof
  simp[taint_ok_def, mk_inst_def, source_memory_read_ranges_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem toplevel_load_store_taint_ok:
  tmp <> dst /\ op_taint tn (Var dst) = {} ==>
  taint_ok fn
    (step_taint (mk_inst id opc [src] [tmp]) s t tn)
    (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) t
Proof
  strip_tac >> irule toplevel_store_taint_ok >>
  simp[step_taint_other_output, mk_inst_def]
QED

(* Unlike the existing clean-store boundary, storage copying permits a
   tainted value.  Only its destination address must be clean. *)
Theorem toplevel_ptr_inst_ok_mstore:
  !G tn p s ctx D fuel fn id v.
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; v] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem toplevel_ptr_inst_ok_load:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [src] [tmp]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem toplevel_load_store_checks:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn dst s 32 /\ tmp <> dst ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [src] [tmp]) s /\
  ptr_inst_ok D 0 fuel ctx fn
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) (update_var tmp w s)
Proof
  metis_tac[toplevel_ptr_inst_ok_load, toplevel_ptr_inst_ok_mstore,
            toplevel_load_preserves_destination]
QED

(* A checked two-instruction sequence, with the actual index-adjusted
   state used by the counted runner at the store. *)
Theorem toplevel_load_store_seq_ptr:
  !opc tn src ctx G dst s tmp i j u w PG G1 tn1 u1 t Gf tnf D fn.
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn dst s 32 /\ tmp <> dst /\
  i = mk_inst id opc [src] [tmp] /\
  j = mk_inst (id+1) MSTORE [Var dst; Var tmp] [] /\
  u = update_var tmp w s /\ step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base j u1 = OK t /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 ==>
  inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G1 tn1 dst u 32` by
    metis_tac[toplevel_load_preserves_destination] >>
  `ptr_covers G1 tn1 dst u1 32` by
    gvs[ptr_covers_def, lookup_var_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    metis_tac[toplevel_ptr_inst_ok_load] >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 j u1` by
    metis_tac[toplevel_ptr_inst_ok_mstore] >>
  gvs[] >> simp[inst_seq_ptr_def]
QED

Theorem toplevel_load_store_counted_ptr:
  !opc tn src ctx G dst s tmp i j u w PG G1 tn1 u1 t Gf tnf D fn bb r.
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn dst s 32 /\ tmp <> dst /\
  i = mk_inst id opc [src] [tmp] /\
  j = mk_inst (id+1) MSTORE [Var dst; Var tmp] [] /\
  u = update_var tmp w s /\ step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base j u1 = OK t /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [i;j] s = OK r ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (r with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf` by
    metis_tac[toplevel_load_store_seq_ptr] >>
  `EVERY (\k. k.inst_opcode <> INVOKE /\ ~is_terminator k.inst_opcode)
     [i;j] /\ LENGTH (FILTER (\k. k.inst_opcode = GAS) [i;j]) = 0` by
    (gvs[mk_inst_def, is_terminator_def] >> rpt strip_tac >> gvs[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
