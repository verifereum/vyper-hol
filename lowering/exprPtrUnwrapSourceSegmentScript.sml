(* Source-address ADD followed by the generated storage/transient load. *)
Theory exprPtrUnwrapSourceSegment
Ancestors
  exprPtrUnwrapScalarSegments exprPtrUnwrapLoadSegment exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr fragExec
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map exprLoweringProps

Theorem copy_source_segment:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\ eval_operand counter s = SOME k /\
  op_taint tn src = {} /\ op_taint tn counter = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [src;counter] [addr];
      mk_inst lid load [Var addr] [value]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [src;counter] [addr];
       mk_inst lid load [Var addr] [value]] s Gf tnf /\
    t = update_var value (slot_copy_word load s (srcword+k))
          (update_var addr (srcword+k) s) /\
    op_taint tnf (Var value) =
      key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> addr /\ p <> value ==>
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> addr /\ p <> value /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> (
  mp_tac (Q.INST [`opc` |-> `ADD`, `tmp` |-> `addr`,
    `left` |-> `src`, `right` |-> `counter`,
    `x` |-> `srcword`, `y` |-> `k`] (SPEC_ALL copy_arith_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qabbrev_tac `u = update_var addr (srcword+k) s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand (Var addr) v = SOME (srcword+k) /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (fs[Abbr `v`, Abbr `u`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`arg` |-> `Var addr`, `out` |-> `value`,
    `G` |-> `Gm`, `id` |-> `lid`, `s` |-> `v`, `tn` |-> `tnm`,
    `key` |-> `srcword+k`] (SPEC_ALL copy_slot_load_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ v Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`,
    `update_var value (slot_copy_word load s (srcword+k)) u`] >>
  conj_tac
  >- (simp[Abbr `u`, run_inst_seq_def, step_inst_base_def,
        mk_inst_def, exec_pure2_def, exec_read1_def, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE, slot_copy_word_def, sload_def, tload_def,
        contract_storage_def, contract_transient_def]) >>
  conj_tac
  >- (irule inst_seq_ptr_cons_compose >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`Gm`, `u`, `tnm`] >>
      gvs[Abbr `v`, Abbr `u`, mk_inst_def, is_terminator_def]) >>
  gvs[Abbr `v`, Abbr `u`, copy_update_inst_idx, ptr_covers_inst_idx] >>
  gvs[slot_copy_word_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def, update_var_def] >>
  metis_tac[])
QED
