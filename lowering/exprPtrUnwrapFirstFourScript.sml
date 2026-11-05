(* Composition of source and covered destination address pairs. *)
Theory exprPtrUnwrapFirstFour
Ancestors
  exprPtrUnwrapSourceSegment exprPtrUnwrapDestinationSegment exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr
  fragExec bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState finite_map exprLoweringProps instIdxIndep list

Theorem copy_first_four_segment:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\ eval_operand counter s = SOME k /\
  op_taint tn src = {} /\ op_taint tn counter = {} /\
  counter <> Var addr /\ counter <> Var value /\
  root <> addr /\ root <> value /\ root <> tmp /\ root <> out /\
  value <> tmp /\ value <> out /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off + n <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [src;counter] [addr];
      mk_inst lid load [Var addr] [value];
      mk_inst mid MUL [counter;Lit 32w] [tmp];
      mk_inst aid ADD [Var root;Var tmp] [out]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [src;counter] [addr];
       mk_inst lid load [Var addr] [value];
       mk_inst mid MUL [counter;Lit 32w] [tmp];
       mk_inst aid ADD [Var root;Var tmp] [out]] s Gf tnf /\
    t = update_var out (a+n2w off) (update_var tmp (n2w off)
      (update_var value (slot_copy_word load s (srcword+k))
        (update_var addr (srcword+k) s))) /\
    ptr_covers Gf tnf out t n /\
    op_taint tnf (Var value) =
      key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> addr /\ p <> value /\ p <> tmp /\ p <> out ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> addr /\ p <> value /\ p <> tmp /\ p <> out /\
      ptr_covers G tn p s c ==> ptr_covers Gf tnf p t c)
Proof
  strip_tac >> (
  mp_tac (SPEC_ALL copy_source_segment) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qabbrev_tac `u = update_var value (slot_copy_word load s (srcword+k))
    (update_var addr (srcword+k) s)` >>
  qabbrev_tac `v = u with vs_inst_idx := s.vs_inst_idx + 2` >>
  `eval_operand counter v = SOME k /\ op_taint tnm counter = {} /\
   lookup_var root v = SOME a /\ ptr_covers Gm tnm root v capacity /\
   allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (Cases_on `counter` >>
     fs[Abbr `v`, Abbr `u`, slot_copy_operand_update, eval_operand_def,
        op_taint_def, ptr_covers_inst_idx, lookup_var_def, update_var_def,
        FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `v`, `G` |-> `Gm`, `tn` |-> `tnm`,
    `id` |-> `mid`] (SPEC_ALL copy_destination_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ v Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`, `update_var out (a+n2w off) (update_var tmp (n2w off) u)`] >>
  conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `[mk_inst mid MUL [counter;Lit 32w] [tmp];
        mk_inst aid ADD [Var root;Var tmp] [out]]` mp_tac) >>
      simp[] >> disch_then SUBST1_TAC >>
      qpat_assum `lookup_var root s = SOME a`
        (assume_tac o REWRITE_RULE [lookup_var_def]) >>
      simp[Abbr `u`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
        exec_pure2_def, slot_copy_operand_update, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule (SRULE [] (Q.INST
        [`prefix` |-> `[mk_inst id ADD [src;counter] [addr];
                       mk_inst lid load [Var addr] [value]]`]
        (SPEC_ALL inst_seq_ptr_append))) >>
      simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`Gm`, `tnm`] >>
      gvs[Abbr `v`, mk_inst_def, is_terminator_def]) >>
  gvs[Abbr `v`, copy_update_inst_idx, ptr_covers_inst_idx,
      allocas_from_def, allocas_below_fmp_def] >> metis_tac[])
QED
