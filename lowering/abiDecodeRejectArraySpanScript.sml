(* Joint rejection at the capacity or scaled-span guard, after the count load. *)
Theory abiDecodeRejectArraySpan
Ancestors
  exprSimAbiDecodeArrayPrefix abiDecoderAbortReentry abiDecoderReentry
  stmtReasonLitFragMemory abiDecoderDynarrayBound abiDecoderGuard
  bodyPtrBopScalarSeq fragGasOriginPtr ptrDiscipline emitHelperProps
  loweringStateRelDefs venomExecSemantics venomState venomInst words list

(* Discharged by the local scalar lifts in the first-failure proof. *)
val guard_abort = ``
  !PG R A code B G tn ctx lo s func bb t.
    bop_scalar_seq R A code B /\
    (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq code s = Abort Revert_abort t ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn'))``;

val count_compare = ``
  !PG cnt n sa sb A func s cv G tn ctx lo.
    abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
    bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit (n2w n)} (emitted_insts sa sb) A /\
    fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
    eval_operand cnt s = SOME cv /\ abi_decoder_operand_live sa.cs_next_var cnt /\
    n < dimword(:256) /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    if w2n cv <= n then
      ?u G' tn'.
        u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
          FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_mem = tn.t_mem /\
        (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK u,G',tn'))
    else
      ?u G' tn'.
        u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
        u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
        (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (Abort Revert_abort u,G',tn'))``;

Theorem malformed_dynarray_span_abort[local]:
  ^guard_abort ==>
  abi_decode_dynarray_payload_guard head cnt stride hi sc = ((),sp) /\
  hi <> Lit 0w /\ fn_has_code sc sp func /\ sp.cs_current_bb = sc.cs_current_bb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sc sp) /\
  bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;Lit (n2w stride);hi}
    (emitted_insts sc sp) B /\
  eval_operand head s = SOME (n2w q) /\ eval_operand cnt s = SOME (n2w n) /\
  eval_operand hi s = SOME (n2w L) /\ q < dimword(:256) /\ L < dimword(:256) /\
  n*stride < dimword(:256) /\ L < q+n*stride /\
  EVERY (abi_decoder_operand_live sc.cs_next_var) [head;cnt;hi] /\
  (!op. op IN {head;cnt;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (mk_asm "guard_abort") >> strip_tac >> fs[EVERY_DEF] >>
  qabbrev_tac `clean = abi_decoder_prune_vars sc.cs_next_var s` >>
  `eval_operand head clean = SOME (n2w q) /\ eval_operand cnt clean = SOME (n2w n) /\
   eval_operand hi clean = SOME (n2w L) /\ fresh_vars_wrt sc clean` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  `?t. run_inst_seq (emitted_insts sc sp) clean = Abort Revert_abort t` by
    (irule abi_decode_dynarray_payload_guard_revert >> simp[] >>
     goal_assum (drule_at (Pat `abi_decode_dynarray_payload_guard _ _ _ _ _ = _`)) >>
     qexistsl_tac [`q`,`L`,`n`] >> simp[]) >>
  `?actual. run_inst_seq (emitted_insts sc sp) s = Abort Revert_abort actual` by
    (qunabbrev_tac `clean` >> metis_tac[abi_decoder_sequence_revert_reentry]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sc sp) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
     fs[inst_extends_def] >> drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  asm "guard_abort" (qspec_then `PG` irule) >> simp[] >>
  goal_assum (drule_at (Pat `bop_scalar_seq _ _ _ _`)) >>
  fs[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]
QED

Theorem malformed_dynarray_compare_span_abort:
  ^count_compare ==> ^guard_abort ==>
  abi_decode_le_guard cnt (Lit (n2w cap)) sl = ((),sc) /\
  abi_decode_dynarray_payload_guard head cnt stride hi sc = ((),sp) /\ hi <> Lit 0w /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sl sc) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sc sp) /\
  bop_scalar_seq {x | not_fresh_at sl x} {cnt;Lit (n2w cap)} (emitted_insts sl sc) A /\
  bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;Lit (n2w stride);hi}
    (emitted_insts sc sp) B /\
  fn_has_code sl sc func /\ fn_has_code sc sp func /\
  sp.cs_current_bb = sc.cs_current_bb /\ sc.cs_current_bb = sl.cs_current_bb /\
  sl.cs_next_var <= sc.cs_next_var /\
  eval_operand head s = SOME (n2w q) /\ eval_operand cnt s = SOME cv /\
  eval_operand hi s = SOME (n2w L) /\ q < dimword(:256) /\ L < dimword(:256) /\
  cap < dimword(:256) /\ (w2n cv <= cap ==> w2n cv*stride < dimword(:256) /\ L < q+w2n cv*stride) /\
  EVERY (abi_decoder_operand_live sl.cs_next_var) [head;cnt;hi] /\
  (!op. op IN {head;cnt;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sl.cs_current_bb /\ s.vs_inst_idx = LENGTH sl.cs_current_insts ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (mk_asm "count_compare") >> disch_then (mk_asm "guard_abort") >>
  strip_tac >> RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE[EVERY_DEF]) >>
  `op_prov G cnt = NONE /\ op_taint tn cnt = {}` by metis_tac[pred_setTheory.IN_INSERT] >>
  asm "count_compare" drule_all >>
  disch_then (qspec_then `PG` mp_tac) >>
  Cases_on `w2n cv <= cap` >> simp[] >> strip_tac >>
  rename1 `r = s with <|vs_vars := r.vs_vars; vs_inst_idx := _|>` >>
  `~r.vs_halted /\ r.vs_allocas = s.vs_allocas /\ r.vs_current_bb = sc.cs_current_bb /\
    r.vs_inst_idx = LENGTH sc.cs_current_insts /\ r.vs_labels = s.vs_labels /\
    r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
    r.vs_call_ctx = s.vs_call_ctx /\ r.vs_immutables = s.vs_immutables` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[]) >>
  `!op. abi_decoder_operand_live sl.cs_next_var op ==>
    eval_operand op r = eval_operand op s /\
    op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      GSYM not_fresh_at_def, eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[op_taint_def]) >>
  `EVERY (abi_decoder_operand_live sc.cs_next_var) [head;cnt;hi]` by
    (simp[EVERY_DEF] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `eval_operand head r = SOME (n2w q) /\ eval_operand cnt r = SOME (n2w (w2n cv)) /\
   eval_operand hi r = SOME (n2w L)` by metis_tac[n2w_w2n] >>
  `allocas_from lo r` by
    (qpat_assum `r.vs_allocas = s.vs_allocas`
       (fn th => PURE_REWRITE_TAC[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o PURE_REWRITE_RULE[allocas_from_def])) >>
  `w2n cv*stride < dimword(:256) /\ L < q+w2n cv*stride` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o SRULE [allocas_below_fmp_def])) >>
  asm "guard_abort" (drule_all o MATCH_MP malformed_dynarray_span_abort) >>
  disch_then (qspec_then `PG` (qx_choose_then `u` (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
