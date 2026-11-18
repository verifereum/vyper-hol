(* Local merge-iszero boundary checks.  No pending symbolic relation is used. *)
Theory staticAbortOptMergeIszeroBoundaryProbe
Ancestors
  staticAbortTrace stackOpAsmSim stackOpSim asmOptMergeIszero
  asmOptOwnMergeIszero asmSymBridge asmSymPc asmSem asmIR asmOptimizer list words

Theorem static_abort_merge_iszero_destination_branch:
  asm_block_at q s.as_pc [AsmPushLabel l; AsmOp "JUMPI"] /\
  s.as_stack = w::stk /\ FLOOKUP lo l = SOME off /\
  FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest ==>
  static_abort_normal lo o2pc q 2 s
    (s with <|as_stack := stk;
       as_pc := if w = 0w then s.as_pc + 2 else dest|>)
Proof
  strip_tac >> gvs[asm_block_at_cons] >>
  `!u. asm_step_op o2pc "JUMPI" u = asm_jumpi o2pc u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_jumpi``])) >> simp[]) >>
  simp[static_abort_normal_def] >> conj_tac
  >- (rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_def, asm_step_jumpi, asm_jumpi_def,
           asm_next_def] >>
      Cases_on `w = 0w` >> simp[]) >>
  simp[static_abort_trace_def] >> rpt gen_tac >> strip_tac >>
  `k = 0 \/ k = 1` by decide_tac >> gvs[]
  >- (simp[static_abort_safe_at_def] >> EVAL_TAC) >>
  qpat_x_assum `asm_steps _ _ _ 1 _ = _` mp_tac >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_def, asm_next_def] >> strip_tac >>
  gvs[static_abort_safe_at_def] >> EVAL_TAC
QED

(* The eliminated source window is ISZERO;ISZERO;PUSHLABEL;JUMPI.
   At the destination it is PUSHLABEL;JUMPI.  Neither arbitrary w nor
   either exit is discarded.  Continuations include any required tags
   through D; requests, height and call context are retained explicitly. *)
Theorem static_abort_merge_iszero_pending_exits:
  q = pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  s.as_pc = LENGTH pre /\ s.as_stack = w::stk /\
  FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
  off < dimword(:256) /\
  FLOOKUP (build_offset_to_pc q) off = SOME dest /\
  (!t. t.as_pc = LENGTH pre + 2 /\ t.as_stack = stk /\
       t.as_call_ctx = s.as_call_ctx /\ t.as_requests = s.as_requests ==>
       ?r'. r' < r /\ D r' t) /\
  (!t. t.as_pc = dest /\ t.as_stack = stk /\
       t.as_call_ctx = s.as_call_ctx /\ t.as_requests = s.as_requests ==>
       ?r'. r' < r /\ D r' t) ==>
  ?r' t. r' < r /\
    static_abort_normal (SND (compute_label_offsets q))
      (build_offset_to_pc q) q 2 s t /\ D r' t
Proof
  strip_tac >>
  `asm_block_at q s.as_pc [AsmPushLabel l; AsmOp "JUMPI"]` by
    (gvs[asm_block_at_def, listTheory.EL_APPEND_EQN] >>
     rpt strip_tac >> `j = 0 \/ j = 1` by decide_tac >> gvs[]) >>
  `FLOOKUP (build_offset_to_pc q) (w2n (n2w off : bytes32)) = SOME dest`
    by gvs[] >>
  drule_all static_abort_merge_iszero_destination_branch >>
  strip_tac >> Cases_on `w = 0w` >> gvs[]
  >- (qpat_x_assum `!t. t.as_pc = LENGTH pre + 2 /\ _ ==> _`
        (qspec_then `s with <|as_stack := stk; as_pc := LENGTH pre + 2|>` mp_tac) >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `!t. t.as_pc = dest /\ _ ==> _`
    (qspec_then `s with <|as_stack := stk; as_pc := dest|>` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Two REAL code arguments.  The ordinary one-step bridge can be used for
   a Boolean X (including successful calls); a whole own-code refinement
   instead quantifies one fixed own byte sequence on both sides. *)
Theorem static_abort_merge_iszero_protected_real_code:
  p = pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail /\
  q = pre ++ [x] ++ tail /\ asm_returns_zero_or_one x /\
  asm_static_wf p /\ asm_static_wf q /\
  cs.as_pc = LENGTH pre /\ ds.as_pc = LENGTH pre /\
  asm_sym_rel p env (cs with as_code := assemble p ++ data) ss /\
  asm_sym_rel q env (ds with as_code := assemble q ++ data) ss /\
  sym_step p env x ss = SymOK out ==>
  (?w stk. out.sym_stack = Val w::stk /\ (w = 0w \/ w = 1w)) /\
  (?ct dt.
    asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) x
      (cs with as_code := assemble p ++ data) = AsmOK ct /\
    asm_sym_rel p env ct out /\
    asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q) x
      (ds with as_code := assemble q ++ data) = AsmOK dt /\
    asm_sym_rel q env dt out)
Proof
  strip_tac >> conj_tac
  >- metis_tac[sym_step_zero_or_one] >>
  `x <> AsmOp "JUMP" /\ x <> AsmOp "JUMPI"` by
    gvs[asm_returns_zero_or_one_def] >>
  `sym_step p env x ss = sym_step q env x ss` by
    (irule sym_step_prog_cong >> gvs[]) >>
  `cs.as_pc < LENGTH p /\ EL cs.as_pc p = x /\
   ds.as_pc < LENGTH q /\ EL ds.as_pc q = x` by
    simp[listTheory.EL_APPEND_EQN] >>
  `(cs with as_code := assemble p ++ data).as_pc < LENGTH p /\
   (ds with as_code := assemble q ++ data).as_pc < LENGTH q` by simp[] >>
  (* E0025's failed route was drule_all asm_sym_step; simp; strip_tac;
     rev_drule_all asm_sym_step; simp; metis.  It expanded p/q without
     normalizing the fetched instructions and symbolic results first. *)
  `sym_step q env x ss = SymOK out` by metis_tac[] >>
  qpat_x_assum `p = _` kall_tac >> qpat_x_assum `q = _` kall_tac >>
  `asm_sym_step_rel p env (SymOK out)
    (asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) x
      (cs with as_code := assemble p ++ data))` by
    (qpat_x_assum `asm_static_wf q` kall_tac >>
     drule_all asm_sym_step >> gvs[]) >>
  `asm_sym_step_rel q env (SymOK out)
    (asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q) x
      (ds with as_code := assemble q ++ data))` by
    (qpat_x_assum `asm_static_wf p` kall_tac >>
     drule_all asm_sym_step >> gvs[]) >>
  gvs[asm_sym_step_rel_def] >> metis_tac[]
QED
