Theory readonlyInvokeCopyFwdStepsLog
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdRel
  taintAgree venomState venomExecSemantics internalReturnCopyFwdSim
  ptrDiscipline finite_map words list pred_set

(* Append to the live logs, including when viewing a suspended caller.
   No historical saved memory is identified with the current memory. *)
Theorem ricf_frame_logs_append:
  ricf_frame_agree D X sites PG H tn s t ==>
  ricf_frame_agree D X sites PG H tn
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  strip_tac >>
  `taint_agree D X tn
    (s with vs_logs := s.vs_logs ++ [ev])
    ((t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)
      with vs_logs := t.vs_logs ++ [ev])` by
    (fs[ricf_frame_agree_def] >>
     drule taint_agree_logs_append >>
     disch_then (qspec_then `ev` mp_tac) >> simp[]) >>
  fs[ricf_frame_agree_def] >>
  simp[ricf_frame_agree_def, ircf_cross_def, op_taint_def] >>
  gvs[ircf_cross_def]
QED

Theorem ricf_cert_logs_append:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (s with vs_logs := s.vs_logs ++ [ev]) H)
    (ricf_effective_taint fn (s with vs_logs := s.vs_logs ++ [ev]) un) fn
    sites maps targets H un cur curs
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >- (drule ricf_frame_logs_append >> disch_then (qspec_then `ev` mp_tac) >>
      simp[ircf_dead_def]) >>
  fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_frame_logs_append >> disch_then (qspec_then `ev` mp_tac) >>
  simp[merge_callee_state_def]
QED

(* Physical LOG tails are reversed.  The addresses may be relocated;
   the consumer supplies equality of the actual bytes and scalar topics. *)
Theorem ricf_cert_step_log:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_opcode = LOG /\ ti.inst_opcode = LOG /\
  inst.inst_outputs = [] /\ ti.inst_outputs = [] /\
  inst.inst_operands = Lit tc :: REVERSE (addr::len::tops) /\
  ti.inst_operands = Lit tc :: REVERSE (taddr::tlen::ttops) /\
  LENGTH tops = w2n tc /\ LENGTH ttops = w2n tc /\
  eval_operand addr s = SOME p /\ eval_operand taddr t = SOME r /\
  eval_operand len s = SOME n /\ eval_operand tlen t = SOME n /\
  eval_operands tops s = SOME topics /\ eval_operands ttops t = SOME topics /\
  read_memory (w2n p) (w2n n) s = read_memory (w2n r) (w2n n) t /\
  ~s.vs_call_ctx.cc_static /\ ~t.vs_call_ctx.cc_static /\
  ev = <|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := read_memory (w2n p) (w2n n) s|> ==>
  step_inst_base inst s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
  step_inst_base ti t = OK (t with vs_logs := t.vs_logs ++ [ev]) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (s with vs_logs := s.vs_logs ++ [ev]) H)
    (ricf_effective_taint fn (s with vs_logs := s.vs_logs ++ [ev]) un) fn
    sites maps targets H un cur curs
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def] >>
     drule taint_agree_call_ctx >> simp[]) >>
  reverse (rpt conj_tac)
  >- metis_tac[ricf_cert_logs_append] >>
  simp[step_inst_base_opcode_eqs, REVERSE_APPEND, GSYM read_memory_def] >>
  gvs[]
QED
