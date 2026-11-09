(* Fuel-free agreement of reached GAS events between a source and a target
   execution, composed along the finite execution rules.  Each relation
   compares the events at every pair of fuels whose results are the given
   non-error outcomes, so it needs no fuel bookkeeping. *)
Theory frameGasEvents
Ancestors gasEvents frameFiniteExecution venomExecSemantics venomState
  venomInst list arithmetic

Definition step_events_agree_def:
  step_events_agree C C' i s j t r r' <=>
    !owner k k'.
      step_inst k C i s = r /\ step_inst k' C' j t = r' /\
      (!e. r <> Error e) /\ (!e. r' <> Error e) ==>
      gas_events_step k' C' owner j t = gas_events_step k C owner i s
End

Definition block_events_agree_def:
  block_events_agree C C' bb s bb' t r r' <=>
    !owner k k'.
      exec_block k C bb s = r /\ exec_block k' C' bb' t = r' /\
      (!e. r <> Error e) /\ (!e. r' <> Error e) ==>
      gas_events_block k' C' owner bb' t = gas_events_block k C owner bb s
End

Definition run_events_agree_def:
  run_events_agree C C' fn s fn' t r r' <=>
    !k k'.
      run_blocks k C fn s = r /\ run_blocks k' C' fn' t = r' /\
      (!e. r <> Error e) /\ (!e. r' <> Error e) ==>
      gas_events_blocks k' C' fn' t = gas_events_blocks k C fn s
End

(* Simulation outcome relations strengthened with event agreement. *)
Definition events_OS_def:
  events_OS C C' OS q n qe m i s j t r r' <=>
    OS q n qe m i s j t r r' /\ step_events_agree C C' i s j t r r'
End

Definition events_OB_def:
  events_OB C C' OB q n qe m bb s bb' t r r' <=>
    OB q n qe m bb s bb' t r r' /\ block_events_agree C C' bb s bb' t r r'
End

Definition events_OutR_def:
  events_OutR C C' OutR q n qe m fn s fn' t r r' <=>
    OutR q n qe m fn s fn' t r r' /\ run_events_agree C C' fn s fn' t r r'
End

(* A finite derivation fixes the result at every fuel that does not fail. *)
Theorem step_inst_finite_eq:
  finite_step C i s r /\ (!e. step_inst k C i s <> Error e) ==>
  step_inst k C i s = r
Proof
  rpt strip_tac >>
  `finite_step C i s (step_inst k C i s)` by
    metis_tac[cj 1 finite_execution_complete] >>
  `?n1. !m. n1 <= m ==> step_inst m C i s = r` by
    metis_tac[cj 1 finite_execution_realizable] >>
  `?n2. !m. n2 <= m ==> step_inst m C i s = step_inst k C i s` by
    metis_tac[cj 1 finite_execution_realizable] >>
  `n1 <= n1 + n2 /\ n2 <= n1 + n2` by decide_tac >> metis_tac[]
QED

Theorem exec_block_finite_eq:
  finite_block C bb s r /\ (!e. exec_block k C bb s <> Error e) ==>
  exec_block k C bb s = r
Proof
  rpt strip_tac >>
  `finite_block C bb s (exec_block k C bb s)` by
    metis_tac[cj 2 finite_execution_complete] >>
  `?n1. !m. n1 <= m ==> exec_block m C bb s = r` by
    metis_tac[cj 2 finite_execution_realizable] >>
  `?n2. !m. n2 <= m ==> exec_block m C bb s = exec_block k C bb s` by
    metis_tac[cj 2 finite_execution_realizable] >>
  `n1 <= n1 + n2 /\ n2 <= n1 + n2` by decide_tac >> metis_tac[]
QED

Theorem run_blocks_finite_eq:
  finite_run C fn s r /\ (!e. run_blocks k C fn s <> Error e) ==>
  run_blocks k C fn s = r
Proof
  rpt strip_tac >>
  `finite_run C fn s (run_blocks k C fn s)` by
    metis_tac[cj 3 finite_execution_complete] >>
  `?n1. !m. n1 <= m ==> run_blocks m C fn s = r` by
    metis_tac[cj 3 finite_execution_realizable] >>
  `?n2. !m. n2 <= m ==> run_blocks m C fn s = run_blocks k C fn s` by
    metis_tac[cj 3 finite_execution_realizable] >>
  `n1 <= n1 + n2 /\ n2 <= n1 + n2` by decide_tac >> metis_tac[]
QED

(* One-step unfoldings at a known instruction or block. *)
Theorem exec_block_at:
  get_instruction bb s.vs_inst_idx = SOME i ==>
  exec_block k C bb s =
    case step_inst k C i s of
      OK p =>
        if is_terminator i.inst_opcode then
          if p.vs_halted then Halt p else OK p
        else exec_block k C bb (p with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v p => IntRet v p
    | Halt p => Halt p
    | Abort a p => Abort a p
    | Error e => Error e
Proof
  strip_tac >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[]
QED

Theorem gas_events_block_at:
  get_instruction bb s.vs_inst_idx = SOME i ==>
  gas_events_block k C owner bb s =
    gas_events_step k C owner i s ++
    case step_inst k C i s of
      OK p =>
        if is_terminator i.inst_opcode then []
        else gas_events_block k C owner bb
               (p with vs_inst_idx := SUC s.vs_inst_idx)
    | _ => []
Proof
  strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_events_block_def])) >>
  simp[]
QED

Theorem run_blocks_at:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi ==>
  run_blocks (SUC n) C fn s =
    case exec_block n C bb
           (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
      OK p => if p.vs_halted then Halt p else run_blocks n C fn p
    | IntRet v p => IntRet v p
    | Halt p => Halt p
    | Abort a p => Abort a p
    | Error e => Error e
Proof
  strip_tac >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  simp[] >> CASE_TAC >> simp[]
QED

Theorem gas_events_blocks_at:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi ==>
  gas_events_blocks (SUC n) C fn s =
    gas_events_block n C fn.fn_name bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
    case exec_block n C bb
           (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
      OK p => if p.vs_halted then [] else gas_events_blocks n C fn p
    | _ => []
Proof
  strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >>
  simp[]
QED

Theorem exec_block_step_nonerror:
  get_instruction bb s.vs_inst_idx = SOME i /\
  (!e. exec_block k C bb s <> Error e) ==>
  !e. step_inst k C i s <> Error e
Proof
  rpt strip_tac >> imp_res_tac exec_block_at >> gvs[]
QED

Theorem run_blocks_block_nonerror:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  (!e. run_blocks (SUC n) C fn s <> Error e) ==>
  !e. exec_block n C bb
        (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) <>
      Error e
Proof
  rpt strip_tac >> imp_res_tac run_blocks_at >> gvs[]
QED

Theorem run_blocks_zero_error:
  run_blocks 0 C fn s = Error "out of fuel"
Proof
  simp[Once run_blocks_def]
QED

Theorem lookup_function_fn_name:
  !fns name fn. lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  Cases_on `h.fn_name = name` >> gvs[lookup_function_def]
QED

(* Steps. *)
Theorem gas_events_step_plain:
  i.inst_opcode <> INVOKE ==>
  gas_events_step k C owner i s =
    if i.inst_opcode = GAS then [(owner,i.inst_id)] else []
Proof
  simp[gas_events_step_def]
QED

Theorem step_events_agree_plain:
  i.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE /\
  (j.inst_opcode = GAS <=> i.inst_opcode = GAS) /\
  (i.inst_opcode = GAS ==> j.inst_id = i.inst_id) ==>
  step_events_agree C C' i s j t r r'
Proof
  rw[step_events_agree_def, gas_events_step_plain]
QED

Theorem step_events_agree_invoke:
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  finite_run C fn cs rcb /\
  j.inst_opcode = INVOKE /\ decode_invoke j = SOME (name',ops') /\
  lookup_function name' C'.ctx_functions = SOME fn' /\
  eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
  finite_run C' fn' ct rcb' /\
  run_events_agree C C' fn cs fn' ct rcb rcb' ==>
  step_events_agree C C' i s j t r r'
Proof
  rpt strip_tac >> simp[step_events_agree_def] >> rpt strip_tac >>
  simp[gas_events_step_def] >>
  `!e. run_blocks k C fn cs <> Error e` by
    (rpt strip_tac >> qpat_x_assum `step_inst k C i s = r` mp_tac >>
     simp[step_inst_def]) >>
  `!e. run_blocks k' C' fn' ct <> Error e` by
    (rpt strip_tac >> qpat_x_assum `step_inst k' C' j t = r'` mp_tac >>
     simp[step_inst_def]) >>
  `run_blocks k C fn cs = rcb /\ run_blocks k' C' fn' ct = rcb'` by
    metis_tac[run_blocks_finite_eq] >>
  qpat_x_assum `run_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [run_events_agree_def]) >>
  disch_then (qspecl_then [`k`, `k'`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[]
QED

(* Blocks. *)
Theorem block_events_agree_term:
  get_instruction bb s.vs_inst_idx = SOME i /\ finite_step C i s (OK p) /\
  is_terminator i.inst_opcode /\
  get_instruction bb' t.vs_inst_idx = SOME j /\ finite_step C' j t (OK p') /\
  is_terminator j.inst_opcode /\
  step_events_agree C C' i s j t (OK p) (OK p') ==>
  block_events_agree C C' bb s bb' t r r'
Proof
  rpt strip_tac >> simp[block_events_agree_def] >> rpt strip_tac >>
  `step_inst k C i s = OK p /\ step_inst k' C' j t = OK p'` by
    metis_tac[step_inst_finite_eq, exec_block_step_nonerror] >>
  qpat_x_assum `step_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [step_events_agree_def]) >>
  disch_then (qspecl_then [`owner`, `k`, `k'`] mp_tac) >> simp[] >>
  strip_tac >> imp_res_tac gas_events_block_at >> simp[]
QED

Theorem block_events_agree_next:
  get_instruction bb s.vs_inst_idx = SOME i /\ finite_step C i s (OK p) /\
  ~is_terminator i.inst_opcode /\
  get_instruction bb' t.vs_inst_idx = SOME j /\ finite_step C' j t (OK p') /\
  ~is_terminator j.inst_opcode /\
  step_events_agree C C' i s j t (OK p) (OK p') /\
  block_events_agree C C' bb (p with vs_inst_idx := SUC s.vs_inst_idx)
    bb' (p' with vs_inst_idx := SUC t.vs_inst_idx) r r' ==>
  block_events_agree C C' bb s bb' t r r'
Proof
  rpt strip_tac >> simp[block_events_agree_def] >> rpt strip_tac >>
  `step_inst k C i s = OK p /\ step_inst k' C' j t = OK p'` by
    metis_tac[step_inst_finite_eq, exec_block_step_nonerror] >>
  qpat_x_assum `step_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [step_events_agree_def]) >>
  disch_then (qspecl_then [`owner`, `k`, `k'`] mp_tac) >> simp[] >>
  strip_tac >>
  qpat_x_assum `block_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [block_events_agree_def]) >>
  disch_then (qspecl_then [`owner`, `k`, `k'`] mp_tac) >>
  impl_tac
  >- (rpt (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac) >>
      imp_res_tac exec_block_at >> simp[]) >>
  strip_tac >> imp_res_tac gas_events_block_at >> simp[]
QED

(* A source step the target does not take: no events, same target state. *)
Theorem block_events_agree_skip:
  get_instruction bb s.vs_inst_idx = SOME i /\ finite_step C i s (OK p) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
  i.inst_opcode <> INVOKE /\
  block_events_agree C C' bb (p with vs_inst_idx := SUC s.vs_inst_idx)
    bb' t r r' ==>
  block_events_agree C C' bb s bb' t r r'
Proof
  rpt strip_tac >> simp[block_events_agree_def] >> rpt strip_tac >>
  `step_inst k C i s = OK p` by
    metis_tac[step_inst_finite_eq, exec_block_step_nonerror] >>
  qpat_x_assum `block_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [block_events_agree_def]) >>
  disch_then (qspecl_then [`owner`, `k`, `k'`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `exec_block k C bb s = _` mp_tac >>
      imp_res_tac exec_block_at >> simp[]) >>
  strip_tac >> imp_res_tac gas_events_block_at >>
  simp[gas_events_step_plain]
QED

Theorem block_events_agree_exit:
  get_instruction bb s.vs_inst_idx = SOME i /\ finite_step C i s r /\
  (!p. r <> OK p) /\
  get_instruction bb' t.vs_inst_idx = SOME j /\ finite_step C' j t r' /\
  (!p. r' <> OK p) /\
  step_events_agree C C' i s j t r r' ==>
  block_events_agree C C' bb s bb' t r r'
Proof
  rpt strip_tac >> simp[block_events_agree_def] >> rpt strip_tac >>
  `step_inst k C i s = r /\ step_inst k' C' j t = r'` by
    metis_tac[step_inst_finite_eq, exec_block_step_nonerror] >>
  qpat_x_assum `step_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [step_events_agree_def]) >>
  disch_then (qspecl_then [`owner`, `k`, `k'`] mp_tac) >> simp[] >>
  strip_tac >> imp_res_tac gas_events_block_at >> simp[] >>
  Cases_on `r` >> Cases_on `r'` >> gvs[]
QED

(* Runs. *)
Theorem run_blocks_nonerror_suc:
  (!e. run_blocks k C fn s <> Error e) ==> ?n. k = SUC n
Proof
  Cases_on `k` >> simp[run_blocks_zero_error]
QED

Theorem run_events_agree_next:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  finite_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (OK post) /\ ~post.vs_halted /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\
  finite_block C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    (OK post') /\ ~post'.vs_halted /\
  fn'.fn_name = fn.fn_name /\
  block_events_agree C C' bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    (OK post) (OK post') /\
  run_events_agree C C' fn post fn' post' r r' ==>
  run_events_agree C C' fn s fn' t r r'
Proof
  rpt strip_tac >> simp[run_events_agree_def] >>
  rpt strip_tac >>
  `?n. k = SUC n` by metis_tac[run_blocks_nonerror_suc] >>
  `?n'. k' = SUC n'` by metis_tac[run_blocks_nonerror_suc] >>
  rpt (qpat_x_assum `_ = SUC _` SUBST_ALL_TAC) >>
  `exec_block n C bb
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   OK post` by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  `exec_block n' C' bb'
     (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) =
   OK post'` by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  `run_blocks n C fn post = r /\ run_blocks n' C' fn' post' = r'` by
    (rpt (qpat_x_assum `run_blocks (SUC _) _ _ _ = _` mp_tac) >>
     imp_res_tac run_blocks_at >> simp[]) >>
  qpat_x_assum `run_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [run_events_agree_def]) >>
  disch_then (qspecl_then [`n`, `n'`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qpat_x_assum `block_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [block_events_agree_def]) >>
  disch_then (qspecl_then [`fn.fn_name`, `n`, `n'`] mp_tac) >> simp[] >>
  strip_tac >> imp_res_tac gas_events_blocks_at >> simp[]
QED

Theorem run_events_agree_halt:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  finite_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (OK post) /\ post.vs_halted /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\
  finite_block C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    (OK post') /\ post'.vs_halted /\
  fn'.fn_name = fn.fn_name /\
  block_events_agree C C' bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    (OK post) (OK post') ==>
  run_events_agree C C' fn s fn' t r r'
Proof
  rpt strip_tac >> simp[run_events_agree_def] >> rpt strip_tac >>
  `?n. k = SUC n` by metis_tac[run_blocks_nonerror_suc] >>
  `?n'. k' = SUC n'` by metis_tac[run_blocks_nonerror_suc] >>
  rpt (qpat_x_assum `_ = SUC _` SUBST_ALL_TAC) >>
  `exec_block n C bb
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   OK post` by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  `exec_block n' C' bb'
     (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) =
   OK post'` by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  qpat_x_assum `block_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [block_events_agree_def]) >>
  disch_then (qspecl_then [`fn.fn_name`, `n`, `n'`] mp_tac) >> simp[] >>
  strip_tac >> imp_res_tac gas_events_blocks_at >> simp[]
QED

Theorem run_events_agree_exit:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  finite_block C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) rb /\
  (!p. rb <> OK p) /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\
  finite_block C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) rb' /\
  (!p. rb' <> OK p) /\
  fn'.fn_name = fn.fn_name /\
  block_events_agree C C' bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    rb rb' ==>
  run_events_agree C C' fn s fn' t r r'
Proof
  rpt strip_tac >> simp[run_events_agree_def] >> rpt strip_tac >>
  `?n. k = SUC n` by metis_tac[run_blocks_nonerror_suc] >>
  `?n'. k' = SUC n'` by metis_tac[run_blocks_nonerror_suc] >>
  rpt (qpat_x_assum `_ = SUC _` SUBST_ALL_TAC) >>
  `exec_block n C bb
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = rb`
    by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  `exec_block n' C' bb'
     (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = rb'`
    by metis_tac[exec_block_finite_eq, run_blocks_block_nonerror] >>
  `(!e. rb <> Error e) /\ (!e. rb' <> Error e)` by
    metis_tac[cj 2 finite_execution_nonerror] >>
  qpat_x_assum `block_events_agree _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [block_events_agree_def]) >>
  disch_then (qspecl_then [`fn.fn_name`, `n`, `n'`] mp_tac) >> simp[] >>
  strip_tac >> imp_res_tac gas_events_blocks_at >> simp[] >>
  Cases_on `rb` >> Cases_on `rb'` >> gvs[]
QED

val _ = export_theory();
