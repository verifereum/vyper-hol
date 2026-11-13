Theory bodyPtrPrecompileBuiltinsSuffixPaths
Ancestors bodyPtrPrecompileBuiltinsSuffixGhost fragGasSeqPtr fragGasPathPtr
          exprSimPrecompiles venomInst venomState venomExecSemantics
          compileEnv loweringStateRelDefs exprLoweringProps list

Theorem suffix_normal_path:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  (?G' tn'. inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s G' tn') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [gi;ci;ai] s = OK t ==>
  gas_path_ptr D lo ctx fn PG G tn s 1
    (step_prov PG (step_prov PG G gi u) ci v)
    (step_taint ci u v (step_taint gi s u tn))
    (OK (t with vs_inst_idx := s.vs_inst_idx + 3))
Proof
  strip_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s
    (step_prov PG (step_prov PG G gi u) ci v)
    (step_taint ci u v (step_taint gi s u tn))` by
    (irule suffix_checked_ghost >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [gi;ci;ai]` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def]
QED

Theorem suffix_revert_path:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  (?G' tn'. inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s G' tn') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [gi;ci;ai] s = Abort Revert_abort t ==>
  ?n j. gas_path_ptr D lo ctx fn PG G tn s n
    (step_prov PG (step_prov PG G gi u) ci v)
    (step_taint ci u v (step_taint gi s u tn))
    (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s
    (step_prov PG (step_prov PG G gi u) ci v)
    (step_taint ci u v (step_taint gi s u tn))` by
    (irule suffix_checked_ghost >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [gi;ci;ai]` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_abort_gas_path_ptr >> simp[]
QED

Theorem computed_emitted_suffix_paths:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  ptr_covers G tn src s (w2n insz) /\ ptr_covers G tn dst s (w2n outsz) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u v G' tn'.
    step_inst_base (EL 0 (emitted_insts sm sb)) s = OK u /\
    step_inst_base (EL 1 (emitted_insts sm sb)) u = OK v /\
    G' = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sb)) u)
          (EL 1 (emitted_insts sm sb)) v /\
    tn' = step_taint (EL 1 (emitted_insts sm sb)) u v
          (step_taint (EL 0 (emitted_insts sm sb)) s u tn) /\
    (!t. run_inst_seq (emitted_insts sm sb) s = OK t ==>
      gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + 3))) /\
    (!t. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t ==>
      ?n j. gas_path_ptr D lo ctx fn PG G tn s n G' tn'
        (Abort Revert_abort (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  drule_all bodyPtrPrecompileBuiltinsEmittedSuffixTheory.computed_emitted_suffix_checked >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  drule computed_suffix_shape >> strip_tac >>
  `src <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString sm.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all bodyPtrPrecompileBuiltinsRuntimeTheory.computed_call_prefix >>
  disch_then (qspecl_then [`outsz`, `sm.cs_next_id`,
    `STRING #"%" (toString (sm.cs_next_var+1))`]
    (strip_assume_tac o SRULE [run_inst_seq_def, AllCaseEqs()])) >>
  rename1 `step_inst_base (mk_inst sm.cs_next_id GAS _ _) s = OK u` >>
  rename1 `step_inst_base (mk_inst (sm.cs_next_id+1) STATICCALL _ _) u = OK v` >>
  qmatch_asmsub_abbrev_tac `emitted_insts sm sb = [gi;ci;ai]` >>
  qexistsl_tac [`u`, `v`, `G'`, `tn'`] >>
  simp[] >>
  `G' = step_prov PG (step_prov PG G gi u) ci v /\
   tn' = step_taint ci u v (step_taint gi s u tn)` by
    (irule suffix_final_ghost >>
     simp[Abbr `gi`, Abbr `ci`, Abbr `ai`] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule suffix_normal_path >>
      gvs[Abbr `gi`, Abbr `ci`, Abbr `ai`, mk_inst_def] >> metis_tac[]) >>
  rpt strip_tac >> irule suffix_revert_path >>
  gvs[Abbr `gi`, Abbr `ci`, Abbr `ai`, mk_inst_def] >> metis_tac[]
QED

Theorem computed_suffix_success_path:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sm sb) s G' tn' /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
      gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + 3))
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sm sb) s = OK t` by
    (metis_tac[computed_suffix_success]) >>
  qexists_tac `t` >> simp[] >>
  drule computed_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED

Theorem computed_suffix_failure_path:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sm sb) s G' tn' /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t n j. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t /\
      gas_path_ptr D lo ctx fn PG G tn s n G' tn'
        (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all computed_suffix_failure >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED

Theorem computed_suffix_oracle_failure_path:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  (s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sm sb) s G' tn' /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t n j. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t /\
      gas_path_ptr D lo ctx fn PG G tn s n G' tn'
        (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t` by
    (irule computed_suffix_oracle_failure >> metis_tac[]) >>
  drule computed_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED
