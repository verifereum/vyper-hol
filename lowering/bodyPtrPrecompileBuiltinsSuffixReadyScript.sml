Theory bodyPtrPrecompileBuiltinsSuffixReady
Ancestors bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsRuntime
          exprSimHash venomInstProofs venomExecSemantics venomState
          ptrCoverage bodyPtrDefs finite_map pred_set venomInst
          exprSimPrecompiles exprLoweringProps ptrDiscipline venomCallOracleDefs context compileEnv loweringStateRelDefs

Theorem computed_call_step_frame:
  ci = mk_inst id STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  eval_operand (Var gv) u = SOME gas /\
  eval_operand (Var src) u = SOME wi /\
  eval_operand (Var dst) u = SOME wo /\
  computed_precompile (venom_call_request u addr 0w wi an T) /\
  step_inst_base ci u = OK v ==>
  v.vs_allocas = u.vs_allocas /\ v.vs_fmp = u.vs_fmp /\
  v.vs_halted = u.vs_halted /\ v.vs_current_bb = u.vs_current_bb /\
  v.vs_inst_idx = u.vs_inst_idx /\
  (!x. x <> cv ==> lookup_var x v = lookup_var x u)
Proof
  strip_tac >>
  `exec_ext_call ci u gas addr 0w wi an wo rn T = OK v` by
    (gvs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `ci.inst_outputs = [cv]` by simp[mk_inst_def] >>
  (* Specialize the provider before discharging it. Type-instantiating an
     assumption theorem afterwards would retain a new, undischargeable hyp. *)
  drule_all (INST_TYPE [alpha |-> ``:256 word``, beta |-> ``:256``,
    gamma |-> ``:256``] computed_static_exec_eq) >>
  disch_then (qspecl_then [`rn`,`wo`,`gas`] mp_tac) >> simp[] >> strip_tac >>
  gvs[update_var_def, write_memory_with_expansion_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem suffix_load_ready:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) ==>
  ptr_covers G2 tn2 dst q 32 /\ allocas_from lo q /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn2.t_mem) /\
  q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
  q.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` by gvs[step_GAS] >>
  `eval_operand (Var gv) u = SOME (HD (s.vs_gas_readings ++ [0w])) /\
   eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo` by
    gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (gvs[update_var_def, venom_call_request_def, read_memory_def]) >>
  drule_all computed_call_step_frame >> strip_tac >>
  `q = v` by
    (gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         AllCaseEqs()]) >>
  `tn2.t_mem SUBSET tn.t_mem` by (irule suffix_memory_subset >> metis_tac[]) >>
  `lookup_var dst v = lookup_var dst s` by
    (gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `gi.inst_outputs = [gv] /\ ci.inst_outputs = [cv]` by simp[mk_inst_def] >>
  drule_all suffix_old_variable >> strip_tac >>
  conj_tac
  >- gvs[ptr_covers_def] >>
  conj_tac
  >- (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  reverse conj_tac >- gvs[update_var_def] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem computed_suffix_load_ready:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  step_inst_base (EL 0 (emitted_insts sm sb)) s = OK u /\
  step_inst_base (EL 1 (emitted_insts sm sb)) u = OK v /\
  run_inst_seq (emitted_insts sm sb) s = OK q /\
  G2 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sb)) u)
         (EL 1 (emitted_insts sm sb)) v /\
  tn2 = step_taint (EL 1 (emitted_insts sm sb)) u v
          (step_taint (EL 0 (emitted_insts sm sb)) s u tn) /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) ==>
  ptr_covers G2 tn2 dst q 32 /\ allocas_from lo q /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn2.t_mem) /\
  q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
  q.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule computed_suffix_shape >> strip_tac >>
  `src <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString (sm.cs_next_var+1))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
      arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  gvs[] >> irule suffix_load_ready >> metis_tac[]
QED
