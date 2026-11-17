Theory bodyPtrPrecompileBuiltinsEmittedSuffix
Ancestors bodyPtrPrecompileBuiltinsRuntime bodyPtrPrecompileBuiltinsSuffix
          exprSimPrecompiles compileEnv loweringStateRelDefs ptrDiscipline

Theorem computed_emitted_suffix_checked:
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
    (s.vs_transient s.vs_call_ctx.cc_address) ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sm sb) s G' tn'
Proof
  strip_tac >> drule computed_suffix_shape >> strip_tac >>
  `src <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString sm.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  Cases_on `s.vs_outcomes = []`
  >- (qabbrev_tac `gi = mk_inst sm.cs_next_id GAS []
        [STRING #"%" (toString sm.cs_next_var)]` >>
      qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
        [Var (STRING #"%" (toString sm.cs_next_var)); Lit target;
         Var src; Lit insz; Var dst; Lit outsz]
        [STRING #"%" (toString (sm.cs_next_var+1))]` >>
      qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var))
        (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
      `step_inst_base gi s = OK u` by simp[Abbr `gi`, Abbr `u`, step_GAS] >>
      `step_inst_base ci u = Abort ExHalt_abort (halt_state (set_returndata [] u))` by
        (simp[Abbr `ci`, mk_inst_def, step_inst_base_def,
           eval_operand_def, lookup_var_def, Abbr `u`, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE, exec_ext_call_def] >>
         gvs[eval_operand_def, lookup_var_def]) >>
      qexistsl_tac [`step_prov PG G gi u`, `step_taint gi s u tn`] >>
      irule suffix_abort_checked >> simp[Abbr `gi`, Abbr `ci`] >> metis_tac[]) >>
  drule_all computed_call_prefix >> strip_tac >>
  simp[] >> irule suffix_checked >> simp[] >>
  simp[venomInstTheory.mk_inst_def] >> metis_tac[]
QED
