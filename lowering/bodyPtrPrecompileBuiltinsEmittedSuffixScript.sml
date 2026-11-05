Theory bodyPtrPrecompileBuiltinsEmittedSuffix
Ancestors bodyPtrPrecompileBuiltinsRuntime bodyPtrPrecompileBuiltinsSuffix
          exprSimPrecompiles compileEnv ptrDiscipline

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
  drule_all computed_call_prefix >> strip_tac >>
  simp[] >> irule suffix_checked >> simp[] >>
  simp[venomInstTheory.mk_inst_def] >> metis_tac[]
QED
