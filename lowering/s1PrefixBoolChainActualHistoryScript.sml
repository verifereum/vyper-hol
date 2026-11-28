(* Right-extension induction over paired native BoolChain entries. *)
Theory s1PrefixBoolChainActualHistory
Ancestors
  s1PrefixBoolChainActualReach relation pair
  exprLowering emitHelper fragExec fragGasOriginPtr
  gasShadow gasShadowCompileBase gasShadowState gasExplicitSites gasSummary
  vyperAST vyperInterpreter vyperValueOperation vyperState vyperStorageFootprint
  venomState vyperTypeCallGraph list

Theorem bool_chain_actual_reached_induction:
  P (bool_chain_operands p (n - 1) e) sg shadow_sg es0 s0 G0 tn0 /\
  (!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf
      st shadow_st marks mid G1 tn1 u.
    bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 n e sg shadow_sg es0 s0 G0 tn0 (c::rest) sa shadow_sa es s G tn /\
    P (c::rest) sa shadow_sa es s G tn /\
    lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr c) shadow_sa = (op,shadow_sc) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] sj = ((),sn) /\
    fn_has_code sj sn func /\ st.cs_current_bb = (if p then lt else lf) /\
    st.cs_current_insts = [] /\ gas_shadow_state st shadow_st /\
    compile_bool_chain_ops compile_expr cenv p rv xl rest st = ((),sf) /\
    compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
      (MAP gas_shadow_expr rest) shadow_st = ((),shadow_sf) /\
    bind (eval_expr cx c) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV p),mid) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,G1,tn1)) ==>
    P rest st shadow_st mid (jump_to st.cs_current_bb u) G1 tn1) ==>
  !xs sa shadow_sa es s G tn.
    bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 n e sg shadow_sg es0 s0 G0 tn0 xs sa shadow_sa es s G tn ==>
    P xs sa shadow_sa es s G tn
Proof
  rewrite_tac[bool_chain_actual_reached_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `RTC R _ _` >>
  qmatch_goalsub_abbrev_tac `RTC _ root _` >>
  qspecl_then [`R`,
    `\(xs,sa,shadow_sa,es,s,G,tn).
       RTC R root (xs,sa,shadow_sa,es,s,G,tn) /\ P xs sa shadow_sa es s G tn`,
    `root`] mp_tac RTC_ALT_RIGHT_INDUCT >>
  impl_tac
  >- (conj_tac >- simp[Abbr `root`] >>
      simp[pairTheory.FORALL_PROD] >>
      rpt gen_tac >> strip_tac >> conj_tac
      >- (irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >> metis_tac[]) >>
      qpat_x_assum `R _ _` mp_tac >>
      simp[Abbr `R`,bool_chain_actual_advance_def] >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem bool_chain_operands_calls:
  !n p e. EVERY P (int_calls_expr e) ==>
    EVERY (\a. EVERY P (int_calls_expr a)) (bool_chain_operands p n e)
Proof
  Induct_on `n` >> rpt gen_tac >> Cases_on `e` >>
  simp[bool_chain_operands_def, int_calls_expr_def, EVERY_APPEND] >>
  rpt (COND_CASES_TAC >> gvs[]) >>
  simp[int_calls_expr_def, EVERY_APPEND] >> metis_tac[]
QED

Theorem bool_chain_actual_reached_calls:
  EVERY admissible (int_calls_expr e) /\
  bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
    func PG st0 n e sg shadow_sg es0 s0 G0 tn0 xs sa shadow_sa es s G tn ==>
  EVERY (\a. EVERY admissible (int_calls_expr a)) xs
Proof
  strip_tac >>
  mp_tac (Q.INST [`P` |-> `\xs sa shadow_sa es s G tn.
    EVERY (\a. EVERY admissible (int_calls_expr a)) xs`]
    bool_chain_actual_reached_induction) >>
  simp[bool_chain_operands_calls] >> disch_then (drule_then ACCEPT_TAC)
QED
