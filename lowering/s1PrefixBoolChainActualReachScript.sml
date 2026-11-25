(* Paired residual entries reached by the native BoolChain continuing step. *)
Theory s1PrefixBoolChainActualReach
Ancestors
  exprLowering emitHelper fragExec fragGasOriginPtr
  gasShadow gasShadowCompileBase gasShadowState gasExplicitSites gasSummary
  vyperAST vyperInterpreter vyperValueOperation vyperState vyperStorageFootprint
  venomState relation

Definition bool_chain_actual_advance_def:
  bool_chain_actual_advance cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 (xs,sa,shadow_sa,es,s,G,tn) (rest,st,shadow_st,mid,z,G1,tn1) <=>
    ?c sc shadow_sc op sj sn lt lf marks u.
      xs = c::rest /\ z = jump_to st.cs_current_bb u /\
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
          (s,G,tn) marks (OK u,G1,tn1))
End

Definition bool_chain_actual_reached_def:
  bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 n e sg shadow_sg es s0 G0 tn0 xs sa shadow_sa ee s G tn <=>
    RTC (bool_chain_actual_advance cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
           func PG st0)
      (bool_chain_operands p (n - 1) e,sg,shadow_sg,es,s0,G0,tn0)
      (xs,sa,shadow_sa,ee,s,G,tn)
End

Theorem bool_chain_actual_reached_root:
  bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
    func PG st0 n e sg shadow_sg es s0 G0 tn0
    (bool_chain_operands p (n - 1) e) sg shadow_sg es s0 G0 tn0
Proof
  simp[bool_chain_actual_reached_def]
QED

Theorem bool_chain_actual_reached_advance:
  bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
    func PG st0 n e sg shadow_sg es0 s0 G0 tn0 (c::rest) sa shadow_sa es s G tn /\
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
  bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
    func PG st0 n e sg shadow_sg es0 s0 G0 tn0 rest st shadow_st mid
    (jump_to st.cs_current_bb u) G1 tn1
Proof
  rewrite_tac[bool_chain_actual_reached_def] >> strip_tac >>
  irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
  qexists_tac `(c::rest,sa,shadow_sa,es,s,G,tn)` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[bool_chain_actual_advance_def] >>
  map_every qexists_tac [`c`,`sc`,`shadow_sc`,`op`,`sj`,`sn`,`lt`,`lf`,`marks`,`u`] >>
  simp[]
QED
