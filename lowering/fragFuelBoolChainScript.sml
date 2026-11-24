Theory fragFuelBoolChain
Ancestors
  fragFuel exprLowering compileEnv emitHelper venomInst context pair pred_set
Libs
  fragFuelLib

(* The first fragment may jump into either of the blocks introduced later. *)
fun chain_seq lm lf tac =
  match_mp_tac (Q.SPECL [lm, lf] fuel_ok_seq_fwd) >> conj_tac
  >- tac
  >> reverse conj_tac >- simp[SUBSET_DEF]

Theorem fuel_ok_compile_bool_chain_ops:
  !es cfn cenv is_and result exit_lbl Wv E.
    (!e. MEM e es ==> fuel_ok Wv {} E (lower_value cfn cenv (BaseT BoolT) e)) /\
    result IN Wv /\ exit_lbl IN E ==>
    fuel_ok Wv {} E (compile_bool_chain_ops cfn cenv is_and result exit_lbl es)
Proof
  Induct_on `es` >- simp[compile_bool_chain_ops_def, fuel_ok_return] >>
  rpt gen_tac >> strip_tac >> Cases_on `es`
  >- (pure_rewrite_tac[compile_bool_chain_ops_def] >>
      match_mp_tac fuel_ok_bind0 >> conj_tac
      >- (first_assum irule >> simp[]) >>
      gen_tac >> BETA_TAC >> match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
      >- (irule fuel_ok_emit_inst >> simp[is_terminator_def]) >>
      irule fuel_ok_emit_inst_jmp >> simp[]) >>
  pure_rewrite_tac[compile_bool_chain_ops_def] >>
  match_mp_tac fuel_ok_bind0 >> conj_tac
  >- (first_assum irule >> simp[]) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac fuel_ok_bind0 >> conj_tac
  >- (Cases_on `is_and` >> simp[] >> fuel_auto []) >>
  qx_gen_tac `lbls` >> BETA_TAC >>
  chain_seq `{}` `{FST lbls; SND lbls}`
    (Cases_on `is_and` >> simp[] >> irule fuel_ok_emit_inst_jnz >> simp[]) >>
  chain_seq `{SND lbls}` `{FST lbls}` (MATCH_ACCEPT_TAC fuel_ok_new_block) >>
  match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
  >- (irule fuel_ok_emit_inst >> simp[is_terminator_def]) >>
  match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
  >- (irule fuel_ok_emit_inst_jmp >> simp[]) >>
  chain_seq `{FST lbls}` `{}` (MATCH_ACCEPT_TAC fuel_ok_new_block) >>
  first_x_assum irule >> simp[]
QED
