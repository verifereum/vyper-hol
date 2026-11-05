(* Restatements of identically named local lemmas in
   exprSimPrecompilesScript.sml, using the S1 base proofs.
   Public computed_suffix execution and framing facts are reused. *)
Theory bodyMemBiECRecoverSuffix
Ancestors
  bodyMemBiECRecoverFacts exprSimPrecompiles exprSimDefs exprSimProps
  exprSimWordArgs exprLoweringProps builtinMisc compileEnv context emitHelper
  emitHelperProps venomExecSemantics venomInst venomState venomMemDefs
  venomCallOracleDefs extCallOracle valueEncoding words byte list rich_list
Libs
  monadsyntax

Theorem compile_ecrecover_prefix:
  compile_ecrecover h v r sig =
    do bufs <-
         (do ib <- context$compile_alloc_buffer 128;
             emit_void MSTORE [ib.buf_operand; h];
             p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [p1; v];
             p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [p2; r];
             p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
             emit_void MSTORE [p3; sig];
             ob <- context$compile_alloc_buffer 32;
             emit_void MSTORE [ob.buf_operand; Lit 0w];
             return (ib.buf_operand,ob.buf_operand) od);
       gas <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas; Lit 1w; FST bufs; Lit 128w; SND bufs; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [SND bufs]
    od
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem ecrecover_suffix_core:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success]; emit_op MLOAD [op] od) sm = (res,sb) ==>
  ?sc. (do gas <- emit_op GAS [];
           success <- emit_op STATICCALL
             [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
           emit_void ASSERT [success]; comp_return op od) sm = (op,sc) /\
       emit_op MLOAD [op] sc = (res,sb) /\
       emitted_insts sm sb = emitted_insts sm sc ++
         [mk_inst (sm.cs_next_id + 3) MLOAD [op]
           [STRING #"%" (toString (sm.cs_next_var + 2))]] /\
       res = Var (STRING #"%" (toString (sm.cs_next_var + 2)))
Proof
  simp[comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem ecrecover_suffix_shape:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) ==>
  res = Var (STRING #"%" (toString (sm.cs_next_var + 2))) /\
  sb.cs_next_var = sm.cs_next_var + 3 /\
  sb.cs_next_id = sm.cs_next_id + 4 /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb =
    [mk_inst sm.cs_next_id GAS []
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst (sm.cs_next_id + 1) STATICCALL
       [Var (STRING #"%" (toString sm.cs_next_var)); Lit 1w;
        ip; Lit 128w; op; Lit 32w]
       [STRING #"%" (toString (sm.cs_next_var + 1))];
     mk_inst (sm.cs_next_id + 2) ASSERT
       [Var (STRING #"%" (toString (sm.cs_next_var + 1)))] [];
     mk_inst (sm.cs_next_id + 3) MLOAD [op]
       [STRING #"%" (toString (sm.cs_next_var + 2))]]
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  qpat_x_assum `emit_op MLOAD [op] sc = _` mp_tac >>
  simp[emitHelperTheory.emit_op_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem ecrecover_code_shape:
  compile_ecrecover h v r s sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_ecrecover_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem compile_ecrecover_extends:
  compile_ecrecover h v r sig sa = (op,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >> drule ecrecover_code_shape >>
  simp[same_blocks_def, cs_extends_def] >> strip_tac >>
  qexists_tac `[]` >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem ecrecover_suffix_run:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  mem_word_at (w2n wo)
    (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory = w ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand res t = SOME w
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_success >> simp[] >>
  disch_then (qspecl_then [`wo`, `wi`, `s`, `data`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s = OK st` >> strip_tac >>
  drule_all computed_suffix_output >> strip_tac >>
  `mem_word_at (w2n wo) st.vs_memory = w` by
    gvs[wordsTheory.dimword_def] >>
  qexists_tac `update_var (STRING #"%" (toString (sm.cs_next_var + 2))) w st` >>
  conj_tac
  >- (drule run_inst_seq_append >> disch_then (qspec_then
        `[mk_inst (sm.cs_next_id + 3) MLOAD [op]
           [STRING #"%" (toString (sm.cs_next_var + 2))]]` mp_tac) >>
      asm_rewrite_tac[] >> disch_then SUBST1_TAC >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
           mload_def, mem_word_at_def, eval_operand_def] >>
      gvs[mem_word_at_def, word_of_bytes_be_def, wordsTheory.dimword_def]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ecrecover_suffix_oracle_failure:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  ~( ?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  `computed_precompile (venom_call_request s 1w 0w wi 128w T)` by
    simp[computed_precompile_def, venom_call_request_def, precompile_result_def,
         wordsTheory.w2w_n2w, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `?u. run_inst_seq (emitted_insts sm sc) s = Abort Revert_abort u` by
    (irule computed_suffix_oracle_failure >> simp[] >>
     Cases_on `s.vs_outcomes` >> gvs[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  `!v. run_inst_seq (emitted_insts sm sc) s <> OK v` by simp[] >>
  drule run_inst_seq_append_err >> simp[]
QED

Theorem ecrecover_suffix_preserves:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 32 off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx
    (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\ wb_frame cenv es sf s t
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_success >> simp[] >>
  disch_then (qspecl_then [`wo`, `wi`, `s`, `data`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s = OK st` >> strip_tac >>
  drule computed_suffix_preserves >>
  simp[wordsTheory.dimword_def] >>
  disch_then drule >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_all computed_suffix_output >> strip_tac >>
  drule run_inst_seq_append >> disch_then (qspec_then
    `[mk_inst (sm.cs_next_id + 3) MLOAD [op]
       [STRING #"%" (toString (sm.cs_next_var + 2))]]` assume_tac) >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) s = OK t` mp_tac >>
  asm_rewrite_tac[] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  `!n. sm.cs_next_var <= n ==>
     not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `st`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]
QED
