(* The physical endpoint of the already successful EC arithmetic packet.
   Its ordinary machine frame does not assume a singleton ghost invariant. *)
Theory bodyECArithSuccessRunMods
Ancestors
  bodyFullBuiltinPrecompileSuffixPath bodyPtrPrecompileBuiltinsSuffixFrame
  bodyBinopFragMemory builtinIntClamp exprSimPrecompiles
  exprSimRawCallCalldata entrySinkExtraction valueEncodingProps bodyPtrDefs
  exprLoweringProps exprSimHash loweringPosts vyperStorageFootprint
  venomExecSemantics venomInst venomState venomCallOracleDefs extCallOracle
  finite_map list rich_list words byte compileEnv ptrDiscipline pred_set
Libs horizonTypeLib

Theorem ec_arith_success_raw_fields[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  precompile_result (venom_call_request s addr 0w wi an T).cr_target
    (venom_call_request s addr 0w wi an T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  run_inst_seq (emitted_insts sm sb) s = OK q ==>
  q.vs_returndata = data /\ q.vs_alloca_next = s.vs_alloca_next /\
  q.vs_immutables = s.vs_immutables /\ q.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_success) >>
  disch_then (qspecl_then [`wo`,`wi`,`s`,`data`] mp_tac) >>
  `?co rest. s.vs_outcomes = co::rest /\ co.co_success` by (qexistsl [`co`,`rest`] >> simp[]) >>
  simp[] >> disch_then (assume_tac o GSYM) >>
  simp[update_var_def, write_memory_with_expansion_def]
QED

Theorem ec_arith_success_run_mods:
  ((addr = 6w /\ an = 128w) \/ (addr = 7w /\ an = 96w)) /\
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\ emitted_insts sm sb = [gi;ci;ai] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  precompile_result (venom_call_request s addr 0w wi an T).cr_target
    (venom_call_request s addr 0w wi an T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  data = word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  w2n wi + w2n an <= s.vs_alloca_next /\ w2n wo + 64 <= s.vs_alloca_next /\
  ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s 64 /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) 64 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wo) 64 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ stor_taint_ok_at (DF H) tn s) ==>
  let ee = SND (take_call_outcome NONE (w2w addr) (read_memory (w2n wi) (w2n an) s) NONE es) in
  ?t G' tn'.
    t = (q with vs_inst_idx := s.vs_inst_idx + 3) /\
    G' = step_prov PG (step_prov PG G gi u) ci v /\
    tn' = step_taint ci u v (step_taint gi s u tn) /\
    step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
    run_inst_seq [gi;ci;ai] s = OK q /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    eval_operand (Var dst) t = SOME wo /\ ptr_covers G' tn' dst t 64 /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\
    t.vs_memory = (write_memory_with_expansion (w2n wo) data s).vs_memory /\
    mem_bytes_at (w2n wo) 64 t.vs_memory = data /\
    (!off len. regions_disjoint off len (w2n wo) 64 ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n wo <= i /\ i < w2n wo + 64} /\
    (!i. w2n wo <= i /\ i < w2n wo + 64 ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx ee t /\ wb_frame cenv es ee sf s t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `G2 = step_prov PG (step_prov PG G gi u) ci v` >>
  qabbrev_tac `tn2 = step_taint ci u v (step_taint gi s u tn)` >>
  qabbrev_tac `t = q with vs_inst_idx := s.vs_inst_idx + 3` >>
  `LENGTH data = 64` by simp[LENGTH_word_to_bytes, dimword_def] >>
  `run_inst_seq (emitted_insts sm sb) s = OK q` by
    (qpat_assum `emitted_insts sm sb = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  drule_all ec_arith_success_raw_fields >> strip_tac >>
  qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_output) >>
  disch_then (qspecl_then [`wo`,`wi`,`q`,`s`,`data`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `_ sm = (_,sb)`
       (mp_tac o AP_TERM ``\r:operand # compile_state. (SND r).cs_current_bb``) >>
     simp[NoAsms, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by suspend "cursor" >>
  `alloca_history func t` by suspend "history" >>
  `q = v` by
    (Cases_on `eval_operand (Var cv) v` >>
     gvs[run_inst_seq_def, clamp_assert_step, AllCaseEqs()] >>
     pop_assum mp_tac >> rw[]) >>
  `computed_precompile (venom_call_request s addr 0w wi an T)` by
    simp[computed_precompile_def, venom_call_request_def] >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    tn2.t_mem = tn.t_mem DIFF {i | w2n wo <= i /\ i < w2n wo + 64} /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x))` by
    suspend "effects" >>
  `ptr_covers G2 tn2 dst t 64 /\ eval_operand (Var dst) t = SOME wo` by
    suspend "cover" >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
     simp[Abbr `t`, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `t.vs_memory = (write_memory_with_expansion (w2n wo) data s).vs_memory /\
    mem_bytes_at (w2n wo) 64 t.vs_memory = data /\
    (!off len. regions_disjoint off len (w2n wo) 64 ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)` by
    suspend "bytes" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section` by simp[Abbr `t`] >>
  `!i. w2n wo <= i /\ i < w2n wo + 64 ==> i NOTIN tn2.t_mem` by simp[IN_DIFF] >>
  qexistsl [`t`,`G2`,`tn2`] >>
  simp[] >>
  suspend "horizon"
QED

Resume ec_arith_success_run_mods[cursor]:
  qspecl_then [`[gi;ci;ai]`,`s`,`q`] mp_tac
    entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >>
  simp[Abbr `t`,mk_inst_def,is_terminator_def]
QED

Resume ec_arith_success_run_mods[history]:
  `q.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `t.vs_current_bb = sb.cs_current_bb`
       (mp_tac o SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]) >> gvs[Abbr `t`]) >>
  qpat_assum `isPREFIX [gi;ci;ai] _`
    (qx_choose_then `tail` assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  qspecl_then [`func`,`s`,`q`,`bb`,`[gi;ci;ai]`,`tail`] mp_tac
    alloca_history_no_alloca_slice >>
  simp[Abbr `t`,mk_inst_def]
QED

Resume ec_arith_success_run_mods[effects]:
  mp_tac (Q.INST [`rn` |-> `64w:bytes32`] suffix_same_endpoint_effects) >>
  simp[Abbr `G2`, Abbr `tn2`, dimword_def] >> strip_tac >>
  `v.vs_returndata = data` by
    (qpat_x_assum `q = v` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  gvs[Abbr `t`, lookup_var_def] >>
  rpt strip_tac >>
  qpat_assum `!x. x <> gv /\ x <> cv ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume ec_arith_success_run_mods[cover]:
  qpat_assum `!x. not_fresh_at sm x ==> lookup_var _ _ = _ /\ _`
    (qspec_then `dst` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `ptr_covers G tn dst s 64` mp_tac >> simp[ptr_covers_def,eval_operand_def] >>
  fs[eval_operand_def]
QED

Resume ec_arith_success_run_mods[bytes]:
  `TAKE 64 data = data` by simp[TAKE_LENGTH_TOO_LONG] >>
  `t.vs_memory = (write_memory_with_expansion (w2n wo) data s).vs_memory` by
    simp[Abbr `t`,dimword_def,LENGTH_word_to_bytes,TAKE_LENGTH_TOO_LONG] >>
  simp[] >> conj_tac
  >- (qspecl_then [`w2n wo`,`data`,`s`] mp_tac write_memory_mem_bytes_at_same >> simp[]) >>
  rpt strip_tac >> irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  qpat_x_assum `regions_disjoint off len (w2n wo) 64` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume ec_arith_success_run_mods[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (unabbrev_all_tac >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F]
        (OK (q with vs_inst_idx := s.vs_inst_idx + 3),
         step_prov PG (step_prov PG G gi u) ci v,
         step_taint ci u v (step_taint gi s u tn))` by
        (qpat_assum `stor_taint_ok_at _ _ _`
           (assume_tac o CONJUNCT1 o REWRITE_RULE [stor_taint_ok_at_def]) >>
         qpat_assum `stor_taint_ok_at _ _ _`
           (assume_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [stor_taint_ok_at_def]) >>
         mp_tac (Q.INST [`rn` |-> `64w:bytes32`,
             `D` |-> `DF (H:(bool # bytes32 # type_value) list # num list)`,
             `G2` |-> `step_prov PG (step_prov PG G gi u) ci v`,
             `tn2` |-> `step_taint ci u v (step_taint gi s u tn)`]
           precompile_suffix_origin_path) >>
         (impl_tac >- (rpt conj_tac >> simp[dimword_def])) >>
         disch_then ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  simp[Abbr `t`,stmt_state_rel_inst_idx,raw_call_wb_frame_inst_idx] >>
  `w2n (64w:bytes32) = 64` by simp[dimword_def] >>
  qpat_assum `w2n (64w:bytes32) = 64` (fn width =>
    mp_tac (PURE_REWRITE_RULE [width]
      (Q.INST [`target` |-> `addr`, `insz` |-> `an`, `outsz` |-> `64w:bytes32`,
        `ip` |-> `Var src`, `op` |-> `Var dst`, `t` |-> `q`]
        (horizonTypeLib.at_horizon_named "H" computed_suffix_preserves)))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (fn post =>
    qpat_assum `q = v` (fn raw => ACCEPT_TAC (PURE_REWRITE_RULE [raw] post)))
QED

Finalise ec_arith_success_run_mods
