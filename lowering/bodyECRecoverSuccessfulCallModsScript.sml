Theory bodyECRecoverSuccessfulCallMods
Ancestors
  bodyFullBuiltinPrecompileSuffixSuccess bodyFullBuiltinPrecompileSuffixPath
  bodyPtrPrecompileBuiltinsRuntime bodyPtrPrecompileBuiltinsSuffixFrame
  bodyMemoryDefs stateRelProj allocaHistoryFragment exprSimAbiEncodeMemoryLength
  valueCopy extCallOracle vyperCallOutcomeProps venomCallOracleDefs
  venomInstProofs emitHelperProps exprSimPrecompiles exprSimHash
  exprLoweringProps loweringPosts loweringStateRelDefs bodyPtrDefs
  venomState venomInst venomExecSemantics ptrDiscipline
  finite_map pred_set list rich_list words
Libs
  monadsyntax

Theorem recovery_success_prefix[local]:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit 1w; Var qi; Lit 128w; Var qo; Lit 32w] [cv] /\
  qi <> gv /\ qo <> gv /\
  eval_operand (Var qi) s = SOME wi /\ eval_operand (Var qo) s = SOME wo /\
  computed_precompile (venom_call_request s 1w 0w wi 128w T) /\
  s.vs_outcomes <> [] ==>
  ?u v. step_inst_base gi s = OK u /\ step_inst_base ci u = OK v
Proof
  strip_tac >>
  `?v. run_inst_seq [gi;ci] s = OK v` by
    (simp[] >> irule computed_call_prefix >> simp[] >> qexists_tac `wi` >> simp[]) >>
  `?u. step_inst_base gi s = OK u` by simp[step_GAS] >>
  qpat_x_assum `gi = _` kall_tac >> qpat_x_assum `ci = _` kall_tac >>
  qpat_x_assum `run_inst_seq [gi;ci] s = OK v` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base ci u` >> simp[run_inst_seq_def]
QED

Theorem recovery_success_raw[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; Var qi; Lit 128w; Var qo; Lit 32w];
      emit_void ASSERT [success]; return (Var qo) od) cz = (Var qo,cq) /\
  eval_operand (Var qi) s = SOME wi /\ eval_operand (Var qo) s = SOME wo /\
  not_fresh_at cz qi /\ not_fresh_at cz qo /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success ==>
  ?q. run_inst_seq (emitted_insts cz cq) s = OK q /\
    q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory /\
    q.vs_data_section = s.vs_data_section /\ q.vs_allocas = s.vs_allocas /\
    q.vs_alloca_next = s.vs_alloca_next /\ q.vs_current_bb = s.vs_current_bb /\
    q.vs_halted = s.vs_halted
Proof
  strip_tac >>
  qpat_assum `_ cz = (Var qo,cq)` (mp_then Any mp_tac computed_suffix_success) >>
  simp[wordsTheory.dimword_def] >>
  disch_then (irule_at Any) >>
  simp[update_var_def, write_memory_with_expansion_def]
QED

Theorem recovery_success_frame[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; Var src; Lit 128w; Var dst; Lit 32w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sb) /\
  emitted_insts sm sb = [gi;ci;ai] /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s 1w 0w wi 128w T) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  tn2.t_mem SUBSET tn.t_mem /\
  (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  mp_tac (Q.INST [`target` |-> `1w:bytes32`, `insz` |-> `128w:bytes32`,
                 `sl` |-> `sb`] computed_suffix_frame_effects) >>
  simp[] >> strip_tac >> rpt strip_tac >> res_tac
QED

(* All physical and logical posts describe the same successful suffix run.
   In particular its memory effect allows data = [], on an unsuccessful
   recovery with a successful precompile call. *)
Theorem ecrecover_successful_call_physical_mods:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; Var src; Lit 128w; Var dst; Lit 32w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sb) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,sm.cs_next_id) NOTIN explicit /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  computed_precompile (venom_call_request s 1w 0w wi 128w T) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  read_memory (w2n wi) 128 s = precompile_input ECRecover vals /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sf s /\
  w2n wi + 128 <= s.vs_alloca_next /\ w2n wo + 32 <= s.vs_alloca_next /\
  lo <= w2n wo /\ allocas_from lo s /\
  ptr_covers G tn src s 128 /\ ptr_covers G tn dst s 32 /\
  (!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tn.t_mem) /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 32 off (type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) 0 d cenv cx es G tn s /\
    stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_rel func cenv es.scopes s /\
    tn.t_stor SUBSET (DF H).d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET (DF H).d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)) ==>
  let after_call = SND (take_call_outcome NONE 1w (precompile_input ECRecover vals) NONE es) in
  ?t G' tn'.
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    t.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory /\
    (!p n. regions_disjoint (w2n wo) 32 p n ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ghost_kept_at lo cenv es sf G tn s G' tn' /\ return_buf_frame d cenv sb t /\
    eval_operand (Var dst) t = SOME wo /\ ptr_covers G' tn' dst t 32 /\
    (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn'.t_mem) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx after_call t /\
      ghost_inv_at (DF H) 0 d cenv cx after_call G' tn' t /\ wb_frame cenv es after_call sf s t)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  qabbrev_tac `gv = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (sm.cs_next_var+1))` >>
  qabbrev_tac `gi = mk_inst sm.cs_next_id GAS [] [gv]` >>
  qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
    [Var gv; Lit 1w; Var src; Lit 128w; Var dst; Lit 32w] [cv]` >>
  qabbrev_tac `ai = mk_inst (sm.cs_next_id+2) ASSERT [Var cv] []` >>
  `~not_fresh_at sm gv /\ ~not_fresh_at sm cv` by
    simp[Abbr `gv`, Abbr `cv`, not_fresh_at_def] >>
  `src <> gv /\ dst <> gv /\ dst <> cv` by metis_tac[] >>
  `?u v. step_inst_base gi s = OK u /\ step_inst_base ci u = OK v` by
    (irule recovery_success_prefix >> simp[Abbr `gi`, Abbr `ci`, mk_inst_def] >>
     qexists_tac `wi` >> simp[]) >>
  drule_all recovery_success_raw >> strip_tac >>
  qabbrev_tac `G2 = step_prov PG (step_prov PG G gi u) ci v` >>
  qabbrev_tac `tn2 = step_taint ci u v (step_taint gi s u tn)` >>
  qabbrev_tac `t = q with vs_inst_idx := s.vs_inst_idx + 3` >>
  suspend "finish"
QED

Resume ecrecover_successful_call_physical_mods[finish]:
  `run_inst_seq [gi;ci;ai] s = OK q` by metis_tac[] >>
  `isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  mp_tac (Q.INST [`addr` |-> `1w:bytes32`, `an` |-> `128w:bytes32`,
     `rn` |-> `32w:bytes32`, `lo` |-> `0`, `id` |-> `sm.cs_next_id`,
     `trace` |-> `es.storage_trace`, `res` |-> `Var dst`]
       precompile_suffix_success_full_family) >>
  (impl_tac >-
    (simp[wordsTheory.dimword_def, Abbr `G2`, Abbr `tn2`, allocas_from_def,
          Abbr `gi`, Abbr `ci`, Abbr `ai`] >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >> disch_then assume_tac >>
  `tn2.t_mem SUBSET tn.t_mem /\
   (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
     FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x))` by
    (mp_tac recovery_success_frame >> simp[Abbr `G2`, Abbr `tn2`]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `t`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `!x. not_fresh_at sf x ==> not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `ghost_kept_at lo cenv es sf G tn s G2 tn2` by
    (simp[ghost_kept_at_def] >> metis_tac[SUBSET_DEF]) >>
  `return_buf_frame d cenv sb t` by suspend "return_buf" >>
  `alloca_history func t` by suspend "history" >>
  `ptr_covers G2 tn2 dst t 32 /\ eval_operand (Var dst) t = SOME wo` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var _ _ = _ /\ _`
       (qspec_then `dst` mp_tac) >> simp[] >> strip_tac >>
     fs[ptr_covers_def, eval_operand_def] >> metis_tac[optionTheory.SOME_11]) >>
  `!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn2.t_mem` by
    (rpt strip_tac >> metis_tac[SUBSET_DEF]) >>
  qexistsl [`t`,`G2`,`tn2`] >>
  simp[] >>
  suspend "remaining"
QED

Resume ecrecover_successful_call_physical_mods[return_buf]:
  irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sf`] >>
  simp[Abbr `t`, lookup_var_def] >> metis_tac[lookup_var_def]
QED

Resume ecrecover_successful_call_physical_mods[history]:
  qunabbrev_tac `t` >>
  qpat_assum `isPREFIX [gi;ci;ai] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) [gi;ci;ai]` by
    simp[Abbr `gi`, Abbr `ci`, Abbr `ai`, mk_inst_def, is_terminator_def] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Resume ecrecover_successful_call_physical_mods[remaining]:
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts + 3 /\
   ~t.vs_halted /\ t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory` by
    simp[Abbr `t`] >>
  `allocas_from lo t` by (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  simp[abi_encode_write_memory_length] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_write_disjoint >>
      `LENGTH (TAKE 32 data) <= 32` by simp[LENGTH_TAKE_EQ] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  simp[] >>
  mp_tac (Q.INST [`addr` |-> `1w:bytes32`, `an` |-> `128w:bytes32`,
     `rn` |-> `32w:bytes32`, `id` |-> `sm.cs_next_id`,
     `D` |-> `DF (H:(bool # bytes32 # type_value) list # num list)`]
       precompile_suffix_origin_path) >>
  simp[wordsTheory.dimword_def, Abbr `gi`, Abbr `ci`, Abbr `ai`,
       Abbr `G2`, Abbr `tn2`, Abbr `t`]
QED

Finalise ecrecover_successful_call_physical_mods
