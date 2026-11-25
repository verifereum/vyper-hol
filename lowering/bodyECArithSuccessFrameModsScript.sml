(* Frame and pointer facts on the already-selected successful suffix endpoint. *)
Theory bodyECArithSuccessFrameMods
Ancestors
  bodyFullBuiltinPrecompileSuffixFrame bodyPtrPrecompileBuiltinsSuffixFrame
  bodyShaRegisteredFrameMods bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit
  exprSimAbiEncodeMemoryLength vyperCallOutcomeProps exprSimPrecompiles
  bodyPtrDefs loweringPosts loweringStateRelDefs exprLoweringProps ptrDiscipline
  venomCallOracleDefs venomExecSemantics venomInst venomState valueCopy
  compileEnv finite_map pred_set list rich_list words

Theorem ec_arith_launch_ghost_zero[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s ==>
  ghost_inv_at D 0 d ce cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ec_arith_written_region_frame[local]:
  t.vs_memory = (write_memory_with_expansion b (TAKE 64 data) s).vs_memory /\
  (!name p n. local_region ce es.scopes s name p n ==> regions_disjoint b 64 p n) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sf.cs_next_id <= inst.inst_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,64) ==>
  pure_frame ce func es sf s t /\ LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> pure_rewrite_tac[pure_frame_def] >>
  reverse conj_tac >- simp[abi_encode_write_memory_length] >>
  `!p n. regions_disjoint b 64 p n ==>
     mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mem_bytes_at_write_disjoint >>
     `LENGTH (TAKE 64 data) <= 64` by simp[LENGTH_TAKE_EQ] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  qpat_assum `!i p n. _ ==> regions_disjoint _ _ p n`
    (qspecl_then [`inst`,`b`,`64`] mp_tac) >> simp[regions_disjoint_def] >> metis_tac[]
QED

Theorem ec_arith_success_frame_mods:
  ((addr = 6w /\ an = 128w) \/ (addr = 7w /\ an = 96w)) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK sg /\ step_inst_base ci sg = OK sc /\
  run_inst_seq [gi;ci;ai] s = OK q /\ t = (q with vs_inst_idx := s.vs_inst_idx + 3) /\
  G2 = step_prov PG (step_prov PG G gi sg) ci sc /\
  tn2 = step_taint ci sg sc (step_taint gi s sg tn) /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  precompile_result (venom_call_request s addr 0w wi an T).cr_target
    (venom_call_request s addr 0w wi an T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\ 64 <= LENGTH data /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  sf.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved ce sf /\ local_ptrs_reserved ce sm /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  local_ptrs_rel func ce es.scopes s /\ lo <= w2n wo /\
  ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s 64 /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
  (!name b n. local_region ce es.scopes s name b n ==> regions_disjoint (w2n wo) 64 b n) /\
  MEM out (fn_insts func) /\ out.inst_opcode = ALLOCA /\
  sf.cs_next_id <= out.inst_id /\ FLOOKUP s.vs_allocas out.inst_id = SOME (w2n wo,64) /\
  t.vs_data_section = s.vs_data_section /\
  immutable_frame_mods func ce cx es s /\ ghost_inv_at_mods D lo d ce cx es G tn s ==>
  let ee = SND (take_call_outcome NONE (w2w addr) (read_memory (w2n wi) (w2n an) s) NONE es) in
    immutable_frame_mods func ce cx ee t /\ ghost_inv_at_mods D lo d ce cx ee G2 tn2 t /\
    ghost_kept_at lo ce es sf G tn s G2 tn2 /\ ptr_covers G2 tn2 dst t 64 /\
    (!i. w2n wo <= i /\ i < w2n wo + 64 ==> i NOTIN tn2.t_mem) /\
    (!i. ~(w2n wo <= i /\ i < w2n wo + 64) ==> (i IN tn2.t_mem <=> i IN tn.t_mem))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ghost_inv_at D 0 d ce cx es G tn s` by (drule_then ACCEPT_TAC ec_arith_launch_ghost_zero) >>
  `(!i. i IN tn2.t_mem <=> i IN tn.t_mem /\
     ~(w2n wo <= i /\ i < w2n wo + MIN 64 (LENGTH sc.vs_returndata))) /\
   (!x. not_fresh_at sf x ==> FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn2 (Var x) = op_taint tn (Var x))` by
    (drule_all (SIMP_RULE (srw_ss()) [wordsTheory.dimword_def, IN_DIFF] suffix_same_endpoint_effects) >>
     disch_then strip_assume_tac >> conj_tac
     >- simp[wordsTheory.dimword_def, IN_DIFF] >>
     gen_tac >> disch_tac >>
     `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `x <> gv /\ x <> cv` by metis_tac[] >>
     qpat_assum `!x. x <> gv /\ x <> cv ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  suspend "ordinary"
QED

Resume ec_arith_success_frame_mods[ordinary]:
  `ghost_inv_at D 0 d ce cx (es with outcomes := SOME rest) G2 tn2 t /\
   ghost_kept_at 0 ce es sf G tn s G2 tn2 /\ ptr_covers G2 tn2 dst t 64 /\
   (!i. w2n wo <= i /\ i < w2n wo + 64 ==> i NOTIN tn2.t_mem) /\
   t.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 64 data) s).vs_memory /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)` by
    (`addr <> 1w` by
       (qpat_assum `_ \/ _` strip_assume_tac >> simp[wordsTheory.dimword_def]) >>
     `addr = 1w /\ an = 128w /\ (64w:256 word) = 32w \/
      addr = 6w /\ an = 128w /\ (64w:256 word) = 64w \/
      addr = 7w /\ an = 96w /\ (64w:256 word) = 64w` by simp[] >>
     `addr = 1w ==> !i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem` by simp[] >>
     `addr <> 1w ==> 64 <= LENGTH data` by simp[] >>
     drule_all (SIMP_RULE (srw_ss()) [wordsTheory.dimword_def]
       (Q.INST [`rn` |-> `64w:256 word`, `lo` |-> `0`] precompile_suffix_ghost_output_at)) >>
     qpat_x_assum `!i. i IN tn2.t_mem <=> _` kall_tac >> simp[]) >>
  suspend "linked"
QED

Resume ec_arith_success_frame_mods[linked]:
  `ghost_inv_at D 0 d ce cx es G2 tn2 t` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ (es with outcomes := _) _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def, vyperStateTheory.evaluation_state_accfupds] >>
     simp[NoAsms]) >>
  `ghost_kept_at lo ce es sf G tn s G2 tn2` by
    (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `(!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x))` by
    (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `FLOOKUP t.vs_allocas out.inst_id = SOME (w2n wo,64)` by
    (qpat_assum `t.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all ec_arith_written_region_frame >> strip_tac >>
  `!i. i < lo /\ i IN tn2.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `!aid a sz. FLOOKUP t.vs_allocas aid = SOME (a,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a` by
    (qpat_assum `t.vs_allocas = _` (fn th => simp[NoAsms, th])) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `t.vs_alloca_next = _` (fn th => simp[NoAsms, th])) >>
  drule_all sha_registered_frame_mods >> strip_tac >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es t` mp_tac >>
      pure_rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
           immutable_alloca_sep_mods_def, immutable_alloca_sep_def, take_call_outcome_preserved_fields] >>
      disch_then ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ t` mp_tac >>
      pure_rewrite_tac[ghost_inv_at_mods_def, take_call_outcome_preserved_fields] >>
      disch_then ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
  `MIN 64 (LENGTH sc.vs_returndata) <= 64` by simp[] >>
  `~(w2n wo <= i /\ i < w2n wo + MIN 64 (LENGTH sc.vs_returndata))` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> simp[]
QED

Finalise ec_arith_success_frame_mods
