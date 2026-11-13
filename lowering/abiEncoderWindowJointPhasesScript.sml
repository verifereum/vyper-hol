(* Initialize an ABI scratch cursor on one execution before choosing dead masks. *)
Theory abiEncoderWindowJointPhases
Ancestors
  abiEncoderWindowJointLeaves abiEncoderWindowArrayEntry
  abiEncoderWindowArrayInvariant exprSimAbiEncodeFramedArray
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  abiEncoderWindowCursor abiEncoderWindowPhase abiEncoderWindowSequence
  allocationPtr wordLoadStorePtr fragExecPtr fragGasSeqPtr ptrSafetyTransport
  exprLoweringProps fragExec venomInstProofs
  ptrDiscipline ptrCoverage ghostPcTransportPtr emitHelperProps emitHelper compileEnv
  venomExecSemantics venomState venomMemDefs venomInst finite_map
  valueEncodingProps words list rich_list arithmetic pred_set

Theorem window_cursor_init_joint:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor;value_op] mid = ((),en) /\
  fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32) /\
  eval_operand value_op s = SOME w /\
  op_taint tn value_op = {} /\
  (!x. value_op = Var x ==> not_fresh_at st x) /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b p G' tn'.
    run_inst_seq (emitted_insts st en) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\
    abi_encode_exec_frame func s t /\
    cursor = Var p /\ not_fresh_at en p /\
    eval_operand cursor t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b + 32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = w /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    ptr_covers G' tn' p t 32 /\
    G' = G |+ (p,(b,32)) /\
    tn'.t_var = tn.t_var |+ (p,{}) /\
    tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b + 32} /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  `cursor = Var p` by simp[Abbr `p`] >>
  `emitted_insts st en =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w] [p];
     mk_inst mid.cs_next_id MSTORE [cursor;value_op] []]` by
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND, Abbr `p`] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func)` by
    (irule abi_encode_emitted_instruction_member >>
     goal_assum (drule_at Any) >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    metis_tac[markerTheory.Abbrev_def] >>
  drule_all window_cursor_init_sequence >> strip_tac >>
  rename1 `window_seq st en s raw` >>
  `raw.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt] >>
  `b < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts st en) s = OK raw` by
    fs[window_seq_def] >>
  `?u. step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]) s = OK u /\
    step_inst_base (mk_inst mid.cs_next_id MSTORE [cursor;value_op] []) u = OK raw` by
    (qpat_x_assum `run_inst_seq _ _ = OK raw` mp_tac >>
     pure_asm_rewrite_tac[run_inst_seq_def] >>
     simp_tac (srw_ss()) [AllCaseEqs()] >> metis_tac[]) >>
  `raw.vs_halted = s.vs_halted /\
   raw.vs_current_bb = s.vs_current_bb /\
   raw.vs_inst_idx = s.vs_inst_idx` by
    (`step_inst 0 ctx (mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]) s = OK u` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     `step_inst 0 ctx (mk_inst mid.cs_next_id MSTORE [cursor;value_op] []) u = OK raw` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     imp_res_tac step_preserves_control_flow >>
     imp_res_tac step_preserves_halted >>
     fs[mk_inst_def, is_terminator_def]) >>
  `window_phase ctx func st en {st.cs_next_id} [] s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_seq_phase >> simp[]) >>
  `abi_encode_exec_frame func s raw` by
    (irule abi_encode_setup_sequence_frame >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `raw = mstore b w u /\
    lookup_var p u = SOME (n2w b) /\
    u.vs_allocas = raw.vs_allocas /\
    u.vs_alloca_next = raw.vs_alloca_next` by
    (qpat_assum `step_inst_base _ u = OK raw` mp_tac >>
     qpat_assum `eval_operand cursor raw = _` mp_tac >>
     qpat_assum `mem_word_at b raw.vs_memory = w` mp_tac >>
     qpat_assum `cursor = Var p` mp_tac >>
     qpat_assum `b < dimword _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
        eval_operand_def, AllCaseEqs()] >>
     qpat_x_assum `mstore _ _ _ = raw` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `eval_operand cursor (mstore _ _ _) = _` mp_tac >>
     simp[eval_operand_def, lookup_var_def, mstore_def] >> strip_tac >>
     gvs[eval_operand_def, lookup_var_def, w2n_n2w, mstore_mem_word_at_same] >>
     simp[mstore_def]) >>
  qabbrev_tac `ai = mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]` >>
  qabbrev_tac `si = mk_inst mid.cs_next_id MSTORE [Var p;value_op] []` >>
  qabbrev_tac `Ga = step_prov PG G ai u` >>
  qabbrev_tac `ta = step_taint ai s u tn` >>
  `Ga = G |+ (p,(b,32)) /\ ptr_covers Ga ta p u 32 /\
   ta.t_var = tn.t_var |+ (p,{}) /\
   ta.t_mem DIFF {i | b <= i /\ i < b+32} =
     tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
   allocas_from lo u /\ lo <= u.vs_alloca_next` by
    suspend "allocation_alignment" >>
  `op_taint ta value_op = {}` by
    (qpat_assum `ta.t_var = _` mp_tac >>
     qpat_assum `op_taint tn value_op = {}` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `value_op` >> simp[op_taint_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[]) >>
  `eval_operand value_op u = SOME w` by
    (qpat_assum `step_inst_base _ u = OK raw` mp_tac >>
     qpat_assum `raw = mstore b w u` mp_tac >>
     qpat_assum `lookup_var p u = _` mp_tac >>
     qpat_assum `cursor = Var p` mp_tac >>
     qpat_assum `b < dimword _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
         eval_operand_def, AllCaseEqs(), w2n_n2w] >>
     metis_tac[mstore_mem_word_at_same]) >>
  qabbrev_tac `tf = step_taint si u raw ta` >>
  `step_prov PG Ga si raw = Ga /\
   tf.t_var = ta.t_var /\ tf.t_stor = ta.t_stor /\
   tf.t_trans = ta.t_trans /\
   tf.t_mem = ta.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `Ga`, `mid.cs_next_id`] mp_tac) >>
     simp_tac (srw_ss()) [Abbr `tf`, Abbr `si`] >>
     qpat_assum `raw = mstore b w u` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [w2n_n2w] >>
     metis_tac[w2n_n2w, LESS_MOD]) >>
  `tf.t_imm = ta.t_imm` by
    (qpat_assum `raw = mstore b w u` mp_tac >>
     simp_tac (srw_ss()) [Abbr `tf`, Abbr `si`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     simp[step_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def,
       mstore_def]) >>
  `ptr_covers Ga tf p raw 32 /\ allocas_from lo raw /\ lo <= raw.vs_alloca_next` by
    (qpat_assum `ptr_covers Ga ta p u 32` mp_tac >>
     qpat_assum `tf.t_var = ta.t_var` mp_tac >>
     qpat_assum `raw = mstore b w u` mp_tac >>
     qpat_assum `allocas_from lo u` mp_tac >>
     qpat_assum `lo <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def, mstore_def,
       allocas_from_def] >> metis_tac[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn ai s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (first_assum ACCEPT_TAC) >> qexists_tac `0` >> simp[] >>
     simp_tac (srw_ss()) [Abbr `ai`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Ga ta si u` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (first_assum ACCEPT_TAC) >> qexists_tac `0` >> simp[] >>
     simp_tac (srw_ss()) [Abbr `si`] >> irule ptr_inst_ok_mstore >> metis_tac[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Ga ta si
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (simp_tac (srw_ss()) [allocas_from_def] >>
       metis_tac[allocas_from_def]) >>
     qexists_tac `0` >> simp[] >>
     simp_tac (srw_ss()) [Abbr `si`] >> irule ptr_inst_ok_mstore >>
     qpat_assum `ptr_covers Ga ta p u 32` mp_tac >>
     qpat_assum `op_taint ta value_op = {}` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `Ga = G |+ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def]) >>
  `run_inst_seq_mem_ok [ai;si] s` by
    (`inst_mem_below_frontier ai s` by
       (irule instMemFrontierTheory.below_frontier_no_ranges >>
        simp[Abbr `ai`, mk_inst_def]) >>
     `inst_mem_below_frontier si u` by
       (simp_tac (srw_ss()) [Abbr `si`, instMemFrontierTheory.below_frontier_MSTORE] >>
        qpat_assum `lookup_var p u = _` mp_tac >>
        qpat_assum `u.vs_alloca_next = _` mp_tac >>
        qpat_assum `b + 32 <= raw.vs_alloca_next` mp_tac >>
        qpat_assum `b < dimword _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        gvs[eval_operand_def, w2n_n2w]) >>
     `inst_dload_in_section ai s /\ inst_dload_in_section si u` by
       simp_tac (srw_ss()) [Abbr `ai`, Abbr `si`,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     simp_tac (srw_ss()) [fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >>
     Cases_on `step_inst_base si u` >> simp_tac (srw_ss()) []) >>
  `step_inst_base si u = OK raw` by
    metis_tac[markerTheory.Abbrev_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [ai;si] s Ga tf` by
    (gen_tac >>
     `step_inst_base si (u with vs_inst_idx := SUC s.vs_inst_idx) =
       OK (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
          Abbr `si`, mk_inst_def, is_terminator_def] >>
        qpat_assum `step_inst_base si u = OK raw` mp_tac >>
        simp_tac (srw_ss()) [mk_inst_def] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[instIdxIndepTheory.exec_result_map_def]) >>
     qpat_assum `step_inst_base ai s = OK u` mp_tac >>
     qpat_assum `step_inst_base si (u with vs_inst_idx := _) = _` mp_tac >>
     qpat_assum `!D. ptr_inst_ok D lo 0 ctx func G tn ai s` mp_tac >>
     qpat_assum `!D. ptr_inst_ok D lo 0 ctx func Ga ta si (u with vs_inst_idx := _)` mp_tac >>
     qpat_assum `step_prov PG Ga si raw = Ga` mp_tac >>
     simp_tac (srw_ss()) [Abbr `Ga`, Abbr `ta`, Abbr `tf`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[inst_seq_ptr_def]) >>
  `en.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit 32w] [p];
       mk_inst mid.cs_next_id MSTORE [Var p;value_op] []] /\
   en.cs_current_bb = st.cs_current_bb` by
    (conj_tac >- (asm_rewrite_tac[APPEND_ASSOC] >>
         simp_tac (srw_ss()) [Abbr `ai`]) >>
     metis_tac[window_seq_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [mk_inst st.cs_next_id ALLOCA [Lit 32w] [p];
       mk_inst mid.cs_next_id MSTORE [Var p;value_op] []]
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code st en func` mp_tac >>
     qpat_assum `en.cs_current_insts = _` mp_tac >>
     qpat_assum `en.cs_current_bb = _` mp_tac >>
     qpat_assum `s.vs_current_bb = _` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >>
     qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp_tac (srw_ss()) []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),Ga,tf)` by
    (gen_tac >>
     `s.vs_inst_idx + 2 = LENGTH en.cs_current_insts` by
       (qpat_assum `en.cs_current_insts = _` mp_tac >>
        qpat_assum `s.vs_inst_idx = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `isPREFIX [ai;si] (DROP s.vs_inst_idx bb.bb_instructions)` by
       metis_tac[markerTheory.Abbrev_def] >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [ai;si]` by
       simp[Abbr `ai`, Abbr `si`, mk_inst_def, is_terminator_def] >>
     `run_inst_seq [ai;si] s = OK raw` by
       metis_tac[markerTheory.Abbrev_def] >>
     `inst_seq_ptr D lo ctx func PG G tn [ai;si] s Ga tf` by metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `ai`, Abbr `si`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`,
    `b`, `p`, `Ga`, `tf`] >>
  qpat_x_assum `raw = mstore b w u` kall_tac >>
  qpat_x_assum `u.vs_allocas = _` kall_tac >>
  qpat_x_assum `u.vs_alloca_next = _` kall_tac >>
  simp[allocas_from_def, bodyPtrDefsTheory.ptr_covers_def,
    eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (qpat_assum `raw.vs_inst_idx = _` mp_tac >>
      qpat_assum `s.vs_inst_idx = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `p`] >>
      rpt strip_tac >> irule fresh_var_distinct >> decide_tac) >>
  metis_tac[allocas_from_def]
QED

Resume window_cursor_init_joint[allocation_alignment]:
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)] [p]) s = OK u` by
    metis_tac[markerTheory.Abbrev_def] >>
  `FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32)` by metis_tac[] >>
  `u.vs_alloca_next < dimword (:256)` by metis_tac[] >>
  `32 < dimword (:256)` by simp[] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      `u = update_var p (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,32));
                  vs_alloca_next := s.vs_alloca_next + 32|>)` by
        (drule_all loweringHaltTheory.step_alloca_fresh >>
         disch_then (qspec_then `p` mp_tac) >>
         qpat_assum `step_inst_base (mk_inst _ _ _ _) s = OK u` mp_tac >>
         simp_tac (srw_ss()) []) >>
      `b = s.vs_alloca_next /\ s.vs_alloca_next + 32 < dimword (:256)` by
        (qpat_assum `FLOOKUP u.vs_allocas _ = _` mp_tac >>
         qpat_assum `u.vs_alloca_next < _` mp_tac >>
         qpat_assum `u = update_var _ _ _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp_tac (srw_ss()) [update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
      `ptr_covers Ga ta p u 32` by
        (simp_tac (srw_ss()) [Abbr `Ga`, Abbr `ta`, Abbr `ai`] >>
         irule (cj 1 fresh_alloca_ptr_covers) >> simp[]) >>
      `allocas_from lo u /\ lo <= u.vs_alloca_next` by
        (qpat_assum `u = update_var _ _ _` mp_tac >>
         qpat_assum `allocas_from lo s` mp_tac >>
         qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
         rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
      `Ga = G |+ (p,(b,32)) /\
       ta = tn with <|t_mem := tn.t_mem UNION {i | b <= i /\ i < b+32};
                     t_var := tn.t_var |+ (p,{})|>` by
        metis_tac[markerTheory.Abbrev_def] >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
      pred_setLib.SET_TAC[]) >>
  PairCases_on `x` >>
  `x1 = 32` by metis_tac[] >>
  `u = update_var p (n2w x0) s` by
    (drule reused_alloca_step >>
     disch_then (qspec_then `p` mp_tac) >>
     qpat_assum `step_inst_base (mk_inst _ _ _ _) s = OK u` mp_tac >>
     qpat_assum `x1 = 32` mp_tac >>
     simp_tac (srw_ss()) []) >>
  `x0 = b` by
    (qpat_assum `u = update_var _ _ _` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = _` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas _ = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[update_var_def]) >>
  `b + 32 < dimword (:256)` by decide_tac >>
  `ptr_covers Ga ta p u 32` by
    (simp_tac (srw_ss()) [Abbr `Ga`, Abbr `ta`, Abbr `ai`] >>
     qpat_assum `u = update_var _ _ _` SUBST1_TAC >>
     irule (cj 1 reused_alloca_ptr_covers) >> metis_tac[]) >>
  `Ga = G |+ (p,(b,32)) /\
   ta = tn with t_var := tn.t_var |+ (p,{})` by
    (drule reused_alloca_ghost >>
     disch_then (qspecl_then [`p`, `PG`, `G`, `tn`] strip_assume_tac) >>
     metis_tac[markerTheory.Abbrev_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `u = update_var _ _ _` mp_tac >>
     qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) []
QED

Finalise window_cursor_init_joint


Theorem window_array_root_prefix_joint:
  window_array_root ctx func st ids ei asz msz active ty avs
    src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),en) /\
  st.cs_next_id IN ids /\
  fn_has_code st en func /\
  (?p. src = Var p /\ ptr_covers G tn p s 32) /\
  (?p. dst = Var p /\ ptr_covers G tn p s 32) /\
  (!i. sb <= i /\ i < sb + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b p G' tn'.
    window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st
      {st.cs_next_id} [(d,32)] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs
      src dst sb cap d t /\
    abi_encoder_array_prefix ty avs 0 d t.vs_memory /\
    window_array_cursor T en pp st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    abi_encode_exec_frame func s t /\
    pp = Var p /\ ptr_covers G' tn' p t 32 /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\
    op_taint tn' count_op = {} /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    tn'.t_mem =
      tn.t_mem DIFF
        ({i | b <= i /\ i < b + 32} UNION
         {i | d <= i /\ i < d + 32}) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  cheat
QED
