(* Initialize an ABI scratch cursor on one execution before choosing dead masks. *)
Theory abiEncoderWindowJointPhases
Ancestors
  abiEncoderWindowJointLeaves abiEncoderWindowArrayEntry
  abiEncoderArrayPhases abiDecoderIndexInit abiEncoderWindowStructuralMembers
  abiEncoderWindowArrayBody abiEncoderWindow abiEncoderWindowArrayLayout freshWrites
  abiEncoder abiEncoderRegisteredEffect abiEncoderPrimitiveEffect
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
  strip_tac >>
  `?c1 c2. abi_decode_index_init st = (pp,c1) /\
    emit_op MLOAD [src] c1 = (count_op,c2) /\
    emit_void MSTORE [dst;count_op] c2 = ((),en)` by
    (qpat_assum `abi_encode_array_prefix _ _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_encode_array_prefix_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]) >>
  `?a1. emit_op ALLOCA [Lit 32w] st = (pp,a1) /\
    emit_void MSTORE [pp;Lit 0w] a1 = ((),c1)` by
    (qpat_assum `abi_decode_index_init _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_index_init_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends st a1 /\ cs_extends a1 c1 /\ cs_extends c1 c2 /\
   cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `alloca_inv s /\ alloca_room ctx func s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\
   op_taint tn (Lit 0w) = {} /\
   (!x. Lit 0w = Var x ==> not_fresh_at st x)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all window_cursor_init_joint >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  rename1 `window_phase ctx func st c1 _ [] s u` >>
  suspend "after_cursor"
QED

Resume window_array_root_prefix_joint[after_cursor]:
  rename1 `src = Var sp` >> rename1 `dst = Var dp` >>
  rename1 `pp = Var cursor_var` >>
  rename1 `ptr_covers Gi ti cursor_var u 32` >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (`window_sizes32 {st.cs_next_id} u` by simp[window_sizes32_def] >>
     `abi_encoder_registered_effect {st.cs_next_id} [] s u` by
       metis_tac[window_phase_effect] >>
     qpat_assum `window_sizes32 _ u` mp_tac >>
     qpat_assum `abi_encoder_registered_effect _ _ s u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[window_sizes32_def] >> rpt strip_tac >>
     drule_all window_registered_sizes_transport >> metis_tac[]) >>
  `window_array_transition ctx func st {st.cs_next_id} [] s u` by
    metis_tac[window_array_phase_transition] >>
  `{st.cs_next_id} SUBSET ids /\
   EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) []` by simp[] >>
  `window_array_root ctx func st ids ei asz msz active ty avs
    src dst sb cap d u` by metis_tac[window_array_root_transition] >>
  `not_fresh_at st sp /\ not_fresh_at st dp` by
    fs[window_array_root_def] >>
  `cursor_var = STRING #"%" (toString st.cs_next_var)` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at st x ==> cursor_var <> x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `ptr_covers Gi ti sp u 32 /\ ptr_covers Gi ti dp u 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def, op_taint_def] >>
     simp[FLOOKUP_UPDATE] >> metis_tac[window_phase_vars]) >>
  suspend "word_pre"
QED

Resume window_array_root_prefix_joint[word_pre]:
  `32 <= cap /\ mem_word_at sb u.vs_memory = n2w (LENGTH avs)` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     fs[abi_encoder_window_array_iff]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     drule window_array_layout >> decide_tac) >>
  `alloca_inv u /\ alloca_room ctx func u /\
   fn_inst_ids_distinct func /\
   eval_operand src u = SOME (n2w sb) /\
   eval_operand dst u = SOME (n2w d) /\
   sb+32 <= u.vs_alloca_next /\ d+32 <= u.vs_alloca_next` by
    (fs[window_array_root_def] >> decide_tac) >>
  `u.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `~u.vs_halted /\ u.vs_current_bb = c1.cs_current_bb /\
   u.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_control] >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= en.cs_next_var` by
    (drule abi_decode_index_init_shape >> strip_tac >>
     `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= en.cs_next_var` by
       metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     decide_tac) >>
  `not_fresh_at c1 sp /\ not_fresh_at c1 dp` by
    metis_tac[not_fresh_at_mono] >>
  `!i. sb <= i /\ i < sb+32 ==> i NOTIN ti.t_mem` by simp[] >>
  `compile_abi_encode_to_buf dst src AbiPrimWord c1 = (Lit 32w,en)` by
    (simp_tac bool_ss [Once compile_abi_encode_child_def,
       compile_abi_encode_static_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> simp[]) >>
  `compile_abi_encode_to_buf (Var dp) (Var sp) AbiPrimWord c1 = (Lit 32w,en)` by
    metis_tac[] >>
  `eval_operand (Var sp) u = SOME (n2w sb) /\
   eval_operand (Var dp) u = SOME (n2w d)` by metis_tac[] >>
  drule_all window_word_joint_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  suspend "word_endpoint"
QED

Resume window_array_root_prefix_joint[word_endpoint]:
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (u,Gi,ti) [] (OK t,Gf,tf)` >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  `!x. dst = Var x ==> not_fresh_at c1 x` by simp[] >>
  drule_all abiEncoderWindowLeavesTheory.window_word_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 en) u = OK raw` >>
  `t = raw with vs_inst_idx := LENGTH en.cs_current_insts` by
    simp[Abbr `t`] >>
  `alloca_inv raw /\ alloca_room ctx func raw /\
   (!x. not_fresh_at c1 x ==> lookup_var x raw = lookup_var x u) /\
   window_alloca_growth u raw` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `alloca_room ctx func u` mp_tac >>
     qpat_assum `raw = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >> ntac 2 strip_tac >>
     mp_tac (Q.INST [`s` |-> `u`, `st` |-> `c1`, `w` |-> `mload sb u`,
       `ix` |-> `u.vs_inst_idx`] abiEncoderWindowLeavesTheory.window_word_state_resources) >>
     simp[mstore_def, update_var_def, write_memory_with_expansion_def] >>
     strip_tac >> fs[lookup_var_def]) >>
  `window_seq c1 en u raw` by
    simp[window_seq_def] >>
  `abi_encoder_registered_effect {} [(d,32)] u raw` by
    (qpat_assum `raw = _` SUBST1_TAC >>
     irule abi_encoder_registered_effect_trans >>
     qexists_tac `update_var (STRING #"%" (toString c1.cs_next_var)) (mload sb u) u` >>
     simp[abi_encoder_registered_update_var, abi_encoder_output_store]) >>
  `raw.vs_halted = u.vs_halted /\ raw.vs_current_bb = u.vs_current_bb` by
    (qpat_assum `raw = _` SUBST1_TAC >>
     simp[NoAsms, update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  `window_phase ctx func c1 en {} [(d,32)] u t` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     irule window_seq_phase >> simp[]) >>
  suspend "observations"
QED

Resume window_array_root_prefix_joint[observations]:
  `window_phase ctx func st en {st.cs_next_id} [(d,32)] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[(d,32)]`, `u`] >>
     simp[]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R t` by
    (rpt strip_tac >>
     `window_sizes32 R u` by metis_tac[] >>
     qpat_x_assum `window_sizes32 R u` mp_tac >>
     simp[NoAsms, window_sizes32_def, Abbr `t`, mstore_def, update_var_def,
        write_memory_with_expansion_def]) >>
  `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t` by
    metis_tac[window_array_phase_transition] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) [(d,32)]` by
    (simp[] >>
     `venomMemDefs$regions_disjoint (sb,cap)
       (d,LENGTH (enc (Array NONE ty) (ListV avs)))` by metis_tac[window_array_root_def] >>
     qpat_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
     qpat_assum `32 <= LENGTH _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def,
       GSYM LENGTH_NIL] >> decide_tac) >>
  `window_array_root ctx func st ids ei asz msz active ty avs
    src dst sb cap d t` by metis_tac[window_array_root_transition] >>
  `abi_encode_exec_frame func u t` by
    (simp[Abbr `t`] >> irule abi_encode_exec_frame_trans >>
     qexists_tac `update_var (STRING #"%" (toString c1.cs_next_var)) (mload sb u) u` >>
     conj_tac >-
       simp_tac (srw_ss()) [abi_encode_exec_frame_def, pending_alloca_size_def,
         update_var_def, exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def] >> simp[]) >>
  `abi_encode_exec_frame func s t` by metis_tac[abi_encode_exec_frame_trans] >>
  suspend "finish"
QED

Resume window_array_root_prefix_joint[finish]:
  `count_op = Var (STRING #"%" (toString c1.cs_next_var))` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
  `eval_operand count_op t = SOME (n2w (LENGTH avs))` by
    (simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def,
       mstore_def, write_memory_with_expansion_def, FLOOKUP_UPDATE,
       GSYM mem_word_at_eq_mload]) >>
  `!x. count_op = Var x ==> not_fresh_at en x` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
     qpat_assum `emit_void MSTORE [dst;count_op] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `mem_word_at d t.vs_memory = n2w (LENGTH avs)` by
    simp[Abbr `t`, mstore_mem_word_at_same, GSYM mem_word_at_eq_mload] >>
  `abi_encoder_array_prefix ty avs 0 d t.vs_memory` by
    metis_tac[abiEncoderArrayPrefixTheory.abi_encoder_array_prefix_empty] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     simp[NoAsms, Abbr `t`, allocas_from_def, mstore_def, update_var_def,
       write_memory_with_expansion_def] >> simp[]) >>
  `venomMemDefs$regions_disjoint (sb,cap) (b,32) /\
   venomMemDefs$regions_disjoint
     (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,32)` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >> metis_tac[]) >>
  `b+32 <= d \/ d+32 <= b` by
    (qpat_assum `venomMemDefs$regions_disjoint (d,_) (b,32)` mp_tac >>
     qpat_assum `32 <= LENGTH _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def, GSYM LENGTH_NIL] >>
     decide_tac) >>
  `mem_word_at b t.vs_memory = 0w` by
    simp[Abbr `t`, mstore_mem_word_at_disjoint, update_var_def] >>
  `window_array_cursor T en pp st.cs_next_id b 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) t` by
    (simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
     conj_tac >-
       (qpat_x_assum `not_fresh_at c1 cursor_var` mp_tac >>
        simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
     conj_tac >-
       (qpat_assum `window_phase ctx func c1 en {} [(d,32)] u t`
          (mp_then Any mp_tac abiEncoderWindowChildTheory.window_phase_eval_var) >>
        disch_then (qspecl_then [`n2w b`, `pp`] mp_tac) >>
        qpat_assum `eval_operand pp u = _` mp_tac >>
        qpat_assum `not_fresh_at c1 cursor_var` mp_tac >>
        qpat_assum `pp = Var cursor_var` mp_tac >>
        qpat_assum `cursor_var = _` mp_tac >>
        qpat_assum `Abbrev (t = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
     simp[Abbr `t`, mstore_def, update_var_def, write_memory_with_expansion_def]) >>
  `lookup_var cursor_var t = lookup_var cursor_var u` by
    (qpat_assum `!x. not_fresh_at c1 x ==> lookup_var x raw = _` mp_tac >>
     qpat_assum `not_fresh_at c1 cursor_var` mp_tac >>
     qpat_assum `t = raw with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def]) >>
  `FLOOKUP Gf cursor_var = FLOOKUP Gi cursor_var /\
   op_taint tf (Var cursor_var) = op_taint ti (Var cursor_var)` by metis_tac[] >>
  `ptr_covers Gf tf cursor_var t 32` by
    (qpat_assum `ptr_covers Gi ti cursor_var u 32` mp_tac >>
     qpat_assum `lookup_var cursor_var t = _` mp_tac >>
     qpat_assum `FLOOKUP Gf cursor_var = _` mp_tac >>
     qpat_assum `op_taint tf (Var cursor_var) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def]) >>
  `!x. not_fresh_at st x ==>
     FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at c1 x` by metis_tac[not_fresh_at_mono] >>
     `cursor_var <> x` by metis_tac[] >>
     `FLOOKUP Gf x = FLOOKUP Gi x /\
      op_taint tf (Var x) = op_taint ti (Var x)` by metis_tac[] >>
     qpat_assum `Gi = _` mp_tac >>
     qpat_assum `ti.t_var = _` mp_tac >>
     qpat_assum `FLOOKUP Gf x = _` mp_tac >>
     qpat_assum `op_taint tf (Var x) = _` mp_tac >>
     qpat_assum `cursor_var <> x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]) >>
  `tf.t_mem = tn.t_mem DIFF
    ({i | b <= i /\ i < b+32} UNION {i | d <= i /\ i < d+32})` by
    (qpat_assum `tf.t_mem = _` mp_tac >>
     qpat_assum `ti.t_mem = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> SET_TAC[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`, `Gi`, `ti`, `[]`, `OK t`, `Gf`, `tf`] mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gi,ti) _ _`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qexistsl_tac [`t`, `b`, `cursor_var`, `Gf`, `tf`] >> asm_rewrite_tac[]
QED

Finalise window_array_root_prefix_joint
