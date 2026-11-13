(* Initialize an ABI scratch cursor on one execution before choosing dead masks. *)
Theory abiEncoderWindowJointPhases
Ancestors
  abiEncoderChildCode abiEncoderWindowChild abiEncoderWindowSequence
  abiEncoderArrayTailInit
  abiEncoderWindowJointLeaves abiEncoderWindowArrayEntry
  abiEncoderArrayPhases abiDecoderIndexInit abiEncoderWindowStructuralMembers
  abiEncoderWindowArrayBody abiEncoderWindow abiEncoderWindowArrayLayout freshWrites
  abiEncoder abiEncoderRegisteredEffect abiEncoderPrimitiveEffect
  abiEncoderWindowArrayInvariant exprSimAbiEncodeFramedArray
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  exprSimAbiEncodeFramedArrayBody
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


Theorem window_array_root_prefix_joint_strong:
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
    op_prov G' count_op = NONE /\
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

Resume window_array_root_prefix_joint_strong[after_cursor]:
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

Resume window_array_root_prefix_joint_strong[word_pre]:
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
  drule_all window_word_joint_path_strong >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  suspend "word_endpoint"
QED

Resume window_array_root_prefix_joint_strong[word_endpoint]:
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

Resume window_array_root_prefix_joint_strong[observations]:
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

Resume window_array_root_prefix_joint_strong[finish]:
  `count_op = Var (STRING #"%" (toString c1.cs_next_var))` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
  `op_prov Gf count_op = NONE` by simp[] >>
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

Finalise window_array_root_prefix_joint_strong

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
  rpt gen_tac >>
  disch_then (mp_tac o MATCH_MP window_array_root_prefix_joint_strong) >>
  metis_tac[]
QED

Theorem window_array_root_tail_init_joint:
  window_array_root ctx func st ids ei asz msz active ty avs
    src dst sb cap d s /\
  abi_encode_array_tail_init count_op asz st = (dp,en) /\
  st.cs_next_id IN ids /\
  fn_has_code st en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  op_taint tn count_op = {} /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b p G' tn'.
    run_inst_seq (emitted_insts st en) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs
      src dst sb cap d t /\
    window_array_cursor T en dp st.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (contractABI$enc (Array NONE ty) (ListV avs))) t /\
    abi_encode_exec_frame func s t /\
    dp = Var p /\
    ptr_covers G' tn' p t 32 /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b + 32} /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule window_array_tail_init_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_op ALLOCA _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `q = STRING #"%" (toString c1.cs_next_var)` >>
  `dp = Var p /\ offset = Var q` by simp[Abbr `p`, Abbr `q`] >>
  `emitted_insts st en =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w] [p];
     mk_inst c1.cs_next_id MUL [count_op;Lit (n2w asz)] [q];
     mk_inst c2.cs_next_id MSTORE [dp;offset] []]` by
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND, Abbr `p`, Abbr `q`] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (irule abi_encode_emitted_instruction_member >>
     goal_assum (drule_at Any) >> simp[Abbr `p`]) >>
  drule_all abi_encode_framed_array_root_tail_init_sequence >> strip_tac >>
  qabbrev_tac `raw = t with vs_inst_idx := s.vs_inst_idx` >>
  qabbrev_tac `ai = mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]` >>
  qabbrev_tac `mi = mk_inst c1.cs_next_id MUL [count_op;Lit (n2w asz)] [q]` >>
  qabbrev_tac `si = mk_inst c2.cs_next_id MSTORE [Var p;Var q] []` >>
  `?u v. step_inst_base ai s = OK u /\
     step_inst_base mi u = OK v /\ step_inst_base si v = OK raw` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     pure_asm_rewrite_tac[run_inst_seq_def] >>
     simp_tac (srw_ss()) [AllCaseEqs(), Abbr `ai`, Abbr `mi`, Abbr `si`, Abbr `raw`] >>
     metis_tac[]) >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     qpat_assum `st.cs_next_id IN ids` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  `eval_operand dp t = SOME (n2w b) /\
   FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
   b+32 <= t.vs_alloca_next /\ b < dimword (:256)` by
    (qpat_assum `window_array_cursor _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
     drule window_phase_resources >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  `p <> q` by
    (simp[Abbr `p`, Abbr `q`] >> irule fresh_var_distinct >> simp[]) >>
  `raw = mstore b (THE (lookup_var q v)) v /\
   lookup_var p v = SOME (n2w b) /\
   v.vs_allocas = t.vs_allocas /\ v.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `step_inst_base si v = OK raw` mp_tac >>
     qpat_assum `eval_operand dp t = _` mp_tac >>
     qpat_assum `dp = Var p` mp_tac >>
     qpat_assum `b < dimword _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `si`, Abbr `raw`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       eval_operand_def, AllCaseEqs()] >>
     `lookup_var p v = lookup_var p t /\
      v.vs_allocas = t.vs_allocas /\ v.vs_alloca_next = t.vs_alloca_next` by
       (qpat_x_assum `mstore _ _ _ = _` mp_tac >>
        simp_tac (srw_ss()) [mstore_def, lookup_var_def, venom_state_component_equality] >>
        metis_tac[]) >>
     gvs[w2n_n2w]) >>
  `?w. v = update_var q w u` by
    (qpat_assum `step_inst_base mi u = OK v` mp_tac >>
     simp_tac (srw_ss()) [Abbr `mi`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `lookup_var p u = SOME (n2w b) /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `v = update_var q w u` mp_tac >>
     qpat_assum `lookup_var p v = _` mp_tac >>
     qpat_assum `v.vs_allocas = _` mp_tac >>
     qpat_assum `v.vs_alloca_next = _` mp_tac >>
     qpat_assum `p <> q` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[window_phase_resources, alloca_room_next_lt] >>
  qabbrev_tac `Ga = step_prov PG G ai u` >>
  qabbrev_tac `ta = step_taint ai s u tn` >>
  `Ga = G |+ (p,(b,32)) /\ ptr_covers Ga ta p u 32 /\
   ta.t_var = tn.t_var |+ (p,{}) /\
   ta.t_mem DIFF {i | b <= i /\ i < b+32} =
     tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
   allocas_from lo u /\ lo <= u.vs_alloca_next` by
    suspend "tail_allocation" >>
  `!x. not_fresh_at st x ==> x <> p /\ x <> q` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `p`, Abbr `q`] >>
     rpt strip_tac >> irule fresh_var_distinct >> decide_tac) >>
  `op_taint ta count_op = {}` by
    (qpat_assum `ta.t_var = _` mp_tac >>
     qpat_assum `op_taint tn count_op = {}` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `count_op` >>
     simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     simp[] >> IF_CASES_TAC >> simp[]) >>
  qabbrev_tac `Gm = step_prov PG Ga mi v` >>
  qabbrev_tac `tm = step_taint mi u v ta` >>
  `Gm = Ga \\ q /\
   tm = ta with t_var := ta.t_var |+ (q,{})` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (Gm = _)`, `Abbrev (tm = _)`, `Abbrev (mi = _)`,
        `v = update_var q w u`, `p <> q`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[Abbr `Gm`, Abbr `tm`, Abbr `mi`, step_prov_def, out_prov_def,
       set_prov_def, step_taint_def, mk_inst_def,
       mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def, update_var_def,
       set_var_taint_def, out_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, AllCaseEqs(), taint_component_equality]
     >- (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
         gen_tac >> Cases_on `x = q` >> simp[]) >>
     conj_tac
     >- (simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
     Cases_on `eval_operand count_op u` >> simp[]) >>
  `ptr_covers Gm tm p v 32 /\ allocas_from lo v /\ lo <= v.vs_alloca_next /\
   op_taint tm (Var q) = {} /\ eval_operand (Var q) v = SOME w` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Ga ta p u 32`, `Gm = _`, `tm = _`, `v = update_var q w u`,
        `p <> q`, `allocas_from lo u`, `lo <= u.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[bodyPtrDefsTheory.ptr_covers_def, allocas_from_def,
       update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
       FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  qabbrev_tac `tf = step_taint si v raw tm` >>
  `step_prov PG Gm si raw = Gm /\
   tf.t_var = tm.t_var /\ tf.t_stor = tm.t_stor /\
   tf.t_trans = tm.t_trans /\
   tf.t_mem = tm.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var p v = _`, `eval_operand (Var q) v = SOME w`,
        `op_taint tm (Var q) = {}`, `raw = mstore _ _ _`,
        `b < dimword _`, `Abbrev (tf = _)`, `Abbrev (si = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `raw = mstore b w v` by gvs[eval_operand_def] >>
     drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `Gm`, `c2.cs_next_id`] mp_tac) >>
     simp[Abbr `tf`, Abbr `si`, w2n_n2w]) >>
  `tf.t_imm = tm.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tf`, Abbr `si`, step_taint_def,
      imm_taint_def, set_var_taint_def, adopt_reset_def, mk_inst_def, LET_THM]) >>
  `ptr_covers Gm tf p raw 32 /\ allocas_from lo raw /\ lo <= raw.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gm tm p v 32`, `tf.t_var = tm.t_var`,
        `raw = mstore _ _ _`, `allocas_from lo v`, `lo <= v.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def,
       mstore_def, allocas_from_def] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==>
     FLOOKUP Gm x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Gm = _`, `Ga = _`, `tf.t_var = _`, `tm = _`, `ta.t_var = _`,
        `!x. not_fresh_at st x ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[op_taint_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM]) >>
  `tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    (qpat_assum `tm = _` (fn th => rewrite_tac[th]) >>
     asm_rewrite_tac[] >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn ai s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (first_assum ACCEPT_TAC) >> qexists_tac `0` >> simp[] >>
     simp_tac (srw_ss()) [Abbr `ai`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Ga ta mi
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint ta count_op = {}`, `~ctx_has_dalloca ctx`,
        `allocas_from lo u`, `Abbrev (mi = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[Abbr `mi`, ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `op = count_op` >> gvs[] >>
         Cases_on `op = Lit (n2w asz)` >> gvs[op_taint_def]) >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, AllCaseEqs(), update_var_def] >>
     conj_tac >- gvs[allocas_from_def] >> rpt strip_tac >> gvs[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Gm tm si
      (v with vs_inst_idx := s.vs_inst_idx + 2)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (simp_tac (srw_ss()) [allocas_from_def] >>
       metis_tac[allocas_from_def]) >>
     qexists_tac `0` >> simp_tac (srw_ss()) [] >>
     simp_tac (srw_ss()) [Abbr `si`] >> irule ptr_inst_ok_mstore >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gm tm p v 32`, `op_taint tm (Var q) = {}`,
        `~ctx_has_dalloca ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def, lookup_var_def]) >>
  `run_inst_seq_mem_ok [ai;mi;si] s` by
    (`inst_mem_below_frontier ai s /\ inst_mem_below_frontier mi u` by
       (conj_tac >> irule instMemFrontierTheory.below_frontier_no_ranges >>
        simp[Abbr `ai`, Abbr `mi`, mk_inst_def]) >>
     `inst_mem_below_frontier si v` by
       (simp_tac (srw_ss()) [Abbr `si`, instMemFrontierTheory.below_frontier_MSTORE] >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`lookup_var p v = _`, `v.vs_alloca_next = _`,
           `b+32 <= t.vs_alloca_next`, `b < dimword _`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        gvs[eval_operand_def, w2n_n2w]) >>
     `inst_dload_in_section ai s /\ inst_dload_in_section mi u /\
      inst_dload_in_section si v` by
       simp_tac (srw_ss()) [Abbr `ai`, Abbr `mi`, Abbr `si`,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`inst_mem_below_frontier ai s`, `inst_mem_below_frontier mi u`,
        `inst_mem_below_frontier si v`, `inst_dload_in_section ai s`,
        `inst_dload_in_section mi u`, `inst_dload_in_section si v`,
        `step_inst_base ai s = OK u`, `step_inst_base mi u = OK v`,
        `step_inst_base si v = OK raw`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_def]) >>
  `step_inst_base mi (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
       Abbr `mi`, mk_inst_def, is_terminator_def] >>
     qpat_assum `step_inst_base mi u = OK v` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[instIdxIndepTheory.exec_result_map_def]) >>
  `step_inst_base si (v with vs_inst_idx := s.vs_inst_idx+2) =
     OK (raw with vs_inst_idx := s.vs_inst_idx+2)` by
    (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
       Abbr `si`, mk_inst_def, is_terminator_def] >>
     qpat_assum `step_inst_base si v = OK raw` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[instIdxIndepTheory.exec_result_map_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [ai;mi;si] s Gm tf` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`step_inst_base ai s = OK u`,
        `step_inst_base mi (u with vs_inst_idx := _) = _`,
        `step_inst_base si (v with vs_inst_idx := _) = _`,
        `!D. ptr_inst_ok D lo 0 ctx func G tn ai s`,
        `!D. ptr_inst_ok D lo 0 ctx func Ga ta mi _`,
        `!D. ptr_inst_ok D lo 0 ctx func Gm tm si _`,
        `step_prov PG Gm si raw = Gm`] >>
     simp_tac (srw_ss()) [Abbr `Ga`, Abbr `ta`, Abbr `Gm`, Abbr `tm`, Abbr `tf`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[arithmeticTheory.ADD1] >> simp[inst_seq_ptr_def, arithmeticTheory.ADD1]) >>
  `en.cs_current_insts = st.cs_current_insts ++ [ai;mi;si] /\
   en.cs_current_bb = st.cs_current_bb` by
    (conj_tac
     >- (simp_tac (srw_ss()) [Abbr `si`] >> asm_rewrite_tac[APPEND_ASSOC] >>
         simp_tac (srw_ss()) [GSYM APPEND_ASSOC]) >>
     (map_every (fn pat => qpat_assum pat mp_tac)
        [`emit_op ALLOCA _ st = _`, `emit_op MUL _ c1 = _`,
         `emit_void MSTORE _ c2 = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
           fresh_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, LET_THM] >>
      rpt strip_tac >> gvs[])) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [ai;mi;si] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code st en func`, `en.cs_current_insts = _`,
        `en.cs_current_bb = _`, `s.vs_current_bb = _`, `s.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),Gm,tf)` by
    (gen_tac >>
     `s.vs_inst_idx + 3 = LENGTH en.cs_current_insts` by
       (qpat_assum `en.cs_current_insts = _` mp_tac >>
        qpat_assum `s.vs_inst_idx = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [ai;mi;si]` by
       simp[Abbr `ai`, Abbr `mi`, Abbr `si`, mk_inst_def, is_terminator_def] >>
     `run_inst_seq [ai;mi;si] s = OK raw` by
       metis_tac[markerTheory.Abbrev_def] >>
     `inst_seq_ptr D lo ctx func PG G tn [ai;mi;si] s Gm tf` by metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `ai`, Abbr `mi`, Abbr `si`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `t.vs_inst_idx = LENGTH en.cs_current_insts` by
    (qpat_assum `window_phase ctx func st en _ _ s t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[window_phase_def, window_seq_def]) >>
  `raw with vs_inst_idx := LENGTH en.cs_current_insts = t` by
    (qpat_assum `t.vs_inst_idx = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `raw`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[venom_state_component_equality]) >>
  `ptr_covers Gm tf p t 32 /\ allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gm tf p raw 32`, `allocas_from lo raw`,
        `lo <= raw.vs_alloca_next`] >>
     simp_tac (srw_ss()) [Abbr `raw`, bodyPtrDefsTheory.ptr_covers_def,
                          allocas_from_def, lookup_var_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qexistsl_tac [`t`, `b`, `p`, `Gm`, `tf`] >>
  qpat_x_assum `raw = mstore _ _ _` kall_tac >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [GSYM markerTheory.Abbrev_def] >>
  metis_tac[markerTheory.Abbrev_def]
QED

Resume window_array_root_tail_init_joint[tail_allocation]:
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)] [p]) s = OK u` by
    metis_tac[markerTheory.Abbrev_def] >>
  `FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32)` by metis_tac[] >>
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

Finalise window_array_root_tail_init_joint

(* The dynamic child setup shares one raw endpoint and ghost pair. *)
Theorem window_child_prefix_joint:
  abi_encode_child_prefix (Var dst) ho (Var dp) st = (ops,en) /\
  fn_has_code st en func /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  eval_operand (Var dp) s = SOME (n2w slot) /\
  not_fresh_at st dst /\ not_fresh_at st dp /\
  ptr_covers G tn dst s bound /\ ptr_covers G tn dp s 32 /\
  ho + 32 <= bound /\ off <= bound /\
  d + bound <= s.vs_alloca_next /\
  slot + 32 <= s.vs_alloca_next /\
  mem_word_at slot s.vs_memory = n2w off /\
  (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn.t_mem) /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn' hp cp.
    run_inst_seq (emitted_insts st en) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    window_phase ctx func st en {} [] s t /\
    abi_encode_exec_frame func s t /\
    FST ops = Var hp /\ SND (SND ops) = Var cp /\
    eval_operand (FST ops) t = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
      SND (SND ops) = Var x ==> not_fresh_at en x) /\
    op_taint tn' (FST ops) = {} /\
    op_taint tn' (FST (SND ops)) = {} /\
    op_taint tn' (SND (SND ops)) = {} /\
    ptr_covers G' tn' hp t 32 /\
    ptr_covers G' tn' cp t (bound-off) /\
    t.vs_memory = s.vs_memory /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule_all window_child_prefix_context >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `slot < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st a s u` >>
  `st.cs_next_var <= a.cs_next_var` by fs[window_pure_seq_def, window_seq_def] >>
  `not_fresh_at a dp` by metis_tac[not_fresh_at_mono] >>
  `eval_operand (Var dp) u = SOME (n2w slot)` by
    fs[window_pure_seq_def, window_seq_def, eval_operand_def] >>
  drule_all window_emit_load_pure >> strip_tac >>
  rename1 `window_pure_seq a b u v` >>
  `a.cs_next_var <= b.cs_next_var` by fs[window_pure_seq_def, window_seq_def] >>
  `not_fresh_at b dst` by metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
  `window_pure_seq st b s v` by metis_tac[window_pure_seq_chain] >>
  `eval_operand (Var dst) v = SOME (n2w d)` by
    fs[window_pure_seq_def, window_seq_def, eval_operand_def] >>
  `eval_operand offset v = SOME (n2w off)` by
    fs[window_pure_seq_def, GSYM mem_word_at_eq_mload] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq b en v raw` >>
  `window_pure_seq st en s raw` by metis_tac[window_pure_seq_chain] >>
  `window_phase ctx func st en {} [] s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_pure_seq_phase >> simp[]) >>
  qpat_assum `emit_op ADD [Var dst;Lit (n2w ho)] _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD [Var dst;offset] _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qabbrev_tac `hp = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `opv = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `childp = STRING #"%" (toString b.cs_next_var)` >>
  `head = Var hp /\ offset = Var opv /\ child = Var childp` by
    simp[Abbr `hp`, Abbr `opv`, Abbr `childp`] >>
  `!x. not_fresh_at st x ==> hp <> x /\ opv <> x /\ childp <> x` by
    (simp[Abbr `hp`, Abbr `opv`, Abbr `childp`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_TRANS]) >>
  `hp <> opv /\ hp <> childp /\ opv <> childp` by
    (simp[Abbr `hp`, Abbr `opv`, Abbr `childp`] >>
     rpt conj_tac >> irule fresh_var_distinct >> decide_tac) >>
  qabbrev_tac `i1 = mk_inst st.cs_next_id ADD [Var dst;Lit (n2w ho)] [hp]` >>
  qabbrev_tac `i2 = mk_inst a.cs_next_id MLOAD [Var dp] [opv]` >>
  qabbrev_tac `i3 = mk_inst b.cs_next_id ADD [Var dst;offset] [childp]` >>
  `emitted_insts st en = [i1;i2;i3]` by
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND,
      Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `hp`, Abbr `opv`, Abbr `childp`] >>
  `abi_encode_exec_frame func s raw` by
    (irule abi_encode_framed_ordinary_pure_sequence >>
     qexistsl_tac [`en`, `st`] >>
     simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def,
       is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  `step_inst_base i1 s = OK u /\ step_inst_base i2 u = OK v /\
   step_inst_base i3 v = OK raw` by
    (gvs[window_pure_seq_def, window_seq_def, run_inst_seq_def,
       Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `hp`, Abbr `opv`, Abbr `childp`,
       AllCaseEqs()]) >>
  `eval_operand (Var opv) v = SOME (n2w off)` by metis_tac[] >>
  `u = update_var hp (n2w (d+ho)) s /\
   v = update_var opv (n2w off) u /\
   raw = update_var childp (n2w (d+off)) v` by
    (rpt conj_tac
     >- (qpat_x_assum `step_inst_base i1 s = OK u` mp_tac >>
         simp[Abbr `i1`, mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
           word_add_n2w] >> metis_tac[])
     >- (qpat_x_assum `step_inst_base i2 u = OK v` mp_tac >>
         simp[Abbr `i2`, step_inst_base_opcode_eqs, exec_read1_def,
           w2n_n2w, LESS_MOD] >>
         `mload slot u = n2w off` by
           fs[window_pure_seq_def, GSYM mem_word_at_eq_mload] >>
         simp[] >> metis_tac[]) >>
     qpat_x_assum `step_inst_base i3 v = OK raw` mp_tac >>
     simp[Abbr `i3`, step_inst_base_opcode_eqs, exec_pure2_def,
       word_add_n2w] >> metis_tac[]) >>
  qabbrev_tac `G1 = step_prov PG G i1 u` >>
  qabbrev_tac `tn1 = step_taint i1 s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 v` >>
  qabbrev_tac `tn2 = step_taint i2 u v tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i3 raw` >>
  qabbrev_tac `tn3 = step_taint i3 v raw tn2` >>
  `tn1.t_var = tn.t_var |+ (hp,{}) /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp[Abbr `tn1`, Abbr `i1`, step_taint_def, mk_inst_def,
      set_var_taint_def, out_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      update_var_def, FLOOKUP_DEF] >> SET_TAC[]) >>
  `op_taint tn2 (Var opv) = {} /\ tn2.t_mem = tn.t_mem /\
   tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans` by
    (simp[Abbr `tn2`, Abbr `i2`] >>
     qpat_assum `eval_operand (Var dp) u = _`
       (mp_then Any mp_tac mload_ghost_clean) >>
     simp[w2n_n2w, LESS_MOD] >>
     `mload slot u = n2w off` by
       fs[window_pure_seq_def, GSYM mem_word_at_eq_mload] >>
     metis_tac[]) >>
  `tn3.t_var = tn2.t_var |+ (childp,{}) /\
   tn3.t_mem = tn.t_mem /\ tn3.t_stor = tn.t_stor /\
   tn3.t_trans = tn.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (simp[Abbr `tn3`, Abbr `i3`, step_taint_def, mk_inst_def,
      set_var_taint_def, out_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      FLOOKUP_DEF] >> simp[update_var_def, FLOOKUP_DEF] >>
     CASE_TAC >> simp[] >> SET_TAC[]) >>
  `tn2.t_imm = tn.t_imm /\
   !x. x <> opv ==> FLOOKUP tn2.t_var x = FLOOKUP tn1.t_var x` by
    simp[Abbr `tn2`, Abbr `i2`, step_taint_def, mk_inst_def,
      imm_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >>
  `op_taint tn3 (Var hp) = {} /\ op_taint tn3 (Var opv) = {} /\
   op_taint tn3 (Var childp) = {}` by
    (simp[op_taint_def, FLOOKUP_UPDATE] >>
     gvs[op_taint_def]) >>
  `?gbase gsize. FLOOKUP G dst = SOME (gbase,gsize)` by
    metis_tac[bodyPtrDefsTheory.ptr_covers_def] >>
  `hp <> dst /\ opv <> dst /\ childp <> dst` by metis_tac[] >>
  `G1 = G |+ (hp,(gbase,gsize)) /\
   G2 = DRESTRICT G1 (COMPL {opv}) /\
   G3 = G2 |+ (childp,(gbase,gsize))` by
    simp[Abbr `G1`, Abbr `G2`, Abbr `G3`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
      step_prov_def, set_prov_def, out_prov_def, first_prov_def,
      op_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `!x. not_fresh_at st x ==>
    FLOOKUP G3 x = FLOOKUP G x /\
    op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `hp <> x /\ opv <> x /\ childp <> x` by metis_tac[] >>
     simp[Abbr `G3`, Abbr `G2`, Abbr `G1`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  `eval_operand (Var hp) raw = SOME (n2w (d+ho)) /\
   eval_operand (Var opv) raw = SOME (n2w off) /\
   eval_operand (Var childp) raw = SOME (n2w (d+off))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `d+ho < dimword (:256) /\ d+off < dimword (:256)` by
    (conj_tac >- decide_tac >>
     Cases_on `off = bound` >- decide_tac >> decide_tac) >>
  `lookup_var dst s = SOME (n2w d) /\
   lookup_var hp raw = SOME (n2w (d+ho)) /\
   lookup_var childp raw = SOME (n2w (d+off))` by
    metis_tac[eval_operand_def] >>
  `d < dimword (:256)` by decide_tac >>
  `gbase <= d /\ d+bound <= gbase+gsize` by
    (qpat_x_assum `ptr_covers G tn dst s bound` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def, w2n_n2w, LESS_MOD]) >>
  `ptr_covers G3 tn3 hp raw 32 /\
   ptr_covers G3 tn3 childp raw (bound-off)` by
    (simp[bodyPtrDefsTheory.ptr_covers_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, w2n_n2w, LESS_MOD] >> decide_tac) >>
  `hp <> dp /\ opv <> dp /\ childp <> dp` by metis_tac[] >>
  `ptr_covers G1 tn1 dp u 32 /\ op_taint tn2 (Var dst) = {}` by
    (qpat_x_assum `ptr_covers G tn dp s 32` mp_tac >>
     qpat_x_assum `ptr_covers G tn dst s bound` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def, update_var_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq_mem_ok [i1;i2;i3] s` by
    (pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     qpat_assum `step_inst_base i1 s = OK u` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `step_inst_base i2 u = OK v` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `step_inst_base i3 v = OK raw` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     simp[Abbr `i1`, Abbr `i2`, Abbr `i3`,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def] >>
     `lookup_var dp s = SOME (n2w slot)` by metis_tac[eval_operand_def] >>
     simp[w2n_n2w, LESS_MOD, update_var_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G tn i1
     (s with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i1`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       allocas_from_def, op_taint_def, step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, AllCaseEqs()] >>
     conj_tac
     >- (`op_taint tn (Var dst) = {}` by
           metis_tac[bodyPtrDefsTheory.ptr_covers_def] >>
         gen_tac >> Cases_on `op = Var dst` >> simp[] >>
         Cases_on `FLOOKUP tn.t_var dst` >> fs[op_taint_def]) >>
     metis_tac[allocas_from_def]) >>
  `allocas_from lo u /\ allocas_from lo v` by
    (simp[allocas_from_def, update_var_def] >> metis_tac[allocas_from_def]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1 i2
      (u with vs_inst_idx := k)` by
    (rpt gen_tac >>
     `ptr_inst_ok D 0 0 ctx func G1 tn1 i2 (u with vs_inst_idx := k)` by
       (simp[NoAsms, Abbr `i2`] >> irule ptr_inst_ok_mload >>
        simp[NoAsms] >> metis_tac[]) >>
     `allocas_from lo (u with vs_inst_idx := k)` by
       (simp[NoAsms, allocas_from_def] >> metis_tac[allocas_from_def]) >>
     metis_tac[ptr_inst_ok_lower_bound_transport, ZERO_LESS_EQ]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G2 tn2 i3
      (v with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i3`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       allocas_from_def, step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, AllCaseEqs()] >>
     conj_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     conj_tac >- metis_tac[allocas_from_def] >>
     rpt strip_tac >> gvs[]) >>
  `!k. step_inst_base i2 (u with vs_inst_idx := k) =
       OK (v with vs_inst_idx := k) /\
       step_inst_base i3 (v with vs_inst_idx := k) =
       OK (raw with vs_inst_idx := k)` by
    (gen_tac >>
     `~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
       simp[Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
     asm_simp_tac bool_ss [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i1;i2;i3] s G3 tn3` by
    (gen_tac >>
     pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base i1 s = OK u` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     qpat_assum `!k. step_inst_base i2 _ = _ /\ _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     qpat_assum `!k. step_inst_base i2 _ = _ /\ _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (G1 = _)`, `Abbrev (tn1 = _)`,
        `Abbrev (G2 = _)`, `Abbrev (tn2 = _)`,
        `Abbrev (G3 = _)`, `Abbrev (tn3 = _)`] >>
     conj_tac
     >- (qpat_assum `!D k. ptr_inst_ok D lo 0 ctx func G tn i1 _`
           (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     metis_tac[]) >>
  `en.cs_current_insts = st.cs_current_insts ++ [i1;i2;i3] /\
   en.cs_current_bb = st.cs_current_bb` by
    (conj_tac >- simp[APPEND_ASSOC] >>
     (map_every (fn pat => qpat_assum pat mp_tac)
        [`emit_op ADD _ st = _`, `emit_op MLOAD _ a = _`,
         `emit_op ADD _ b = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, LET_THM] >>
      rpt strip_tac >> gvs[])) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [i1;i2;i3] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code st en func`, `en.cs_current_insts = _`,
        `en.cs_current_bb = _`, `s.vs_current_bb = _`, `s.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),G3,tn3)` by
    (gen_tac >>
     `s.vs_inst_idx + 3 = LENGTH en.cs_current_insts` by simp[] >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [i1;i2;i3]` by
       simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
     `run_inst_seq [i1;i2;i3] s = OK raw` by
       (qpat_assum `window_pure_seq st en s raw` mp_tac >>
        qpat_assum `emitted_insts st en = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[window_pure_seq_def, window_seq_def] >> metis_tac[]) >>
     `inst_seq_ptr D lo ctx func PG G tn [i1;i2;i3] s G3 tn3` by metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `u = update_var _ _ _` kall_tac >>
  qpat_x_assum `v = update_var _ _ _` kall_tac >>
  qpat_x_assum `raw = update_var _ _ _` kall_tac >>
  qpat_x_assum `G1 = G |+ _` kall_tac >>
  qpat_x_assum `G2 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G3 = G2 |+ _` kall_tac >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`,
    `G3`, `tn3`, `hp`, `childp`] >>
  simp[eval_operand_def, lookup_var_def,
    bodyPtrDefsTheory.ptr_covers_def, allocas_from_def] >>
  conj_tac
  >- (qpat_assum `window_pure_seq st en s raw` mp_tac >>
      qpat_assum `emitted_insts st en = _` mp_tac >>
      qpat_assum `s.vs_inst_idx = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[window_pure_seq_def, window_seq_def] >>
      rpt strip_tac >> gvs[] >> simp[venom_state_component_equality]) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!x. head = Var x ==> not_fresh_at a x`,
         `!x. offset = Var x ==> not_fresh_at b x`,
         `!x. child = Var x ==> not_fresh_at en x`,
         `head = Var hp`, `offset = Var opv`, `child = Var childp`,
         `b.cs_next_var = a.cs_next_var + 1`,
         `en.cs_next_var = b.cs_next_var + 1`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[]) >>
  qpat_assum `window_pure_seq st en s raw` mp_tac >>
  qpat_assum `allocas_from lo s` mp_tac >>
  qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[window_pure_seq_def, allocas_from_def] >> metis_tac[]
QED

Finalise window_child_prefix_joint

Theorem window_child_suffix_joint:
  abi_encode_child_suffix (Var head) (Var dp) offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand (Var head) s = SOME (n2w h) /\
  eval_operand (Var dp) s = SOME (n2w slot) /\
  eval_operand offset s = SOME (n2w off) /\
  eval_operand len s = SOME (n2w n) /\
  (!x. Var head = Var x \/ Var dp = Var x \/ offset = Var x \/
    len = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn dp s 32 /\
  op_taint tn offset = {} /\ op_taint tn len = {} /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h + 32 <= s.vs_alloca_next /\
  slot + 32 <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (h,32) (slot,32) /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts st en) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    window_phase ctx func st en {site} [(h,32)] s t /\
    abi_encode_exec_frame func s t /\
    out = len /\ eval_operand out t = SOME (n2w n) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    op_taint tn' out = {} /\
    t.vs_memory =
      (mstore slot (n2w (off+n)) (mstore h (n2w off) s)).vs_memory /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF
      ({i | h <= i /\ i < h + 32} UNION
       {i | slot <= i /\ i < slot + 32}) /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `h < dimword (:256) /\ slot < dimword (:256)` by decide_tac >>
  `!x. Var dp = Var x \/ len = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all abi_encode_framed_child_suffix_steps_strong >> strip_tac >>
  `window_phase ctx func a en {site} [] t1 t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `b`, `{site}`, `[]`, `t2`] >> simp[]) >>
  `window_phase ctx func st en {site} [(h,32)] s t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{site}`, `[]`, `t1`] >> simp[]) >>
  drule_all window_child_suffix_context >> strip_tac >>
  rename1 `emit_void MSTORE [Var head;offset] st = ((),ca)` >>
  rename1 `emit_op ADD [offset;len] ca = (next,cb)` >>
  qpat_assum `emit_void MSTORE [Var head;offset] st = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qpat_assum `emit_op ADD [offset;len] ca = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_void MSTORE [Var dp;next] cb = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qabbrev_tac `p = STRING #"%" (toString ca.cs_next_var)` >>
  `next = Var p` by simp[Abbr `p`] >>
  qabbrev_tac `i1 = mk_inst st.cs_next_id MSTORE [Var head;offset] []` >>
  qabbrev_tac `i2 = mk_inst ca.cs_next_id ADD [offset;len] [p]` >>
  qabbrev_tac `i3 = mk_inst cb.cs_next_id MSTORE [Var dp;next] []` >>
  `emitted_insts st en = [i1;i2;i3]` by
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND,
      Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `p`] >>
  `?u v raw. step_inst_base i1 s = OK u /\
    step_inst_base i2 u = OK v /\ step_inst_base i3 v = OK raw /\
    raw = (t3 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `run_inst_seq (emitted_insts st en) s = _` mp_tac >>
     qpat_assum `emitted_insts st en = _` (fn th => pure_rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==> p <> x` by
    (simp[Abbr `p`, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  `u = mstore h (n2w off) s` by
    (qpat_x_assum `step_inst_base i1 s = OK u` mp_tac >>
     simp[Abbr `i1`, step_inst_base_opcode_eqs, exec_write2_def,
       w2n_n2w, LESS_MOD]) >>
  `eval_operand offset u = SOME (n2w off) /\
   eval_operand len u = SOME (n2w n)` by
    (simp[eval_operand_def, lookup_var_def, mstore_def,
      write_memory_with_expansion_def] >>
     Cases_on `offset` >> Cases_on `len` >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `v = update_var p (n2w (off+n)) u` by
    (qpat_x_assum `step_inst_base i2 u = OK v` mp_tac >>
     simp[Abbr `i2`, step_inst_base_opcode_eqs, exec_pure2_def, word_add_n2w]) >>
  `p <> dp /\ p <> head` by metis_tac[] >>
  `eval_operand (Var dp) v = SOME (n2w slot)` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, mstore_def,
      write_memory_with_expansion_def, FLOOKUP_UPDATE] >>
     fs[eval_operand_def, lookup_var_def]) >>
  `eval_operand next v = SOME (n2w (off+n))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `raw = mstore slot (n2w (off+n)) v` by
    (qpat_assum `step_inst_base i3 v = OK raw` mp_tac >>
     simp[NoAsms, Abbr `i3`, step_inst_base_opcode_eqs, exec_write2_def] >>
     qpat_assum `eval_operand (Var dp) v = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `eval_operand next v = _` (fn th => pure_rewrite_tac[th]) >>
     simp[w2n_n2w, LESS_MOD]) >>
  qabbrev_tac `G1 = step_prov PG G i1 u` >>
  qabbrev_tac `tn1 = step_taint i1 s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 v` >>
  qabbrev_tac `tn2 = step_taint i2 u v tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i3 raw` >>
  qabbrev_tac `tn3 = step_taint i3 v raw tn2` >>
  `G1 = G /\ tn1.t_var = tn.t_var /\
   tn1.t_mem = tn.t_mem DIFF {i | h <= i /\ i < h+32} /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i1`, step_prov_def,
       set_prov_def, out_prov_def, step_taint_def, mk_inst_def,
       set_var_taint_def, DRESTRICT_UNIV, store_taint_def, adopt_reset_def,
       mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, written_taint_def,
       range_bytes_def, new_site_bytes_def, w2n_n2w, LESS_MOD,
       mstore_def, write_memory_with_expansion_def, FLOOKUP_DEF] >>
     fs[eval_operand_def] >> SET_TAC[]) >>
  `tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `i1`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `op_taint tn1 offset = {} /\ op_taint tn1 len = {}` by
    (Cases_on `offset` >> Cases_on `len` >> gvs[op_taint_def]) >>
  `tn2.t_var = tn1.t_var |+ (p,{}) /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (simp[Abbr `tn2`, Abbr `i2`, step_taint_def, mk_inst_def,
      set_var_taint_def, out_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      FLOOKUP_DEF, update_var_def] >> SET_TAC[]) >>
  `op_taint tn2 next = {}` by simp[op_taint_def, FLOOKUP_UPDATE] >>
  `G3 = G2 /\ tn3.t_var = tn2.t_var /\
   tn3.t_mem = tn2.t_mem DIFF {i | slot <= i /\ i < slot+32} /\
   tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans` by
    (qspecl_then [`PG`, `G2`, `tn2`, `v`] mp_tac mstore_ghost_frame >>
     disch_then (qspecl_then [`cb.cs_next_id`, `dp`, `next`] mp_tac) >>
     simp[GSYM eval_operand_def] >>
     simp[Abbr `G3`, Abbr `tn3`, Abbr `i3`, w2n_n2w, LESS_MOD,
       range_bytes_def]) >>
  `tn3.t_imm = tn2.t_imm` by
    simp[Abbr `tn3`, Abbr `i3`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!x. not_fresh_at st x ==>
    FLOOKUP G3 x = FLOOKUP G x /\
    op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `p <> x` by metis_tac[] >>
     Cases_on `first_prov G [offset;len]` >>
     simp[Abbr `G2`, Abbr `i2`, step_prov_def, set_prov_def,
       out_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def] >> metis_tac[]) >>
  `allocas_from lo u /\ allocas_from lo v` by
    (simp[allocas_from_def, mstore_def, write_memory_with_expansion_def,
      update_var_def] >> metis_tac[allocas_from_def]) >>
  `ptr_covers G2 tn2 dp v 32` by
    (`not_fresh_at st dp` by metis_tac[] >>
     `FLOOKUP G2 dp = FLOOKUP G dp` by metis_tac[] >>
     qpat_x_assum `ptr_covers G tn dp s 32` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def,
       FLOOKUP_UPDATE, mstore_def, write_memory_with_expansion_def,
       update_var_def, lookup_var_def]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G tn i1
    (s with vs_inst_idx := k)` by
    (rpt gen_tac >>
     `ptr_inst_ok D 0 0 ctx func G tn i1 (s with vs_inst_idx := k)` by
       (simp[NoAsms, Abbr `i1`] >> irule ptr_inst_ok_mstore >>
        simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def] >>
        metis_tac[bodyPtrDefsTheory.ptr_covers_def]) >>
     `allocas_from lo (s with vs_inst_idx := k)` by
       (simp[NoAsms, allocas_from_def] >> metis_tac[allocas_from_def]) >>
     metis_tac[ptr_inst_ok_lower_bound_transport, ZERO_LESS_EQ]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G2 tn2 i3
    (v with vs_inst_idx := k)` by
    (rpt gen_tac >>
     `ptr_inst_ok D 0 0 ctx func G2 tn2 i3 (v with vs_inst_idx := k)` by
       (simp[NoAsms, Abbr `i3`] >> irule ptr_inst_ok_mstore >>
        simp[bodyPtrDefsTheory.ptr_covers_def, op_taint_def] >>
        metis_tac[bodyPtrDefsTheory.ptr_covers_def]) >>
     `allocas_from lo (v with vs_inst_idx := k)` by
       (simp[NoAsms, allocas_from_def] >> metis_tac[allocas_from_def]) >>
     metis_tac[ptr_inst_ok_lower_bound_transport, ZERO_LESS_EQ]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1 i2
      (u with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i2`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       allocas_from_def, step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, AllCaseEqs()] >>
     conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     metis_tac[allocas_from_def]) >>
  `!k. step_inst_base i2 (u with vs_inst_idx := k) =
       OK (v with vs_inst_idx := k) /\
       step_inst_base i3 (v with vs_inst_idx := k) =
       OK (raw with vs_inst_idx := k)` by
    (gen_tac >>
     `~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
       simp[Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
     asm_simp_tac bool_ss [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i1;i2;i3] s G3 tn3` by
    (gen_tac >>
     pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base i1 s = OK u` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms] >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     qpat_assum `!k. step_inst_base i2 _ = _ /\ _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     qpat_assum `!k. step_inst_base i2 _ = _ /\ _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (G1 = _)`, `Abbrev (tn1 = _)`,
        `Abbrev (G2 = _)`, `Abbrev (tn2 = _)`,
        `Abbrev (G3 = _)`, `Abbrev (tn3 = _)`] >>
     conj_tac
     >- (qpat_assum `!D k. ptr_inst_ok D lo 0 ctx func G tn i1 _`
           (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     metis_tac[]) >>
  `en.cs_current_insts = st.cs_current_insts ++ [i1;i2;i3] /\
   en.cs_current_bb = st.cs_current_bb` by
    (conj_tac >- simp[APPEND_ASSOC] >>
     (map_every (fn pat => qpat_assum pat mp_tac)
        [`emit_void MSTORE _ st = _`, `emit_op ADD _ ca = _`,
         `emit_void MSTORE _ cb = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, LET_THM] >>
      rpt strip_tac >> gvs[])) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [i1;i2;i3] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code st en func`, `en.cs_current_insts = _`,
        `en.cs_current_bb = _`, `s.vs_current_bb = _`, `s.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `run_inst_seq_mem_ok [i1;i2;i3] s` by
    (pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     qpat_assum `step_inst_base i1 s = OK u` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `step_inst_base i2 u = OK v` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     qpat_assum `step_inst_base i3 v = OK raw` (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     simp[Abbr `i1`, Abbr `i2`, Abbr `i3`,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       w2n_n2w, LESS_MOD, eval_operand_def] >>
     `lookup_var head s = SOME (n2w h) /\
      lookup_var dp v = SOME (n2w slot)` by metis_tac[eval_operand_def] >>
     simp[w2n_n2w, LESS_MOD, mstore_def, write_memory_with_expansion_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     `FLOOKUP s.vs_vars head = SOME (n2w h)` by
       (qpat_assum `eval_operand (Var head) s = _`
          (mp_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >> simp[]) >>
     `FLOOKUP s.vs_vars dp = SOME (n2w slot)` by
       (qpat_assum `eval_operand (Var dp) s = _`
          (mp_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >> simp[]) >>
     simp[w2n_n2w, LESS_MOD]) >>
  `run_inst_seq [i1;i2;i3] s = OK raw` by metis_tac[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),G3,tn3)` by
    (gen_tac >>
     `s.vs_inst_idx + 3 = LENGTH en.cs_current_insts` by simp[] >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [i1;i2;i3]` by
       simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
     `inst_seq_ptr D lo ctx func PG G tn [i1;i2;i3] s G3 tn3` by metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `t3.vs_inst_idx = LENGTH en.cs_current_insts` by simp[] >>
  `raw with vs_inst_idx := LENGTH en.cs_current_insts = t3` by
    (qpat_assum `raw = t3 with vs_inst_idx := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `t3.vs_memory =
    (mstore slot (n2w (off+n)) (mstore h (n2w off) s)).vs_memory /\
   t3.vs_allocas = s.vs_allocas /\
   t3.vs_alloca_next = s.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`raw = t3 with vs_inst_idx := _`, `raw = mstore slot _ v`,
        `v = update_var _ _ u`, `u = mstore h _ s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     qpat_x_assum `u = mstore h _ s`
       (fn th => pure_rewrite_tac[GSYM th] >> mp_tac th) >>
     disch_tac >>
     conj_tac
     >- (qpat_x_assum `raw = t3 with vs_inst_idx := _`
           (mp_tac o AP_TERM ``\z. z.vs_memory``) >>
         qpat_x_assum `u = mstore h _ s` kall_tac >>
         simp[mstore_def, update_var_def]) >>
     conj_tac
     >- (qpat_x_assum `raw = t3 with vs_inst_idx := _`
           (mp_tac o AP_TERM ``\z. z.vs_allocas``) >>
         simp[mstore_def, write_memory_with_expansion_def, update_var_def]) >>
     qpat_x_assum `raw = t3 with vs_inst_idx := _`
       (mp_tac o AP_TERM ``\z. z.vs_alloca_next``) >>
     simp[mstore_def, write_memory_with_expansion_def, update_var_def]) >>
  `mem_word_at h t3.vs_memory = n2w off /\
   mem_word_at slot t3.vs_memory = n2w (off+n)` by
    (simp[mstore_mem_word_at_same] >>
     irule EQ_TRANS >>
     qexists_tac `mem_word_at h (mstore h (n2w off) s).vs_memory` >>
     conj_tac >- (irule mstore_mem_word_at_disjoint >>
       fs[venomMemDefsTheory.regions_disjoint_def]) >>
     simp[mstore_mem_word_at_same]) >>
  `!x. out = Var x ==> not_fresh_at en x` by
    (rpt strip_tac >>
     `not_fresh_at st x` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `op_taint tn3 out = {}` by
    (Cases_on `out` >> gvs[op_taint_def] >> metis_tac[]) >>
  `tn3.t_mem = tn.t_mem DIFF
      ({i | h <= i /\ i < h+32} UNION {i | slot <= i /\ i < slot+32})` by
    (simp[] >> SET_TAC[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t3,G3,tn3)` by metis_tac[] >>
  qpat_x_assum `t3 = mstore _ _ _ with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `raw = t3 with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `raw = mstore _ _ _` kall_tac >>
  qpat_x_assum `G3 = G2` kall_tac >>
  qexistsl_tac [`t3`, `G3`, `tn3`] >>
  simp[allocas_from_def] >>
  qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]
QED
