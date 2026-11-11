Theory bodyPtrIntCallMaterialize
Ancestors
  bodyPtrIntCallEntryContracts ghostObservationPtr
  bodyPtrDefs ptrDiscipline venomState finite_map words list pred_set
  allocationPtr wordLoadStorePtr bodyPtrMakeArrayWordStore fragGasSeqPtr
  fragExecPtr mstoreOperandStep exprSimProps venomMemProps loweringHalt
  fragExec ghostPcTransportPtr instIdxIndep exprLoweringProps
  venomInst venomExecSemantics moduleLowering compileEnv intCallCallee
  bodyPtrPrecompileBuiltinsSeq

Theorem intcall_local_value_transport:
  intcall_local_value entry p sz G tn s /\
  lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
  op_taint un (Var p) = {} /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_local_value entry p sz H un t
Proof
  strip_tac >> fs[intcall_local_value_def] >>
  conj_tac >- metis_tac[ptr_covers_def] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_no_new_taint >>
  simp[] >> qexists_tac `{a | s.vs_alloca_next <= a}` >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem intcall_completed_transport:
  intcall_completed env ce G tn s /\
  (!p sz name. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint un (Var p) = {}) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_completed env ce H un t
Proof
  strip_tac >> simp[intcall_completed_def] >> rpt strip_tac >>
  qpat_x_assum `intcall_completed _ _ _ _ _` mp_tac >>
  simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
  qexistsl_tac [`p`,`sz`] >> simp[] >>
  irule intcall_local_value_transport >> metis_tac[]
QED

Theorem intcall_pending_transport:
  intcall_pending env ce caps G tn s /\
  (!op. MEM op (MAP (SND o SND) caps) ==>
    eval_operand op t = eval_operand op s /\
    op_taint un op = op_taint tn op /\
    (!p. op = Var p ==> FLOOKUP H p = FLOOKUP G p)) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_pending env ce caps H un t
Proof
  strip_tac >> simp[intcall_pending_def, EVERY_MEM] >>
  gen_tac >> strip_tac >> PairCases_on `e` >> gvs[] >>
  qpat_x_assum `intcall_pending _ _ _ _ _ _` mp_tac >>
  simp[intcall_pending_def, EVERY_MEM] >>
  disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  `MEM e2 (MAP (SND o SND) caps)` by
    (simp[MEM_MAP] >> qexists_tac `(e0,e1,e2)` >> simp[]) >>
  qpat_x_assum `!op. MEM op _ ==> _` drule >> strip_tac >>
  qexistsl_tac [`entry`,`off`,`sz`,`w`] >> simp[] >>
  Cases_on `e1` >> gvs[] >>
  irule intcall_local_value_transport >>
  gvs[eval_operand_def] >> metis_tac[]
QED

Theorem intcall_materialize_scalar_ptr:
  p <> q /\ lookup_var p s = SOME w /\ op_taint tn (Var p) = {} /\
  FLOOKUP s.vs_allocas aid = NONE /\ 32 <= sz /\
  s.vs_alloca_next + sz < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  val_wf entry.type entry.value /\ type_memory_size entry.type <= sz /\
  (!b m. mem_word_at b m = w ==> val_in_memory entry.type entry.value b m) ==>
  ?t H un.
    run_inst_seq [mk_inst aid ALLOCA [Lit (n2w sz)] [q];
      mk_inst (aid+1) MSTORE [Var q; Var p] []] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ALLOCA [Lit (n2w sz)] [q];
       mk_inst (aid+1) MSTORE [Var q; Var p] []]
      (s with vs_inst_idx := k) H un) /\
    (!bb. ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX [mk_inst aid ALLOCA [Lit (n2w sz)] [q];
        mk_inst (aid+1) MSTORE [Var q; Var p] []]
        (DROP s.vs_inst_idx bb.bb_instructions) ==>
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un
        (OK (t with vs_inst_idx := s.vs_inst_idx + 2))) /\
    intcall_local_value entry q sz H un t /\
    t.vs_alloca_next = s.vs_alloca_next + sz /\
    (!a. a < s.vs_alloca_next ==>
      mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
    (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. x <> q ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `sz < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  qabbrev_tac `u = update_var q (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,sz));
              vs_alloca_next := s.vs_alloca_next + sz|>)` >>
  `step_inst_base (mk_inst aid ALLOCA [Lit (n2w sz)] [q]) s = OK u` by
    (simp[Abbr `u`, step_alloca_fresh]) >>
  qabbrev_tac `ga = G |+ (q,(s.vs_alloca_next,sz))` >>
  qabbrev_tac `ta = tn with <|t_mem := tn.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + sz};
    t_var := tn.t_var |+ (q,{})|>` >>
  `step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [q]) u = ga /\
   step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [q]) s u tn = ta` by
    (drule_all fresh_alloca_ghost >> simp[Abbr `ga`, Abbr `ta`]) >>
  `lookup_var q u = SOME (n2w s.vs_alloca_next) /\
   lookup_var p u = SOME w /\ op_taint ta (Var p) = {}` by
    fs[Abbr `u`, Abbr `ta`, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, op_taint_def] >>
  qabbrev_tac `t = mstore s.vs_alloca_next w u` >>
  `step_inst_base (mk_inst (aid+1) MSTORE [Var q; Var p] []) u = OK t` by
    (simp[Abbr `t`] >>
     `eval_operand (Var q) u = SOME (n2w s.vs_alloca_next) /\
      eval_operand (Var p) u = SOME w` by simp[eval_operand_def] >>
     qpat_x_assum `eval_operand (Var q) u = _`
       (mp_then (Pos hd) mp_tac step_mstore_operands) >> simp[]) >>
  qabbrev_tac `un = step_taint (mk_inst (aid+1) MSTORE [Var q; Var p] []) u t ta` >>
  `w2n (n2w s.vs_alloca_next : bytes32) = s.vs_alloca_next` by simp[] >>
  `step_prov PG ga (mk_inst (aid+1) MSTORE [Var q; Var p] []) t = ga /\
   un.t_var = ta.t_var /\ un.t_stor = ta.t_stor /\
   un.t_trans = ta.t_trans /\
   un.t_mem = ta.t_mem DIFF
     {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32}` by
    (qpat_assum `lookup_var q u = _`
       (mp_then (Pos hd) (qspecl_then [`PG`,`ga`,`ta`,`aid+1`] mp_tac)
         mstore_ghost_frame) >>
     disch_then (qspec_then `Var p` mp_tac) >>
     simp[eval_operand_def, Abbr `t`, Abbr `un`]) >>
  qexistsl_tac [`t`,`ga`,`un`] >>
  conj_asm1_tac >- simp[run_inst_seq_def] >>
  conj_asm1_tac >- suspend "checks" >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "value" >>
  suspend "frame"
QED

Resume intcall_materialize_scalar_ptr[checks]:
  `ptr_covers ga ta q u sz` by
    (drule_all (cj 1 fresh_alloca_ptr_covers) >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >> simp[]) >>
  `ptr_covers ga ta q u 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `~is_terminator (mk_inst aid ALLOCA [Lit (n2w sz)] [q]).inst_opcode /\
   ~is_terminator (mk_inst (aid+1) MSTORE [Var q; Var p] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  gen_tac >> simp[Once inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore >> simp[]) >>
  simp[step_inst_inst_idx_indep, exec_result_map_def, inst_seq_ptr_def, Abbr `un`]
QED
Resume intcall_materialize_scalar_ptr[path]:
  rpt strip_tac >>
  qpat_assum `run_inst_seq _ _ = _`
    (mp_then (Pos last) mp_tac run_inst_seq_gas_path_ptr) >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
  gvs[mk_inst_def]
QED
Resume intcall_materialize_scalar_ptr[value]:
  `ptr_covers ga ta q u sz` by
    (drule_all (cj 1 fresh_alloca_ptr_covers) >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >> simp[]) >>
  simp[intcall_local_value_def] >>
  conj_tac >- (fs[ptr_covers_def, op_taint_def] >>
    gvs[Abbr `t`, mstore_def, lookup_var_def]) >>
  qexists_tac `n2w s.vs_alloca_next` >>
  simp[Abbr `t`, mstore_def, lookup_var_def] >>
  conj_tac >- (gvs[Abbr `u`, update_var_def] >>
    drule val_footprint_le >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_assum `lookup_var q u = _`
    (mp_then (Pos hd) mp_tac mstore_raw_robust_word) >>
  simp[eval_operand_def, Abbr `un`, mstore_def] >>
  disch_then (qspecl_then [`w`,`Var p`,`ta`,`m`,`aid+1`] mp_tac) >>
  gvs[eval_operand_def, mstore_def]
QED
Resume intcall_materialize_scalar_ptr[frame]:
  `!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     rewrite_tac[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     `a + 1 <= s.vs_alloca_next` by decide_tac >>
     simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint,
       Abbr `u`, update_var_def]) >>
  `un.t_imm = ta.t_imm` by
    simp[Abbr `un`, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[Abbr `t`, mstore_def, Abbr `u`, update_var_def,
       Abbr `ta`, Abbr `ga`] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> decide_tac) >>
  rpt strip_tac >> simp[lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED

Finalise intcall_materialize_scalar_ptr

Theorem intcall_materialize_path_ptr:
  !caps ce st done src s G tn ce' st'.
    materialize_internal_params ce caps st = (ce',st') /\
    intcall_completed done ce G tn s /\ intcall_pending src ce caps G tn s /\
    ALL_DISTINCT (MAP FST caps) /\
    DISJOINT (FDOM done) (set (MAP FST caps)) /\
    EVERY (\c. ?p. SND (SND c) = Var p /\ not_fresh_at st p) caps /\
    (!name p sz. name IN FDOM done /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    s.vs_alloca_next + internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
      < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
    ?t H un.
      run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s = OK t /\
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
        (s with vs_inst_idx := k) H un) /\
      intcall_completed (FUNION done (DRESTRICT src (set (MAP FST caps)))) ce' H un t /\
      t.vs_alloca_next = s.vs_alloca_next +
        internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) /\
      (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id) /\
      (!a. a < s.vs_alloca_next ==>
        mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
      (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint un (Var x) = op_taint tn (Var x))
Proof
  Induct >- suspend "empty" >>
  PairCases >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ce st done src s G tn ce' st'. _` (mk_asm "ih") >>
  gvs[intcall_pending_def, EVERY_DEF] >>
  Cases_on `h1` >- suspend "scalar" >>
  suspend "memory"
QED

Resume intcall_materialize_path_ptr[empty]:
  simp[materialize_internal_params_def, comp_return_def,
       internal_stack_size_def] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`s`,`G`,`tn`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, DRESTRICT_IS_FEMPTY]
QED

Resume intcall_materialize_path_ptr[memory]:
  gvs[] >>
  qabbrev_tac `ce1 = ce with ce_vars := ce.ce_vars |+ (h0,PtrVar (Var p) sz)` >>
  `ce with ce_vars updated_by (\m. m |+ (h0,PtrVar (Var p) sz)) = ce1` by
    simp[Abbr `ce1`, compile_env_component_equality] >>
  `materialize_internal_params ce1 caps st = (ce',st')` by
    (qpat_x_assum `materialize_internal_params _ _ _ = _` mp_tac >>
     simp[Once materialize_internal_params_def, Abbr `ce1`]) >>
  `intcall_completed (done |+ (h0,entry)) ce1 G tn s` by
    (simp[Abbr `ce1`] >> irule intcall_completed_bind >> simp[]) >>
  `intcall_pending src ce1 caps G tn s` by
    (simp[Abbr `ce1`] >> irule intcall_pending_drop_bind >>
     simp[intcall_pending_def] >>
     qpat_x_assum `~MEM h0 (MAP FST caps)` mp_tac >>
     simp[MEM_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
     disch_then (fn th => simp[th])) >>
  `!name q n. name IN FDOM (done |+ (h0,entry)) /\
    FLOOKUP ce1.ce_vars name = SOME (PtrVar (Var q) n) ==> not_fresh_at st q` by
    (simp[Abbr `ce1`, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `name = h0` >> gvs[] >> metis_tac[]) >>
  `DISJOINT (FDOM (done |+ (h0,entry))) (set (MAP FST caps))` by simp[] >>
  `s.vs_alloca_next + internal_stack_size ce1
    (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by
    (qpat_assum `ce with ce_vars updated_by _ = ce1`
       (fn th => once_rewrite_tac[GSYM th]) >>
     simp[mat_tail_stack_size] >> gvs[internal_stack_size_def]) >>
  asm_x "ih" drule_all >>
  strip_tac >> qexistsl_tac [`t`,`H`,`un`] >> simp[] >>
  reverse conj_tac >-
    (qpat_assum `ce with ce_vars updated_by _ = ce1`
       (fn th => once_rewrite_tac[GSYM th]) >>
     simp[mat_tail_stack_size, internal_stack_size_def]) >>
  `FUNION (done |+ (h0,entry)) (DRESTRICT src (set (MAP FST caps))) =
   FUNION done (DRESTRICT src (h0 INSERT set (MAP FST caps)))` by
    (`FLOOKUP done h0 = NONE` by simp[flookup_thm] >>
     simp[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     qx_gen_tac `n` >> Cases_on `n = h0` >> gvs[] >>
     Cases_on `FLOOKUP done n` >> simp[]) >>
  metis_tac[]
QED

Resume intcall_materialize_path_ptr[scalar]:
  gvs[] >> drule_all materialize_stack_split >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString st.cs_next_var)` >>
  `p <> q` by gvs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `q`] >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (simp[flookup_thm] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `s.vs_alloca_next + sz < dimword (:256)` by
    (gvs[internal_stack_size_def] >> decide_tac) >>
  `lookup_var p s = SOME w` by gvs[eval_operand_def] >>
  drule_all intcall_materialize_scalar_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] mp_tac) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  qabbrev_tac `ce1 = ce with ce_vars := ce.ce_vars |+ (h0,PtrVar (Var q) sz)` >>
  `ce with ce_vars updated_by (\m. m |+ (h0,PtrVar (Var q) sz)) = ce1` by
    simp[Abbr `ce1`, compile_env_component_equality] >>
  `!x. not_fresh_at st x ==> x <> q /\ not_fresh_at mid x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `q`] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `intcall_completed done ce G1 tn1 s1` by suspend "scalar_completed" >>
  `intcall_completed (done |+ (h0,entry)) ce1 G1 tn1 s1` by
    (simp[Abbr `ce1`] >> irule intcall_completed_bind >> simp[]) >>
  `intcall_pending src ce1 caps G1 tn1 s1` by suspend "scalar_pending" >>
  `!name r n. name IN FDOM (done |+ (h0,entry)) /\
    FLOOKUP ce1.ce_vars name = SOME (PtrVar (Var r) n) ==> not_fresh_at mid r` by
    (simp[Abbr `ce1`, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `name = h0` >> gvs[] >-
       simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `q`,
            ASCIInumbersTheory.toString_inj] >> metis_tac[]) >>
  `EVERY (\c. ?p. SND (SND c) = Var p /\ not_fresh_at mid p) caps` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `DISJOINT (FDOM (done |+ (h0,entry))) (set (MAP FST caps))` by simp[] >>
  `!aid. aid IN FDOM s1.vs_allocas ==> aid < mid.cs_next_id` by
    suspend "scalar_sites" >>
  `s1.vs_alloca_next + internal_stack_size ce1
    (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by
    (qpat_assum `ce with ce_vars updated_by _ = ce1`
       (fn th => once_rewrite_tac[GSYM th]) >>
     simp[mat_tail_stack_size] >> gvs[internal_stack_size_def]) >>
  `materialize_internal_params ce1 caps mid = (ce',st')` by metis_tac[] >>
  asm_x "ih" drule_all >> strip_tac >> suspend "scalar_join"
QED

Resume intcall_materialize_path_ptr[scalar_completed]:
  simp[intcall_completed_def] >> rpt strip_tac >>
  qpat_x_assum `intcall_completed done ce G tn s` mp_tac >>
  simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
  qexistsl_tac [`p'`,`sz'`] >> simp[] >>
  `not_fresh_at st p'` by metis_tac[flookup_thm] >>
  `p' <> q` by metis_tac[] >>
  `op_taint tn1 (Var p') = {}` by
    (fs[intcall_local_value_def, ptr_covers_def] >> metis_tac[]) >>
  irule intcall_local_value_transport >> simp[] >>
  qexistsl_tac [`G`,`s`,`tn`] >> simp[]
QED
Resume intcall_materialize_path_ptr[scalar_pending]:
  `intcall_pending src ce1 caps G tn s` by
    (simp[Abbr `ce1`] >> irule intcall_pending_drop_bind >>
     simp[intcall_pending_def] >>
     qpat_x_assum `~MEM h0 (MAP FST caps)` mp_tac >>
     simp[MEM_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
     disch_then (fn th => simp[th])) >>
  irule intcall_pending_transport >>
  qexistsl_tac [`G`,`s`,`tn`] >> simp[] >>
  rpt strip_tac >>
  fs[MEM_MAP, EVERY_MEM] >>
  qpat_x_assum `!e. MEM e caps ==> ?p. _` drule >> strip_tac >>
  gvs[eval_operand_def] >> metis_tac[]
QED
Resume intcall_materialize_path_ptr[scalar_sites]:
  qabbrev_tac `u = update_var q (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,sz));
              vs_alloca_next := s.vs_alloca_next + sz|>)` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [q]) s = OK u` by
    simp[Abbr `u`, step_alloca_fresh] >>
  `eval_operand (Var q) u = SOME (n2w s.vs_alloca_next) /\
   eval_operand (Var p) u = SOME w` by
    fs[eval_operand_def, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (st.cs_next_id+1) MSTORE [Var q; Var p] []) u =
    OK (mstore s.vs_alloca_next w u)` by
    (qpat_assum `eval_operand (Var q) u = _`
       (mp_then (Pos hd) mp_tac step_mstore_operands) >> simp[]) >>
  `s1 = mstore s.vs_alloca_next w u` by
    (qpat_x_assum `run_inst_seq _ s = OK s1` mp_tac >> simp[run_inst_seq_def]) >>
  simp[Abbr `u`, mstore_def, update_var_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED
Resume intcall_materialize_path_ptr[scalar_join]:
  `FUNION (done |+ (h0,entry)) (DRESTRICT src (set (MAP FST caps))) =
   FUNION done (DRESTRICT src (h0 INSERT set (MAP FST caps)))` by
    (`FLOOKUP done h0 = NONE` by simp[flookup_thm] >>
     simp[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     qx_gen_tac `n` >> Cases_on `n = h0` >> gvs[] >>
     Cases_on `FLOOKUP done n` >> simp[]) >>
  qexistsl_tac [`t`,`H`,`un`] >>
  conj_tac >-
    (qpat_assum `run_inst_seq _ s = OK s1`
       (mp_then (Pos hd) mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `DROP (LENGTH mid.cs_current_insts) st'.cs_current_insts`
       assume_tac) >> gvs[]) >>
  conj_tac >-
    (qpat_assum `DROP (LENGTH st.cs_current_insts) _ = _` (fn th => rewrite_tac[th]) >>
     irule inst_seq_ptr_append_cursors >>
     simp[mk_inst_def, is_terminator_def] >>
     qexistsl_tac [`G1`,`s1`,`tn1`] >> gvs[mk_inst_def]) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_assum `ce with ce_vars updated_by _ = ce1`
    (fn th => once_rewrite_tac[GSYM th]) >>
  simp[mat_tail_stack_size, internal_stack_size_def]
QED

Finalise intcall_materialize_path_ptr

Theorem intcall_materialize_counted_ptr:
  materialize_internal_params ce caps st = (ce',st') /\
  run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn
    (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (s with vs_inst_idx := k) H un) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H un
    (OK (t with vs_inst_idx := s.vs_inst_idx +
      LENGTH (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)))
Proof
  strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) new` by
    (fs[EVERY_MEM, is_terminator_def] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) new = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >>
     rpt strip_tac >>
     qpat_x_assum `!i. MEM i new ==> i.inst_opcode = ALLOCA \/ _` drule >>
     strip_tac >> gvs[]) >>
  qpat_assum `run_inst_seq _ s = OK t`
    (mp_then (Pos last) mp_tac run_inst_seq_gas_path_ptr) >>
  simp[DROP_PREFIX] >> disch_then irule >> fs[DROP_PREFIX] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem intcall_materialize_return_frame:
  materialize_internal_params ce caps st = (ce',st') /\
  return_buf_ptr d ce G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p /\ op_taint tn (Var p) = {}) /\
  (!p. not_fresh_at st p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint un (Var p) = op_taint tn (Var p)) ==>
  return_buf_ptr d ce' H un t /\
  (!p sz. ce'.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    op_taint un (Var p) = {})
Proof
  strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  gvs[] >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED
