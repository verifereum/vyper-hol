Theory bodyPtrIntCallMaterialize
Ancestors
  bodyPtrIntCallEntryContracts ghostObservationPtr
  bodyPtrDefs ptrDiscipline venomState finite_map words list pred_set
  allocationPtr wordLoadStorePtr bodyPtrMakeArrayWordStore fragGasSeqPtr
  fragExecPtr mstoreOperandStep exprSimProps venomMemProps loweringHalt
  fragExec ghostPcTransportPtr instIdxIndep exprLoweringProps
  venomInst venomExecSemantics

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
