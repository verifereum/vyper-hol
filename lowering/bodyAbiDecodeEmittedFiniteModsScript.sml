Theory bodyAbiDecodeEmittedFiniteMods
Ancestors
  fragGasSeqPtr fragGasSeqAbort fragGasOriginPtr ptrDiscipline unitTransformDefs
  venomExecProofs venomExecSemantics fragExecMem fragExec venomInst venomState
  rich_list list arithmetic pair exprLoweringProps instIdxIndep venomInstProofs
  entryDecoderHistoryFrame emitHelperProps ptrSafetyTransport pred_set

(* The cursor-normalized raw run retains both pointer ghosts at each fetch. *)
Theorem bytes_raw_origin_finite:
  !code s t G tn G' tn' ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    (ctx_has_dalloca ctx ==>
      !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
        dalloca_no_wrap i u) /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\
    run_inst_seq code s = OK t ==>
    RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
      (LENGTH code) (s,G,tn) (t with vs_inst_idx := s.vs_inst_idx + LENGTH code,G',tn')
Proof
  Induct >- (simp[run_inst_seq_def,inst_seq_ptr_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def,inst_seq_ptr_def,run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted,step_preserves_control_flow] >>
  `(ctx_has_dalloca ctx ==> dalloca_no_wrap h s)` by
    (disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> _` (mp_tac o UNDISCH) >>
     disch_then (qspecl_then [`[]`,`h`,`code`,`s`] mp_tac) >> simp[run_inst_seq_def]) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post v. code = pre ++ i::post /\
      run_inst_seq pre (u with vs_inst_idx := SUC s.vs_inst_idx) = OK v ==>
      dalloca_no_wrap i v)` by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_APPEND,EVERY_CONJ] >>
     qpat_x_assum `run_inst_seq pre _ = OK v` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq pre u` >> simp[exec_result_map_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     rename1 `run_inst_seq pre u = OK w` >>
     qpat_assum `ctx_has_dalloca ctx ==> !pre i post v. h::code = _ /\ _ ==> _`
       (mp_tac o UNDISCH) >>
     disch_then (qspecl_then [`h::pre`,`i`,`post`,`w`] mp_tac) >>
     simp[run_inst_seq_def,dalloca_no_wrap_def,eval_op_inst_idx]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_CONJ] >>
  rewrite_tac[NRC] >>
  qexists_tac `(u with vs_inst_idx := SUC s.vs_inst_idx,
    step_prov PG G h u, step_taint h s u tn)` >>
  conj_tac >- (simp[] >> drule_all straight_line_origin_ptr_edge >> simp[]) >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`, `step_prov PG G h u`,
     `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `fn`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx,exec_result_map_def,ADD_CLAUSES] >>
  (impl_tac >-
    (pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
     pure_rewrite_tac[APPEND] >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Theorem bytes_emitted_origin_finite:
  fn_has_code sa sb fn /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn)
    (t with vs_inst_idx := LENGTH sb.cs_current_insts,G',tn')
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by fs[inst_extends_def] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by simp[IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all bytes_raw_origin_finite >> simp[]
QED

Theorem bytes_finite_from_no_dead:
  !n x y.
    RELPOW (\(u,Gu,tu) (v,Gv,tv). gas_origin_ptr_edge
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv)) n x y ==>
    RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv)) n x y
Proof
  Induct >- simp[] >>
  pure_once_rewrite_tac[NRC] >> rpt strip_tac >>
  qexists_tac `z` >> reverse conj_tac >- res_tac >>
  PairCases_on `x` >> PairCases_on `z` >>
  fs[gas_origin_ptr_edge_def] >>
  drule gas_path_ptr_edge_dead_mono >> simp[]
QED
