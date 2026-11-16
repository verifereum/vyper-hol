(* The two readonly header instructions share one actual execution. *)
Theory bodyFullRawCallHeader
Ancestors
  bodyFullRawCallHeaderSteps bodyFullRawCallHeaderView bodyFullGhostFrame
  exprSimHash exprSimHashBoundary exprSimProps exprLoweringProps
  fragGasSeqPtr bodyBinopFragMemory
  bodyMemoryDefs bodyPtrDefs loweringPosts ghostPcTransportPtr ptrSafetyTransport
  loweringStateRelDefs venomState venomInst venomExecSemantics
  ptrDiscipline words list finite_map emitHelper compileEnv ASCIInumbers
  fragExec fragExecMem unitTransformDefs contextCodegenRel codegenRel memSafeRun

Theorem raw_call_header_joint:
  !ctx fn PG G tn s t s2 s3 s4 data len ptr cx ty max bs b cenv es lo explicit.
    emit_op MLOAD [data] s2 = (len,s3) /\
    emit_op ADD [data; Lit 32w] s3 = (ptr,s4) /\
    (!x. data = Var x ==> not_fresh_at s2 x) /\
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic max))) /\
    ~is_word_type ty /\ ptr_val_ok cx ty (BytesV bs) data G tn s /\
    expr_store_bound cx ty (BytesV bs) data s /\
    eval_operand data s = SOME (n2w b) /\
    b+32+LENGTH bs < dimword (:256) /\
    local_ptrs_reserved cenv s2 /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at s2 x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at s2 x) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    fn_has_code s2 s4 fn /\ fn_inst_ids_distinct fn /\
    s.vs_current_bb = s2.cs_current_bb /\
    s.vs_inst_idx = LENGTH s2.cs_current_insts /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    alloca_history fn s /\
    run_inst_seq (emitted_insts s2 s4) s = OK t ==>
    let t4 = t with vs_inst_idx := LENGTH s4.cs_current_insts in
    ?x l p base cap G4 tn4.
      data = Var x /\ len = Var l /\ ptr = Var p /\
      ALL_DISTINCT [x;l;p] /\
      G4 = DRESTRICT G (COMPL {l}) |+ (p,(base,cap)) /\
      tn4 = (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})) /\
      FLOOKUP G x = SOME (base,cap) /\
      base <= b /\ b+32+LENGTH bs <= base+cap /\
      run_inst_seq_mem_ok (emitted_insts s2 s4) s /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t4,G4,tn4)) /\
      eval_operand len t4 = SOME (n2w (LENGTH bs)) /\
      eval_operand ptr t4 = SOME (n2w (b+32)) /\
      op_taint tn4 len = {} /\ op_prov G4 len = NONE /\
      op_taint tn4 ptr = {} /\
      FLOOKUP G4 p = SOME (base,cap) /\
      (LENGTH bs <> 0 ==> ptr_covers G4 tn4 p t4 (LENGTH bs)) /\
      mem_bytes_at (b+32) (LENGTH bs) t4.vs_memory = bs /\
      (!mem. mem_agree_outside tn4.t_mem t4.vs_memory mem ==>
        mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
      (!z. not_fresh_at s2 z ==>
        lookup_var z t4 = lookup_var z s /\
        FLOOKUP G4 z = FLOOKUP G z /\
        op_taint tn4 (Var z) = op_taint tn (Var z)) /\
      (t4 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      t4.vs_memory = s.vs_memory /\ t4.vs_allocas = s.vs_allocas /\
      t4.vs_alloca_next = s.vs_alloca_next /\
      tn4.t_mem = tn.t_mem /\ tn4.t_stor = tn.t_stor /\
      tn4.t_trans = tn.t_trans /\ tn4.t_imm = tn.t_imm /\
      ~t4.vs_halted /\ t4.vs_current_bb = s4.cs_current_bb /\
      t4.vs_inst_idx = LENGTH s4.cs_current_insts /\
      allocas_from lo t4 /\ lo <= t4.vs_alloca_next /\ alloca_history fn t4 /\
      local_ptrs_reserved cenv s4 /\
      (!z. len = Var z \/ ptr = Var z ==> not_fresh_at s4 z) /\
      (!H D d. stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx fn cenv cx es s /\
        ghost_inv_at D lo d cenv cx es G tn s ==>
        stmt_state_rel H ctx fn cenv cx es t4 /\
        ghost_inv_at D lo d cenv cx es G4 tn4 t4) /\
      ghost_kept_at lo cenv es s2 G tn s G4 tn4 /\
      (!sa es0 s0 G0 tn0.
        sa.cs_next_var <= s2.cs_next_var /\
        ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn ==>
        ghost_kept_at lo cenv es0 sa G0 tn0 s0 G4 tn4) /\
      (!sa es0 s0. sa.cs_next_var <= s2.cs_next_var /\
        wb_frame cenv es0 es sa s0 s ==>
        wb_frame cenv es0 es sa s0 t4) /\
      (!sa d. sa.cs_next_var <= s2.cs_next_var /\
        return_buf_frame d cenv sa s ==>
        return_buf_frame d cenv sa t4 /\ return_buf_frame d cenv s4 t4)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_call_header_bytes_view >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ _ = (data_op,s4)` >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `b < dimword (:256)` by decide_tac >>
  `!z. Var x = Var z ==> not_fresh_at s2 z` by simp[] >>
  drule_all hash_data_prefix_run >> strip_tac >> gvs[] >>
  `?l p. len = Var l /\ data_op = Var p /\ ALL_DISTINCT [x;l;p] /\
    emitted_insts s2 s4 =
      [mk_inst s2.cs_next_id MLOAD [Var x] [l];
       mk_inst (s2.cs_next_id+1) ADD [Var x; Lit 32w] [p]] /\
    s4.cs_current_bb = s2.cs_current_bb /\
    (!z. not_fresh_at s2 z ==> z <> l /\ z <> p)` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
          GSYM APPEND_ASSOC, ALL_DISTINCT, toString_inj] >>
     fs[not_fresh_at_def] >> metis_tac[]) >>
  qabbrev_tac `G4 = DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap))` >>
  qabbrev_tac `tn4 = tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})` >>
  qabbrev_tac `t4 = t with vs_inst_idx := LENGTH s4.cs_current_insts` >>
  suspend "assemble"
QED

Resume raw_call_header_joint[assemble]:
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!z. not_fresh_at s2 z ==>
    lookup_var z t4 = lookup_var z s /\ FLOOKUP G4 z = FLOOKUP G z /\
    op_taint tn4 (Var z) = op_taint tn (Var z)` by
    (rpt strip_tac >>
     `z <> l /\ z <> p` by metis_tac[] >>
     simp[Abbr `G4`, Abbr `tn4`, Abbr `t4`, lookup_var_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     metis_tac[lookup_var_def]) >>
  `run_inst_seq_mem_ok (emitted_insts s2 s4) s` by suspend "memory" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK t4,G4,tn4)` by suspend "path" >>
  qexistsl_tac [`l`, `p`] >>
  simp[Abbr `G4`, Abbr `tn4`, Abbr `t4`, op_taint_def, op_prov_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ALL_DISTINCT,
       allocas_from_def, lookup_var_def] >>
  suspend "remaining"
QED

Resume raw_call_header_joint[memory]:
  simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[eval_operand_def] >>
  gvs[eval_operand_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume raw_call_header_joint[path]:
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s2 s4) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l'` >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  gen_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts s2 s4) s G4 tn4` by
    (simp[Abbr `G4`, Abbr `tn4`] >>
     irule raw_call_header_steps_checked >> simp[] >>
     qexistsl_tac [`b`, `LENGTH bs`] >> simp[] >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts s2 s4) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts s2 s4) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[Abbr `t4`]
QED

Resume raw_call_header_joint[remaining]:
  gvs[ALL_DISTINCT, lookup_var_def, allocas_from_def] >>
  conj_tac
  >- (strip_tac >> simp[ptr_covers_def, FLOOKUP_UPDATE, op_taint_def] >>
      qexists_tac `n2w (b+32)` >>
      gvs[eval_operand_def] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "history" >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `s2` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "invariants" >>
  conj_tac >- simp[ghost_kept_at_def] >>
  conj_tac >- suspend "oldghost" >>
  conj_tac >- suspend "wb" >>
  suspend "return"
QED

Resume raw_call_header_joint[history]:
  `?bb rest. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts s2 s4 ++ rest` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  `alloca_history fn
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s2 s4))` by
    (irule alloca_history_no_alloca_slice >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     qexists_tac `rest` >> gvs[mk_inst_def]) >>
  gvs[]
QED

Resume raw_call_header_joint[invariants]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[stmt_state_rel_inst_idx] >>
      irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
      qexists_tac `s2` >> simp[lookup_var_def]) >>
  irule ghost_inv_at_exterior_frame >> goal_assum (drule_at Any) >>
  qexists_tac `s2` >> simp[lookup_var_def]
QED

Resume raw_call_header_joint[oldghost]:
  rpt gen_tac >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  gvs[ghost_kept_at_def] >> metis_tac[]
QED

Resume raw_call_header_joint[wb]:
  rpt gen_tac >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  fs[wb_frame_def, lookup_var_def] >> conj_tac
  >- (first_assum MATCH_ACCEPT_TAC) >>
  irule locals_kept_mem_tail >> goal_assum (drule_at Any) >> simp[]
QED

Resume raw_call_header_joint[return]:
  rpt gen_tac >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  conj_tac >> irule return_buf_frame_frame >>
  goal_assum (drule_at Any) >> simp[lookup_var_def] >>
  rpt strip_tac >> rename1 `not_fresh_at sa z` >>
  `not_fresh_at s2 z` by metis_tac[] >>
  qpat_x_assum `!z. not_fresh_at s2 z ==> FLOOKUP t.vs_vars z = _`
    (drule_then SUBST1_TAC) >> simp[]
QED

Finalise raw_call_header_joint
