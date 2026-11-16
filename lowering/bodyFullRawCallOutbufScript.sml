(* The output allocation is a single actual run, including ALLOCA 0. *)
Theory bodyFullRawCallOutbuf
Ancestors
  bodyFullRawCallOutbufAlloc bodyFullRawCallOutbufAdd
  bodyFullAllocaFresh bodyFullGhostFrame bodyFullUnwrapRun
  bodyPtrSignedConvertSourceFrame
  decoderArraySetupPtr fragExec bodyMemoryDefs arithmeticProps
  vyperStorageFootprint ghostPcTransportPtr exprSimWordArgs
  immutableRegionLoadPtr bodyFullAllocGeneric abiBuiltinAllocation exprSimAccounts
  builtinSystem context emitHelper emitHelperProps
  exprSimAlloc allocationPtr exprLoweringProps loweringHalt
  bodyPtrDefs loweringStateRelDefs compileEnv ptrDiscipline
  fragGasSeqPtr fragExecMem ptrSafetyTransport venomMemDefs
  venomState venomInst venomExecSemantics finite_map words list rich_list

Theorem outbuf_parts[local]:
  compile_raw_call_outbuf M sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (if M = 0 then 0 else ((M+31) DIV 32)*32+32) sa = (buf,sm) /\
    ov = buf.buf_operand /\
    (if M = 0 then op = ov /\ sb = sm
     else emit_op ADD [ov;Lit 32w] sm = (op,sb))
Proof
  Cases_on `M = 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_joint:
  compile_raw_call_outbuf M sa = ((ov,op),sb) /\
  n = (if M = 0 then 0 else ((M+31) DIV 32)*32+32) /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  t7 = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sk.cs_next_var <= sa.cs_next_var /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                aid < sk.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
  (!name b sz. local_region cenv es0.scopes s0 name b sz ==>
               b + sz <= s.vs_alloca_next) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  wb_frame cenv es0 es sk s0 s /\ return_buf_frame d cenv sk s /\
  ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
  ?G7 tn7 b.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t7,G7,tn7)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es t7 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G7 tn7 t7) /\
    storage_trace_domain cx st0 es.storage_trace /\
    wb_frame cenv es0 es sk s0 t7 /\ return_buf_frame d cenv sk t7 /\
    ghost_kept_at lo cenv es0 sk G0 tn0 s0 G7 tn7 /\
    alloca_history func t7 /\ allocas_from lo t7 /\
    s.vs_alloca_next <= t7.vs_alloca_next /\
    ~t7.vs_halted /\ t7.vs_current_bb = sb.cs_current_bb /\
    t7.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t7 with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next;
               vs_inst_idx := s.vs_inst_idx |> = s /\
    eval_operand ov t7 = SOME (n2w b) /\
    eval_operand op t7 = SOME (n2w (if M = 0 then b else b+32)) /\
    FLOOKUP t7.vs_allocas sa.cs_next_id = SOME (b,n) /\
    op_prov G7 ov = SOME (b,n) /\ op_prov G7 op = SOME (b,n) /\
    op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
    b+n < dimword (:256) /\ b+n <= t7.vs_alloca_next /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t7.vs_allocas aid = SOME e) /\
    t7.vs_memory = s.vs_memory /\
    tn7.t_stor = tn.t_stor /\ tn7.t_trans = tn.t_trans /\ tn7.t_imm = tn.t_imm /\
    (!i. i IN tn7.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t7 = lookup_var x s /\ FLOOKUP G7 x = FLOOKUP G x /\
      op_taint tn7 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    (fs[storage_trace_domain_def] >> metis_tac[]) >>
  drule outbuf_parts >> strip_tac >>
  Cases_on `M = 0`
  >- (gvs[] >>
      drule_all (SRULE [] (Q.INST
        [`t` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `n` |-> `0`]
        (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
          raw_call_outbuf_alloc_joint))) >>
      disch_then (qspecl_then [`tn0`, `tn`, `PG`, `G0`, `G`] strip_assume_tac) >>
      qexistsl_tac [`G1`, `tn1`, `b`] >>
      simp[] >> suspend "zero") >>
  suspend "positive"
QED

Resume raw_call_outbuf_joint[zero]:
  conj_tac >- (gen_tac >> strip_tac >>
    qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
    metis_tac[]) >>
  conj_tac >- suspend "zero_wb" >>
  conj_tac >- suspend "zero_return" >>
  qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume raw_call_outbuf_joint[positive]:
  gvs[] >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[compile_alloc_buffer_extends, emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    metis_tac[emit_op_extends] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    metis_tac[emitted_insts_append] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_x_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `?m. run_inst_seq (emitted_insts sa sm) s = OK m /\
       run_inst_seq (emitted_insts sm sb) m = OK u /\
       run_inst_seq (emitted_insts sm sb)
         (m with vs_inst_idx := LENGTH sm.cs_current_insts) =
           OK (u with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >>
     drule_all run_inst_seq_append_aligned >>
     gvs[LENGTH_APPEND]) >>
  drule_all (SRULE [] (Q.INST
    [`t` |-> `m with vs_inst_idx := LENGTH sm.cs_current_insts`,
     `u` |-> `m`, `sb` |-> `sm`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
      raw_call_outbuf_alloc_joint))) >>
  disch_then (qspecl_then [`tn0`, `tn`, `PG`, `G0`, `G`] strip_assume_tac) >>
  suspend "positive_add"
QED
Resume raw_call_outbuf_joint[positive_add]:
  `lo <= m.vs_alloca_next` by decide_tac >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `eval_operand buf.buf_operand (m with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME (n2w b)` by
    simp[eval_operand_def, lookup_var_def] >>
  drule_all (SRULE [] (Q.INST
    [`sa` |-> `sm`,
     `s` |-> `m with vs_inst_idx := LENGTH sm.cs_current_insts`,
     `u` |-> `u with vs_inst_idx := LENGTH sm.cs_current_insts`,
     `t` |-> `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
      raw_call_outbuf_add_joint)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "positive_pack"
QED
Resume raw_call_outbuf_joint[positive_pack]:
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s /\
    FLOOKUP G1' x = FLOOKUP G x /\
    op_taint tn1' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `u.vs_memory = m.vs_memory /\ u.vs_allocas = m.vs_allocas /\
   u.vs_alloca_next = m.vs_alloca_next /\
   u.vs_call_ctx = m.vs_call_ctx /\ u.vs_accounts = m.vs_accounts /\
   u.vs_transient = m.vs_transient /\ u.vs_immutables = m.vs_immutables` by
    (qpat_x_assum `u with <|vs_vars := m.vs_vars; vs_inst_idx := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `m with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`G1'`, `tn1'`, `b`] >>
  simp[GSYM word_add_n2w] >>
  conj_tac >- suspend "positive_path" >>
  conj_tac >- suspend "positive_horizon" >>
  conj_tac >- suspend "positive_wb" >>
  conj_tac >- suspend "positive_return" >>
  conj_tac >- suspend "positive_kept" >>
  conj_tac >- suspend "positive_history" >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- suspend "positive_record" >>
  metis_tac[]
QED
Resume raw_call_outbuf_joint[positive_path]:
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspecl_then
    [`m with vs_inst_idx := LENGTH sm.cs_current_insts`, `G1`, `tn1`, `[]`] mp_tac) >>
  simp_tac bool_ss [APPEND] >> disch_then irule >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  simp[NoAsms, Once (GSYM arithmeticTheory.ADD_ASSOC)] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
    (LENGTH (emitted_insts sa sm) + LENGTH (emitted_insts sm sb))` by
    metis_tac[LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >> simp[]
QED
Resume raw_call_outbuf_joint[positive_horizon]:
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (m with vs_inst_idx := LENGTH sm.cs_current_insts) /\
   ghost_inv_at (DF H) lo d cenv cx es G1 tn1 (m with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    metis_tac[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- suspend "positive_state" >> simp[] >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G1`, `es`, `m with vs_inst_idx := LENGTH sm.cs_current_insts`, `sm`, `tn1`] >>
  simp[] >> (gvs[])
QED
Resume raw_call_outbuf_joint[positive_wb]:
  irule wb_frame_readonly_tail >> qexistsl_tac [`sa`, `s`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x (u with vs_inst_idx := _) = lookup_var x s /\ _` drule >>
  gvs[lookup_var_def]
QED
Resume raw_call_outbuf_joint[positive_return]:
  irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sk`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x (u with vs_inst_idx := _) = lookup_var x s /\ _` drule >>
  simp[lookup_var_def] >> gvs[lookup_var_def]
QED
Resume raw_call_outbuf_joint[positive_kept]:
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G1`, `tn1`] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sa x` by (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED
Resume raw_call_outbuf_joint[positive_history]:
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es
     (m with vs_inst_idx := LENGTH sm.cs_current_insts)` by metis_tac[] >>
  `alloca_inv (m with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ (m with vs_inst_idx := _)` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_op_extends, same_blocks_def] >>
  mp_tac (Q.SPECL
    [`emitted_insts sm sb`, `sm`, `sb`,
     `m with vs_inst_idx := LENGTH sm.cs_current_insts`,
     `u with vs_inst_idx := LENGTH sm.cs_current_insts`]
       emitted_alloca_history) >>
  (impl_tac >- simp[]) >> simp[]
QED
Resume raw_call_outbuf_joint[positive_record]:
  qpat_x_assum `m with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
  qpat_x_assum `u with <|vs_vars := m.vs_vars; vs_inst_idx := _|> = _` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume raw_call_outbuf_joint[zero_wb]:
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  irule wb_frame_readonly_tail >> qexists_tac `sa` >> simp[] >>
  metis_tac[]
QED
Resume raw_call_outbuf_joint[zero_return]:
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s`, `sk`] >> simp[] >>
  (simp[not_fresh_at_def])
QED
Resume raw_call_outbuf_joint[positive_state]:
  irule stmt_state_rel_readonly_vars_pc >>
  qexistsl_tac [`m with vs_inst_idx := LENGTH sm.cs_current_insts`, `sm`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x _ = _ /\ _` drule >>
      gvs[lookup_var_def]) >>
  qpat_x_assum `u with <|vs_vars := m.vs_vars; vs_inst_idx := _|> = _` mp_tac >>
  simp[venom_state_component_equality]
QED
Finalise raw_call_outbuf_joint
