Theory bodyFullRawCallOutbufAlloc
Ancestors
  bodyFullAllocaFresh bodyFullAllocGeneric bodyFullUnwrapRun
  bodyPtrIfExpAllocKept bodyPtrPrecompileBuiltinsAllocationFrame
  bodyPtrIfExpBytesCounted bodyPtrIfExpAllocCompiler
  abiBuiltinAllocation allocationPtr exprSimAlloc emitHelperProps emitHelper
  fragExecPtr exprLoweringProps loweringHalt venomMemDefs
  decoderGhostFramePtr bodyPtrIfExpAllocGhost instMemFrontier ptrSafeRun ghostPcTransportPtr
  bodyPtrDefs loweringStateRelDefs ptrDiscipline ptrSafetyTransport
  fragGasSeqPtr fragExecMem venomState venomInst venomExecSemantics
  finite_map words list pred_set

Theorem raw_call_outbuf_alloc_joint:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  stmt_state_rel H0 ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sk.cs_next_var <= sa.cs_next_var /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                aid < sk.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
  (!name b sz. local_region cenv es0.scopes s0 name b sz ==>
               b + sz <= s.vs_alloca_next) ==>
  ?G1 tn1 q b.
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
         stmt_state_rel H ctx func cenv cx es t) /\
    (!D d H. stmt_state_rel H ctx func cenv cx es s /\
             ghost_inv_at D lo d cenv cx es G tn s ==>
             ghost_inv_at D lo d cenv cx es G1 tn1 t) /\
    (ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
     ghost_kept_at lo cenv es0 sk G0 tn0 s0 G1 tn1) /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
    op_prov G1 buf.buf_operand = SOME (b,n) /\
    op_taint tn1 buf.buf_operand = {} /\
    b+n < dimword (:256) /\ b+n <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t.vs_allocas aid = SOME e) /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!i. i IN tn1.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `?b. FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
       lookup_var q u = SOME (n2w b) /\ b+n < dimword (:256) /\
       u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                vs_alloca_next := s.vs_alloca_next|> = s /\
       s.vs_alloca_next <= u.vs_alloca_next /\
       b+n <= u.vs_alloca_next /\
       (!lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==> allocas_from lo u) /\
       (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP u.vs_allocas aid = SOME e) /\
       (!i. i IN (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s u tn).t_mem <=>
            i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+n))` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
         drule_all fresh_alloca_ghost >>
         disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
         drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
         simp[] >> disch_then (qspec_then `q` assume_tac) >> gvs[] >>
         qexists_tac `s.vs_alloca_next` >>
         simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
              venom_state_component_equality, allocas_from_def] >>
         rpt strip_tac >> gvs[AllCaseEqs()] >>
         TRY (first_x_assum irule >> goal_assum (drule_at Any) >> NO_TAC) >>
         strip_tac >> gvs[]) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
     drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
     `site0+buf.buf_size <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
        res_tac >> decide_tac) >>
     drule reused_alloca_ghost >>
     disch_then (qspecl_then [`q`, `[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
     drule reused_alloca_step >> disch_then (qspec_then `q` assume_tac) >> gvs[] >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          venom_state_component_equality, allocas_from_def] >>
     rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[]) >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]` >>
  qabbrev_tac `G1 = step_prov PG G ins u` >>
  qabbrev_tac `tn1 = step_taint ins s u tn` >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `q`]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `G1`, Abbr `tn1`, Abbr `ins`,
                           step_prov_other_output, step_taint_other_output, mk_inst_def] >>
     metis_tac[alloca_step_lookup_preserved]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _|> = s`
      (SUBST1_TAC o SYM) >> simp[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `ins`, alloca_ghost_frames] >>
  `op_prov G1 (Var q) = SOME (b,n)` by
    simp[Abbr `G1`, Abbr `ins`, step_prov_def, out_prov_def, set_prov_def,
         mk_inst_def, FLOOKUP_UPDATE, op_prov_def] >>
  `op_taint tn1 (Var q) = {}` by
    simp[Abbr `tn1`, Abbr `ins`, step_taint_def, mk_inst_def, op_taint_def,
         set_var_taint_def, out_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
  qexistsl_tac [`G1`, `tn1`, `q`, `b`] >>
  simp[] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "record" >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "history" >>
  `allocas_from lo u` by metis_tac[] >>
  fs[lookup_var_def, eval_operand_def, allocas_from_def] >> first_assum ACCEPT_TAC
QED

Resume raw_call_outbuf_alloc_joint[fresh]:
  simp[not_fresh_at_def, Abbr `q`, ASCIInumbersTheory.toString_11]
QED
Resume raw_call_outbuf_alloc_joint[path]:
  rpt gen_tac >>
  `run_inst_seq [ins] s = OK u` by gvs[] >>
  `run_inst_seq_mem_ok [ins] s` by
    (simp[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `ins`, mk_inst_def]) >>
     simp[Abbr `ins`, mk_inst_def, memSafeRunTheory.inst_dload_in_section_def]) >>
  `inst_seq_ptr D lo ctx func PG G tn [ins] s G1 tn1` by
    (simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `ins`, ptr_inst_ok_alloca]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [ins]` by
    simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  qspecl_then [`[ins]`, `sa`, `sb`, `s`, `u`, `G`, `tn`, `G1`, `tn1`]
    mp_tac emitted_origin_ptr_path >> simp[]
QED
Resume raw_call_outbuf_alloc_joint[record]:
  qpat_x_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume raw_call_outbuf_alloc_joint[state]:
  rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` kall_tac >>
  unabbrev_all_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[]
QED
Resume raw_call_outbuf_alloc_joint[ghost]:
  rpt strip_tac >>
  `allocas_from lo u` by metis_tac[] >>
  irule alloc_buffer_ghost_inv_at >>
  rpt (first_assum (irule_at Any)) >>
  qexists_tac `b+n` >>
  fs[lookup_var_def, allocas_from_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume raw_call_outbuf_alloc_joint[kept]:
  strip_tac >> irule alloc_buffer_ghost_kept_at >>
  rpt (first_assum (irule_at Any)) >>
  qexists_tac `b+n` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  metis_tac[]
QED
Resume raw_call_outbuf_alloc_joint[history]:
  qspecl_then [`[ins]`, `sa`, `sb`, `s`, `u`] mp_tac emitted_alloca_history >>
  simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  disch_then irule >> fs[stmt_state_rel_def, mk_inst_def]
QED
Finalise raw_call_outbuf_alloc_joint
