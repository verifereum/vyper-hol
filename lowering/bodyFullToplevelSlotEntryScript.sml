(* TopLevelName allocation and the zero-prefix loop header, on one run. *)
Theory bodyFullToplevelSlotEntry
Ancestors
  exprSimAlloc allocationPtr bufferAllocationExecution venomMemDefs
  exprPtrUnwrapEnsureShape exprPtrUnwrapFrames createSourceCallback
  bodyFullToplevelCodeAllocation exprPtrUnwrapLoopEntry exprPtrUnwrapStorageEntry
  exprPtrUnwrapScalarSegments exprPtrUnwrapScalarEdges exprPtrUnwrapBackedge
  exprPtrUnwrapRuntimeFrame exprPtrUnwrapFrames exprPtrUnwrapCondition
  exprPtrUnwrapLoopInvariant
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathMem gasEvents
  memSafeRun fragExecMem instMemFrontier unitTransformDefs fragGasPathPtr ptrSafetyTransport
  exprLowering exprLoweringProps slotCopyExecution copyExecution
  ptrDiscipline ptrSafeRun bodyPtrDefs venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel finite_map pred_set list rich_list arithmetic words

Theorem toplevel_slot_copy_initial_path[local]:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  run_inst_seq [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]] s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]] s G1 tn1 /\
  t = update_var (slot_copy_var cs 0) 0w s /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (slot_copy_initial cs s),G1,tn1)
Proof
  strip_tac >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_gas_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`t`,`bb`] mp_tac) >>
  (impl_tac >- simp[slot_copy_init_insts_def, mk_inst_def, is_terminator_def,
    DROP_LENGTH_APPEND, eval_operand_def, run_inst_seq_mem_ok_def, step_inst_base_opcode_eqs, inst_mem_below_frontier_def,
    inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  simp[mk_inst_def] >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx+1` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    gvs[Abbr `u`, update_var_def] >>
  `get_instruction bb u.vs_inst_idx =
    SOME (mk_inst (cs.cs_next_id+1) JMP [Label (slot_copy_cond cs)] [])` by
    simp[Abbr `u`, slot_copy_init_insts_def, get_instruction_def, EL_APPEND_EQN] >>
  `gas_path_ptr_edge D lo ctx fn PG G1 tn1 u 0 G1 tn1
    (OK (jump_to (slot_copy_cond cs) u))` by
    (irule copy_jmp_counted_edge >> simp[Abbr `u`] >>
     qexists `cs.cs_next_id+1` >>
     simp[slot_copy_init_insts_def, get_instruction_def, EL_APPEND_EQN]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,G1,tn1) []
    (OK (jump_to (slot_copy_cond cs) u),G1,tn1)` by
    (simp[gas_origin_ptr_edge_def] >> irule gas_path_mem_edge_zero_origin >>
     qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_path_ptr_edge_def, gas_path_mem_edge_def] >> strip_tac >>
     `mem_safe_step fuel ctx (mk_inst (cs.cs_next_id+1) JMP [Label (slot_copy_cond cs)] []) u` by
       simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def] >>
     metis_tac[]) >>
  `jump_to (slot_copy_cond cs) u = slot_copy_initial cs s` by
    simp[Abbr `u`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  `~(slot_copy_initial cs s).vs_halted` by simp[slot_copy_initial_def, jump_to_def, update_var_def] >>
  drule gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`] mp_tac) >>
  simp[Abbr `u`] >> disch_then irule >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  qexistsl [`G1`,`slot_copy_initial cs s`,`tn1`] >>
  gvs[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem toplevel_slot_copy_initial_joint:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  n < 2**256 /\ w2n (d:bytes32)+32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
  slot_copy_external cs (Var root) /\ ptr_covers G tn root s (32*n) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G1 tn1.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
       (OK (slot_copy_initial cs s),G1,tn1)) /\
    slot_copy_inv cs load s p d n regions 0 (slot_copy_initial cs s) /\
    slot_copy_ghost_inv cs load p d root n G tn 0 G1 tn1 (slot_copy_initial cs s) /\
    allocas_from lo (slot_copy_initial cs s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_initial cs s))
Proof
  strip_tac >>
  mp_tac (Q.INST [`id` |-> `cs.cs_next_id`, `arg` |-> `Lit 0w`,
    `tmp` |-> `slot_copy_var cs 0`, `x` |-> `0w`, `D` |-> `ARB`]
    (SPEC_ALL copy_assign_segment)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  qexistsl [`Gf`,`tnf`] >> reverse conj_tac
  >- (conj_tac >- simp[slot_copy_initial_invariant] >> conj_tac
      >- (irule copy_initial_ghost_frame >> simp[] >> metis_tac[]) >>
      gvs[slot_copy_initial_def, allocas_from_def, allocas_below_fmp_def,
          jump_to_def, update_var_def] >> metis_tac[]) >>
  rpt gen_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]] s Gf tnf` by
    (gvs[inst_seq_ptr_def] >> simp[ptr_inst_ok_copy_assign, eval_operand_def, op_taint_def]) >>
  irule toplevel_slot_copy_initial_path >> simp[] >> metis_tac[]
QED

Theorem toplevel_slot_copy_allocation_entry:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,sa) /\
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\ 32*n <= nb ==>
  ?root d a G0 tn0 u.
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    buf.buf_operand = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0)) /\
    a.vs_current_bb = sm.cs_current_bb /\ a.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ~a.vs_halted /\ slot_copy_external sm src /\ slot_copy_external sm (Var root) /\
    eval_operand src a = SOME p /\ lookup_var root a = SOME d /\ op_taint tn0 src = {} /\
    ptr_covers G0 tn0 root a (32*n) /\ ptr_covers G0 tn0 root a nb /\
    w2n d+32*n < 2**256 /\ w2n d+32*n <= a.vs_alloca_next /\
    allocas_from lo a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`,`G`,`ARB`] strip_assume_tac) >>
  qexistsl [`root`,`d`,`a`,`G0`,`tn0`,`u`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> drule_all toplevel_code_allocation_full >>
      disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
      gvs[]) >>
  `allocas_from lo u` by
    (irule (cj 1 step_inst_allocas_from) >>
     qexistsl [`ctx`,`0`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]`,`s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  reverse conj_tac >- (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `buffer_allocation_base s sa.cs_next_id MOD dimword (:256) <= buffer_allocation_base s sa.cs_next_id` by simp[MOD_LESS_EQ] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (gvs[buffer_allocation_fields_def, buffer_allocation_base_def] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME allocation` >>
  PairCases_on `allocation` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  gvs[buffer_allocation_fields_def, buffer_allocation_base_def,
      stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  qpat_x_assum `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) ==> _` drule >>
  decide_tac
QED

Theorem toplevel_slot_copy_entry_joint:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,sa) /\
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ n < 2**256 /\ 32*n <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32) \/
     w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32)+32*n <= off)) regions ==>
  ?root d a G0 tn0 sm buf u h Gh tnh lab.
    compile_alloc_buffer nb sa = (buf,sm) /\ op = Var root /\ buf.buf_operand = Var root /\
    compile_slot_to_memory src (Var root) n loc sm = (lab,sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    d = n2w (buffer_allocation_base s sa.cs_next_id) /\ h = slot_copy_initial sm a /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK h,Gh,tnh)) /\
    slot_copy_inv sm (if loc=LocStorage then SLOAD else TLOAD) a p d n regions 0 h /\
    slot_copy_ghost_inv sm (if loc=LocStorage then SLOAD else TLOAD) p d root n G0 tn0 0 Gh tnh h /\
    slot_copy_external sm src /\ slot_copy_external sm (Var root) /\
    eval_operand src a = SOME p /\ lookup_var root a = SOME d /\
    op_taint tnh src = {} /\ ~h.vs_halted /\
    h.vs_current_bb = slot_copy_cond sm /\ h.vs_inst_idx = 0 /\
    lookup_block (slot_copy_cond sm) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond sm; bb_instructions := slot_copy_cond_insts sm n|> /\
    lookup_block (slot_copy_body sm) func.fn_blocks =
      SOME <|bb_label := slot_copy_body sm; bb_instructions := slot_copy_body_insts sm src (Var root)
        (if loc=LocStorage then SLOAD else TLOAD)|> /\
    w2n d+32*n <= h.vs_alloca_next /\
    allocas_from lo h /\ (ctx_has_dalloca ctx ==> allocas_below_fmp h) /\
    ptr_covers G0 tn0 root a nb /\ ptr_covers Gh tnh root h nb /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule_all ensure_slot_memory_loop_code >> strip_tac >>
  drule_all toplevel_slot_copy_allocation_entry >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  `fn_has_code sm (slot_copy_final sm src (Var root) n
    (if loc=LocStorage then SLOAD else TLOAD)) func` by metis_tac[] >>
  drule_all slot_copy_lookup >> strip_tac >>
  `create_memory_snapshot regions a` by gvs[create_memory_snapshot_def] >>
  `EVERY (\(off,bs). off+LENGTH bs <= LENGTH a.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions` by metis_tac[] >>
  `lookup_block a.vs_current_bb func.fn_blocks = SOME
    <|bb_label := sm.cs_current_bb; bb_instructions := sm.cs_current_insts ++ slot_copy_init_insts sm|>` by simp[] >>
  mp_tac (Q.INST [`s` |-> `a`, `cs` |-> `sm`, `G` |-> `G0`, `tn` |-> `tn0`,
    `fn` |-> `func`, `cb` |-> `sa`,
    `bb` |-> `<|bb_label := sm.cs_current_bb; bb_instructions := sm.cs_current_insts ++ slot_copy_init_insts sm|>`,
    `load` |-> `if loc=LocStorage then SLOAD else TLOAD`]
    (SPEC_ALL toplevel_slot_copy_initial_joint)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl [`root`,`d`,`a`,`G0`,`tn0`,`sm`,`buf`,`u`,`slot_copy_initial sm a`,`G1`,`tn1`,`lab`] >>
  `~(slot_copy_initial sm a).vs_halted /\
   (slot_copy_initial sm a).vs_current_bb = slot_copy_cond sm /\
   (slot_copy_initial sm a).vs_inst_idx = 0 /\
   (slot_copy_initial sm a).vs_alloca_next = a.vs_alloca_next` by
    (simp[NoAsms, slot_copy_initial_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 src = {}` by
    (qpat_x_assum `slot_copy_ghost_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[slot_copy_ghost_inv_def] >> strip_tac >>
     Cases_on `src` >> simp[NoAsms, op_taint_def]
     >> rename1 `(case FLOOKUP tn1.t_var x of NONE => {} | SOME m => m) = {}` >>
     qpat_x_assum `!v. slot_copy_external sm (Var v) ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (CONJUNCTS_THEN2 kall_tac mp_tac) >>
     qpat_x_assum `op_taint tn0 (Var x) = {}` mp_tac >>
     pure_rewrite_tac[op_taint_def] >> simp[]) >>
  `ptr_covers G1 tn1 root (slot_copy_initial sm a) nb` by
    (qpat_x_assum `slot_copy_ghost_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[slot_copy_ghost_inv_def] >> strip_tac >>
     qpat_x_assum `!v. slot_copy_external sm (Var v) ==> _` (qspec_then `root` mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >>
     `lookup_var root (slot_copy_initial sm a) = lookup_var root a` by
       (qpat_x_assum `slot_copy_external sm (Var root)` mp_tac >>
        simp[NoAsms, slot_copy_external_def, slot_copy_initial_def, jump_to_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
     metis_tac[ptr_covers_def]) >>
  metis_tac[]
QED
