(* Output-allocation boundaries for the counted raw_call pointer proof. *)
Theory rawCallAllocationProofPtr
Ancestors
  rawCallPrefixPtr rawCallBufferPtr builtinSystem context emitHelper compileEnv loweringStateRelDefs
  fragGasSeqPtr fragExecPtr typedCopyPtr exprSimAlloc exprSimPtrLiteralBuffer
  exprLoweringProps venomInst bodyPtrDefs pred_set

Theorem raw_call_outbuf_steps:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (((cap + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
    ov = buf.buf_operand /\ emit_op ADD [ov; Lit 32w] sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_zero_steps:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) ==>
  ?buf. compile_alloc_buffer 0 sa = (buf,sb) /\
    ov = buf.buf_operand /\ op = buf.buf_operand
Proof
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_positive_code:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (((cap+31) DIV 32)*32+32))]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (SUC sa.cs_next_id) ADD [ov; Lit 32w]
       [STRING #"%" (toString (SUC sa.cs_next_var))]] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[arithmeticTheory.ADD1, listTheory.APPEND_ASSOC]
QED

(* Allocation succeeds by the semantic allocation invariant at its caller;
   this boundary checks that actual successful step, not an erased run. *)
Theorem raw_call_alloca_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit n] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id ALLOCA [Lit n] [out]) s` by simp[ptr_inst_ok_alloca] >>
  `(mk_inst id ALLOCA [Lit n] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id ALLOCA [Lit n] [out]).inst_opcode` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  `step_inst 0 ctx (mk_inst id ALLOCA [Lit n] [out]) s = OK u` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all venomInstProofsTheory.step_preserves_halted >> simp[]
QED

Theorem raw_call_emit_alloca_path_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_alloca_path_ptr >> simp[]
QED

Theorem raw_call_alloc_buffer_stage:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?u b dirty.
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
    stmt_state_rel ctx func cenv cx es u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b n a len) /\
    b+n < dimword(:256) /\
    lookup_var (STRING #"%" (toString sa.cs_next_var)) u = SOME (n2w b) /\
    step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) u =
      G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)) /\
    step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn =
      tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
        t_mem := tn.t_mem UNION dirty|> /\
    dirty SUBSET {i | b <= i /\ i < b+n} /\
    gas_path_ptr D 0 ctx func PG G tn s 0
      (G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)))
      (tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
        t_mem := tn.t_mem UNION dirty|>)
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\ sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def, emitted_insts_def] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (gvs[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `b`, `dirty`] >> simp[] >>
  drule_all raw_call_emit_alloca_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* A fresh allocation may dirty padding, but never old allocations or locals. *)
Theorem raw_call_alloc_dirty_kept:
  (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem UNION dirty /\
  dirty SUBSET {i | b <= i /\ i < b+n} /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len) ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def, regions_disjoint_def, SUBSET_DEF] >>
  rpt strip_tac >> gvs[] >>
  `b <= i /\ i < b+n` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >> decide_tac
QED

Theorem raw_call_alloc_dirty_inv:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len) /\
  u.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem UNION dirty /\
  dirty SUBSET {i | b <= i /\ i < b+n} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' u
Proof
  strip_tac >> irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all literal_ptr_local_footprint_exterior >> simp[]) >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem raw_call_alloca_state_frame:
  step_inst_base (mk_inst id ALLOCA [Lit nw] [out]) s = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
  (!aid. aid <> id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
  u.vs_returndata = s.vs_returndata
Proof
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[venomStateTheory.update_var_def]
QED

Theorem raw_call_alloc_ghost_frame:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> out /\ lookup_var x u = lookup_var x s) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  step_inst_base (mk_inst id ALLOCA [Lit nw] [out]) s = OK u /\
  dirty SUBSET {i | b <= i /\ i < b+n} ==>
  ghost_inv d cenv cx es (G |+ (out,(b,n)))
    (tn with <|t_var := tn.t_var |+ (out,{}); t_mem := tn.t_mem UNION dirty|>) u /\
  ghost_kept cenv es sa G tn s (G |+ (out,(b,n)))
    (tn with <|t_var := tn.t_var |+ (out,{}); t_mem := tn.t_mem UNION dirty|>)
Proof
  strip_tac >>
  `!name a len. local_region cenv es.scopes u name a len <=>
    local_region cenv es.scopes s name a len` by
    (irule literal_ptr_local_region_frame >> simp[] >> metis_tac[]) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len` by metis_tac[] >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP (G |+ (out,(b,n))) x = FLOOKUP G x /\
    op_taint (tn with <|t_var := tn.t_var |+ (out,{});
      t_mem := tn.t_mem UNION dirty|>) (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE,
      ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  drule raw_call_alloca_state_frame >> strip_tac >> conj_tac
  >- (irule raw_call_alloc_dirty_inv >>
      qexistsl_tac [`G`, `b`, `ctx`, `dirty`, `func`, `n`, `s`, `sa`, `tn`] >>
      simp[] >> metis_tac[]) >>
  irule raw_call_alloc_dirty_kept >> simp[] >>
  qexistsl_tac [`b`, `dirty`, `n`] >> simp[] >> metis_tac[]
QED


Theorem raw_call_alloc_buffer_ghost_stage:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  n < dimword(:256) /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?u b H un.
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_current_bb = sb.cs_current_bb /\ ~u.vs_halted /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    op_prov H buf.buf_operand = SOME (b,n) /\
    op_taint un buf.buf_operand = {} /\ b+n < dimword(:256) /\
    u.vs_memory = s.vs_memory /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    (!name a len. local_region cenv es.scopes s name a len ==>
      regions_disjoint b n a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    H = G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)) /\
    (?dirty. dirty SUBSET {i | b <= i /\ i < b+n} /\
      un = tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
        t_mem := tn.t_mem UNION dirty|>) /\
    (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    u.vs_returndata = s.vs_returndata /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\ sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule_all raw_call_alloc_buffer_stage >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `ghost_inv dep cenv cx es
    (G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)))
    (tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
      t_mem := tn.t_mem UNION dirty|>) u /\
   ghost_kept cenv es sa G tn s
    (G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)))
    (tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
      t_mem := tn.t_mem UNION dirty|>)` by
    (irule raw_call_alloc_ghost_frame >> simp[] >>
     `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
       (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     metis_tac[]) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len` by
    (`!name a len. local_region cenv es.scopes u name a len <=>
        local_region cenv es.scopes s name a len` by
       (irule literal_ptr_local_region_frame >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  drule raw_call_alloca_state_frame >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  `wb_frame cenv es sa s (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
       venomStateTheory.lookup_var_def] >> metis_tac[venomStateTheory.lookup_var_def]) >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `b`,
    `G |+ (STRING #"%" (toString sa.cs_next_var),(b,n))`,
    `tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
      t_mem := tn.t_mem UNION dirty|>`] >>
  simp[rawCallHeaderFramePtrTheory.ghost_inv_inst_idx, stmt_state_rel_inst_idx] >>
  `buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
    venomStateTheory.lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[venomStateTheory.lookup_var_def]) >>
  qexists_tac `dirty` >> simp[]
QED

Theorem raw_call_outbuf_add_stage:
  emit_op ADD [Var x; Lit 32w] sa = (Var dx,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ not_fresh_at sa x /\
  lookup_var x s = SOME (n2w b) /\ FLOOKUP G x = SOME (b,n) /\
  op_taint tn (Var x) = {} /\ 32+cap <= n /\ b+n < dimword(:256) ==>
  ?H un u. gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u n /\ ptr_covers H un dx u cap /\
    eval_operand (Var dx) u = SOME (n2w (b+32)) /\
    u.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    u.vs_returndata = s.vs_returndata /\ u.vs_allocas = s.vs_allocas /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s /\
      FLOOKUP H z = FLOOKUP G z /\ op_taint un (Var z) = op_taint tn (Var z))
Proof
  strip_tac >>
  `op_taint tn (Lit 32w) = {} /\ eval_operand (Lit 32w) s = SOME 32w /\
    eval_operand (Var x) s = SOME (n2w b)` by
    simp[ptrDisciplineTheory.op_taint_def, venomStateTheory.eval_operand_def] >>
  drule_all rawCallDataHeaderPtrTheory.raw_call_emit_add_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H un (OK u)` >>
  `ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un` by
    (qunabbrev_tac `u` >> irule rawCallHeaderFramePtrTheory.raw_call_emit_add_ghost_frame >>
     goal_assum (drule_at Any) >> simp[Abbr `H`, Abbr `un`] >>
     qexistsl_tac [`PG`, `Var x`, `Lit 32w`] >> simp[]) >>
  `~not_fresh_at sa dx /\ sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[not_fresh_at_def]) >>
  `x <> dx` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u` by
    (qunabbrev_tac `u` >> irule rawCallDataHeaderPtrTheory.raw_call_fresh_update_state_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  `H = G |+ (dx,(b,n)) /\ un = tn with t_var := tn.t_var |+ (dx,{})` by
    (simp[Abbr `H`, Abbr `un`] >>
     metis_tac[exprSimPtrLiteralOpsTheory.literal_add_ghost]) >>
  qexistsl_tac [`H`, `un`, `u`] >> simp[] >>
  simp[Abbr `u`, Abbr `H`, Abbr `un`, exprSimPtrLiteralOpsTheory.literal_add_ghost,
    ptr_covers_def, ptrDisciplineTheory.op_taint_def, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    venomStateTheory.eval_operand_def, GSYM wordsTheory.word_add_n2w,
    wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> fs[not_fresh_at_def, ptrDisciplineTheory.op_taint_def,
    venomStateTheory.lookup_var_def] >>
  qexists_tac `n2w b` >> simp[wordsTheory.w2n_n2w] >> decide_tac
QED

Theorem raw_call_outbuf_split_code:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  fn_has_code sa sb func ==>
  ?buf sm. compile_alloc_buffer (((cap+31) DIV 32)*32+32) sa = (buf,sm) /\
    ov = buf.buf_operand /\ emit_op ADD [ov; Lit 32w] sm = (op,sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    (local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sm)
Proof
  strip_tac >> drule_all raw_call_outbuf_steps >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     simp[listTheory.APPEND_ASSOC]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  qexistsl_tac [`buf`, `sm`] >> simp[] >>
  strip_tac >> irule local_ptrs_reserved_next_var >>
  qexists_tac `sa` >> simp[] >>
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem raw_call_alloc_buffer_metadata:
  compile_alloc_buffer n sa = (buf,sm) ==>
  ?x. buf.buf_operand = Var x /\ not_fresh_at sm x /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[not_fresh_at_def] >>
  qexists_tac `sa.cs_next_var` >> simp[]
QED

Theorem raw_call_outbuf_capacity:
  32+cap <= ((cap+31) DIV 32)*32+32
Proof
  mp_tac (Q.SPEC `cap+31` (MATCH_MP arithmeticTheory.DIVISION (DECIDE ``0 < 32:num``))) >>
  ` (cap+31) MOD 32 < 32` by simp[] >>
  simp[] >> decide_tac
QED

Theorem raw_call_outbuf_positive_stage:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ((cap+31) DIV 32)*32+32 < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un u x dx. ov = Var x /\ op = Var dx /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u (((cap+31) DIV 32)*32+32) /\
    ptr_covers H un dx u cap /\ u.vs_memory = s.vs_memory /\
    (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (?dst. eval_operand op u = SOME (n2w dst) /\
      dst < dimword(:256) /\ dst+cap < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint dst cap a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint dst cap a len)) /\
    (?ob. sa.cs_next_id < sb.cs_next_id /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,((cap+31) DIV 32)*32+32) /\
      eval_operand ov u = SOME (n2w ob) /\
      eval_operand op u = SOME (n2w (ob+32)) /\
      ob+(((cap+31) DIV 32)*32+32) < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint ob (((cap+31) DIV 32)*32+32) a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint ob (((cap+31) DIV 32)*32+32) a len))
Proof
  strip_tac >> drule_all raw_call_outbuf_split_code >>
  disch_then (qspec_then `cenv` strip_assume_tac) >>
  drule raw_call_alloc_buffer_metadata >> strip_tac >> gvs[] >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    metis_tac[] >>
  `?dx. op = Var dx` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> metis_tac[]) >> gvs[] >>
  drule_all raw_call_alloc_buffer_ghost_stage >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
  `32+cap <= ((cap+31) DIV 32)*32+32` by simp[raw_call_outbuf_capacity] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    metis_tac[] >>
  `32+cap <= 32*((cap+31) DIV 32)+32` by simp[raw_call_outbuf_capacity] >>
  drule_all raw_call_outbuf_add_stage >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u')` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  `wb_frame cenv es sa s u'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [`u`, `sm`, `es`] >> simp[] >> metis_tac[]) >>
  `?dst. eval_operand (Var dx) u' = SOME (n2w dst) /\
    dst < dimword(:256) /\ dst+cap < dimword(:256) /\
    (!name a len. local_region cenv es.scopes s name a len ==>
      regions_disjoint dst cap a len) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint dst cap a len)` by
    (qexists_tac `b+32` >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _`
           drule >> simp[regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!aid a len. _ /\ FLOOKUP _ _ = SOME _ ==> _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`H`, `un`, `u'`] >> simp[] >>
  gvs[ghost_kept_def, venomStateTheory.eval_operand_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `b+32` >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem raw_call_outbuf_zero_stage:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un u x. ov = Var x /\ op = Var x /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u 0 /\ u.vs_memory = s.vs_memory /\
    (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (?dst. eval_operand op u = SOME (n2w dst) /\
      dst < dimword(:256) /\ dst+0 < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint dst 0 a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint dst 0 a len)) /\
    (?ob. sa.cs_next_id < sb.cs_next_id /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,0) /\
      eval_operand ov u = SOME (n2w ob) /\ ob < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint ob 0 a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint ob 0 a len))
Proof
  strip_tac >> drule raw_call_outbuf_zero_steps >> strip_tac >> gvs[] >>
  drule raw_call_alloc_buffer_metadata >> strip_tac >>
  `0 < dimword(:256)` by simp[] >>
  drule_all raw_call_alloc_buffer_ghost_stage >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `un`, `u`, `x`] >> simp[] >>
  gvs[ptr_covers_def, venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
  conj_tac >- (qexists_tac `b` >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem raw_call_outbuf_stage:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un u x dx. ov = Var x /\ op = Var dx /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
    ptr_covers H un dx u cap /\ u.vs_memory = s.vs_memory /\
    (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (?dst. eval_operand op u = SOME (n2w dst) /\
      dst < dimword(:256) /\ dst+cap < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint dst cap a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint dst cap a len)) /\
    (?ob bytes. sa.cs_next_id < sb.cs_next_id /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,bytes) /\
      eval_operand ov u = SOME (n2w ob) /\
      eval_operand op u = SOME (n2w (if cap = 0 then ob else ob+32)) /\
      ob+bytes < dimword(:256) /\
      bytes = (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint ob bytes a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint ob bytes a len))
Proof
  strip_tac >> Cases_on `cap = 0`
  >- (gvs[] >> drule_all raw_call_outbuf_zero_stage >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl_tac [`H`, `un`, `u`, `x`, `x`] >> simp[] >>
      conj_tac >- (qexists_tac `dst` >> simp[] >> metis_tac[]) >>
      gvs[wordsTheory.n2w_11] >> metis_tac[]) >>
  `0 < cap` by decide_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [arithmeticTheory.MULT_COMM] raw_call_outbuf_positive_stage) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ob+32 < dimword(:256)` by decide_tac >>
  `dst = ob+32` by fs[wordsTheory.n2w_11] >>
  qexistsl_tac [`H`, `un`, `u`, `x`, `dx`] >> simp[] >>
  conj_tac >- (qexists_tac `dst` >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem raw_call_outbuf_ready_stage:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) =
    SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) /\
  (!z. data_op = Var z ==> not_fresh_at sa z) /\
  op_prov G data_op = SOME (region_base,sz) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) ==>
  ?H un u x dx. ov = Var x /\ op = Var dx /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK u) /\
    ghost_inv dep cenv cx es H un u /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es sa s u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
    ptr_covers H un dx u cap /\ u.vs_memory = s.vs_memory /\
    (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    op_prov H data_op = SOME (region_base,sz) /\
    (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN un.t_mem) /\
    (!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
      eval_operand arg u = eval_operand arg s /\
      op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg) /\
    (?dst. eval_operand op u = SOME (n2w dst) /\
      dst < dimword(:256) /\ dst+cap < dimword(:256) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint dst cap a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint dst cap a len)) /\
    (?ob bytes. sa.cs_next_id < sb.cs_next_id /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,bytes) /\
      eval_operand ov u = SOME (n2w ob) /\
      eval_operand op u = SOME (n2w (if cap = 0 then ob else ob+32)) /\
      ob+bytes < dimword(:256) /\
      bytes = (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        regions_disjoint ob bytes a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint ob bytes a len))
Proof
  strip_tac >> drule_all raw_call_outbuf_stage >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
      eval_operand arg u = eval_operand arg s /\
      op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg` by
    (rpt strip_tac >> Cases_on `arg` >>
     fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, ghost_kept_def]) >>
  `op_prov H data_op = SOME (region_base,sz)` by
    (Cases_on `data_op` >> fs[ptrDisciplineTheory.op_prov_def, ghost_kept_def]) >>
  `(if cap = 0 then ob else ob+32) < dimword(:256)` by
    (Cases_on `cap = 0` >> gvs[] >> decide_tac) >>
  `dst = (if cap = 0 then ob else ob+32)` by fs[wordsTheory.n2w_11] >>
  qexistsl_tac [`H`, `un`, `u`, `x`, `dx`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- (qexists_tac `dst` >> simp[] >> metis_tac[]) >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `i IN tn.t_mem` suffices_by
    (strip_tac >> qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem`
      (qspec_then `i` mp_tac) >> simp[]) >>
  irule rawCallKeywordPrefixPtrTheory.saved_value_footprint_taint_kept >>
  first_assum (irule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
    wordsTheory.w2n_n2w] >>
  qexistsl_tac [`un`, `G`, `H`] >> simp[] >>
  irule stmtSimLogArgsTheory.log_arg_clear_base >> goal_assum (drule_at Any)
QED

(* Preserve the prefix post at the predecessor, avoiding a second copy of
   its semantic witnesses.  Allocation transports all old request operands. *)
Theorem raw_call_outbuf_ready_outcome:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) < dimword(:256) /\
  ~ctx_has_dalloca ctx /\
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!rr ee G tn t. Q rr ee G tn t ==>
    stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee G tn t /\
    t.vs_current_bb = sa.cs_current_bb /\
    t.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~t.vs_halted /\
    expr_sim_inv cenv cx env ee /\
    ?sd lim bs b base sz.
      expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa ee (BytesV bs) data t /\
      evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) =
        SOME (BaseTV (BytesT (Dynamic lim))) /\
      eval_operand data t = SOME (n2w b) /\ b < dimword(:256) /\
      (!z. data_op = Var z ==> not_fresh_at sa z) /\
      op_prov G data_op = SOME (base,sz) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\rr ee H un u. ?G tn t x dx base sz b bs sd lim.
      Q rr ee G tn t /\ ov = Var x /\ op = Var dx /\
      expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa ee (BytesV bs) data t /\
      ghost_inv dep cenv cx ee H un u /\ ghost_kept cenv ee sa G tn t H un /\
      stmt_state_rel ctx func cenv cx ee u /\ wb_frame cenv ee sa t u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      ptr_covers H un x u (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
      ptr_covers H un dx u cap /\ u.vs_memory = t.vs_memory /\
      (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP t.vs_allocas aid) /\
      eval_operand data t = SOME (n2w b) /\
      op_prov G data_op = SOME (base,sz) /\ op_prov H data_op = SOME (base,sz) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN un.t_mem) /\
      (!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
        eval_operand arg u = eval_operand arg t /\
        op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg) /\
      (?dst. eval_operand op u = SOME (n2w dst) /\
        dst < dimword(:256) /\ dst+cap < dimword(:256) /\
        (!name a len. local_region cenv ee.scopes t name a len ==>
          regions_disjoint dst cap a len) /\
        (!aid a len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
          regions_disjoint dst cap a len)) /\
      (?ob bytes. sa.cs_next_id < sb.cs_next_id /\
        FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,bytes) /\
        eval_operand ov u = SOME (n2w ob) /\
        eval_operand op u = SOME (n2w (if cap = 0 then ob else ob+32)) /\
        ob+bytes < dimword(:256) /\
        bytes = (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
        (!name a len. local_region cenv ee.scopes t name a len ==>
          regions_disjoint ob bytes a len) /\
        (!aid a len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
          regions_disjoint ob bytes a len))) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def,
    gasSummaryComposePtrTheory.gas_summary_ptr_at_marked] >>
  strip_tac
  >- suspend "normal"
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Resume raw_call_outbuf_ready_outcome[normal]:
  gvs[] >> first_assum drule >> strip_tac >>
  `?H un u x dx. ov = Var x /\ op = Var dx /\
    gas_path_ptr D 0 ctx func PG G tn t 0 H un (OK u) /\
    ghost_inv dep cenv cx (es_end with gas_obs := []) H un u /\
    ghost_kept cenv (es_end with gas_obs := []) sa G tn t H un /\
    stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) u /\
    wb_frame cenv (es_end with gas_obs := []) sa t u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ptr_covers H un x u (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
    ptr_covers H un dx u cap /\ u.vs_memory = t.vs_memory /\
      (!aid. aid < sa.cs_next_id ==> FLOOKUP u.vs_allocas aid = FLOOKUP t.vs_allocas aid) /\
    op_prov H data_op = SOME (base',sz) /\
    (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN un.t_mem) /\
    (!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
      eval_operand arg u = eval_operand arg t /\
      op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg) /\
    (?dst. eval_operand op u = SOME (n2w dst) /\
      dst < dimword(:256) /\ dst+cap < dimword(:256) /\
      (!name a len. local_region cenv (es_end with gas_obs := []).scopes t name a len ==>
        regions_disjoint dst cap a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint dst cap a len)) /\
    (?ob bytes. sa.cs_next_id < sb.cs_next_id /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (ob,bytes) /\
      eval_operand ov u = SOME (n2w ob) /\
      eval_operand op u = SOME (n2w (if cap = 0 then ob else ob+32)) /\
      ob+bytes < dimword(:256) /\
      bytes = (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
      (!name a len. local_region cenv (es_end with gas_obs := []).scopes t name a len ==>
        regions_disjoint ob bytes a len) /\
      (!aid a len. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
        regions_disjoint ob bytes a len))` by
    (irule raw_call_outbuf_ready_stage >> simp[] >> conj_tac
     >- (qexists_tac `env` >> fs[]) >>
     qexistsl_tac [`data`, `lim`, `sd`] >> simp[]) >>
  suspend "package"
QED

Resume raw_call_outbuf_ready_outcome[package]:
  qexists_tac `marks ++ REPLICATE 0 F` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `H`, `un`, `OK u`] >> conj_tac
  >- (irule gas_marked_exec_ptr_implicit_suffix >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  disj1_tac >> qexists_tac `u` >> simp[] >>
  qexistsl_tac [`G`, `tn`, `t`, `b`, `bs`, `sd`, `lim`] >>
  fs[] >> conj_tac >- (qexists_tac `dst` >> simp[] >> metis_tac[]) >> gvs[] >> metis_tac[]
QED

Finalise raw_call_outbuf_ready_outcome

val _ = if List.all (null o hyp)
  [raw_call_alloc_buffer_stage, raw_call_alloc_buffer_ghost_stage,
   raw_call_outbuf_add_stage, raw_call_outbuf_positive_stage,
   raw_call_outbuf_zero_stage, raw_call_outbuf_stage,
   raw_call_outbuf_ready_stage, raw_call_outbuf_ready_outcome] then ()
  else raise Fail "raw_call allocation exports have kernel hypotheses";
