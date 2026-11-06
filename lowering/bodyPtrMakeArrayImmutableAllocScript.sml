(* Allocation and counted immutable copying meet at an actual advanced cursor. *)
Theory bodyPtrMakeArrayImmutableAlloc
Ancestors
  bodyPtrMakeArrayAllocBuffer bodyPtrMakeArrayImmutableResult exprSimCopy
  exprSimProps exprLoweringProps ptrDiscipline bodyPtrDefs venomState venomInst
  context compileEnv finite_map arithmetic list rich_list freshWrites
  instIdxIndep fragGasSeqAbort fragGasPathPtr

Theorem alloc_buffer_copy_start:
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?u root w G1 tn1.
    buf.buf_operand = Var root /\ not_fresh_at sm root /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand src u = SOME a /\ lookup_var root u = SOME w /\
    op_taint tn1 src = {} /\ allocas_from 0 u /\
    ptr_covers G1 tn1 root u sz /\
    FLOOKUP G1 root = SOME (w2n w,sz) /\ w2n w+sz < dimword (:256) /\
    ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = SUC s.vs_inst_idx /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP G1 p = FLOOKUP G p /\
      op_taint tn1 (Var p) = op_taint tn (Var p)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u)
Proof
  strip_tac >> drule_all literal_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule alloc_buffer_emitted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [inst]` >>
  `step_inst_base inst s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `!p. not_fresh_at sa p ==> p <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[alloc_buffer_root_fresh] >>
  `?b. b+sz < dimword (:256) /\
     step_prov PG G inst u = G |+ (STRING #"%" (toString sa.cs_next_var),(b,sz)) /\
     lookup_var (STRING #"%" (toString sa.cs_next_var)) u = SOME (n2w b)` by
    (simp[Abbr `inst`] >> irule literal_alloca_root_bound >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
   u.vs_labels = s.vs_labels /\
   u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
   u.vs_fmp = s.vs_fmp /\ u.vs_memory = s.vs_memory /\
   (!p. p <> STRING #"%" (toString sa.cs_next_var) ==> lookup_var p u = lookup_var p s)` by
    (qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
     simp[Abbr `inst`] >> strip_tac >>
     drule_then strip_assume_tac literal_alloca_static_frame >>
     simp[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
   (!p. p <> STRING #"%" (toString sa.cs_next_var) ==>
     FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `inst`] >> drule_all literal_alloca_old_ghost >>
     disch_then (qspecl_then [`tn`, `PG`, `G`] mp_tac) >> simp[]) >>
  `eval_operand src u = SOME a /\ op_taint tn1 src = {}` by
    (Cases_on `src`
     >- gvs[eval_operand_def, op_taint_def]
     >- (gvs[copy_old_operand_def, eval_operand_def] >>
         rename1 `lookup_var x s = SOME a` >>
         `x <> STRING #"%" (toString sa.cs_next_var)` by
           (strip_tac >> gvs[]) >> simp[])
     >> gvs[eval_operand_def, op_taint_def]) >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `p`, `w`, `G1`, `tn1`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, eval_op_inst_idx, allocas_from_def] >>
  `b < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem alloc_buffer_installed_split:
  compile_alloc_buffer sz sa = (buf,sm) /\
  isPREFIX (emitted_insts sa sm ++ code) (DROP k bb.bb_instructions) ==>
  isPREFIX (emitted_insts sa sm) (DROP k bb.bb_instructions) /\
  isPREFIX code (DROP (SUC k) bb.bb_instructions)
Proof
  strip_tac >> drule alloc_buffer_emitted >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  pure_asm_rewrite_tac[APPEND] >> disch_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> Cases_on `DROP k bb.bb_instructions` >> gvs[]
QED

Theorem immutable_allocated_buffer_ptr_path:
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand (type_slot_size tv) 0 sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ type_memory_size tv < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\ op_taint tn src = {} /\
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  ?u root w G1 tn1 z Gf tnf.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (OK (z with vs_inst_idx := SUC s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    copy_runtime_frame sm u sb z /\
    val_wf tv v /\ val_footprint tv v <= type_memory_size tv /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    lookup_var root z = SOME w /\ ptr_covers Gf tnf root z (type_memory_size tv) /\
    FLOOKUP Gf root = SOME (w2n w,type_memory_size tv) /\
    w2n w + type_memory_size tv < dimword (:256) /\
    z.vs_data_section = s.vs_data_section /\ z.vs_immutables = s.vs_immutables /\
    tnf.t_mem SUBSET tn1.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p z = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u)
Proof
  strip_tac >> drule_all alloc_buffer_installed_split >> strip_tac >>
  drule_all alloc_buffer_copy_start >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size tv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >> gvs[ci_mono_def]) >>
  `copy_old_operand sm src /\ copy_old_operand sm (Var root)` by
    (conj_tac >- (irule copy_old_operand_mono >> metis_tac[]) >>
     fs[copy_old_operand_def]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `immutable_holds cenv cx t (Value v) a es u` by
    metis_tac[immutable_holds_memory_cong] >>
  `w2n w + type_memory_size tv <= dimword (:256)` by decide_tac >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac[] >> disch_tac >>
  drule_all immutable_runtime_buffer_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
     (OK (z with vs_inst_idx := SUC s.vs_inst_idx + LENGTH (emitted_insts sm sb)))` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  `lookup_var root z = SOME w /\
   FLOOKUP Gf root = SOME (w2n w,type_memory_size tv)` by simp[] >>
  qexistsl_tac [`u`, `root`, `w`, `G1`, `tn1`, `z`, `Gf`, `tnf`] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm p` by (irule not_fresh_at_mono >> metis_tac[]) >>
  metis_tac[]
QED
