Theory abiEncodePtrEmptySetupAllocate
Ancestors bodyPtrDefs abiBuiltinEncodeAllocate bodyPtrHashBuiltinsAllocFrame
  bodyPtrPrecompileBuiltinsAllocationTransport bodyPtrPrecompileBuiltinsAllocationFrame
  bodyPtrIfExpBytesCounted
  bodyPtrHashBuiltinsGhostFrame fragGasSeqPtr ptrDiscipline
  compileEnv emitHelper emitHelperProps loweringHalt exprLoweringProps
  venomState venomInst finite_map words list rich_list arithmetic pred_set

Theorem abi_encode_empty_allocate_ptr:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\
  stmt_state_rel ctx func cenv cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ outsz < dimword (:256) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  ghost_inv rb cenv cx es G tn initial /\ ~ctx_has_dalloca ctx /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  eval_operand src initial = SOME sv /\ op_taint tn src = {} ==>
  ?raw addressed Ga tna x a.
    run_inst_seq (emitted_insts st address_st) initial = OK raw /\
    addressed = raw with vs_inst_idx := LENGTH address_st.cs_current_insts /\
    inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn
      (emitted_insts st address_st) initial Ga tna /\
    FST ops = Var x /\ ptr_covers Ga tna x addressed outsz /\
    eval_operand (FST ops) addressed = SOME a /\
    eval_operand (SND ops) addressed = SOME (a + n2w data_offset) /\
    op_taint tna (FST ops) = {} /\ op_taint tna (SND ops) = {} /\
    eval_operand src addressed = SOME sv /\ op_taint tna src = {} /\
    ghost_inv rb cenv cx es Ga tna addressed /\
    ghost_kept cenv es st G tn initial Ga tna /\
    (!v. not_fresh_at st v ==> lookup_var v addressed = lookup_var v initial /\
      FLOOKUP Ga v = FLOOKUP G v /\ op_taint tna (Var v) = op_taint tn (Var v)) /\
    (?allocated. run_inst_seq [mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)] [x]] initial = OK allocated /\
      tna.t_mem = tn.t_mem UNION new_site_bytes initial allocated) /\
    tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule emitted_allocation_singleton >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)] [p]) initial = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all emitted_allocation_transport >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  suspend "join"
QED

Resume abi_encode_empty_allocate_ptr[join]:
  `G' = G1 /\ tn' = tn1` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `initial.vs_inst_idx` mp_tac) >>
     gvs[inst_seq_ptr_def]) >>
  qpat_x_assum `G' = G1` SUBST_ALL_TAC >>
  qpat_x_assum `tn' = tn1` SUBST_ALL_TAC >>
  `?y. data_ptr = Var y` by
    (drule emitted_insts_emit_op >> strip_tac >> metis_tac[]) >>
  `op_taint tn1 buf.buf_operand = {}` by gvs[ptr_covers_def] >>
  `?Gf tnf sf.
     inst_seq_ptr (cx_dead cx) 0 ctx func PG G1 tn1
       (emitted_insts allocated address_st)
       (t with vs_inst_idx := SUC initial.vs_inst_idx) Gf tnf /\
     run_inst_seq (emitted_insts allocated address_st)
       (t with vs_inst_idx := SUC initial.vs_inst_idx) = OK sf /\
     lookup_var y sf = SOME (w + n2w data_offset) /\
     (sf with vs_vars := (t with vs_inst_idx := SUC initial.vs_inst_idx).vs_vars) = (t with vs_inst_idx := SUC initial.vs_inst_idx) /\
     (!v. not_fresh_at allocated v ==> lookup_var v sf = lookup_var v (t with vs_inst_idx := SUC initial.vs_inst_idx)) /\
     op_taint tnf (Var y) = {} /\
     tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
     (!v. not_fresh_at allocated v ==> FLOOKUP Gf v = FLOOKUP G1 v /\
        op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (irule emit_copy_len_binop_seq_ptr >>
     simp[] >> qexistsl [`buf.buf_operand`, `ADD`, `Lit (n2w data_offset)`] >>
     gvs[eval_operand_def, op_taint_def, lookup_var_def]) >>
  suspend "address_post"
QED

Resume abi_encode_empty_allocate_ptr[address_post]:
  drule emitted_insts_emit_op >> strip_tac >>
  `sf = update_var y (w + n2w data_offset)
       (t with vs_inst_idx := SUC initial.vs_inst_idx)` by
    (qpat_x_assum `run_inst_seq (emitted_insts allocated address_st) _ = _` mp_tac >>
     simp[run_inst_seq_def] >>
     `step_inst_base (mk_inst allocated.cs_next_id ADD
        [buf.buf_operand; Lit (n2w data_offset)] [y])
        (t with vs_inst_idx := SUC initial.vs_inst_idx) =
       OK (update_var y (w + n2w data_offset)
         (t with vs_inst_idx := SUC initial.vs_inst_idx))` by
       (irule copy_len_binop_step >> simp[eval_operand_def] >> gvs[eval_operand_def, lookup_var_def]) >>
     gvs[]) >>
  `tnf = step_taint (mk_inst allocated.cs_next_id ADD
      [buf.buf_operand; Lit (n2w data_offset)] [y])
      (t with vs_inst_idx := SUC initial.vs_inst_idx) sf tn1` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts allocated address_st) _ _ _` mp_tac >>
     gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()]) >>
  `tnf.t_imm = tn1.t_imm` by
    simp[Once step_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def] >>
  suspend "transport"
QED

Resume abi_encode_empty_allocate_ptr[transport]:
  `local_ptrs_reserved cenv allocated` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `ghost_inv rb cenv cx es Gf tnf sf` by
    (irule hash_readonly_ghost_inv >>
     qexistsl [`G1`, `t with vs_inst_idx := SUC initial.vs_inst_idx`, `allocated`, `tn1`] >>
     simp[hash_ghost_inv_inst_idx] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
  `ghost_kept cenv es st G tn initial Gf tnf` by
    (irule hash_ghost_kept_clean_tail >> qexistsl [`G1`, `tn1`] >>
     simp[] >> metis_tac[]) >>
  `!v. not_fresh_at st v ==> lookup_var v sf = lookup_var v initial /\
     FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)` by
    (rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  `t.vs_labels = initial.vs_labels` by
    (qpat_x_assum `step_inst_base _ initial = OK t` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
       venomExecSemanticsTheory.exec_alloca_def] >>
     strip_tac >> gvs[AllCaseEqs(), update_var_def]) >>
  `eval_operand src sf = SOME sv /\ op_taint tnf src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def, update_var_def] >> metis_tac[]) >>
  `ptr_covers Gf tnf p sf outsz /\ eval_operand buf.buf_operand sf = SOME w /\
    op_taint tnf buf.buf_operand = {}` by
    (gvs[ptr_covers_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  suspend "execution"
QED

Resume abi_encode_empty_allocate_ptr[execution]:
  `allocated.cs_current_insts = st.cs_current_insts ++ emitted_insts st allocated` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def]) >>
  `emitted_insts st address_st = emitted_insts st allocated ++ emitted_insts allocated address_st` by
    (irule emitted_insts_append >> simp[]) >>
  `inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn
      (emitted_insts st address_st) initial Gf tnf` by
    (qpat_assum `emitted_insts st address_st = _` (fn th => pure_rewrite_tac [th]) >>
     irule inst_seq_ptr_append_run >>
     conj_tac >- simp[mk_inst_def, is_terminator_def] >>
     qexistsl [`G1`, `t`, `tn1`] >>
     qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `initial.vs_inst_idx` assume_tac) >>
     gvs[ADD1]) >>
  `step_inst_base (mk_inst allocated.cs_next_id ADD
      [buf.buf_operand; Lit (n2w data_offset)] [y]) t =
      OK (update_var y (w + n2w data_offset) t)` by
    (irule copy_len_binop_step >> simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts st address_st) initial =
      OK (update_var y (w + n2w data_offset) t)` by
    (asm_rewrite_tac[] >> drule run_inst_seq_append >>
     disch_then (qspec_then `emitted_insts allocated address_st` mp_tac) >>
     gvs[run_inst_seq_def]) >>
  qexistsl [`update_var y (w + n2w data_offset) t`,
    `sf with vs_inst_idx := LENGTH address_st.cs_current_insts`, `Gf`, `tnf`, `p`, `w`] >>
  gvs[update_var_def, hash_ghost_inv_inst_idx, eval_operand_def, lookup_var_def,
    ptr_covers_def] >>
  qexists_tac `t` >> simp[]
QED

Finalise abi_encode_empty_allocate_ptr
