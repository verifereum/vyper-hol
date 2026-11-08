(* Shared clean-store boundaries for folded and runtime selector buffers. *)
Theory bodyPtrEnvBuiltinsSelectorBuffer
Ancestors bodyPtrEnvBuiltinsAllocation bodyPtrEnvBuiltinsEdges
  bodyPtrEnvBuiltinsBoundary typedCopyPtr
  robustCopyTransportPtr bodyPtrDefs exprSimProps exprLoweringProps compileEnv
  ptrDiscipline venomState venomExecSemantics finite_map pred_set
  valueEncoding valueEncodingProps valueEncodingProofs list rich_list
  fragExecPtr fragGasSeqPtr fragGasPathPtr venomInst vyperValue vfmConstants

Theorem mstore_local_robust:
  !fn cenv scopes s name entry p sz a w tv tn tn'.
    local_ptrs_rel fn cenv scopes s /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    (w2n w + sz <= a \/ a + 32 <= w2n w) /\
    tn' = tn DIFF {i | a <= i /\ i < a + 32} /\
    (!m. mem_agree_outside tn s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m) ==>
    !m. mem_agree_outside tn' (mstore a tv s).vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[val_footprint_le] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore a tv s).vs_memory`, `tn`, `tn'`,
    `{i | a <= i /\ i < a + 32}`] >> simp[] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem ghost_inv_mstore_clean:
  !d fn cenv cx es G tn s a v tn'.
    ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
       b + sz <= a \/ a + 32 <= b) /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = tn.t_mem DIFF {i | a <= i /\ i < a + 32} ==>
    ghost_inv d cenv cx es G tn' (mstore a v s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_def] >> strip_tac >> conj_tac
  >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def,
        op_taint_def, lookup_var_def, mstore_def] >> metis_tac[]) >>
  gvs[op_taint_def, stor_taint_ok_def, mstore_def]
QED

Resume ghost_inv_mstore_clean[locals]:
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by fs[lookup_var_def, mstore_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n w + sz <= a \/ a + 32 <= w2n w` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  drule mstore_local_robust >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise ghost_inv_mstore_clean

Theorem mstore_counted_edge:
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst; value] []) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s = OK (mstore (w2n a) w s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> gvs[mk_inst_def]
QED

(* The operand may be a literal or a runtime hash shifted into the high bytes. *)
Theorem selector_buffer_memory:
  !s a w bs.
    LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs ==>
    val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) a
      (mstore (a+32) w (mstore a 4w s)).vs_memory
Proof
  rpt strip_tac >> simp[val_in_memory_def, mstore_mem_word_at_disjoint,
    mstore_mem_word_at_same] >>
  `mem_bytes_at (a+32) 4
     (mstore (a+32) w (mstore a 4w s)).vs_memory =
   TAKE 4 (mem_bytes_at (a+32) 32
     (mstore (a+32) w (mstore a 4w s)).vs_memory)` by
    (irule LIST_EQ >> simp[EL_TAKE, EL_mem_bytes_at]) >>
  gvs[mem_bytes_at_mstore_same]
QED

Theorem clean_memory_window:
  !tn mem mem' a n.
    mem_agree_outside tn mem mem' /\
    (!i. a <= i /\ i < a+n ==> i NOTIN tn) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < n` >>
  `a+j NOTIN tn` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+j) 1 mem = mem_bytes_at (a+j) 1 mem'` by
    (fs[mem_agree_outside_def] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem selector_buffer_robust:
  !s a w bs tn.
    LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs /\
    (!i. a <= i /\ i < a+64 ==> i NOTIN tn) ==>
    !mem. mem_agree_outside tn
      (mstore (a+32) w (mstore a 4w s)).vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) a mem
Proof
  rpt gen_tac >> strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) a
    (mstore (a+32) w (mstore a 4w s)).vs_memory` by
    (irule selector_buffer_memory >> simp[]) >>
  rpt strip_tac >>
  `mem_bytes_at a 32 mem =
    mem_bytes_at a 32 (mstore (a+32) w (mstore a 4w s)).vs_memory` by
    (irule clean_memory_window >> qexists_tac `tn` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+32) 4 mem =
    mem_bytes_at (a+32) 4 (mstore (a+32) w (mstore a 4w s)).vs_memory` by
    (irule clean_memory_window >> qexists_tac `tn` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[val_in_memory_def, mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem mstore_imm_taint:
  !id dst value s s' tn.
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s s' tn).t_imm =
    tn.t_imm
Proof
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem mstore_ghost_kept:
  !cenv es sa G0 tn0 s0 PG G tn s id dst value a w.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  irule ghost_kept_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
  simp[op_taint_def, SUBSET_DEF]
QED

Theorem mstore_step_ghost_inv:
  !d fn cenv cx es PG G tn s id dst value a w.
    ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      b+sz <= w2n a \/ w2n a+32 <= b) /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn) (mstore (w2n a) w s)
Proof
  rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  simp[] >> irule ghost_inv_mstore_clean >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `tn` >> simp[mstore_imm_taint]
QED

Theorem selector_buffer_ptr_val:
  !cx G tn s p a bs.
    LENGTH bs = 4 /\ lookup_var p s = SOME a /\ ptr_covers G tn p s 64 /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n a) mem) ==>
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) (Var p) G tn s
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def, eval_operand_def,
    evaluate_type_def, is_word_type_def, val_store_size_def, word_size_def] >>
  metis_tac[]
QED

Theorem selector_buffer_ptr_buf:
  !cenv args G tn s p.
    ptr_covers G tn p s 64 ==>
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
      (Var p) G s
Proof
  simp[ptr_buf_ok_def, method_id_dynamic_result_capacity, ptr_covers_def,
    eval_operand_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
