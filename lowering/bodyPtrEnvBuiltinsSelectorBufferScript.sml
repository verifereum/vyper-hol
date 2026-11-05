(* Shared clean-store boundaries for folded and runtime selector buffers. *)
Theory bodyPtrEnvBuiltinsSelectorBuffer
Ancestors bodyPtrEnvBuiltinsAllocation bodyPtrEnvBuiltinsEdges typedCopyPtr
  robustCopyTransportPtr bodyPtrDefs exprSimProps exprLoweringProps compileEnv
  ptrDiscipline venomState venomExecSemantics finite_map pred_set
  valueEncodingProps fragExecPtr fragGasSeqPtr fragGasPathPtr venomInst

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
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> gvs[mk_inst_def]
QED
