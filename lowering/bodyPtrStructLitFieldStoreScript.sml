(* Counted ADD/MSTORE field boundary with compiler linkage and frame facts.
   This does not assert initialization outside the written word. *)
Theory bodyPtrStructLitFieldStore
Ancestors
  wordLoadStorePtr
  fragGasSeqPtr fragGasPathPtr fragExecPtr typedCopyPtr
  ptrSafeRun ptrDiscipline bodyPtrDefs venomExecSemantics venomInstProofs
  venomInst venomState contextCodegenRel finite_map robustCopyTransportPtr
  valueEncodingProps pred_set typedCopyLoopHeaderPtr emitHelperProps
  exprLoweringProps context compileEnv loweringStateRelDefs emitHelper fragExec

Theorem covered_word_store_counted:
  !D ctx fn PG G tn s bb id dst value a w.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
    ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
      (OK ((mstore (w2n a) w s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
     OK (mstore (w2n a) w s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  `step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
     (mstore (w2n a) w s) = G` by
    metis_tac[mstore_ghost_frame] >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
     (step_taint (mk_inst id MSTORE [Var dst; value] []) s
       (mstore (w2n a) w s) tn)
     (OK (mstore (w2n a) w s with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `~(mstore (w2n a) w s with
       vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[mstore_def] >>
  drule (cj 1 gas_path_ptr_rules) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_0]
QED

Theorem clean_add_counted:
  !D ctx fn PG G tn s bb id left right out a b.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [left; right] [out]) /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx /\ eval_operand left s = SOME a /\
    eval_operand right s = SOME b ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id ADD [left; right] [out])
        (update_var out (a+b) s))
      (step_taint (mk_inst id ADD [left; right] [out]) s
        (update_var out (a+b) s) tn)
      (OK (update_var out (a+b) s with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id ADD [left; right] [out]) s =
     OK (update_var out (a+b) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id ADD [left; right] [out]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst id ADD [left; right] [out])
       (update_var out (a+b) s))
     (step_taint (mk_inst id ADD [left; right] [out]) s
       (update_var out (a+b) s) tn)
     (OK (update_var out (a+b) s with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `~(update_var out (a+b) s with
       vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  drule (cj 1 gas_path_ptr_rules) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_0]
QED

Theorem field_add_store_counted:
  !D ctx fn PG G tn s bb id buf off dst value a s1 G1 tn1 w.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [buf; Lit (n2w off)] [dst]) /\
    eval_operand buf s = SOME a /\ op_taint tn buf = {} /\
    s1 = (update_var dst (a+n2w off) s with
            vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst id ADD [buf; Lit (n2w off)] [dst])
           (update_var dst (a+n2w off) s) /\
    tn1 = step_taint (mk_inst id ADD [buf; Lit (n2w off)] [dst]) s
            (update_var dst (a+n2w off) s) tn /\
    get_instruction bb s1.vs_inst_idx =
      SOME (mk_inst (id+1) MSTORE [Var dst; value] []) /\
    ptr_covers G1 tn1 dst s1 32 /\
    op_taint tn1 value = {} /\ eval_operand value s1 = SOME w ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1
      (step_taint (mk_inst (id+1) MSTORE [Var dst; value] []) s1
        (mstore (w2n (a+n2w off)) w s1) tn1)
      (OK (mstore (w2n (a+n2w off)) w s1 with
            vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (gvs[] >> irule clean_add_counted >>
     simp[op_taint_def, eval_operand_def] >> metis_tac[]) >>
  `~s1.vs_halted /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   lookup_var dst s1 = SOME (a+n2w off)` by
    simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G1
     (step_taint (mk_inst (id+1) MSTORE [Var dst; value] []) s1
       (mstore (w2n (a+n2w off)) w s1) tn1)
     (OK (mstore (w2n (a+n2w off)) w s1 with
           vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule covered_word_store_counted >> gvs[] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem word_store_ghost_kept:
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
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  gvs[ghost_kept_def, op_taint_def] >> metis_tac[]
QED

Theorem field_add_ghost_kept:
  !cenv es sa G0 tn0 s0 PG G tn s id left right out w.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    ~not_fresh_at sa out ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id ADD [left; right] [out])
        (update_var out w s))
      (step_taint (mk_inst id ADD [left; right] [out]) s
        (update_var out w s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ghost_kept_def] >>
  metis_tac[copy_len_binop_ghost_frame]
QED

Theorem word_store_robust_exterior:
  !tv v p off w s tn.
    val_wf tv v /\
    (p + val_footprint tv v <= off \/ off + 32 <= p) /\
    (!m. mem_agree_outside tn s.vs_memory m ==>
         val_in_memory tv v p m) ==>
    !m. mem_agree_outside
          (tn DIFF {i | off <= i /\ i < off + 32})
          (mstore off w s).vs_memory m ==>
        val_in_memory tv v p m
Proof
  rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore off w s).vs_memory`,
    `tn`, `tn DIFF {i | off <= i /\ i < off + 32}`,
    `{i | off <= i /\ i < off + 32}`] >>
  simp[] >>
  rpt strip_tac >>
  mp_tac mstore_memory_frame >>
  disch_then (qspecl_then [`s`, `off`, `w`] mp_tac) >>
  simp[mem_agree_outside_def] >> metis_tac[]
QED

Theorem field_word_offset_counted:
  !D ctx fn PG G tn s bb id root off dst value a total s1 G1 tn1 w.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var root; Lit (n2w off)] [dst]) /\
    lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
    ptr_covers G tn root s total /\ off < total /\ off + 32 <= total /\
    w2n a + off < dimword(:256) /\ root <> dst /\
    s1 = (update_var dst (a+n2w off) s with
            vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [dst])
           (update_var dst (a+n2w off) s) /\
    tn1 = step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [dst]) s
            (update_var dst (a+n2w off) s) tn /\
    get_instruction bb s1.vs_inst_idx =
      SOME (mk_inst (id+1) MSTORE [Var dst; value] []) /\
    op_taint tn1 value = {} /\ eval_operand value s1 = SOME w ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1
      (step_taint (mk_inst (id+1) MSTORE [Var dst; value] []) s1
        (mstore (w2n (a+n2w off)) w s1) tn1)
      (OK (mstore (w2n (a+n2w off)) w s1 with
            vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  irule field_add_store_counted >>
  simp[eval_operand_def] >>
  `ptr_covers G1 tn1 dst (update_var dst (a+n2w off) s) 32` by
    (gvs[] >> irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def] >>
     rename1 `ptr_covers G tn root s cap` >> qexists_tac `cap` >> simp[]) >>
  conj_tac >- (qexists_tac `Var root` >> gvs[eval_operand_def]) >>
  gvs[ptr_covers_def, lookup_var_def, update_var_def, eval_operand_def]
QED

(* This is compile_store_memory, not the typed variant (which loads src). *)
Theorem field_word_emitted_code:
  !cenv buf off value ty src_ty sa sm sb dst.
    emit_op ADD [buf; Lit (n2w off)] sa = (Var dst,sm) /\
    is_word_type ty /\
    compile_store_memory cenv value (Var dst) ty src_ty sm = ((),sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ADD [buf; Lit (n2w off)] [dst];
       mk_inst (sa.cs_next_id+1) MSTORE [Var dst; value] []] /\
    ~not_fresh_at sa dst
Proof
  rpt gen_tac >> simp[compile_store_memory_def] >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      not_fresh_at_def]
QED

Theorem field_word_emitted_instructions:
  !cenv buf off value ty src_ty sa sm sb dst fn.
    emit_op ADD [buf; Lit (n2w off)] sa = (Var dst,sm) /\
    is_word_type ty /\
    compile_store_memory cenv value (Var dst) ty src_ty sm = ((),sb) /\
    fn_has_code sa sb fn ==>
    ~not_fresh_at sa dst /\
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH sa.cs_current_insts) =
        SOME (mk_inst sa.cs_next_id ADD [buf; Lit (n2w off)] [dst]) /\
      get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
        SOME (mk_inst (sa.cs_next_id+1) MSTORE [Var dst; value] [])
Proof
  rpt gen_tac >> strip_tac >>
  drule_all field_word_emitted_code >> strip_tac >> simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

Theorem field_word_emitted_counted:
  !D ctx fn PG G tn s cenv root off value ty src_ty sa sm sb dst
    a total s1 G1 tn1 w.
    emit_op ADD [Var root; Lit (n2w off)] sa = (Var dst,sm) /\
    is_word_type ty /\
    compile_store_memory cenv value (Var dst) ty src_ty sm = ((),sb) /\
    fn_has_code sa sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
    ptr_covers G tn root s total /\ off < total /\ off + 32 <= total /\
    w2n a + off < dimword(:256) /\ not_fresh_at sa root /\
    s1 = (update_var dst (a+n2w off) s with
            vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G
      (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [dst])
      (update_var dst (a+n2w off) s) /\
    tn1 = step_taint
      (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [dst]) s
      (update_var dst (a+n2w off) s) tn /\
    op_taint tn1 value = {} /\ eval_operand value s1 = SOME w ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1
      (step_taint (mk_inst (sa.cs_next_id+1) MSTORE [Var dst; value] []) s1
        (mstore (w2n (a+n2w off)) w s1) tn1)
      (OK (mstore (w2n (a+n2w off)) w s1 with
            vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all field_word_emitted_instructions >> strip_tac >>
  `root <> dst` by metis_tac[] >>
  irule field_word_offset_counted >>
  simp[] >> qexistsl_tac [`root`, `total'`] >> gvs[]
QED
