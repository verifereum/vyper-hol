(* Caller boundary for aggregate Append scratch staging. *)
Theory appendAggregateStagePtr
Ancestors bodyAppendStorageAdapter bodyExprPreFacts supportedExprs
  appendAggregateAllocationPtr appendAggregateLayout
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsGhostCompose
  annAssignPtrDestinationFrame bodyPtrDefs bodyPtrCallCalldata exprLoweringProps exprOperandVar
  exprSimHyps exprSimHypsDefs bodySim loweringPosts compileEnv
  supportedTypes valueEncodingProps vyperTyping loweringStateRelDefs
  exprSimSource memoryLocalRhsProps bodySimStmtCases
  annAssignPtrStage context emitHelper emitHelperProps fragExec venomState venomInst finite_map arithmetic

Theorem append_aggregate_stage_ptr:
  !tops ctx func PG cenv cx env es es' gs e elem tvd sa sb sc sd tmp raw
    s0 s G0 tn0 G tn d v.
    stmt_state_rel ctx func cenv cx es s0 /\
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_pure_expr tops e /\
    supported_storage_type tops elem /\ expr_type e = elem /\
    ~is_word_type elem /\ ~is_bytestring_type elem /\
    evaluate_type (get_tenv cx) elem = SOME tvd /\
    0 < type_memory_bytes cenv elem /\ type_memory_bytes cenv elem < 2 ** 64 /\
    lower_value compile_expr cenv elem e sa = (raw,sb) /\
    compile_alloc_buffer (type_memory_bytes cenv elem) sb = (tmp,sc) /\
    compile_store_memory cenv raw tmp.buf_operand elem (lowered_value_type cenv e) sc = ((),sd) /\
    expr_post ctx func cenv cx e es sa sb s0 es' v raw s /\
    (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,es') /\
    ptr_val_ok cx (expr_type e) v raw G tn s /\ ptr_buf_ok cenv e raw G s /\
    ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
    fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?Gf tnf sf w p.
      tmp.buf_operand = Var p /\
      gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
      ~sf.vs_halted /\ sf.vs_current_bb = sd.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sd.cs_current_insts /\
      stmt_state_rel ctx func cenv cx es' sf /\ ghost_inv d cenv cx es' Gf tnf sf /\
      ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\
      lookup_var p sf = SOME w /\ ptr_covers Gf tnf p sf (type_memory_bytes cenv elem) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory tvd v (w2n w) m) /\
      (!i. ~(w2n w <= i /\ i < w2n w + type_memory_bytes cenv elem) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!q. not_fresh_at sb q ==> lookup_var q sf = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[]) >>
  qabbrev_tac `p = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `pre = sb with cs_next_var := sb.cs_next_var + 1` >>
  `tmp.buf_operand = Var p /\
   emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv elem))] [p] pre = ((),sc)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def, Abbr `p`, Abbr `pre`] >>
     strip_tac >> gvs[]) >>
  `~not_fresh_at sb p /\ not_local_ptr cenv es'.scopes p` by
    (simp[not_fresh_at_def, Abbr `p`] >>
     metis_tac[local_ptrs_reserved_fresh, LESS_EQ_REFL]) >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\
   sc.cs_next_id <= sd.cs_next_id` by
    (mp_tac (Q.SPECL [`cenv`,`raw`,`tmp.buf_operand`,`elem`,
       `lowered_value_type cenv e`,`sc`] ci_mono_compile_store_memory) >>
     simp[ci_mono_def]) >>
  `cs_extends sb pre` by
    simp[cs_extends_def, Abbr `pre`] >>
  `cs_extends pre sc` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sa pre /\ cs_extends sc sd` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code pre sc func /\ fn_has_code sc sd func` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `MEM (mk_inst pre.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv elem))] [p]) (fn_insts func)` by
    (irule (Q.SPECL [`sa`,`sc`,`sd`] fn_has_code_current_inst) >>
     simp[] >> qexistsl_tac [`sa`,`sc`,`sd`] >>
     reverse conj_tac >- metis_tac[cs_extends_trans] >>
     qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
          comp_return_def, comp_ignore_bind_def] >>
     strip_tac >> gvs[]) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `lowered_value_type cenv e = elem` by
    metis_tac[append_aggregate_lowered_type] >>
  `post_value_type cenv e = expr_type e` by
        (irule post_value_type_lowered >> simp[]) >>
      `ptr_val_ok cx elem v raw G tn s` by metis_tac[] >>
      `type_memory_bytes cenv elem < dimword (:256)` by
        (fs[wordsTheory.dimword_def] >> decide_tac) >>
      drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
        annassign_rhs_stage_input_ptr >>
      disch_then (qspecl_then [`G`,`tn`,`p`,`tvd`,`type_memory_bytes cenv elem`] mp_tac) >>
      simp[] >> strip_tac >>
      `stmt_state_rel ctx func cenv cx es' s` by
        fs[expr_post_def] >>
      `~not_fresh_at sa p` by
        (spose_not_then assume_tac >>
         fs[not_fresh_at_def, Abbr `p`] >> decide_tac) >>
      `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> p) /\
       (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> p)` by
        metis_tac[] >>
      `s.vs_current_bb = pre.cs_current_bb /\
       s.vs_inst_idx = LENGTH pre.cs_current_insts` by simp[Abbr `pre`] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) append_aggregate_allocation_ptr >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (qspecl_then [`sa`,`PG`,`tvd`,`a`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      `sb.cs_next_var <= sc.cs_next_var` by
        (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
         simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
              comp_return_def, comp_ignore_bind_def, Abbr `pre`] >>
         strip_tac >> gvs[]) >>
      `local_ptrs_reserved cenv sc` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[]) >>
      `not_fresh_at sb src` by metis_tac[compile_lower_value_var] >>
      `sb.cs_next_var < sc.cs_next_var` by
        (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
         simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
              comp_return_def, comp_ignore_bind_def, Abbr `pre`] >>
         strip_tac >> gvs[]) >>
      `(!q. not_fresh_at sb q ==> not_fresh_at sc q) /\
       not_fresh_at sc p /\ not_fresh_at sc src` by
        (fs[not_fresh_at_def, Abbr `p`] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
      `(!n lo sz. local_region cenv es'.scopes s n lo sz ==>
          local_region cenv es'.scopes s1 n lo sz)` by
        (fs[local_region_def, not_local_ptr_def] >> metis_tac[]) >>
      `compile_store_memory cenv (Var src) (Var p) elem elem sc = ((),sd)` by
        metis_tac[] >>
      drule_at (Pat `compile_store_memory _ (Var _) (Var _) _ _ _ = _`)
        annassign_allocated_store_memory_path_ptr >>
      disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `lookup_var src s1 = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var p s1 = SOME _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ src s1 _`)) >>
      disch_then (drule_at (Pat `val_wf _ _`)) >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s1`)) >>
      disch_then (qspecl_then [`PG`,`0`,
        `mk_inst pre.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv elem))] [p]`,
        `type_memory_bytes cenv elem`] mp_tac) >>
      (impl_tac >- (simp[mk_inst_def, Abbr `pre`] >>
        conj_tac >- metis_tac[exprSimPropsTheory.val_footprint_le,
                              expr_sim_inv_memory_size] >>
        fs[local_ptrs_reserved_def, not_fresh_at_def] >>
        metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_TRANS])) >>
      strip_tac >>
      `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf)` by
        metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_CLAUSES] >>
      `lookup_var p sf = SOME w /\
       ptr_covers Gf tnf p sf (type_memory_bytes cenv elem)` by
        metis_tac[annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr] >>
      `FLOOKUP u.vs_allocas pre.cs_next_id =
         SOME (w2n w,type_memory_bytes cenv elem)` by fs[] >>
      drule_all hash_alloca_exterior_effects >>
      disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
      `(!i. ~(w2n w <= i /\ i < w2n w + type_memory_bytes cenv elem) ==>
          mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
       (!q. not_fresh_at sb q ==> lookup_var q sf = lookup_var q s /\
          FLOOKUP Gf q = FLOOKUP G q /\
          op_taint tnf (Var q) = op_taint tn (Var q))` by
        (conj_tac >- metis_tac[] >> rpt strip_tac >>
         `q <> p` by metis_tac[] >> metis_tac[]) >>
      `local_ptrs_rel func cenv es.scopes s0` by
        fs[stmt_state_rel_def, state_rel_def] >>
      `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
        fs[expr_post_def, locals_kept_def] >>
      `!n b sz. local_region cenv es'.scopes s n b sz <=>
                 local_region cenv es.scopes s0 n b sz` by
        metis_tac[hash_expr_post_local_regions] >>
      `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
        (irule hash_ghost_kept_compose >>
         first_assum (irule_at (Pat `ghost_kept _ es sa _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `ghost_kept _ es' sa _ _ _ _ _`)) >>
         simp[] >> fs[expr_post_def]) >>
      qexistsl_tac [`Gf`,`tnf`,`sf`,`w`] >> simp[]
QED
