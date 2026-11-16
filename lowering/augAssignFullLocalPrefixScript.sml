(* Joint local AugAssign read prefix; endpoints precede the horizon. *)
Theory augAssignFullLocalPrefix
Ancestors
  augAssignFullSourcePrefix augAssignFullStateFrame augAssignFullHistory
  typedCopyOriginPtrBase exprPtrCtorImmStore decoderSetupStepPtr
  wordLoadStorePtr stmtSimAugAssign bodyFullPreds bodyMemoryDefs bodyPtrDefs
  vyperTyping vyperTypeSystem exprSimHypsDefs exprSimProps
  emitHelperProps exprLoweringProps ptrSafetyTransport
  codegenRel contextCodegenRel unitTransformDefs instMemFrontier memSafeRun venomExecSemantics venomInst venomState
  compileEnv loweringStateRelDefs finite_map list pred_set

Theorem augassign_local_source_prefix_full:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx (NameTarget name) s0 = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_full_ok cx e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty (NameTarget name) bop e) = SOME env' ==>
  body_expr_full_ok cx e /\
  FLOOKUP env.var_types name = SOME ty /\
  augassign_operand_ok ty bop e /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  ?p sz entry.
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_scopes name es.scopes = SOME entry /\
    (!gs. eval_target_place cx (NameTarget name) (es with gas_obs := gs) =
       (INL (MemoryPlace name []),es with gas_obs := gs) /\
      read_place cx (MemoryPlace name []) (es with gas_obs := gs) =
       (INL entry.value,es with gas_obs := gs) /\
      place_type_value cx (MemoryPlace name []) (es with gas_obs := gs) =
       (INL entry.type,es with gas_obs := gs))
Proof
  strip_tac >>
  `FLOOKUP env.var_types name = SOME ty /\ augassign_operand_ok ty bop e /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         DISJ_IMP_THM, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types name` >>
     Cases_on `FLOOKUP env.var_assignable name` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable name = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >> metis_tac[eval_target_place_local]) >>
  simp[] >>
  gen_tac >> irule eval_target_place_local >> simp[]
QED

Theorem augassign_local_prefix_full:
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget name) bop e) sa = (c,sf) /\
  lookup_scopes name es.scopes = SOME entry /\
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME aw /\
  w2n aw + 32 <= s.vs_alloca_next /\ allocas_from lo s /\
  (!i. w2n aw <= i /\ i < w2n aw + 32 ==> i NOTIN tn.t_mem) /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\ alloca_inv s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t G' tn'.
    t = update_var out (mload (w2n aw) s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!gs. eval_target_place cx (NameTarget name) (es with gas_obs := gs) =
       (INL (MemoryPlace name []),es with gas_obs := gs) /\
      read_place cx (MemoryPlace name []) (es with gas_obs := gs) =
       (INL entry.value,es with gas_obs := gs) /\
      place_type_value cx (MemoryPlace name []) (es with gas_obs := gs) =
       (INL entry.type,es with gas_obs := gs)) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand (Var out) t = SOME (mload (w2n aw) s) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
      return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
      local_ptrs_reserved cenv sb) /\
    ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var out (mload (w2n aw) s)
    (s with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  qabbrev_tac `G' = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out])
    (update_var out (mload (w2n aw) s) s)` >>
  qabbrev_tac `tn' = step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s
    (update_var out (mload (w2n aw) s) s) tn` >>
  `!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     mp_tac (Q.INST [`D` |-> `DF (H:(bool # bytes32 # type_value) list # num list)`, `opc` |-> `MLOAD`, `args` |-> `[Var p]`,
       `a` |-> `sa`, `op` |-> `Var out`, `b` |-> `sb`,
       `w` |-> `mload (w2n (aw:bytes32)) s`, `off` |-> `0`, `len` |-> `0`]
       typed_copy_origin_ptr_emit_op_path) >>
     impl_tac
     >- (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
              eval_operand_def, inst_mem_below_frontier_def,
              inst_dload_in_section_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, is_terminator_def] >>
         rewrite_tac[GSYM mk_inst_def] >> gen_tac >>
         irule ptr_inst_ok_mload_lo >> simp[]) >>
     strip_tac >> gvs[Abbr `t`, Abbr `G'`, Abbr `tn'`,
                         update_var_def, arithmeticTheory.ADD1]) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
   tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x))` by
    (qpat_assum `G' = _` SUBST1_TAC >> qpat_assum `tn' = _` SUBST1_TAC >>
     drule setup_mload_ghost >> simp[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> rpt conj_tac
  >- (gen_tac >> irule eval_target_place_local >> simp[])
  >- (drule emit_op_same_blocks >> simp[same_blocks_def])
  >- (drule augassign_emit_word_history >>
      disch_then (qspecl_then [`mload (w2n aw) s`, `s`, `func`] mp_tac) >>
      simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
           eval_operand_def, update_var_def, is_terminator_def])
  >- (gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      irule augassign_exterior_state_frame >> goal_assum (drule_at Any) >>
      simp[update_var_def] >> qexists_tac `LENGTH sb.cs_current_insts` >> simp[] >>
      qexists_tac `sa` >> gvs[update_var_def]) >>
  gvs[ghost_kept_at_def, update_var_def] >> metis_tac[]
QED
