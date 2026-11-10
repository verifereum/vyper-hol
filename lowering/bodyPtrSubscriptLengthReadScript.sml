(* Counted rereading of the current dynamic-array header. *)
Theory bodyPtrSubscriptLengthRead
Ancestors
  wordLoadStorePtr
  bodyPtrSubscriptIndexExecution typedCopyPtr typedCopyLayoutPtr
  representationCleanPtr fragGasSeqPtr emitHelperProps exprSimMemoryPath
  fragExec ptrCoverage venomInstProofs venomExecSemantics
  valueEncodingProps venomState venomInst fragGasPathPtr
  emitHelper compileEnv loweringStateRelDefs ptrDiscipline ptrSafeRun finite_map bodyPtrDefs
  gasSummaryComposePtr loweringPosts bodyPtrSubscriptBounds
  bodyPtrSubscriptNamedTuplePostBoundary exprLoweringProps

Theorem mload_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var p] [out]) /\
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME w ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var p] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst id MLOAD [Var p] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst id MLOAD [Var p] [out]) s`
    by (irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base (mk_inst id MLOAD [Var p] [out]) s =
    OK (update_var out (mload (w2n w) s) s)`
    by simp[step_MLOAD, eval_operand_def] >>
  `(mk_inst id MLOAD [Var p] [out]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id MLOAD [Var p] [out]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `~(update_var out (mload (w2n w) s) s with
      vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  metis_tac[cj 1 gas_path_ptr_rules, cj 2 gas_path_ptr_rules,
            arithmeticTheory.ADD_CLAUSES]
QED

Theorem emit_mload_counted:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var out sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    ~sf.vs_halted /\ sf.vs_allocas = s.vs_allocas /\ sf.vs_fmp = s.vs_fmp /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_requests = s.vs_requests /\
    tnf.t_imm = tn.t_imm /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (mk_inst sa.cs_next_id MLOAD [Var src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
  `!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
     stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> simp[Abbr `t`] >> irule fresh_add_stmt_state_rel >>
     simp[] >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (unabbrev_all_tac >>
    irule mload_counted_edge >> simp[] >> metis_tac[]) >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `op_prov Gf (Var out) = NONE /\ tnf.t_imm = tn.t_imm` by
    simp[Abbr `Gf`, Abbr `tnf`, op_prov_def, step_prov_def, out_prov_def,
         set_prov_def, FLOOKUP_DRESTRICT, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_dynarray_length_counted:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ lookup_var src s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var out sf = SOME (n2w (LENGTH vs)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    ~sf.vs_halted /\ sf.vs_allocas = s.vs_allocas /\ sf.vs_fmp = s.vs_fmp /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_requests = s.vs_requests /\
    tnf.t_imm = tn.t_imm /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  drule dynarray_in_memory_robust_length >> strip_tac >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem`
    by (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all emit_mload_counted >> simp[]
QED

Theorem expr_sim_ptr_local_length_continuation:
  expr_sim_ptr d ctx PG func cenv cx ty idx es /\
  lower_value compile_expr cenv ty idx sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (eval_expr cx idx) (read_result cx)) (es, s0, G0, tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx idx es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv idx) v op G tn t /\
      (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      (!name p sz w entry tv cap vs out sc.
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
        lookup_var p s0 = SOME w /\
        lookup_scopes name ee.scopes = SOME entry /\
        entry.type = ArrayTV tv (Dynamic cap) /\
        entry.value = ArrayV (DynArrayV vs) /\
        32 <= sz /\ ~t.vs_halted /\
        emit_op MLOAD [Var p] sb = (Var out,sc) /\ fn_has_code sb sc func ==>
        ?Gf tnf sf.
          gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf (OK sf) /\
          sf.vs_current_bb = sc.cs_current_bb /\
          sf.vs_inst_idx = LENGTH sc.cs_current_insts /\
          lookup_var out sf = SOME (n2w (LENGTH vs)) /\
          op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
          ~sf.vs_halted /\ sf.vs_allocas = t.vs_allocas /\ sf.vs_fmp = t.vs_fmp /\
          sf.vs_accounts = t.vs_accounts /\ sf.vs_transient = t.vs_transient /\
          sf.vs_call_ctx = t.vs_call_ctx /\ sf.vs_requests = t.vs_requests /\
          tnf.t_imm = tn.t_imm /\
          sf.vs_memory = t.vs_memory /\ tnf.t_mem = tn.t_mem /\
          tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
          (!q. not_fresh_at sb q ==>
            lookup_var q sf = lookup_var q t /\
            FLOOKUP Gf q = FLOOKUP G q /\
            op_taint tnf (Var q) = op_taint tn (Var q))))
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all expr_sim_ptr_local_refresh >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name p sz w. _` drule_all >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[] >> drule_all emit_dynarray_length_counted >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
