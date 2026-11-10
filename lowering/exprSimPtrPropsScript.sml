(*
 * Helpers for the pointer twins of the leaf expressions.  The twin of
 * exprSimMemoryStack: a form compile_expr gives as a
 * stack value, whose source evaluation is a value, has its value_vv
 * simulation from its lowered value's.
 *
 * TOP-LEVEL:
 *   expr_stack_outcome_ptr -- the counted path for the lowered value is
 *     the counted path for the value_vv
 *   expr_vv_sim_ptr_stack -- expr_vv_sim_ptr from expr_sim_ptr
 *   ghost_inv_fresh_frame -- ghost_inv survives a step that touches only
 *     fresh variables (and not memory, storage or their taint)
 *   emit_mload_ptr_path -- emit_op MLOAD through a covered pointer at
 *     untainted bytes is a one-step counted path with a clean output
 *)
Theory exprSimPtrProps
Ancestors
  bodyPtrDefs fragGasPathPtr exprSimStack exprSimDefs loweringPosts
  gasExemptCert exprLowering emitHelper compileEnv loweringStateRelDefs vyperInterpreter
  vyperState ptrDiscipline fragGasSeqPtr typedCopyPtr decoderGhostFramePtr
  emitHelperProps fragExec exprLoweringProps venomInst venomState

Theorem expr_stack_outcome_ptr:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_val_ok cx (expr_type e) v op G tn u /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_expr cx e) (es,s0,G0,tn0)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue ty op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_vv_ok cx (expr_type e) tv (StackValue ty op) ee G tn u /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_outcome_ptr_def] >> rpt strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_ptr_at_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `G`, `tn`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs :=
                gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
              simp[]) >>
          gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def,
              read_result_def, return_def, ptr_vv_ok_def] >>
          metis_tac[]) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                    `es_end`, `G`, `tn`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >>
      disch_then (qspec_then `es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
      simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

Theorem expr_vv_sim_ptr_stack:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv es'. eval_expr cx e s = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rw[expr_vv_sim_ptr_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  irule expr_stack_outcome_ptr >> conj_tac
  >- (first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  gvs[expr_sim_ptr_def] >> first_x_assum irule >> simp[]
QED

Theorem ghost_inv_fresh_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  es'.scopes = es.scopes /\ s'.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es' G' tn' s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
          ptr_covers G' tn' x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_def, stor_taint_ok_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      metis_tac[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem gas_path_ptr_one_step:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> GAS /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = OK u /\ ~u.vs_halted ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 (step_prov PG G i u)
    (step_taint i s u tn) (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr D lo ctx fn PG (step_prov PG G i u) (step_taint i s u tn)
     (u with vs_inst_idx := SUC s.vs_inst_idx) 0 (step_prov PG G i u)
     (step_taint i s u tn) (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    simp[gas_path_ptr_rules] >>
  drule_all gas_path_ptr_step >> simp[]
QED

Theorem emit_mload_ptr_path:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s 32 /\
  lookup_var src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  !D PG. ?out G' tn'.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK ((update_var out (mload (w2n a) s) s) with
             vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src]
        [STRING #"%" (toString sa.cs_next_var)]] /\
   op = Var (STRING #"%" (toString sa.cs_next_var)) /\
   (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var))` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n a) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  qspecl_then [`PG`, `G`, `tn`, `s`, `sa.cs_next_id`, `Var src`, `out`, `a`]
    mp_tac mload_ghost_clean >>
  impl_tac >- simp[eval_operand_def] >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
        (update_var out (mload (w2n a) s) s))
     (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
        (update_var out (mload (w2n a) s) s) tn)
     (OK (update_var out (mload (w2n a) s) s with
            vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule gas_path_ptr_one_step >>
     simp[mk_inst_def, is_terminator_def, update_var_def] >>
     fs[mk_inst_def]) >>
  `!x. x <> out ==>
       FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
                  (update_var out (mload (w2n a) s) s)) x = FLOOKUP G x /\
       op_taint (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
                  (update_var out (mload (w2n a) s) s) tn) (Var x) =
       op_taint tn (Var x)` by
    (rpt strip_tac
     >- (irule step_prov_other_output >> simp[mk_inst_def]) >>
     irule step_taint_other_output >> simp[mk_inst_def]) >>
  `op_prov (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
             (update_var out (mload (w2n a) s) s)) (Var out) = NONE` by
    (irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_other_none >> simp[mk_inst_def]) >>
  `(step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  qpat_x_assum `s.vs_inst_idx = _` kall_tac >>
  qexistsl_tac [`out`,
    `step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
       (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
       (update_var out (mload (w2n a) s) s) tn`] >>
  qunabbrev_tac `out` >> simp[] >> metis_tac[]
QED
