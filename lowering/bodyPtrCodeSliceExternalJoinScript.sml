Theory bodyPtrCodeSliceExternalJoin
Ancestors
  bodyPtrCodeSliceExternalAllocated bodyPtrCodeSliceExternalTail
  exprSimSliceExtcodeContinue bodyPtrCodeSliceSelfOperands
  bodyPtrDefs compileEnv venomState words list vyperState exprSimSource
  gasSummaryComposePtr loweringPosts loweringStateRelDefs exprSimWordArgs
  exprLoweringProps fragExec rich_list

(* Public continuation boundary: the address operand is lowered and read,
   then the whole external-code tail (size, bounds, allocation, copy). *)
Theorem external_code_continue_outcome_ptr:
  lower_value compile_expr cenv ty a sa = (aop,sb) /\
  compile_slice_extcode aop sop lop sz sb = (r,sc) /\
  fn_has_code sa sc fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  expr_type a = BaseT AddressT /\ expr_body_pre cenv cx env a es /\
  expr_sim_ptr d ctx PG fn cenv cx ty a es /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G0 tn0 s /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  op_taint tn0 sop = {} /\ op_taint tn0 lop = {} /\
  op_prov G0 sop = NONE /\ op_prov G0 lop = NONE /\
  (!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  (!x. aop = Var x ==> not_fresh_at sb x) /\
  (!x j. cenv.ce_return_buf = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  (!x j. cenv.ce_return_pc = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32+n <= sz /\ sz < dimword (:256) /\
  type_memory_bytes cenv (lowered_value_type cenv result) <= sz /\
  32+32*word_size n <= sz /\ expr_type result = BaseT (BytesT (Dynamic n)) /\
  (~expr_has_effect result ==> ~expr_has_effect a) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (do av <- bind (eval_expr cx a) (read_result cx);
        code_acc <- get_accounts;
        code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type a] [av]);
        slice_acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx slice_acc (expr_type result) (Slice n)
                      tys [code_v;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s,G0,tn0)
    (\res ee G tn t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx result es sa sc s ee tv
        (LocatedValue (expr_type result) (mk_ptr r LocMemory)) t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s G tn /\
      ptr_vv_ok cx (expr_type result) tv
        (LocatedValue (expr_type result) (mk_ptr r LocMemory)) ee G tn t /\
      ptr_buf_ok cenv result r G t)
    (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >> drule_all slice_extcode_suffix_context >> strip_tac >>
  irule external_code_address_continue_ptr >>
  qpat_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> rewrite_tac[slice_extcode_source_tail] >>
  suspend "tail"
QED

Resume external_code_continue_outcome_ptr[tail]:
  `stmt_state_rel ctx fn cenv cx ee t` by fs[expr_post_def] >>
  `wb_frame cenv es ee sa s t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `!op w. MEM op [sop;lop] /\ eval_operand op s = SOME w ==>
     eval_operand op t = SOME w /\ op_taint tn op = op_taint tn0 op /\
     op_prov G op = op_prov G0 op` by
    (rpt gen_tac >> strip_tac >> irule code_slice_word_operand_frame >>
     conj_tac >- metis_tac[operand_distinct] >>
     qpat_assum `wb_frame _ _ _ sa s t` (irule_at Any) >> simp[] >>
     metis_tac[operand_distinct, operand_11]) >>
  `eval_operand sop t = SOME (n2w i) /\ eval_operand lop t = SOME (n2w k) /\
   op_taint tn sop = {} /\ op_taint tn lop = {} /\
   op_prov G sop = NONE /\ op_prov G lop = NONE` by metis_tac[MEM] >>
  `accounts_well_typed ee.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.state_well_typed_def] >>
  `accounts_agree cx ee.accounts t.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sc)
      (DROP (LENGTH sb.cs_current_insts) bb.bb_instructions)` by
    (drule slice_extcode_tail_control >> strip_tac >>
     qpat_x_assum `fn_has_code sb sc fn` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    fs[ci_mono_def] >>
  `!x. MEM (Var x) [aop;sop;lop] ==> not_fresh_at sb x` by
    (rpt strip_tac >> fs[MEM] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, operand_distinct, operand_11]) >>
  `(!x j. cenv.ce_return_buf = SOME (PtrVar (Var x) j) ==> not_fresh_at sb x) /\
   (!x j. cenv.ce_return_pc = SOME (PtrVar (Var x) j) ==> not_fresh_at sb x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  irule gas_outcome_ptr_conseq >>
  irule_at Any external_code_tail_outcome_ptr >>
  qpat_assum `compile_slice_extcode _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `ghost_inv d cenv cx ee G tn t` (irule_at Any) >>
  qpat_assum `expr_type result = _` (irule_at Any) >>
  simp[] >> suspend "rebase"
QED

Resume external_code_continue_outcome_ptr[rebase]:
  rpt strip_tac >> gvs[] >>
  `~expr_has_effect result ==> pure_frame cenv fn es sa s t` by
    (strip_tac >>
     `~expr_has_effect a` by
       (qpat_assum `~expr_has_effect result ==> ~expr_has_effect a` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post ctx fn cenv cx a es sa sb s ee _ aop t`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         (SPEC_ALL expr_post_pure_frame))) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `vv_post ctx fn cenv cx result es sa sc s ee' tv
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr r LocMemory)) t'` by
    (irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ t _ _ _ _` (irule_at Any) >>
     qpat_assum `wb_frame cenv es ee sa s t` (irule_at Any) >> simp[]) >>
  simp[] >>
  irule wordArgsPtrTheory.ghost_kept_wb_trans >>
  qpat_assum `ghost_kept cenv ee sb G tn t _ _` (irule_at Any) >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s G tn` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise external_code_continue_outcome_ptr
