(* Counted allocation, address evaluation and external-code slice composition. *)
Theory bodyMemSliceExtcodeContinue
Ancestors
  bodyMemSliceExtcodeAddress bodyMemSliceExtcodeTail bodyMemSliceExtcode bodyDeclMemoryCompose
  exprSimSliceExtcodeEntry exprSimSliceExtcodeContinue exprSimMemUnwrap exprSimMemDefs
  bodyMemBiSha256Compose freshWrites loweringPosts exprLoweringProps
  vyperState list rich_list words arithmetic compileEnv fragExec

Theorem slice_extcode_continue_entry_seq_mem:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  lower_value compile_expr cenv ty a sb = (aop,sc) /\
  compile_slice_extcode aop sop lop out dst sc = (r,sd) /\
  fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  expr_type a = BaseT AddressT /\ expr_body_pre cenv cx env a es /\
  expr_sim_mem ctx func cenv cx ty a es /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  (!op. MEM op [sop;lop] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at sa x)) /\
  (!x. aop = Var x ==> not_fresh_at sc x) /\
  i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (BytesT (Dynamic n)) /\
  evaluate_type (get_tenv cx) (expr_type result) = SOME ftv /\ type_memory_size ftv <= sz ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do av <- bind (eval_expr cx a) (read_result cx);
        code_acc <- get_accounts;
        code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type a] [av]);
        slice_acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx slice_acc (expr_type result) (Slice n)
                      tys [code_v;IntV (&i);IntV (&k)]);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result es sa sd s ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (expr_type result) (expr_type result) ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all slice_extcode_suffix_context >> strip_tac >>
  drule_all slice_extcode_output_entry >> strip_tac >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all slice_out_buf_path_mem >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule slice_extcode_out_control >> strip_tac >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (irule sha256_run_inst_seq_alloca_next_mono >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> fs[EVERY_MEM]) >>
  (irule gas_outcome_zero_prefix_mem >> goal_assum (drule_at Any)) >>
  irule slice_address_read_outcome_mem >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`cenv`, `env`, `aop`, `sb`, `sc`, `ty`] >>
  simp[stmt_state_rel_inst_idx] >> rpt gen_tac >> strip_tac >>
  suspend "address_post"
QED

Resume slice_extcode_continue_entry_seq_mem[address_post]:
  `sa.cs_next_id <= sa.cs_next_id` by simp[] >>
  `stmt_state_rel ctx func cenv cx es (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[stmt_state_rel_inst_idx] >>
  `stmt_state_rel ctx func cenv cx ee t /\
   eval_operand out t = SOME p /\ eval_operand dst t = SOME (p+32w) /\
   FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
   (!nm off len. local_region cenv ee.scopes t nm off len ==>
     regions_disjoint (w2n p) sz off len) /\
   (!j off len. FLOOKUP t.vs_allocas j = SOME (off,len) /\ j < sa.cs_next_id ==>
     regions_disjoint (w2n p) sz off len)` by
    (irule slice_extcode_output_post >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[stmt_state_rel_inst_idx] >>
     fs[local_region_def, venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `!op. MEM op [sop;lop] ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `(?w. op = Lit w) \/ (?z. op = Var z /\ not_fresh_at sa z)` by metis_tac[] >>
     gvs[venomStateTheory.eval_operand_def] >>
     `not_fresh_at sb z` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
     fs[expr_post_def, venomStateTheory.lookup_var_def]) >>
  rewrite_tac[slice_extcode_source_tail] >> suspend "tail"
QED

Resume slice_extcode_continue_entry_seq_mem[tail]:
  irule gas_outcome_post_mono >>
  irule_at Any slice_extcode_tail_outcome_mem >>
  qpat_assum `compile_slice_extcode _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP t.vs_allocas _ = _` (irule_at Any) >>
  qexistsl_tac [`sa`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]`, `ftv`, `result`, `cx`, `cenv`] >>
  simp[venomInstTheory.mk_inst_def] >>
  `accounts_well_typed ee.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.state_well_typed_def] >>
  `accounts_agree cx ee.accounts t.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `?bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sc sd) (DROP (LENGTH sc.cs_current_insts) bb.bb_instructions)` by
    (drule slice_extcode_tail_control >> strip_tac >>
     qpat_x_assum `fn_has_code sc sd func` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >> simp[DROP_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  qexists_tac `bb` >> simp[] >>
  suspend "tail_premises"
QED

Resume slice_extcode_continue_entry_seq_mem[tail_premises]:
  conj_tac
  >- (rpt strip_tac >>
      `sa.cs_next_var <= sc.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
        fs[ci_mono_def] >>
      fs[MEM] >>
      metis_tac[not_fresh_at_mono, ci_mono_def,
        venomStateTheory.operand_distinct, venomStateTheory.operand_11]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id < sc.cs_next_id /\
   sa.cs_next_id < sd.cs_next_id` by fs[ci_mono_def] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `s.vs_alloca_next <= t'.vs_alloca_next` by decide_tac >>
  simp[] >>
  irule slice_extcode_entry_post_rebase >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> fs[ci_mono_def, wb_frame_def, venomStateTheory.lookup_var_def]
QED

Finalise slice_extcode_continue_entry_seq_mem
