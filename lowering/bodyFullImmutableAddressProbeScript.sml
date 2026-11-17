(* A fresh constructor address register does not disturb the RHS endpoint. *)
Theory bodyFullImmutableAddressProbe
Ancestors
  bodyFullImmutableStoreRunProbe bodyFullImmutableStoreProbe bodyFullTargetAttribute
  immutableWordExecution
  exprLoweringProps stmtSimDefs bodyPtrDefs ptrDiscipline compileEnv
  loweringStateRelDefs loweringPosts codegenRel memLocDefs
  venomState venomInst emitHelper finite_map pred_set list words arithmetic

Theorem immutable_address_add_preservation:
  stmt_state_rel H ctx func ce cx ee s /\
  ghost_inv_at D lo d ce cx ee G tn s /\
  alloca_frame ce es sa s0 ce ee s /\
  local_ptrs_reserved ce su /\ ~not_fresh_at su tmp /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  op_prov G region = NONE /\ op_prov G off = NONE /\
  op_taint tn region = {} /\ op_taint tn off = {} /\
  u = update_var tmp a s /\
  G1 = step_prov PG G (mk_inst iid ADD [region;off] [tmp]) u /\
  tn1 = step_taint (mk_inst iid ADD [region;off] [tmp]) s u tn ==>
  stmt_state_rel H ctx func ce cx ee u /\
  ghost_inv_at D lo d ce cx ee G1 tn1 u /\
  alloca_frame ce es sa s0 ce ee u /\ tn1.t_mem = tn.t_mem /\
  u.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `not_local_ptr ce ee.scopes tmp` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `out_prov PG G (mk_inst iid ADD [region;off] [tmp]) u = NONE` by
    (irule out_prov_arith_none >> simp[mk_inst_def]) >>
  `G1 = DRESTRICT G (COMPL {tmp})` by
    simp[step_prov_def, set_prov_def, mk_inst_def] >>
  `tn1 = tn with t_var := tn.t_var |+ (tmp,{})` by
    (Cases_on `eval_operand region s` >>
     simp[step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
         store_taint_def, imm_taint_def, written_taint_def, adopt_reset_def,
         mem_taint_def, new_site_bytes_def, range_bytes_def, step_writes_def,
         update_var_def, source_memory_write_ranges_def, FLOOKUP_DEF,
         taint_component_equality, EXTENSION] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  rpt conj_tac
  >- (gvs[] >> irule stmt_state_rel_update_var >> simp[])
  >- (irule ghost_inv_at_fresh_write >>
      qexistsl_tac [`G`, `s`, `su`, `tn`] >>
      simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
           FLOOKUP_DRESTRICT] >> rpt strip_tac >>
      `x <> tmp` by metis_tac[] >> simp[])
  >- (gvs[] >> irule alloca_frame_update_var >> simp[])
  >> simp[update_var_def]
QED

Theorem immutable_uint256_address_store_boundary:
  stmt_state_rel H ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc dst) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME (BaseT (UintT 256)) /\
  write_place cx (ImmutablePlace ce.ce_module id []) sv ee = (INL (),fin) /\
  value_has_type (BaseTV (UintT 256)) sv /\
  ghost_inv_at D lo d ce cx ee G tn s /\ (!im. D.d_imm im = UNIV) /\
  struct_args_unique (cx_tops cx) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable id (BaseT (UintT 256)) slot :: post /\
  dst = compute_immutables_len (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre /\
  alloca_frame ce es sa s0 ce ee s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  ~not_fresh_at su tmp /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  eval_operand region s = SOME 0w /\ op_prov G region = NONE /\
  op_taint tn region = {} /\
  eval_operand op s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) sv) /\
  op_taint tn op = {} /\ op <> Var tmp /\
  dst + 32 <= lo /\ dst < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var tmp (n2w dst) s /\
  G1 = step_prov PG G (mk_inst iid ADD [region;Lit (n2w dst)] [tmp]) u /\
  tn1 = step_taint (mk_inst iid ADD [region;Lit (n2w dst)] [tmp]) s u tn ==>
  run_inst_seq [mk_inst iid ADD [region;Lit (n2w dst)] [tmp];
    mk_inst (iid+1) ISTORE [Var tmp;op] []] s =
    OK (istore dst (typed_val_to_w256 (BaseTV (UintT 256)) sv) u) /\
  stmt_state_rel H ctx func ce cx fin
    (istore dst (typed_val_to_w256 (BaseTV (UintT 256)) sv) u) /\
  ghost_inv_at D lo d ce cx fin G1
    (tn1 with <|t_mem := tn1.t_mem DIFF {i | dst <= i /\ i < dst + 32};
               t_imm := key_update tn1.t_imm dst {}|>)
    (istore dst (typed_val_to_w256 (BaseTV (UintT 256)) sv) u) /\
  alloca_frame ce es sa s0 ce fin
    (istore dst (typed_val_to_w256 (BaseTV (UintT 256)) sv) u) /\
  (!aid a sz i.
     FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                a + sz <= b \/ b + sz' <= a) /\
     a <= i /\ i < a + sz /\
     i IN (tn1.t_mem DIFF {j | dst <= j /\ j < dst + 32}) ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  mp_tac (Q.INST [`off` |-> `Lit (n2w dst)`, `a` |-> `n2w dst`]
    (SPEC_ALL immutable_address_add_preservation)) >>
  simp[op_prov_def, op_taint_def] >> strip_tac >>
  `eval_operand op (update_var tmp (n2w dst) s) =
     SOME (typed_val_to_w256 (BaseTV (UintT 256)) sv)` by
    (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
                         FLOOKUP_UPDATE]) >>
  conj_tac
  >- (mp_tac (Q.INST [`off` |-> `Lit (n2w dst)`, `a` |-> `n2w dst`,
          `value` |-> `op`, `v` |-> `typed_val_to_w256 (BaseTV (UintT 256)) sv`,
          `id` |-> `iid`] (SPEC_ALL immutable_word_ctor_store)) >>
      simp[eval_operand_def, w2n_n2w, LESS_MOD]) >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`, `off` |-> `dst`, `v` |-> `sv`]
    (SPEC_ALL immutable_uint256_store_boundary)) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED
