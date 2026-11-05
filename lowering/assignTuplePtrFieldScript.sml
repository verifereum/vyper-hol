(* Literal field-address computations carry no pointer taint. *)
Theory assignTuplePtrField
Ancestors
  assignTuplePtrLoadStep assignTuplePtrStorage typedCopyPtr ptrDiscipline
  ptrSafeRun venomExecSemantics venomInst venomState emitHelper emitHelperProps
  context compileEnv exprLoweringProps fragExec finite_map ASCIInumbers arithmetic
  localPtrsProps exprSimProps assignTuplePtrCopyEndpoint bodyPtrDefs stateFrame
  stmtLoweringMono stmtLowering exprLowering tupleTargetStoreRun fragGasPathPtr

Theorem emit_literal_add_path_ptr:
  emit_op ADD [Lit a; Lit b] sa = (pv,sm) /\
  fn_has_code sa sm func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'. pv = Var out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    lookup_var out t = SOME (a+b) /\ op_taint tn' (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!out. ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >>
     simp[eval_operand_def, op_taint_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id ADD [Lit a; Lit b] [out]) s =
    OK (update_var out (a+b) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `ADD`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK t)` >>
  qexistsl [`out`, `t`, `G1`, `tn1`] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  gvs[] >> simp[Abbr `t`, Abbr `G1`, Abbr `tn1`] >>
  simp[copy_len_binop_ghost_frame, op_taint_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, state_frame_def] >>
  conj_tac >- simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  gen_tac >> strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[] >> pure_rewrite_tac[GSYM update_var_def] >>
  simp[copy_len_binop_ghost_frame, step_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem tuple_field_add_frame_path_ptr:
  emit_op ADD [Lit slot; Lit off] st = (dst,st') /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'. stmt_state_rel ctx func cenv cx es t /\
    ghost_inv d cenv cx es G' tn' t /\
    eval_operand dst t = SOME (slot+off) /\ op_taint tn' dst = {} /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  strip_tac >> drule_all emit_literal_add_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[eval_operand_def] >>
  conj_tac
  >- (irule stmt_state_rel_old_vars_frame_ptr >>
      qexistsl [`s`, `st`] >> metis_tac[]) >>
  irule ghost_inv_old_vars_frame_ptr >>
  qexistsl [`G`, `s`, `st`, `tn`] >> simp[]
QED

Theorem tuple_field_storage_head_path_ptr:
  emit_op ADD [Lit slot; Lit off] st = (dst,sp) /\
  compile_store_at_loc cenv.ce_imm_alloca dst op
    (SOME (if tr then LocTransient else LocStorage)) sp = ((),sf) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  (!u mem. storage_dead cx tr (update_storage (slot+off) u mem) = storage_dead cx tr mem) /\
  write_storage_slot cx tr (slot+off) tv v es = (INL (),es') /\
  encode_value tv v = SOME [(0,typed_val_to_w256 tv v)] /\
  fn_has_code st sf func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'. stmt_state_rel ctx func cenv cx es' t /\
    ghost_inv d cenv cx es' G' tn' t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  strip_tac >>
  `cs_extends st sp /\ cs_extends sp sf` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
     metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `fn_has_code st sp func /\ fn_has_code sp sf func` by
    metis_tac[fn_has_code_split] >>
  drule_all tuple_field_add_frame_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `stmt_state_rel ctx func cenv cx es mid` >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v) /\ op_taint tn' op = {}` by
    (Cases_on `op` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all tuple_storage_store_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`t`, `G'`, `tn''`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  first_assum (irule_at Any) >> simp[]
QED
