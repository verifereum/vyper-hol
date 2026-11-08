(* Safe tuple member loads: robust representations justify clean scalar reads. *)
Theory assignTuplePtrLoadStep
Ancestors
  assignTuplePtrBoundary assignTuplePtrPrefix representationCleanPtr bodyPtrDefs compileEnv
  tupleTypedLoad tupleMemoryLayout words arithmetic list rich_list valueEncoding valueEncodingProofs
  typedCopyPtr ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState emitHelperProps
  emitHelper fragExec exprLoweringProps fragGasSeqPtr fragGasPathPtr exprSimProps stateFrame

Theorem tuple_word_member_clean:
  !tys tvs vs tenv cenv a mem tn i.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vs /\
    (!m. mem_agree_outside tn.t_mem mem m ==> tuple_in_memory vs tvs a m) /\
    a + type_memory_size_list tvs < dimword (:256) /\
    i < LENGTH tys /\ is_word_type (EL i tys) ==>
    !j. a + SUM (MAP type_memory_size (TAKE i tvs)) <= j /\
        j < a + SUM (MAP type_memory_size (TAKE i tvs)) + 32 ==>
        j NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >> rename1 `a + type_memory_size_list tvs < _` >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
   SUM (MAP type_memory_size (TAKE i tvs))` by
    (irule tuple_prefix_sizes >> simp[]) >>
  `a + SUM (MAP type_memory_size (TAKE i tvs)) < dimword (:256)` by
    (`i < LENGTH tvs` by metis_tac[] >>
     drule tuple_element_interval >> fs[type_memory_size_list_sum] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem mem m ==>
    mem_word_at (a + SUM (MAP type_memory_size (TAKE i tvs))) m =
      typed_val_to_w256 (EL i tvs) (EL i vs)` by
    (rpt strip_tac >>
     qspecl_then [`tys`, `tvs`, `vs`, `tenv`, `cenv`, `n2w a`, `m`, `i`]
       mp_tac tuple_typed_load_value >>
     simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     disch_then irule >> simp[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

(* Fresh variable writes preserve the ghost at an unchanged source scope. *)
Theorem ghost_inv_old_vars_frame_ptr:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  strip_tac >>
  fs[ghost_inv_def, local_ptrs_reserved_def, ptr_covers_def,
     stor_taint_ok_def] >>
  conj_tac >- metis_tac[] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem emit_add_zero_path_ptr:
  emit_inst ADD [left; right] [tmp] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [tmp])
      (update_var tmp (a+b) s))
    (step_taint (mk_inst sa.cs_next_id ADD [left;right] [tmp]) s
      (update_var tmp (a+b) s) tn)
    (OK (update_var tmp (a+b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule emit_inst_zero_path_ptr >> simp[is_terminator_def] >>
  conj_tac
  >- (irule emitHelperPropsTheory.step_ADD >> simp[]) >>
  irule ptr_inst_ok_copy_len_binop >> simp[]
QED

Theorem add_source_site_ptr:
  FLOOKUP G src = SOME site ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst]) u) dst =
    SOME site
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Compiler-facing boundary: fresh_var changes no emitted code. *)
Theorem emit_op_zero_path_ptr:
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sa.cs_next_id opc args [out]) s) /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
     OK (update_var out w s)) ==>
  ?out. op = Var out /\
    gas_path_ptr D lo ctx func PG G tn s 0
      (step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s))
      (step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn)
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qmatch_asmsub_abbrev_tac `op = Var out` >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc args [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `out`]) >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn)
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_assum `!out. step_inst_base _ _ = _` (qspec_then `out` assume_tac) >>
     drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     simp[mk_inst_def] >> disch_then irule >> gvs[mk_inst_def] >>
     metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then (qspec_then `0` mp_tac) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem emit_add_member_path_ptr:
  emit_op ADD [Var src; Lit off] sa = (pv,sm) /\
  fn_has_code sa sm func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  FLOOKUP G src = SOME site ==>
  ?out t G' tn'. pv = Var out /\ not_fresh_at sm out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    lookup_var out t = SOME (w+off) /\ op_taint tn' (Var out) = {} /\
    FLOOKUP G' out = SOME site /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
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
    (mk_inst sa.cs_next_id ADD [Var src; Lit off] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >>
     simp[eval_operand_def, op_taint_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id ADD [Var src; Lit off] [out]) s =
    OK (update_var out (w+off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `ADD`, `PG` |-> `PG`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`out`,
    `update_var out (w+off) s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [Var src; Lit off] [out])
      (update_var out (w+off) s)`,
    `step_taint (mk_inst sa.cs_next_id ADD [Var src; Lit off] [out]) s
      (update_var out (w+off) s) tn`] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `not_fresh_at sm out` by
    gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  gvs[] >>
  simp[copy_len_binop_ghost_frame, add_source_site_ptr] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, state_frame_def] >>
  conj_tac
  >- simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  gen_tac >> strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[] >>
  pure_rewrite_tac[GSYM update_var_def] >>
  simp[copy_len_binop_ghost_frame]
QED

Theorem emit_mload_member_path_ptr:
  emit_op MLOAD [Var src] sa = (pv,sm) /\
  fn_has_code sa sm func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) ==>
  ?out t G' tn'. pv = Var out /\ not_fresh_at sm out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    lookup_var out t = SOME (mload (w2n w) s) /\ op_taint tn' (Var out) = {} /\
    op_prov G' (Var out) = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
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
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_mload >> simp[]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s =
    OK (update_var out (mload (w2n w) s) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `MLOAD`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`out`,
    `update_var out (mload (w2n w) s) s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s)`,
    `step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn`] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `not_fresh_at sm out` by
    gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  gvs[] >>
  simp[mload_ghost_clean, eval_operand_def] >>
  `!out. op_prov (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s)) (Var out) = NONE` by
    simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
         finite_mapTheory.FLOOKUP_DRESTRICT] >>
  asm_rewrite_tac[] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, state_frame_def] >>
  conj_tac >- simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  gen_tac >> strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem robust_typed_word_clean:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  (!m. mem_agree_outside tm mem m ==> val_in_memory tv v a m) ==>
  (!m. mem_agree_outside tm mem m ==>
       mem_word_at a m = typed_val_to_w256 tv v) /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN tm)
Proof
  strip_tac >>
  `!m. mem_agree_outside tm mem m ==>
       mem_word_at a m = typed_val_to_w256 tv v` by
    (rpt strip_tac >> irule val_in_memory_word_type >> metis_tac[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem stmt_state_rel_old_vars_frame_ptr:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `t = (s with vs_inst_idx := t.vs_inst_idx) with vs_vars := t.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  pop_assum SUBST1_TAC >> irule stmt_state_rel_vars_frame >>
  simp[stmt_state_rel_inst_idx] >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED
