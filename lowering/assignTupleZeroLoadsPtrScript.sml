(* Empty-layout tuple members still execute their address ADD instructions. *)
Theory assignTupleZeroLoadsPtr
Ancestors
  assignTuplePtrLoads assignTuplePtrLoadStep annAssignPtrLength externalReturnBufferlessNormalize
  loweringShapeRules stmtLowering compileEnv loweringStateRelDefs emitHelper context
  exprLoweringProps exprSimProps bodyPtrDefs fragGasPathPtr stateFrame
  valueEncoding valueEncodingDefs valueTypingMemoryProps venomState
  venomExecSemantics words list arithmetic stmtSimReturn fragExec ptrDiscipline

Theorem compile_tuple_zero_load_all_offset_path_ptr:
  !tys cenv bop off sa elems sb cx tvs vals s w G tn ctx func d es PG D.
  compile_tuple_load_all cenv bop tys off sa = (elems,sb) /\
  (!p. bop = Var p ==> not_fresh_at sa p) /\
  eval_operand bop s = SOME w /\ op_taint tn bop = {} /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  type_memory_size_list tvs = 0 /\ values_have_types tvs vals /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) elems /\
  local_ptrs_reserved cenv sb /\
  ?t G' tn'. gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q)) /\
    (!i. i < LENGTH tys ==>
      ~is_word_type (EL i tys) /\
      ptr_val_ok cx (EL i tys) (EL i vals) (EL i elems) G' tn' t /\
      eval_operand (EL i elems) t = SOME (w + n2w off))
Proof
  Induct
  >- (rpt gen_tac >> simp[compile_tuple_load_all_def, comp_return_def] >>
      strip_tac >> gvs[] >> qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_path_ptr_rules]) >>
  pop_assum (mk_asm "ih") >> rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >- fs[] >>
  Cases_on `vals` >- fs[vyperTypingTheory.value_has_type_def] >>
  fs[vyperTypingTheory.value_has_type_def, type_memory_size_def] >>
  rename1 `evaluate_type _ h = SOME tv` >>
  rename1 `value_has_type tv v` >>
  `~is_word_type h` by metis_tac[word_tv_memory_size, DECIDE ``~(32 = 0)``] >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_tuple_load_all_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[comp_return_def] >> strip_tac >>
  qpat_x_assum `_ = elems` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  gvs[compile_load_memory_def, comp_return_def] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  suspend "step"
QED

Resume compile_tuple_zero_load_all_offset_path_ptr[step]:
  `cs_extends sa sm` by
    (qspec_then `ADD` (qspec_then `[bop; Lit (n2w off)]`
       (qspec_then `sa` mp_tac)) ci_mono_emit_op >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sm sb` by metis_tac[compile_tuple_load_all_grows] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  drule_at (Pat `emit_op _ _ _ = _`) annassign_emit_len_binop_path_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then (qspecl_then [`D`, `ctx`, `func`, `PG`, `G`, `tn`] mp_tac) >>
  simp[GSYM op_taint_def] >> strip_tac >>
  suspend "remaining"
QED

Resume compile_tuple_zero_load_all_offset_path_ptr[remaining]:
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (simp[not_fresh_at_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `state_frame sf = state_frame (s with vs_inst_idx := sf.vs_inst_idx)` by
    (qpat_x_assum `sf with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >> simp[venom_state_component_equality, state_frame_def]) >>
  `sf.vs_allocas = s.vs_allocas /\ sf.vs_accounts = s.vs_accounts /\
   sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `sf with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >> simp[venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx es sf` by
    (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  `ghost_inv d cenv cx es Gf tnf sf` by
    (irule ghost_inv_old_vars_frame_ptr >> simp[op_taint_def] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by metis_tac[] >>
  `(!p. bop = Var p ==> not_fresh_at sm p) /\
   eval_operand bop sf = SOME w /\ op_taint tnf bop = {}` by
    (Cases_on `bop` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `sf.vs_current_bb = sm.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[] >>
  asm_x "ih" drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume compile_tuple_zero_load_all_offset_path_ptr[assemble]:
  `sm.cs_next_var <= sb.cs_next_var` by metis_tac[compile_tuple_load_all_grows] >>
  `not_fresh_at sb out` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `lookup_var out t'' = SOME (w + n2w off) /\ op_taint tn' (Var out) = {}` by
    (simp[op_taint_def] >> metis_tac[op_taint_def]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t'')` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >> qexistsl_tac [`t''`, `G'`, `tn'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> simp[op_taint_def] >> gvs[op_taint_def]) >>
  gen_tac >> Cases_on `i`
  >- (simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> rpt strip_tac >> gvs[] >>
      `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
      `val_footprint tv v = 0` by metis_tac[val_footprint_le, DECIDE ``n <= 0 ==> n = 0``] >>
      drule_all return_zero_wf_memory >> simp[]) >>
  simp[]
QED

Finalise compile_tuple_zero_load_all_offset_path_ptr
