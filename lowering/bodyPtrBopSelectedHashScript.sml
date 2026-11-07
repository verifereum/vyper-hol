Theory bodyPtrBopSelectedHash
Ancestors
  bodyPtrBopHashSuffix bodyPtrBopEntry bodyPtrBopTypedSource
  fragGasPathPtr ptrDiscipline stmtFragPtr vyperValueOperation
  exprSimHash exprSimLiteralWord bytestringHashProps exprSimWordArgs wordArgsPtr
  gasSummaryComposePtr exprSimOperators exprSimHypsDefs exprSimDefs
  exprLoweringProps emitHelper emitHelperProps fragExec bodyPtrBopOperandContract localPtrsProps freshWrites
  bodyPtrDefs venomState exprOperandVar bodyPtrBopHashCompile vyperTyping loweringPosts vyperInterpreter vyperValue vyperAST compileEnv exprLowering list
Libs pairLib

Theorem bop_selected_hash_grows:
  (case bytestring_literal_hash e of
     NONE => (\(m,sm). compile_bytestring_hash m sm)
       (lower_value compile_expr cenv ty e sa)
   | SOME h => (Lit h,sa)) = (op,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id
Proof
  Cases_on `bytestring_literal_hash e` >> simp[]
  >- (pairarg_tac >> strip_tac >> gvs[] >>
      drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
      drule bop_hash_compile_layout >> strip_tac >>
      `sb.cs_next_id = sm.cs_next_id + 3` by
        (qpat_x_assum `compile_bytestring_hash _ _ = _` mp_tac >>
         simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
           emit_def] >> strip_tac >> gvs[]) >>
      metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_ADD]) >>
  strip_tac >> gvs[cs_extends_refl]
QED

Theorem bop_selected_hash_dynamic_success[local]:
  bop_operand_entry d ctx func cenv cx e es ca cz h s G tn /\
  bop_operand_post d ctx func cenv cx e es ca cb m s G tn v ee t H un /\
  lower_value compile_expr cenv (expr_type e) e ca = (m,cb) /\
  compile_bytestring_hash m cb = (h,cz) /\ cs_extends ca cb /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ~t.vs_halted ==>
  ?contents u H' un'.
    (v = BytesV contents \/ ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
    gas_path_ptr D 0 ctx func PG H un t 0 H' un' (OK u) /\
    eval_operand h u = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    op_prov H' h = NONE /\ op_taint un' h = {} /\
    (!z. h = Var z ==> not_fresh_at cz z) /\ (!l. h <> Label l) /\
    stmt_state_rel ctx func cenv cx ee u /\ ghost_inv d cenv cx ee H' un' u /\
    ~u.vs_halted /\ u.vs_current_bb = cz.cs_current_bb /\
    u.vs_inst_idx = LENGTH cz.cs_current_insts /\
    wb_frame cenv es ca s u /\ ghost_kept cenv es ca G tn s H' un'
Proof
  strip_tac >> gvs[bop_operand_post_def] >>
  suspend "prepare"
QED
Resume bop_selected_hash_dynamic_success[prepare]:
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `expr_val_at cenv cx (expr_type e) ca cb ee v m t` by
    metis_tac[loweringPostsTheory.expr_post_def] >>
  `?w. eval_operand m t = SOME w` by
    metis_tac[loweringPostsTheory.expr_val_at_def] >>
  `val_footprint tv v <> 0` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
     Cases_on `v` >> gvs[evaluate_type_def, value_has_type_def, val_footprint_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def, val_footprint_def]) >>
  `?p. m = Var p` by metis_tac[ptr_val_ok_def, ptr_mem_ok_def] >>
  gvs[] >>
  `lookup_var p t = SOME w` by gvs[eval_operand_def] >>
  `local_ptrs_reserved cenv ca` by gvs[bop_operand_entry_def] >>
  `not_fresh_at cb p` by metis_tac[compile_lower_value_var] >>
  drule_all bop_hash_compile_run >> strip_tac >>
  `?contents b.
     (v = BytesV contents \/ ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
     w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
     mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
     b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >- (gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
         drule hash_string_post_view >> simp[evaluate_type_def] >> strip_tac >>
         metis_tac[optionTheory.SOME_11, LENGTH_MAP]) >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
     drule hash_dynamic_post_view >> simp[evaluate_type_def] >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  `eval_operand h t' = SOME (word_of_bytes_be (Keccak_256_w64 contents))` by
    (`b < dimword(:256)` by decide_tac >>
     `w2n ((n2w b:bytes32) + 32w) = b + 32` by
       simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     `mload b t = n2w (LENGTH contents)` by
       gvs[venomStateTheory.mload_def, valueEncodingTheory.mem_word_at_def] >>
     gvs[valueEncodingTheory.mem_bytes_at_def]) >>
  (Q.SUBGOAL_THEN
   `((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
     (?str. v = StringV str /\ LENGTH str < dimword(:256)))` assume_tac
  >- (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def])) >>
  drule bop_hash_compile_layout >> strip_tac >>
  `fn_has_code cb cz func` by
    (gvs[bop_operand_entry_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `stmt_state_rel ctx func cenv cx ee t` by metis_tac[expr_post_state] >>
  `local_ptrs_reserved cenv cb /\ ~ctx_has_dalloca ctx /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x)` by
    (`ca.cs_next_var <= cb.cs_next_var` by
       (drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
     gvs[bop_operand_entry_def] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `ca` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `ca` >> simp[]) >>
  `?H' un'.
    gas_path_ptr D 0 ctx func PG H un t 0 H' un'
      (OK (t' with vs_inst_idx := LENGTH cz.cs_current_insts)) /\
    ghost_inv d cenv cx ee H' un' (t' with vs_inst_idx := LENGTH cz.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx ee (t' with vs_inst_idx := LENGTH cz.cs_current_insts) /\
    ~t'.vs_halted /\ t'.vs_current_bb = cz.cs_current_bb /\
    local_ptrs_reserved cenv cz /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cz x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cz x) /\
    ghost_kept cenv ee cb H un t H' un' /\
    op_prov H' h = NONE /\ op_taint un' h = {} /\
    un'.t_imm = un.t_imm /\ un'.t_mem = un.t_mem /\
    un'.t_stor = un.t_stor /\ un'.t_trans = un.t_trans /\
    (!x. not_fresh_at cb x ==> lookup_var x t' = lookup_var x t /\
      FLOOKUP H' x = FLOOKUP H x /\ FLOOKUP un'.t_var x = FLOOKUP un.t_var x)` by
    (irule bop_hash_compile_endpoint >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`p`, `ca`, `cb`, `tv`, `expr_type e`, `v`, `w`] >>
     simp[] >> metis_tac[LENGTH_MAP]) >>
  `wb_frame cenv es ca s t` by (gvs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  drule_all bop_hash_compile_readonly >> strip_tac >>
  `t'.vs_memory = t.vs_memory /\ t'.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `(t' with vs_vars := _) = t` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `ca.cs_next_var <= cb.cs_next_var /\ ca.cs_next_id <= cb.cs_next_id` by
    (drule (CONJUNCT2 compile_expr_grows) >> simp[]) >>
  `wb_frame cenv es ca s (t' with vs_inst_idx := LENGTH cz.cs_current_insts)` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`cb`, `t`] >>
     gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `ghost_kept cenv es ca G tn s H' un'` by
    (irule ghost_kept_wb_trans >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`ctx`, `cx`, `func`] >> gvs[bop_operand_entry_def]) >>
     qexistsl_tac [`H`, `ee`, `t`, `cb`, `un`] >> simp[]) >>
  `(!z. h = Var z ==> not_fresh_at cz z) /\ (!l. h <> Label l)` by
    (qpat_x_assum `compile_bytestring_hash _ _ = _` mp_tac >>
     simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       not_fresh_at_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qexists_tac `contents` >>
  qexists_tac `t' with vs_inst_idx := LENGTH cz.cs_current_insts` >>
  qexists_tac `H'` >> qexists_tac `un'` >>
  simp[eval_operand_def, lookup_var_def] >> metis_tac[]
QED
Finalise bop_selected_hash_dynamic_success

Theorem bop_selected_hash_outcome_ptr:
  (case bytestring_literal_hash e of
     NONE => (\(m,cb). compile_bytestring_hash m cb)
       (lower_value compile_expr cenv (expr_type e) e ca)
   | SOME digest => (Lit digest,ca)) = (h,cz) /\
  bop_operand_entry d ctx func cenv cx e es ca cz h s G tn /\
  expr_body_pre cenv cx env e es /\ body_inv tops ctx cenv cx /\
  is_bytestring_type (expr_type e) /\
  (bytestring_literal_hash e = NONE ==>
    expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es) /\
  (!gs rr ee. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (rr,ee) ==> P rr ee) /\
  (!v ee contents t H un.
    P (INL v) ee /\ ee.gas_obs = [] /\
    (v = BytesV contents \/ ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
    eval_operand h t = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    op_prov H h = NONE /\ op_taint un h = {} /\
    (!z. h = Var z ==> not_fresh_at cz z) /\ (!l. h <> Label l) /\
    stmt_state_rel ctx func cenv cx ee t /\ ghost_inv d cenv cx ee H un t /\
    ~t.vs_halted /\ t.vs_current_bb = cz.cs_current_bb /\
    t.vs_inst_idx = LENGTH cz.cs_current_insts /\
    wb_frame cenv es ca s t /\ ghost_kept cenv es ca G tn s H un ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next v) (ee,t,H,un) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
      (es,s) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s,G,tn) Q (\res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bytestring_literal_hash e`
  >- (gvs[] >> pairarg_tac >> gvs[] >> suspend "dynamic") >>
  `(?ann bs. e = Literal ann (BytesL bs)) \/
   (?ann str. e = Literal ann (StringL str))` by
    (Cases_on `e` >> gvs[bytestring_literal_hash_def] >>
     rename1 `Literal ann lit` >> Cases_on `lit` >>
     gvs[bytestring_literal_hash_def]) >>
  suspend "literal"
QED

Resume bop_selected_hash_outcome_ptr[dynamic]:
  drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  `bop_operand_entry d ctx func cenv cx e es ca cb m s G tn` by
    (gvs[bop_operand_entry_def] >>
     metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  irule bop_operand_contract_ptr >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`\rr ee. P rr ee /\ ?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (rr,ee)`,
    `cenv`, `d`, `m`, `ca`, `cb`, `expr_type e`] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v`, `ee`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all bop_selected_hash_dynamic_success >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  irule gas_outcome_ptr_prefix >>
  goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[]
QED

Resume bop_selected_hash_outcome_ptr[literal]:
  markerLib.RESUME_TAC >>
  gvs[bytestring_literal_hash_def] >>
  qmatch_goalsub_abbrev_tac `eval_expr cx (Literal ann lit)` >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G`, `[]`, `es`, `s`, `tn`, `evaluate_literal lit`] >>
  (conj_tac >- metis_tac[]) >>
  (reverse conj_tac >- (simp[gas_marked_exec_ptr_def, literal_read_all_tails] >>
    irule (cj 1 gas_path_ptr_rules) >> gvs[bop_operand_entry_def])) >>
  (first_x_assum irule >>
    simp[evaluate_literal_def, eval_operand_def, op_prov_def, op_taint_def,
      wb_frame_refl, ghost_kept_refl, stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
    `P (INL (evaluate_literal lit)) (es with gas_obs := [])` by
      metis_tac[literal_read_all_tails] >>
    gvs[Abbr `lit`, evaluate_literal_def, bop_operand_entry_def])
QED
Finalise bop_selected_hash_outcome_ptr
