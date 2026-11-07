Theory bodyPtrBopHashSuffix
Ancestors
  bodyPtrBopHashFrame bodyPtrBopHashCompile bodyPtrBopHashSequence
  bodyPtrHashBuiltinsGhostFrame bodyPtrBopCompareCompile bodyPtrBopCompare
  exprPtrUnwrapCopyEdges
  exprSimHash exprLoweringProps venomExecSemantics venomInst
  venomState finite_map exprLowering emitHelper compileEnv emitHelperProps
  rich_list fragExec codegenRel instIdxIndep fragGasPathPtr arithmetic ptrDiscipline

Theorem bop_hash_compile_readonly:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  lookup_var p s = SOME w /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> drule_all bop_hash_compile_emission >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  drule_all bop_hash_add_state >> strip_tac >> gvs[] >>
  `p <> q` by metis_tac[] >>
  `lookup_var p (update_var q (w + 32w) s) = SOME w` by
    fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all bop_hash_mload_state >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def] >>
  Cases_on `eval_operand (Var q)
    (update_var l (mload (w2n w) (update_var q (w + 32w) s))
      (update_var q (w + 32w) s))` >> simp[] >>
  Cases_on `eval_operand (Var l)
    (update_var l (mload (w2n w) (update_var q (w + 32w) s))
      (update_var q (w + 32w) s))` >>
  simp[update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem bop_hash_compile_state_rel:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  lookup_var p s = SOME w /\
  run_inst_seq (emitted_insts sc sd) s = OK t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sc ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := idx)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  irule hash_readonly_state_rel >>
  qexistsl_tac [`s`, `sc`] >> simp[] >>
  drule_all bop_hash_compile_readonly >> strip_tac >>
  drule_all bop_hash_compile_run_frame >> simp[]
QED

Theorem bop_hash_compile_layout:
  compile_bytestring_hash ptr_op sc = (op,sd) ==>
  inst_extends sc sd /\ cs_extends sc sd /\
  sd.cs_current_bb = sc.cs_current_bb /\
  LENGTH sd.cs_current_insts = LENGTH sc.cs_current_insts + 3 /\
  sd.cs_next_var = sc.cs_next_var + 3
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem bop_run_inst_seq_append_ok:
  run_inst_seq (is1 ++ is2) s = OK t <=>
  ?u. run_inst_seq is1 s = OK u /\ run_inst_seq is2 u = OK t
Proof
  eq_tac
  >- (strip_tac >> Cases_on `?u. run_inst_seq is1 s = OK u`
      >- (gvs[] >> drule run_inst_seq_append >>
          disch_then (qspec_then `is2` assume_tac) >> metis_tac[]) >>
      `!u. run_inst_seq is1 s <> OK u` by metis_tac[] >>
      drule run_inst_seq_append_err >>
      disch_then (qspec_then `is2` assume_tac) >> metis_tac[]) >>
  strip_tac >> metis_tac[run_inst_seq_append]
QED

Theorem bop_hash_compile_run_cursor:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  run_inst_seq (emitted_insts sc sd) (s with vs_inst_idx := idx) =
    OK (t with vs_inst_idx := idx)
Proof
  strip_tac >> drule_all bop_hash_compile_emission >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sd)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`s`, `idx`] mp_tac) >>
  simp[exec_result_map_def]
QED

Theorem bop_hash_pair_run_split:
  compile_bytestring_hash (Var p) sc = (h1,sd) /\
  compile_bytestring_hash (Var r) sd = (h2,se) /\
  not_fresh_at sd r /\ fn_has_code sc se fn /\
  run_inst_seq (emitted_insts sc se) s = OK t ==>
  ?u. run_inst_seq (emitted_insts sc sd) s = OK u /\
    run_inst_seq (emitted_insts sd se)
      (u with vs_inst_idx := LENGTH sd.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    fn_has_code sc sd fn /\ fn_has_code sd se fn
Proof
  strip_tac >> imp_res_tac bop_hash_compile_layout >>
  `emitted_insts sc se = emitted_insts sc sd ++ emitted_insts sd se` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `fn_has_code sc sd fn /\ fn_has_code sd se fn` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac[bop_run_inst_seq_append_ok] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all bop_hash_compile_run_cursor >> simp[]
QED

Theorem bop_hash_compile_result_old:
  compile_bytestring_hash ptr_op sc = (op,sd) ==>
  ?h. op = Var h /\ not_fresh_at sd h
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def]
QED

Theorem bop_hash_compile_operand_frame:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  lookup_var p s = SOME w /\
  run_inst_seq (emitted_insts sc sd) s = OK t /\
  local_ptrs_reserved cenv sc /\ not_fresh_at sc r /\
  expr_val_at cenv cx ty sa sb es v (Var r) s /\
  ptr_val_ok cx ty v (Var r) G tn s /\ tn'.t_mem = tn.t_mem /\
  FLOOKUP G' r = FLOOKUP G r /\
  FLOOKUP tn'.t_var r = FLOOKUP tn.t_var r ==>
  expr_val_at cenv cx ty sa sb es v (Var r) (t with vs_inst_idx := idx) /\
  ptr_val_ok cx ty v (Var r) G' tn' (t with vs_inst_idx := idx)
Proof
  strip_tac >> drule_all bop_hash_compile_run_frame >> strip_tac >>
  conj_tac
  >- (irule bop_expr_val_readonly_frame_cursor >>
      qexistsl_tac [`s`, `sc`] >> simp[]) >>
  irule bop_ptr_val_readonly_frame_cursor >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[]
QED

Theorem bop_hash_compile_ptr_cursor_full:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  expr_val_at cenv cx ty sa sb es v (Var p)
    (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ptr_val_ok cx ty v (Var p) G tn (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p (s with vs_inst_idx := LENGTH sc.cs_current_insts) = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) (s with vs_inst_idx := LENGTH sc.cs_current_insts) = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn (s with vs_inst_idx := LENGTH sc.cs_current_insts)
      0 G' tn' (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule bop_hash_compile_layout >> strip_tac >>
  drule_all (GEN_ALL (SIMP_RULE (srw_ss()) []
    (Q.INST [`s` |-> `u with vs_inst_idx := LENGTH sc.cs_current_insts`]
      (SPEC_ALL bop_hash_compile_ptr_full)))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED

Theorem bop_hash_compile_ptr_cursor:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  expr_val_at cenv cx ty sa sb es v (Var p)
    (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ptr_val_ok cx ty v (Var p) G tn (s with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p (s with vs_inst_idx := LENGTH sc.cs_current_insts) = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) (s with vs_inst_idx := LENGTH sc.cs_current_insts) = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn (s with vs_inst_idx := LENGTH sc.cs_current_insts)
      0 G' tn' (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_hash_compile_ptr_cursor_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Theorem bop_hash_pair_ptr:
  compile_bytestring_hash (Var p) sc = (h1,sd) /\
  compile_bytestring_hash (Var r) sd = (h2,se) /\
  not_fresh_at sc p /\ not_fresh_at sc r /\ local_ptrs_reserved cenv sc /\
  fn_has_code sc se fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty1 sa1 sb1 es v1 (Var p) s /\
  expr_val_at cenv cx ty2 sa2 sb2 es v2 (Var r) s /\
  ptr_val_ok cx ty1 v1 (Var p) G tn s /\
  ptr_val_ok cx ty2 v2 (Var r) G tn s /\
  evaluate_type (get_tenv cx) ty1 = SOME tv1 /\ ~is_word_type ty1 /\
  evaluate_type (get_tenv cx) ty2 = SOME tv2 /\ ~is_word_type ty2 /\
  lookup_var p s = SOME w1 /\ lookup_var r s = SOME w2 /\
  ((?bs. v1 = BytesV bs /\ LENGTH bs < dimword(:256) /\
      tv1 <> BaseTV AddressT /\ (!k. tv1 <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v1 = StringV str /\ LENGTH str < dimword(:256))) /\
  ((?bs. v2 = BytesV bs /\ LENGTH bs < dimword(:256) /\
      tv2 <> BaseTV AddressT /\ (!k. tv2 <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v2 = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc se) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 6)) /\
    op_prov G' h1 = NONE /\ op_prov G' h2 = NONE /\
    op_taint tn' h1 = {} /\ op_taint tn' h2 = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  imp_res_tac bop_hash_compile_layout >>
  `not_fresh_at sd r` by fs[not_fresh_at_def] >>
  drule_all bop_hash_pair_run_split >> strip_tac >>
  drule_all bop_hash_compile_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es
    (u with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (irule bop_hash_compile_state_rel >> metis_tac[]) >>
  qpat_x_assum `expr_val_at _ _ ty1 _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ptr_val_ok _ ty1 _ _ _ _ _` kall_tac >>
  `FLOOKUP G' r = FLOOKUP G r /\
   FLOOKUP tn'.t_var r = FLOOKUP tn.t_var r` by metis_tac[] >>
  drule_all bop_hash_compile_operand_frame >>
  disch_then (qspec_then `LENGTH sd.cs_current_insts` strip_assume_tac) >>
  drule_all bop_hash_compile_readonly >> strip_tac >>
  drule_all bop_hash_compile_run_frame >> strip_tac >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
  `lookup_var r (u with vs_inst_idx := LENGTH sd.cs_current_insts) = SOME w2` by
    fs[lookup_var_def] >>
  `u.vs_current_bb = sd.cs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ s` kall_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ _ G tn s` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ s` kall_tac >>
  drule_all bop_hash_compile_ptr_cursor >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  `!x. not_fresh_at sc x ==> not_fresh_at sd x` by fs[not_fresh_at_def] >>
  `op_prov G'' h1 = NONE /\ op_taint tn'' h1 = {}` by
    (qpat_assum `compile_bytestring_hash (Var p) sc = _`
       (mp_then Any strip_assume_tac bop_hash_compile_result_old) >>
     fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `LENGTH sd.cs_current_insts = s.vs_inst_idx + 3` by simp[] >>
  qexistsl_tac [`G''`, `tn''`] >> simp[] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`G'`, `u with vs_inst_idx := LENGTH sd.cs_current_insts`, `tn'`] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn _ _ _ _ _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G' tn' _ _ _ _ _` mp_tac >>
  simp[arithmeticTheory.ADD_ASSOC]
QED

(* The hash endpoint carries the complete ghost invariant, not just the
   memory-taint projection. Cursor transport is done only after framing. *)
Theorem bop_hash_compile_endpoint:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    ghost_inv d cenv cx es H un (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    local_ptrs_reserved cenv sd /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
    ghost_kept cenv es sc G tn s H un /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_imm = tn.t_imm /\ un.t_mem = tn.t_mem /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_hash_compile_ptr_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all bop_hash_compile_readonly >> strip_tac >>
  drule_all bop_hash_compile_run_frame >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  `ghost_inv d cenv cx es G' tn' t` by
    (irule hash_readonly_ghost_inv >>
     qexistsl_tac [`G`, `s`, `sc`, `tn`] >> simp[op_taint_def]) >>
  `stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (irule bop_hash_compile_state_rel >> metis_tac[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
  `ghost_kept cenv es sc G tn s G' tn'` by
    (irule hash_ghost_kept_frame >> simp[op_taint_def]) >>
  `!x. not_fresh_at sc x ==> not_fresh_at sd x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `LENGTH sd.cs_current_insts = s.vs_inst_idx + 3` by simp[] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[hash_ghost_inv_inst_idx] >>
  qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem bop_compare_emit_endpoint:
  ((opc = EQ /\ ops = [left;right] /\
       op_prov G left = NONE /\ op_prov G right = NONE) \/
   (opc = ISZERO /\ ops = [left])) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  emit_op opc ops sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    ghost_inv d cenv cx es H un (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    ghost_kept cenv es sc G tn s H un /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_imm = tn.t_imm /\ un.t_mem = tn.t_mem /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_compare_emit_placement >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sc.cs_next_id opc ops
    [STRING #"%" (toString sc.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK t` >>
  `((opc = EQ /\ ops = [left;right]) \/ (opc = ISZERO /\ ops = [left]))` by
    metis_tac[] >>
  `(t with vs_vars := s.vs_vars) = s` by
    (irule bop_compare_state_frame >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `?H un. H = step_prov PG G inst t /\ un = step_taint inst s t tn` by simp[] >>
  `un.t_imm = tn.t_imm` by
    (gvs[] >> irule copy_step_immutable_taint >>
     gvs[Abbr `inst`, mk_inst_def]) >>
  `op_prov H (Var (STRING #"%" (toString sc.cs_next_var))) = NONE /\
   op_taint un (Var (STRING #"%" (toString sc.cs_next_var))) = {} /\
   un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
   (!x. x <> STRING #"%" (toString sc.cs_next_var) ==>
     FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)` by
    (gvs[Abbr `inst`] >> irule bop_compare_ghost_frame >> metis_tac[]) >>
  suspend "finish"
QED

Resume bop_compare_emit_endpoint[finish]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at sc x ==> x <> STRING #"%" (toString sc.cs_next_var)` by
    gvs[not_fresh_at_def] >>
  `!x. not_fresh_at sc x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    FLOOKUP un.t_var x = FLOOKUP tn.t_var x` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sc.cs_next_var)` by metis_tac[] >>
     simp[] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     gvs[Abbr `inst`] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, exec_pure1_def,
       AllCaseEqs()] >> rpt strip_tac >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ghost_inv d cenv cx es H un t` by
    (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sc`, `tn`] >>
     simp[op_taint_def]) >>
  `ghost_kept cenv es sc G tn s H un` by
    (irule hash_ghost_kept_frame >> simp[op_taint_def]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s`, `sc`] >> simp[]) >>
  drule bop_compare_emit_layout >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 H un
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `H = _` SUBST1_TAC >>
     qpat_x_assum `un = _` SUBST1_TAC >>
     qunabbrev_tac `inst` >> irule bop_compare_counted_edge >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H un
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
     qexistsl_tac [`H`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `un`] >>
     simp[gas_path_ptr_rules]) >>
  `LENGTH sd.cs_current_insts = SUC s.vs_inst_idx` by decide_tac >>
  qexistsl_tac [`H`, `un`] >>
  asm_rewrite_tac[hash_ghost_inv_inst_idx, stmt_state_rel_inst_idx] >>
  metis_tac[]
QED
Finalise bop_compare_emit_endpoint
