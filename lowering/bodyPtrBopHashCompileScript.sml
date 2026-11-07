Theory bodyPtrBopHashCompile
Ancestors
  bodyPtrBopHashSemantic exprLowering exprLoweringProps emitHelper compileEnv
  arithmetic rich_list fragExec venomExecSemantics venomInst venomState finite_map byte

Theorem bop_hash_compile_emission:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p ==>
  ?q l h aId lId hId.
    emitted_insts sc sd =
      [mk_inst aId ADD [Var p; Lit 32w] [q];
       mk_inst lId MLOAD [Var p] [l];
       mk_inst hId SHA3 [Var q; Var l] [h]] /\
    op = Var h /\ p <> q /\ l <> q /\
    (!x. not_fresh_at sc x ==> x <> q /\ x <> l /\ x <> h)
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       emitted_insts_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`STRING #"%" (toString sc.cs_next_var)`,
    `STRING #"%" (toString (sc.cs_next_var + 1))`,
    `sc.cs_next_id`, `sc.cs_next_id + 1`, `sc.cs_next_id + 2`] >>
  fs[not_fresh_at_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem bop_hash_compile_placement:
  compile_bytestring_hash ptr_op sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sc sd) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[fn_has_code_def, emitted_insts_def] >>
  gvs[IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem bop_bytes_hash_compile_ptr_full:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) (Var p) s /\
  ptr_val_ok cx ty (BytesV bs) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  lookup_var p s = SOME w /\ LENGTH bs < dimword(:256) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_hash_compile_placement >> strip_tac >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all (GEN_ALL (REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]
    (Q.INST [`iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
             `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
             `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h]`]
      (SPEC_ALL bop_bytes_hash_run_ptr_full)))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem bop_string_hash_compile_ptr_full:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (StringV str) (Var p) s /\
  ptr_val_ok cx ty (StringV str) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\ LENGTH str < dimword(:256) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_hash_compile_placement >> strip_tac >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all (GEN_ALL (REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]
    (Q.INST [`iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
             `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
             `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h]`]
      (SPEC_ALL bop_string_hash_run_ptr_full)))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem bop_hash_compile_ptr_full:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac
  >- (gvs[] >> drule_all bop_bytes_hash_compile_ptr_full >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      metis_tac[]) >>
  gvs[] >> drule_all bop_string_hash_compile_ptr_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  metis_tac[]
QED

(* Runtime SHA3 needs only the live pointer lookup, not freshness of the
   entire execution state's variable map. *)
Theorem bop_hash_compile_run:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  lookup_var p s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sc sd) s = OK t /\
    eval_operand op t = SOME (word_of_bytes_be (Keccak_256_w64
      (TAKE (w2n (mload (w2n w) s))
        (DROP (w2n (w + 32w)) s.vs_memory ++
         REPLICATE (w2n (mload (w2n w) s)) 0w))))
Proof
  strip_tac >> drule_all bop_hash_compile_emission >> strip_tac >>
  gvs[] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def] >>
  `p <> q` by metis_tac[] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, mload_def] >>
  fs[lookup_var_def] >>
  simp[Once step_inst_base_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, word_of_bytes_be_def]
QED

Theorem bop_bytes_hash_compile_ptr:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) (Var p) s /\
  ptr_val_ok cx ty (BytesV bs) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  lookup_var p s = SOME w /\ LENGTH bs < dimword(:256) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_bytes_hash_compile_ptr_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Theorem bop_string_hash_compile_ptr:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (StringV str) (Var p) s /\
  ptr_val_ok cx ty (StringV str) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\ LENGTH str < dimword(:256) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_string_hash_compile_ptr_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED

Theorem bop_hash_compile_ptr:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\
  ((?bs. v = BytesV bs /\ LENGTH bs < dimword(:256) /\
       tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_hash_compile_ptr_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]
QED
