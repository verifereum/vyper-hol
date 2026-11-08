(* Read-only forcing: semantic and resource facts at one counted endpoint. *)
Theory bodyIntCallForcingReadOnly
Ancestors
  bodyIntCallForceLanding exprSimUnwrap exprSimHash exprSimAggregateChildren
  fragGasMode exprLoweringProps loweringPosts intCallFrame compileEnv
  venomState valueEncoding valueCopy valueCopyBytes list finite_map
  bodyIntCallWordLanding vyperInterpreter vyperState exprLowering

Theorem forcing_readonly_state_rel:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel ctx func ce cx es u
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es (u with vs_inst_idx := s.vs_inst_idx)` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s`, `sa`] >>
     simp[lookup_var_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> fs[lookup_var_def]) >>
  fs[stmt_state_rel_inst_idx]
QED

Theorem protected_word_value_forcing:
  unwrap_value ce (LocatedValue ann p) sa = (op,sb) /\
  vv_holds ce cx ty (Value v) (LocatedValue ann p) es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME stv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b sz. local_region ce scopes u name b sz <=>
      local_region ce scopes s name b sz) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ann = ty` by
    (fs[vv_holds_def] >> metis_tac[is_bytestring_word_type]) >> gvs[] >>
  `?a. eval_operand p.ptr_operand s = SOME a` by fs[vv_holds_def] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `ce.ce_is_ctor ==> !region. ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w` by fs[stmt_state_rel_def, immutable_base_zero_def] >>
  `?b. (p.ptr_location = LocCode /\ ce.ce_is_ctor /\ ce.ce_imm_alloca <> NONE ==>
      eval_operand (THE ce.ce_imm_alloca) s = SOME b) /\
    (case p.ptr_location of
       LocStorage => sload a s | LocTransient => tload a s
     | LocCode => if ce.ce_is_ctor then
         mload (w2n (if ce.ce_imm_alloca = NONE then a else a+b)) s
       else word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
     | _ => mload (w2n a) s) = typed_val_to_w256 stv v` by
    (qexists_tac `0w` >> Cases_on `p.ptr_location` >>
     fs[vv_holds_def, read_result_def, return_def, mload_def, mem_word_at_def] >>
     Cases_on `ce.ce_is_ctor` >> fs[]
     >~ [`immutable_holds _ _ _ _ _ _ _`, `~ce.ce_is_ctor`]
       >- (drule_all exprSimUnwrapTheory.immutable_holds_dload >> gvs[])
     >~ [`immutable_holds _ _ _ _ _ _ _`, `ce.ce_is_ctor`]
       >- (Cases_on `ce.ce_imm_alloca` >> fs[] >>
           drule_all exprSimUnwrapTheory.immutable_holds_iload >>
           simp[mload_def, mem_word_at_def, wordsTheory.WORD_ADD_0] >> gvs[]) >>
     metis_tac[storage_holds_load]) >>
  mp_tac (Q.INST [`ty` |-> `ann`, `value` |-> `typed_val_to_w256 stv v`,
    `reserved` |-> `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x`]
    (SPEC_ALL protected_word_unwrap_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule forcing_readonly_state_rel >> qexistsl_tac [`LENGTH sb.cs_current_insts`, `s`, `sa`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!q. _ ==> eval_operand q u = eval_operand q s`
       (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  qexists_tac `u` >> simp[gas_marked_path_def, expr_val_rel_def]
QED

Theorem protected_identity_value_forcing:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty (Value v) vv es s /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory /\ ~is_word_type ty) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  op = vv_operand vv /\ sb = sa /\ expr_val_rel cx ty v op s /\
  gas_marked_path F ctx func s 0 (OK s)
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[vv_holds_def, read_result_def, return_def, unwrap_value_def,
          comp_return_def, contextTheory.vv_operand_def] >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  rename1 `LocatedValue ann p` >> fs[vv_holds_def] >>
  `~is_word_type ann` by metis_tac[is_bytestring_word_type] >>
  gvs[unwrap_value_def, comp_return_def, contextTheory.vv_operand_def,
      read_result_def, return_def, expr_val_rel_def] >>
  simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules]
QED
