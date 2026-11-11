(* Existential interfaces hide the exact numeric endpoints, not their run.
   ptr_covers_old_transport (appendStorageGhostPtr) is the coverage frame. *)
Theory bodyPtrSubscriptReadOnly
Ancestors
  bodyPtrSubscriptNumeric bodyPtrSubscriptLengthRead appendStorageGhostPtr
  emitHelperProps compileEnv ptrDiscipline venomState finite_map
  bodyPtrSubscriptNamedTuplePostBoundary exprLoweringProps loweringPosts

Theorem numeric_counted_read_only:
  MEM opc [ISZERO; SUB; MUL; LT; OR] /\
  emit_op opc ops sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id opc ops [dst]) s =
         OK (update_var dst w s)) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all emit_numeric_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`DRESTRICT G (COMPL {out})`,
    `tn with t_var := tn.t_var |+ (out,{})`,
    `update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[numeric_endpoint_observations] >> conj_tac
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  rpt strip_tac >> irule fresh_add_stmt_state_rel >> simp[] >> qexists_tac `sa` >>
  simp[] >> metis_tac[]
QED

Theorem assert_counted_read_only:
  emit_void ASSERT [arg] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME w /\ w <> 0w /\ op_taint tn arg = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all emit_numeric_assert_counted >> strip_tac >>
  qexistsl_tac [`G`, `tn`, `s with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[lookup_var_def, stmt_state_rel_inst_idx]
QED

Theorem reserved_operand_read_only:
  (!l. op <> Label l) /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) ==>
  eval_operand op sf = eval_operand op s /\
  op_prov Gf op = op_prov G op /\ op_taint tnf op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
  metis_tac[]
QED
