(* Runtime immutable loads reuse the general counted DLOAD boundary. *)
Theory bodyPtrSubscriptSeamArrayCodeLoad
Ancestors
  exprPtrCodeLoad exprSimSubscriptArrayFramed bodyPtrAttributeAdd
  bodyPtrSubscriptCountedAdd context venomState finite_map

Theorem compile_imm_load_word_runtime_counted:
  compile_imm_load_word F imm arg sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out Gf tnf sf.
    op = Var out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel ctx func cenv cx es sf)
Proof
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule_all emit_code_load_ptr_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `!cenv cx es. stmt_state_rel ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel ctx func cenv cx es u` by
    (rpt strip_tac >>
     `u = update_var out (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s
       with vs_inst_idx := LENGTH sb.cs_current_insts` by gvs[] >>
     asm_rewrite_tac[] >>
     irule (cj 1 compile_imm_load_word_runtime_frame) >>
     simp[compile_imm_load_word_runtime] >> metis_tac[]) >>
  qexistsl [`out`, `G'`, `tn'`, `u`] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED
