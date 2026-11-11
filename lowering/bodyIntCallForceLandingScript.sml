(* Semantic forcing and resources share one counted landing. *)
Theory bodyIntCallForceLanding
Ancestors
  bodyIntCallWordLanding loweringPosts exprLowering compileEnv
  valueCopyBytes valueEncoding venomState fragGasPath

Theorem protected_memory_value_forcing:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty tv vv es s /\ read_result cx tv es = (INL v,es) /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ local_ptrs_reserved ce sa /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_path ctx func s 0 (OK u) /\ expr_val_rel cx ty v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce scopes u name base sz <=>
      local_region ce scopes s name base sz)
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[vv_holds_def, unwrap_value_def, comp_return_def] >>
      qexists_tac `s` >> simp[gas_path_rules]) >>
  rename1 `LocatedValue ann p` >> fs[vv_holds_def] >> (
  `is_word_type ann = is_word_type ty` by
    metis_tac[is_bytestring_word_type] >>
  Cases_on `is_word_type ann`
  >- (drule protected_word_unwrap_landing >> simp[] >>
      disch_then drule_all >>
      disch_then (qspecl_then [`ctx`, `scopes`] strip_assume_tac) >>
      `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next` by
        (rpt conj_tac >>
         qpat_assum `u = _` (fn th => simp[Once th])) >>
      qexists_tac `u` >> simp[expr_val_rel_def] >>
      fs[mload_def, mem_word_at_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
  simp[gas_path_rules, expr_val_rel_def] >> metis_tac[])
QED

Theorem protected_memory_value_forcing_prefix:
  gas_path ctx func start n (OK s) /\
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty tv vv es s /\ read_result cx tv es = (INL v,es) /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ local_ptrs_reserved ce sa /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_path ctx func start n (OK u) /\ expr_val_rel cx ty v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce scopes u name base sz <=>
      local_region ce scopes s name base sz)
Proof
  strip_tac >> drule_all protected_memory_value_forcing >>
  disch_then (qspecl_then [`scopes`, `ctx`] strip_assume_tac) >>
  qexists_tac `u` >> simp[] >>
  drule_all gas_path_then >> simp[]
QED
