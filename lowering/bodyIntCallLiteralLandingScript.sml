(* Typed literal semantics and resources at one counted landing state. *)
Theory bodyIntCallLiteralLanding
Ancestors
  bodyIntCallNormalResource exprLowering loweringPosts compileEnv loweringStateRelDefs context
  vyperValue valueEncoding valueEncodingDefs vyperAST venomState words list

Theorem protected_bytes_literal_landing:
  !ctx func ce cx es s origin sa sb op cap bs lo P reserved.
  lower_value compile_expr ce (BaseT (BytesT (Dynamic cap)))
    (Literal (BaseT (BytesT (Dynamic cap))) (BytesL bs)) sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  LENGTH bs <= cap /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  allocas_above lo s /\ (!a len. P a len ==> a + len <= lo) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!a len. P a len ==>
    mem_bytes_at a len s.vs_memory = mem_bytes_at a len origin.vs_memory) /\
  (!q. reserved q ==> eval_operand q s = eval_operand q origin) /\
  (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) ==>
  ?u w. gas_path ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op u /\
    eval_operand op u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
    lo <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len origin.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q origin) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, compile_literal_vv_def,
       expr_type_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[unwrap_value_def, is_word_type_def, base_ptr_def,
       comp_return_def] >> strip_tac >>
  gvs[unwrap_value_def, is_word_type_def, base_ptr_def, comp_return_def] >>
  drule protected_bytelike_literal_landing >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  simp[expr_val_rel_def, evaluate_type_def, is_word_type_def,
       val_in_memory_def] >> metis_tac[]
QED

(* Unlike freshness-based frames, only the pointer operands need be reserved. *)
Theorem local_region_reserved_operands:
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    R (Var p)) /\
  (!op. R op ==> eval_operand op u = eval_operand op s) ==>
  !name b sz. local_region ce scopes u name b sz <=>
    local_region ce scopes s name b sz
Proof
  strip_tac >>
  `!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p u = lookup_var p s` by
    (rpt strip_tac >>
     `R (Var p)` by metis_tac[] >>
     qpat_x_assum `!op. R op ==> _` drule >> simp[eval_operand_def]) >>
  simp[local_region_def] >> metis_tac[]
QED

Theorem protected_bytes_literal_local_landing:
  !ctx func ce cx es s origin sa sb op cap bs lo P reserved.
  lower_value compile_expr ce (BaseT (BytesT (Dynamic cap)))
    (Literal (BaseT (BytesT (Dynamic cap))) (BytesL bs)) sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  LENGTH bs <= cap /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  allocas_above lo s /\ (!a len. P a len ==> a + len <= lo) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!a len. P a len ==>
    mem_bytes_at a len s.vs_memory = mem_bytes_at a len origin.vs_memory) /\
  (!q. reserved q ==> eval_operand q s = eval_operand q origin) /\
  (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) ==>
  ?u w. gas_path ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op u /\
    eval_operand op u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
    lo <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len origin.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q origin) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b sz. local_region ce es.scopes u name b sz <=>
      local_region ce es.scopes s name b sz)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `R = \q. reserved q \/
    ?name p sz. q = Var p /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz)` >>
  `!q x. R q /\ q = Var x ==> not_fresh_at sa x` by
    (gvs[Abbr `R`, local_ptrs_reserved_def] >> metis_tac[]) >>
  gvs[] >>
  drule (Q.INST [`origin` |-> `s`, `reserved` |-> `R`]
    (SPEC_ALL protected_bytes_literal_landing)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  `!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz` by
    (irule local_region_reserved_operands >> qexists_tac `R` >>
     simp[Abbr `R`] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[Abbr `R`]
QED
