(* Normal certificates use the actual counted landing state.  The reference
   state is fixed across composition; no uniqueness of OK endpoints is used. *)
Theory bodyIntCallNormalResource
Ancestors
  bodyIntCallProtectedBytelike exprLoweringProps exprSimLiteralBuffer
  intCallFrame fragGasPath fragExec venomState finite_map words list

Theorem protected_bytelike_literal_landing:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  allocas_above lo s /\ (!a len. P a len ==> a + len <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!a len. P a len ==>
    mem_bytes_at a len s.vs_memory = mem_bytes_at a len origin.vs_memory) /\
  (!op. reserved op ==> eval_operand op s = eval_operand op origin) /\
  (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) ==>
  ?u w. gas_path ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
    lo <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
    mem_word_at (w2n w) u.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) u.vs_memory = bs /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len origin.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op origin) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP origin.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  strip_tac >> drule_all protected_bytelike_literal_counted >> strip_tac >>
  drule gas_path_normal >> simp[] >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  fs[allocas_above_def] >> metis_tac[]
QED

(* Entry predicates A/B/C may include value and location witnesses.  Inv is
   indexed by a fixed reference memory/operand valuation, not the segment
   entry.  Instantiate Inv with the resource conjunction above. *)
Theorem normal_resource_sequence:
  (!s. A s /\ Inv s ==> ?n u.
    gas_path ctx func s n (OK u) /\ B u /\ Inv u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts) /\
  (!u. B u /\ Inv u /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?m v. gas_path ctx func u m (OK v) /\ C v /\ Inv v /\
      v.vs_current_bb = sb.cs_current_bb /\
      v.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
  !s. A s /\ Inv s ==> ?k v.
    gas_path ctx func s k (OK v) /\ C v /\ Inv v /\
    v.vs_current_bb = sb.cs_current_bb /\
    v.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`n + m`, `v`] >> simp[] >>
  metis_tac[gas_path_then, arithmeticTheory.ADD_COMM]
QED
