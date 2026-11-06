(* Allocation-phase resources for the external singleton encoder. *)
Theory extRetBufferCursorStatePtr
Ancestors
  extRetBufferStatePtr extRetCursorResourcePtr exprSimOperands loweringHalt
  exprLoweringProps abiBuiltinAllocation fragGasPathPtr ptrDiscipline
  bodyPtrDefs compileEnv venomState venomInst codegenRel
  words finite_map arithmetic

Theorem compile_alloc_buffer_cursor_state_counted_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ n < dimword(:256) /\ 0 < n /\ used <= n /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w] [cout]) (fn_insts fn) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    stmt_state_rel ctx fn cenv cx es sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,n) /\
    addr+n < dimword(:256) /\ lookup_var ip sf = SOME (n2w addr) /\
    ptr_covers Gf tnf ip sf n /\ sf.vs_memory = s.vs_memory /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < addr \/ addr+n <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    ?cursor.
      FLOOKUP (abi_builtin_allocate_state sb.cs_next_id 32 sf).vs_allocas
        sb.cs_next_id = SOME (cursor,32) /\
      cursor+32 < dimword(:256) /\
      (cursor+32 <= addr \/ addr+used <= cursor)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> metis_tac[]) >>
  drule_all compile_alloc_buffer_state_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `sa.cs_next_id <> sb.cs_next_id` by decide_tac >>
  drule_all return_cursor_allocation_resources >> strip_tac >>
  qexistsl_tac [`ip`, `addr`, `Gf`, `tnf`, `sf`] >> simp[] >> metis_tac[]
QED
