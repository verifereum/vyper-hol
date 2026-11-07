Theory extRetNestedScratchResourceProbePtr
Ancestors
  extRetScratchResourceInitPtr extRetScratchInitPtr extRetScratchResourcePtr
  fragGasPathPtr compileEnv emitHelper emitHelperProps exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  loweringPosts context codegenRel words finite_map pred_set arithmetic list
  ASCIInumbers

(* A finite runtime resource test, not a recursive encoding theorem.
   No semantic state relation is available at the child entry. *)
Theorem nested_scratch_resource_initializers:
  compile_alloc_buffer 32 sa = (parent,sm) /\
  emit_void MSTORE [parent.buf_operand; Lit wp] sm = ((),sb) /\
  compile_alloc_buffer 32 sb = (child,sn) /\
  emit_void MSTORE [child.buf_operand; Lit wc] sn = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ scratch_resource ctx fn sites q len s /\
  sa.cs_next_id IN sites /\ sb.cs_next_id IN sites /\
  sa.cs_next_id <> sb.cs_next_id ==>
  ?ip jp p c Gf tnf sf.
    parent.buf_operand = Var ip /\ child.buf_operand = Var jp /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w p) /\ ptr_covers Gf tnf ip sf 32 /\
    lookup_var jp sf = SOME (n2w c) /\ ptr_covers Gf tnf jp sf 32 /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (p,32) /\
    FLOOKUP sf.vs_allocas sb.cs_next_id = SOME (c,32) /\
    mload p sf = wp /\ mload c sf = wc /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem) /\
    (!i. c <= i /\ i < c+32 ==> i NOTIN tnf.t_mem) /\
    scratch_resource ctx fn sites q len sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!id b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      FLOOKUP sf.vs_allocas id = SOME (b,sz)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Lit wp) s = SOME wp /\ op_taint tn (Lit wp) = {} /\
   (!v. Lit wp = Var v ==> not_fresh_at sa v)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all scratch_word_init_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`]
    (qx_choose_then `ip` (qx_choose_then `p` (qx_choose_then `G1`
      (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))))) >>
  `not_fresh_at sb ip` by
    (qpat_x_assum `compile_alloc_buffer 32 sa = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE _ sm = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, emit_void_def] >> rpt strip_tac >> gvs[] >>
     simp[not_fresh_at_def, toString_inj] >> decide_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer 32 sa = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE _ sm = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, emit_void_def] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `compile_alloc_buffer 32 sa = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ sm = _` kall_tac >>
  `eval_operand (Lit wc) s1 = SOME wc /\ op_taint tn1 (Lit wc) = {} /\
   (!v. Lit wc = Var v ==> not_fresh_at sb v)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all scratch_word_init_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`]
    (qx_choose_then `jp` (qx_choose_then `c` (qx_choose_then `G2`
      (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))))) >>
  `mload p s2 = mload p s1 /\
   (!i. p <= i /\ i < p+32 ==> i NOTIN tn2.t_mem)` by
    (`!aid site. FLOOKUP s1.vs_allocas aid = SOME site ==>
        FLOOKUP s2.vs_allocas aid = SOME site` by
       (rpt gen_tac >> PairCases_on `site` >> metis_tac[]) >>
     drule_all scratch_word_init_registered_cursor >> simp[]) >>
  `lookup_var ip s2 = SOME (n2w p) /\ ptr_covers G2 tn2 ip s2 32` by
    (qpat_assum `!v. not_fresh_at sb v ==> _` (qspec_then `ip` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> simp[ptr_covers_def] >>
     qpat_x_assum `ptr_covers G1 tn1 ip s1 32` mp_tac >>
     simp[ptr_covers_def]) >>
  qexistsl_tac [`ip`, `jp`, `p`, `c`, `G2`, `tn2`, `s2`] >>
  simp[] >> conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
  qx_gen_tac `v` >> disch_tac >>
  `not_fresh_at sb v` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qpat_assum `!v. not_fresh_at sb v ==> _` (qspec_then `v` mp_tac) >>
  qpat_assum `!v. not_fresh_at sa v ==> _` (qspec_then `v` mp_tac) >> simp[]
QED

(* Reentry: the child site is already registered, with arbitrary old contents.
   The initialized address is that same registration, not a fresh-site premise. *)
Theorem nested_scratch_resource_reused_child:
  compile_alloc_buffer 32 sa = (parent,sm) /\
  emit_void MSTORE [parent.buf_operand; Lit wp] sm = ((),sb) /\
  compile_alloc_buffer 32 sb = (child,sn) /\
  emit_void MSTORE [child.buf_operand; Lit wc] sn = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ scratch_resource ctx fn sites q len s /\
  sa.cs_next_id IN sites /\ sb.cs_next_id IN sites /\
  sa.cs_next_id <> sb.cs_next_id /\
  FLOOKUP s.vs_allocas sb.cs_next_id = SOME (c,32) ==>
  ?ip jp p Gf tnf sf.
    parent.buf_operand = Var ip /\ child.buf_operand = Var jp /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w p) /\ ptr_covers Gf tnf ip sf 32 /\
    lookup_var jp sf = SOME (n2w c) /\ ptr_covers Gf tnf jp sf 32 /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (p,32) /\
    FLOOKUP sf.vs_allocas sb.cs_next_id = SOME (c,32) /\
    mload p sf = wp /\ mload c sf = wc /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem) /\
    (!i. c <= i /\ i < c+32 ==> i NOTIN tnf.t_mem) /\
    scratch_resource ctx fn sites q len sf /\
    s.vs_alloca_next <= sf.vs_alloca_next
Proof
  strip_tac >> drule_all nested_scratch_resource_initializers >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `FLOOKUP sf.vs_allocas sb.cs_next_id = SOME (c,32)` by
    (first_x_assum irule >> simp[]) >>
  gvs[] >> qexistsl_tac [`p`, `Gf`, `tnf`, `sf`] >> simp[]
QED

(* Callback audit against abi_dynamic_child_compose_resource_counted_ptr:
   This test supplies a counted path, PC/nonhalted endpoint, scratch_resource,
   monotone frontier, registration persistence and old-variable frames. Parent
   lookup, coverage and clean cursor contents survive child allocation/reuse.
   Code membership and scratch-site membership, distinct compiler site IDs,
   and placement of external destination/head/off operands remain caller-owned.
   The literal initializer has no operand-transport requirement. This is not an
   encoding child: it supplies neither encoded length, destination capacity nor
   the callback's destination write envelope. Those are separate obligations. *)
