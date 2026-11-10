Theory extRetRecursiveResourceInitPtr
Ancestors
  extRetRecursiveResourcePtr extRetScratchResourcePtr extRetScratchResourceInitPtr
  extRetScratchInitPtr
  allocaSiteResource compileEnv emitHelper fragExec fragGasPathPtr
  ptrDiscipline bodyPtrDefs venomState venomMemDefs words finite_map pred_set
  arithmetic list valueEncodingProps fragGasSeqPtr

Theorem encoder_scratch_init_counted_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites /\ eval_operand init s = SOME w /\ op_taint tn init = {} /\
  (!v. init = Var v ==> not_fresh_at sa v) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    mload addr sf = w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!id b n. MEM (id,b,n) protected /\ n <> 0 ==>
      regions_disjoint (b,n) (addr,32)) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
      parent <> sa.cs_next_id ==>
      mload p sf = mload p s /\
      ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
       (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem)))
Proof
  strip_tac >>
  `scratch_resource ctx fn sites q len s` by fs[encoder_resource_def] >>
  drule_all scratch_word_init_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_registered_intro >> simp[] >>
     fs[encoder_resource_def] >> metis_tac[]) >>
  `!id b n. MEM (id,b,n) protected /\ n <> 0 ==>
    regions_disjoint (b,n) (addr,32)` by
    (rpt gen_tac >> strip_tac >>
     drule_all encoder_resource_protected >> strip_tac >>
     irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
    parent <> sa.cs_next_id ==>
    mload p sf = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))` by
    (rpt gen_tac >> strip_tac >>
     irule scratch_word_init_registered_cursor >>
     conj_tac >- (gen_tac >> Cases >> simp[] >> metis_tac[]) >>
     simp[] >> qexistsl_tac [`addr`,`sa.cs_next_id`,`parent`,`w`] >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ip`,`addr`,`Gf`,`tnf`,`sf`] >> simp[] >> metis_tac[]
QED

Theorem encoder_scratch_child_push:
  encoder_resource ctx fn sites q len protected sf /\
  FLOOKUP sf.vs_allocas id = SOME (addr,32) /\
  children SUBSET sites /\ id NOTIN children ==>
  encoder_resource ctx fn children q len ((id,addr,32)::protected) sf
Proof
  metis_tac[encoder_resource_push]
QED

(* Two real prefixes, with the child site already registered at entry.
   The first initialized cell is pushed into the child's protected list. *)
Theorem encoder_scratch_two_init_reused_child:
  compile_alloc_buffer 32 sa = (parent,sm) /\
  emit_void MSTORE [parent.buf_operand; Lit wp] sm = ((),sb) /\
  compile_alloc_buffer 32 sb = (child,sc) /\
  emit_void MSTORE [child.buf_operand; Lit wc] sc = ((),sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites /\ children SUBSET sites /\
  sa.cs_next_id NOTIN children /\ sb.cs_next_id IN children /\
  FLOOKUP s.vs_allocas sb.cs_next_id = SOME (b,32) ==>
  ?ip ic a Gm tnm mid Gf tnf sf.
    parent.buf_operand = Var ip /\ child.buf_operand = Var ic /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tnm (OK mid) /\
    gas_path_ptr D 0 ctx fn PG Gm tnm mid 0 Gf tnf (OK sf) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    encoder_resource ctx fn children q len
      ((sa.cs_next_id,a,32)::protected) sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (a,32) /\
    FLOOKUP mid.vs_allocas sb.cs_next_id = SOME (b,32) /\
    FLOOKUP sf.vs_allocas sb.cs_next_id = SOME (b,32) /\
    mload a sf = wp /\ mload b sf = wc /\
    (!i. a <= i /\ i < a+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
    a+32 < dimword(:256) /\ b+32 < dimword(:256) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted
Proof
  strip_tac >>
  `eval_operand (Lit wp) s = SOME wp /\ op_taint tn (Lit wp) = {} /\
   (!v. Lit wp = Var v ==> not_fresh_at sa v)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all encoder_scratch_init_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `parent.buf_operand = Var ip` >>
  rename1 `mload a mid = wp` >>
  `encoder_resource ctx fn children q len
    ((sa.cs_next_id,a,32)::protected) mid` by
    (irule encoder_scratch_child_push >> metis_tac[]) >>
  `FLOOKUP mid.vs_allocas sb.cs_next_id = SOME (b,32)` by metis_tac[] >>
  `eval_operand (Lit wc) mid = SOME wc /\ op_taint tnf (Lit wc) = {} /\
   (!v. Lit wc = Var v ==> not_fresh_at sb v)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all encoder_scratch_init_counted_ptr >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `sa.cs_next_id <> sb.cs_next_id` by metis_tac[] >>
  `addr = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `addr = b` SUBST_ALL_TAC >>
  `mload a sf = wp /\
   (!i. a <= i /\ i < a+32 ==> i NOTIN tnf'.t_mem)` by
    (qpat_x_assum `!parent p. FLOOKUP mid.vs_allocas parent = _ /\ _ ==> _`
       (qspecl_then [`sa.cs_next_id`,`a`] mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`ip`,`ip'`,`a`,`Gf`,`tnf`,`mid`,`Gf'`,`tnf'`,`sf`] >>
  simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf`,`mid`,`tnf`] >> simp[]
QED
