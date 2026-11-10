Theory extRetRecursiveResourceInitPtr
Ancestors
  extRetRecursiveResourcePtr extRetScratchResourcePtr extRetScratchResourceInitPtr
  allocaSiteResource compileEnv emitHelper fragExec fragGasPathPtr
  ptrDiscipline bodyPtrDefs venomState venomMemDefs words finite_map pred_set
  arithmetic list valueEncodingProps

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
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
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
