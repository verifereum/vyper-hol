Theory bodyPtrPopEmittedTransfer
Ancestors
  bodyPtrPopSliceTransfer exprSimPopStorage exprLoweringProps
  ptrDiscipline venomInst list rich_list arithmetic

Theorem pop_root_emitted_transfer_nonempty:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?Gf tnf xs.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    op_prov Gf r = NONE /\ op_taint tnf r = {} /\
    EVERY (\x. ~not_fresh_at sa x) xs /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!x. ~MEM x xs ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  qrefinel [`_`, `_`, `[x0;x1;x2;x3;x4;x5;x6]`] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  irule (SRULE [APPEND, GSYM ADD_ASSOC] pop_root_slice_transfer_nonempty) >>
  simp[]
QED
