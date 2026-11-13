Theory bodyPtrPopMemoryHeader
Ancestors exprSimPtrProps typedCopyLayoutPtr representationCleanPtr bodyPtrDefs
  fragGasPathPtr exprLoweringProps compileEnv venomState venomInst

Theorem pop_robust_dynarray_header_clean:
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> drule dynarray_in_memory_robust_length >> strip_tac >>
  metis_tac[robust_mem_word_at_clean]
QED

Theorem pop_memory_header_load:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s bytes /\ 32 <= bytes /\
  lookup_var src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  !D PG. ?out G' tn'.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK ((update_var out (mload (w2n a) s) s) with
             vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ptr_covers G tn src s 32` by (gvs[ptr_covers_def] >> decide_tac) >>
  drule pop_robust_dynarray_header_clean >> strip_tac >>
  drule_all emit_mload_ptr_path >> simp[]
QED
