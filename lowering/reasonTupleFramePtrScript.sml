(* Source-state companion to the checked tuple-copy path. *)
Theory reasonTupleFramePtr
Ancestors reasonScratchFramePtr reasonTupleCopyPtr

Theorem reason_tuple_copy_state_path_ptr:
  emit_inst MLOAD [Var src] [v1] sa = ((),c1) /\
  emit_inst ADD [Var v1;Lit 31w] [v2] c1 = ((),c2) /\
  emit_inst AND [Var v2;Lit (i2w (-32))] [v3] c2 = ((),c3) /\
  emit_inst ADD [Lit 32w;Var v3] [v4] c3 = ((),c4) /\
  emit_void MCOPY [Var dst;Var src;Var v4] c4 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  32 <= n /\ n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  (!p. p = src \/ p = dst ==> p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4) /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [dst] /\
  not_local_ptr cenv es.scopes dst /\ n <= capacity /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,capacity) /\
  (!q. MEM q [v1;v2;v3;v4] ==> not_local_ptr cenv es.scopes q) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    stmt_state_rel ctx func cenv cx es sf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
      {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} /\
    (!p k. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 /\
      ptr_covers G tn p s k ==> ptr_covers Gf tnf p sf k) /\
    (!p. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_tuple_copy_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es sf` by
    (`!q. ~MEM q [v1;v2;v3;v4] ==> lookup_var q sf = lookup_var q s` by
       (simp[] >> metis_tac[]) >>
     drule_all reason_scratch_nonlocal_copy_state_rel >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED
