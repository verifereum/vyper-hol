(* One static copy boundary serves word members and whole static tuples.
   The compiler emits MCOPY even for zero bytes; no positive-size premise. *)
Theory logAbiStaticPtr
Ancestors
  logInstSeqPtr logTopicScalarPtr abiEncoder emitHelper emitHelperProps compileEnv exprLoweringProps
  valueEncodingProps typedCopyPtr bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst words finite_map pred_set list arithmetic

Theorem compile_abi_copy_seq_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy n) sa = (out,sb) /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) /\
  a+n < dimword(:256) /\ b+n < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  ?tm t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tm /\
    eval_operand out t = SOME (n2w n) /\ op_taint tm out = {} /\
    op_prov G out = NONE /\
    mem_bytes_at b n t.vs_memory = mem_bytes_at a n s.vs_memory /\
    (!i. b <= i /\ i < b+n ==> i NOTIN tm.t_mem) /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    mem_agree_outside {i | b <= i /\ i < b+n} t.vs_memory s.vs_memory /\
    tm.t_var = tn.t_var /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `out = Lit (n2w n) /\ emit_void MCOPY [Var dst;Var src;Lit (n2w n)] sa = ((),sb)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  `n < dimword(:256) /\ a < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\
   w2n ((n2w n):256 word) = n` by simp[eval_operand_def, op_taint_def, w2n_n2w] >>
  `ptr_covers G tn dst s (w2n ((n2w n):256 word)) /\
   ptr_covers G tn src s (w2n ((n2w n):256 word))` by simp[] >>
  drule_all emit_mcopy_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac))) >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     drule emitted_insts_emit_void >> simp[mk_inst_def]) >>
  qexistsl_tac [`tm`,`t`] >> suspend "frame"
QED

Resume compile_abi_copy_seq_ptr[frame]:
  markerLib.RESUME_TAC >> (
  `tm.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+n}` by
    (simp[] >>
     `{b+i | i < n /\ a+i IN tn.t_mem} = {}` by
       (simp[EXTENSION, GSYM IMP_DISJ_THM] >> rpt strip_tac >>
        qpat_x_assum `!i. a <= i /\ _ ==> _` (qspec_then `a+i` mp_tac) >> simp[]) >>
     simp[w2n_n2w]) >>
  qpat_x_assum `tm.t_mem = _ UNION _` kall_tac >>
  simp[IN_DIFF, IN_GSPEC_IFF, w2n_n2w, eval_operand_def,
       op_taint_def, op_prov_def, mcopy_mem_bytes_at_same] >>
  conj_tac
  >- (simp[mem_agree_outside_def] >> rpt strip_tac >>
      irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def])
QED
Finalise compile_abi_copy_seq_ptr
