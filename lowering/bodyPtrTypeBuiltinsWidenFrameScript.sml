Theory bodyPtrTypeBuiltinsWidenFrame
Ancestors
  bodyPtrTypeBuiltinsWidenCopyShape exprSimConvertBytes exprSimAlloc
  exprSimBufferStore exprSimHash exprLoweringProps emitHelperProps
  loweringPosts exprLowering compileEnv venomState venomExecSemantics
  context fragExec

(* Normalize a supplied run to its concrete allocation/copy endpoint while
   retaining the allocation's frame. This lemma does not assert run existence. *)
Theorem widen_copy_run_frame_split:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a ==>
  ?mid u w p inst.
    op = Var p /\ t = mcopy (w2n w) (w2n a) n u /\
    stmt_state_rel ctx fn cenv cx es u /\
    lookup_var p u = SOME w /\ u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,capacity) /\
    MEM inst (fn_insts fn) /\ inst.inst_id = sa.cs_next_id /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    ~not_fresh_at sa p /\ sa.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= sb.cs_next_id /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) capacity b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) capacity b len)
Proof
  strip_tac >> drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa mid) s = OK u` >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x u = SOME a` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `n < dimword(:256)` by decide_tac >>
  `run_inst_seq (emitted_insts mid sb) u = OK (mcopy (w2n w) (w2n a) (w2n (n2w n : bytes32)) u)` by
    (irule buffer_emit_mcopy_run >> qexistsl_tac [`Var p`,`x`,`Lit (n2w n)`] >>
     gvs[eval_operand_def]) >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (drule_all widen_copy_code_split >> strip_tac >>
     `sm = mid` by metis_tac[pairTheory.SND] >> simp[]) >>
  `t = mcopy (w2n w) (w2n a) n u` by
    (qpat_assum `run_inst_seq (emitted_insts sa mid) s = OK u`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> simp[] >>
     gvs[]) >>
  qexistsl_tac [`mid`,`u`,`w`,`inst`] >> fs[ci_mono_def, eval_operand_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
