(* Slice's read-only length/data capture, on a common full endpoint. *)
Theory bodyFullBuiltinSliceDynamicCapture
Ancestors
  bodyFullUnwrapRun bodyPtrSignedConvertSourceFixed
  exprSimSliceMemory exprSimSliceCaptureControl builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs exprSimSliceOrdinaryFrame
  venomState venomExecSemantics exprLoweringProps list

Theorem slice_dynamic_capture_full_run:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa src /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
  32 <= capacity /\ w2n p + 32 < dimword (:256) /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. 32 < capacity /\ 32+n <= capacity ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n)
Proof
  strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand len u = SOME (mload (w2n p) s) /\
       eval_operand data u = SOME (p+32w) /\
       u = s with vs_vars := u.vs_vars /\
       (!x. not_fresh_at sa x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)` by
    (irule slice_bytestring_src_run >> qexists_tac `Var src` >>
     simp[eval_operand_def]) >>
  `!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> gvs[]) >>
  drule_all compile_bytestring_src_fixed_frame >>
  disch_then (qspecl_then [`ARB`,`func`,`PG`] strip_assume_tac) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >>
     drule_all compile_bytestring_src_fixed_frame >>
     disch_then (qspecl_then [`D`,`func`,`PG`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` assume_tac) >>
     fs[] >>
     qpat_assum `inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[] >>
      drule slice_bytestring_src_control >> strip_tac >> simp[] >>
      conj_tac >- (drule slice_bytestring_src_zero_code >> simp[EVERY_MEM]) >>
      conj_tac >- metis_tac[compile_bytestring_src_mem_ok, eval_operand_def] >>
      irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]
QED
