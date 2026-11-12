(* Dynamic typed-copy execution: live length and recursive loop resources. *)
Theory assignTupleTypedCopyDynamicArrayPtr
Ancestors
  assignBasePtrBytesPrefix assignTupleTypedCopyArrayPtr typedCopyLayoutPtr
  bodyPtrPopMemoryHeader representationCleanPtr augAssignPtrScalarCertificate
  augAssignPtrScalarSafety augAssignPtrScalarRun
  typedNormalizeDynarrayLoop typedCopyAmbientFramePtr
  bodyPtrDefs ptrDiscipline ptrSafeRun fragGasSeqPtr
  venomState venomInst venomExecSemantics venomInstProofs
  exprSimBufferStore valueEncodingDefs exprLoweringProps fragExec finite_map words arithmetic list pred_set

Theorem typed_dynarray_load_length_ptr:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm u.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [len]] (s with vs_inst_idx := k) H tm) /\
    run_inst_seq [mk_inst id MLOAD [Var src] [len]] s = OK u /\
    u = update_var len (n2w (LENGTH vs)) s /\
    lookup_var len u = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> len ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def, mem_bytes_at_def]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  drule_all assign_base_bytes_mload_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `id`, `len`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `u`] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The bound check keeps the loaded scalar live and provenance-free. *)
Theorem typed_dynarray_check_length_ptr:
  lookup_var len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  len <> long /\ len <> ok /\ ~ctx_has_dalloca ctx ==>
  ?H tm.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s H tm /\
    run_inst_seq
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s =
      OK (update_var ok 1w (update_var long 0w s)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> long /\ p <> ok ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+1) ISZERO [Var long] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  `scalar_code {len} code` by
    simp[Abbr `code`, scalar_code_def, scalar_shape_def, scalar_binary_def,
         scalar_unary_def, scalar_available_def, mk_inst_def] >>
  `!v. v IN {len} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var long 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     `n < dimword(:256)` by decide_tac >>
     gvs[lookup_var_def]) >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >>
  gvs[Abbr `code`, mk_inst_def, op_prov_def] >> metis_tac[]
QED
