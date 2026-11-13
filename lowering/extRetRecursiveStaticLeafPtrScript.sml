Theory extRetRecursiveStaticLeafPtr
Ancestors
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetBytesCopyCountedPtr
  extRetRecursiveBasePtr representationCleanPtr
  abiEncoder exprLowering valueEncoding valueEncodingProps vyperTypeABI
  vyperValue vyperTyping vyperABI compileEnv emitHelper fragExec fragGasPathPtr
  bodyPtrDefs venomState ptrDiscipline words pred_set arithmetic finite_map

(* The ambient MCOPY endpoint retains fields absent from the older static
   copy interface.  Evaluated layouts include zero-sized and None children. *)
Theorem encoder_evaluated_copy_resource_ptr:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ k = type_memory_size tv /\
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy k) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\ k < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n a) mem') /\
  encoder_resource ctx fn sites q len protected s ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w k) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) k s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+k} /\
    (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tnf.t_mem) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p)) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) k)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) k ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+k ==> i NOTIN tn.t_mem` by
    (drule robust_val_in_memory_static_clean >>
     disch_then (qspecl_then [`v`, `tn.t_mem`, `s.vs_memory`, `w2n a`] mp_tac) >>
     simp[]) >>
  `emit_void MCOPY [Var dst; Var src; Lit (n2w k)] sa = ((),sb) /\
   out = Lit (n2w k)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[]) >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k) /\
   op_taint tn (Lit (n2w k)) = {} /\
   ptr_covers G tn src s (w2n (n2w k:bytes32)) /\
   ptr_covers G tn dst s (w2n (n2w k:bytes32))` by
    gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  drule_all emit_mcopy_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `{w2n b+i | i < k /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >>
     Cases_on `i < k` >> simp[] >>
     `w2n a+i NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`tnf`, `sf`] >>
  gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  conj_tac >-
    (irule encoder_memory_frame_mono >>
     qexists_tac `{i | w2n b <= i /\ i < w2n b+type_memory_size tv}` >>
     simp[encoder_write_envelope_def, SUBSET_DEF, mem_agree_outside_def] >>
     rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[encoder_write_envelope_def]
QED
