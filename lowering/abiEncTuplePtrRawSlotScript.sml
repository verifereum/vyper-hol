Theory abiEncTuplePtrRawSlot
Ancestors
  abiTupleEncodeSlot abiDecodePtrBytesTail bodyPtrAttributeAdd
  rawCallHeaderFramePtr assignBasePtrMcopyGhost
  bodyPtrEnvBuiltinsSelectorBuffer bodyPtrStructLitFieldStore
  ghostPcTransportPtr ptrCoverage bodyPtrDefs compileEnv emitHelper emitHelperProps
  loweringStateRelDefs venomState venomInst venomExecSemantics
  typedCopyPtr ptrDiscipline finite_map words arithmetic ASCIInumbers

Theorem abi_tuple_slot_address_resources_ptr:
  emit_op ADD [Var bx;Lit (n2w off)] st = (dst,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var bx s = SOME (n2w b) /\ ptr_covers G tn bx s N /\
  off+n <= N /\ b+N < dimword(:256) /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_inv rb cenv cx es G tn s ==>
  ?out H tf t.
    dst = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK t) /\
    t = (update_var out (n2w (b+off)) s with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    H = step_prov PG G (mk_inst st.cs_next_id ADD [Var bx;Lit (n2w off)] [out])
      (update_var out (n2w (b+off)) s) /\
    tf = step_taint (mk_inst st.cs_next_id ADD [Var bx;Lit (n2w off)] [out]) s
      (update_var out (n2w (b+off)) s) tn /\
    lookup_var out t = SOME (n2w (b+off)) /\ ptr_covers H tf out t n /\
    ghost_inv rb cenv cx es H tf t /\ ghost_kept cenv es st G tn s H tf /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x) /\
      (!sz. ptr_covers G tn x s sz ==> ptr_covers H tf x t sz))
Proof
  strip_tac >>
  `b < dimword(:256)` by decide_tac >>
  `op_taint tn (Var bx) = {}` by gvs[ptr_covers_def] >>
  `eval_operand (Var bx) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[word_add_n2w] >>
  `ready.cs_current_bb = st.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  gvs[listTheory.LENGTH_APPEND, GSYM ADD1] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
      irule (abi_decode_ptr_output_address_covers
        |> Q.INST [`b` |-> `basew`]
        |> Q.INST [`basew` |-> `n2w b:bytes32`]
        |> SRULE [ghostPcTransportPtrTheory.ptr_covers_inst_idx, word_add_n2w]) >>
      simp[] >> qexists_tac `N` >> simp[w2n_n2w]) >>
  conj_tac
  >- (simp[ghost_inv_inst_idx] >>
      irule (cj 1 raw_call_emit_add_ghost_frame
        |> Q.INST [`a` |-> `aw`, `b` |-> `bw`]
        |> Q.INST [`aw` |-> `n2w b:bytes32`, `bw` |-> `n2w off:bytes32`]
        |> SRULE [ghost_inv_inst_idx, word_add_n2w]) >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule (cj 2 raw_call_emit_add_ghost_frame
        |> Q.INST [`a` |-> `aw`, `b` |-> `bw`]
        |> Q.INST [`aw` |-> `n2w b:bytes32`, `bw` |-> `n2w off:bytes32`]
        |> SRULE [word_add_n2w]) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[] >> rpt strip_tac >>
  irule (attribute_ptr_covers_update
    |> SRULE [ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >> simp[] >> metis_tac[]
QED
