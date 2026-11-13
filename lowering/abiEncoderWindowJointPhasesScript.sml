(* Initialize an ABI scratch cursor on one execution before choosing dead masks. *)
Theory abiEncoderWindowJointPhases
Ancestors
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  abiEncoderWindowCursor abiEncoderWindowPhase abiEncoderWindowSequence
  allocationPtr wordLoadStorePtr fragExecPtr fragGasSeqPtr ptrSafetyTransport
  ptrDiscipline ptrCoverage emitHelperProps emitHelper compileEnv
  venomExecSemantics venomState venomMemDefs venomInst finite_map
  valueEncodingProps words list rich_list arithmetic pred_set

Theorem window_cursor_init_joint:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor;value_op] mid = ((),en) /\
  fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32) /\
  eval_operand value_op s = SOME w /\
  op_taint tn value_op = {} /\
  (!x. value_op = Var x ==> not_fresh_at st x) /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b p G' tn'.
    run_inst_seq (emitted_insts st en) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\
    abi_encode_exec_frame func s t /\
    cursor = Var p /\ not_fresh_at en p /\
    eval_operand cursor t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b + 32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = w /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    ptr_covers G' tn' p t 32 /\
    G' = G |+ (p,(b,32)) /\
    tn'.t_var = tn.t_var |+ (p,{}) /\
    tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b + 32} /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  cheat
QED
