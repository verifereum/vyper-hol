Theory abiEncodePtrEmptyBody
Ancestors
  exprSimAbiEncodeEmptyFramed exprSimAbiEncodeEmptyComplex
  fragExecPtr fragGasSeqPtr ptrDiscipline emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState
  compileEnv finite_map words list pred_set codegenRel
  assignTuplePtrLocalCopyRun abiEncoderLeaves abiEncodeEmptyCopyEndpoint
  exprSimAbiEncodeEmptySource abiEncoderWindowContract abiEncoderExtendSim
  abiDecoderContract abiEncoderRegisteredEffect bodyPtrDefs abiEncoderWindow
  abiEncodePtrEmptyBodyCore

Theorem abi_encode_empty_copy_sequence_ptr:
  emit_void MCOPY [dst;src;Lit 0w] sa = ((),sb) /\
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G tn /\
  run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n a) (w2n b) 0 s)
Proof
  MATCH_ACCEPT_TAC abiEncodePtrEmptyBodyCoreTheory.abi_encode_empty_copy_sequence_ptr
QED

Theorem abi_encode_empty_copy_path_ptr:
  compile_abi_encode_to_buf dst src (AbiCopy 0) sa = (out,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK ((mcopy (w2n a) (w2n b) 0 s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  MATCH_ACCEPT_TAC abiEncodePtrEmptyBodyCoreTheory.abi_encode_empty_copy_path_ptr
QED

Theorem abi_encode_empty_copy_body_ptr:
  compile_abi_encode_to_buf dst src (AbiCopy 0) sa = (out,sb) /\
  abi_encode_empty_window_pre ctx func sa sb dst src at av a d s /\
  d < dimword (:256) /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn x s outsz ==>
  ?t. window_strong_result ctx func sa sb out at av d s t /\
    abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels /\
    (!v. lookup_var v t = lookup_var v s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G tn x t outsz /\
    op_taint tn out = {} /\ (!v. out = Var v ==> not_fresh_at sb v) /\
    enc at av = [] /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK t)
Proof
  strip_tac >> drule_all abi_encode_empty_copy_body_observations_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem abi_encode_empty_body_ptr:
  compile_abi_encode_to_buf dst src ei sa = (out,sb) /\
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\
  (ei = AbiCopy 0 ==> abi_encode_empty_window_pre ctx func sa sb dst src at av a d s) /\
  enc at av = [] /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ d < dimword (:256) /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn x s outsz ==>
  ?t. window_strong_result ctx func sa sb out at av d s t /\
    abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels /\
    (!v. lookup_var v t = lookup_var v s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G tn x t outsz /\
    op_taint tn out = {} /\ (!v. out = Var v ==> not_fresh_at sb v) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK t)
Proof
  metis_tac[abi_encode_empty_body_observations_ptr]
QED
