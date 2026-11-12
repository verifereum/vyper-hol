Theory externalReturnBytesJoint
Ancestors
  abiEncoderWindowBytesMem fragGasSeqPtr bodyPtrDefs ptrCoverage
  ptrSafetyTransport contractABI venomState venomInst words list arithmetic finite_map

(* Bytes encoder core, before any external RETURN or aggregate wrapper. *)
Theorem compile_abi_bytes_window_joint:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) st =
    (out,en) /\
  fn_has_code st en func /\ not_fresh_at st dst /\ not_fresh_at st src /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var src) s = SOME p /\
  eval_operand (Var dst) s = SOME q /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  read_memory (w2n p + 32) (LENGTH bs) s = bs /\
  w2n p + 32 + LENGTH bs <= s.vs_alloca_next /\
  w2n p + 32 + LENGTH bs < dimword (:256) /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= s.vs_alloca_next /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
  venomMemDefs$regions_disjoint (w2n p,32 + LENGTH bs)
    (w2n q,32 + contractABI$ceil32 (LENGTH bs)) /\
  ptr_covers G tn src s (32 + LENGTH bs) /\
  ptr_covers G tn dst s (32 + contractABI$ceil32 (LENGTH bs)) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==>
       i NOTIN tn.t_mem) ==>
  ?t G' tn'.
    read_memory (w2n q) (32 + contractABI$ceil32 (LENGTH bs)) t =
      contractABI$enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
    eval_operand out t = SOME (n2w (32 + contractABI$ceil32 (LENGTH bs))) /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    ptr_covers G' tn' dst t (32 + contractABI$ceil32 (LENGTH bs)) /\
    (!i. w2n q <= i /\
         i < w2n q + 32 + contractABI$ceil32 (LENGTH bs) ==>
         i NOTIN tn'.t_mem) /\
    mem_agree_outside
      {i | w2n q <= i /\ i < w2n q + 32 + contractABI$ceil32 (LENGTH bs)}
      s.vs_memory t.vs_memory /\
    (!i. i < w2n q \/ w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= i ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at st x ==>
         lookup_var x t = lookup_var x s /\
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  cheat
QED
