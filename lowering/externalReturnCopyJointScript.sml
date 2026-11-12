(* The static ABI-copy suffix fixes its terminal state and ghosts before
   every dead mask. Empty returns require no source allocation witness. *)
Theory externalReturnCopyJoint
Ancestors
  externalReturnRawJoint allocaSiteResource ptrSafetyTransport
  loweringHalt bodyPtrDefs fragGasOriginPtrExec fragGasOriginPtr
  fragGasPathPtr fragGasPathMem fragGasSeqPtr fragGasSeqMem
  ptrSafeRun ptrDiscipline compileEnv venomState venomExecSemantics
  venomMemDefs venomInst words finite_map contextCodegenRel emitHelperProps

Theorem compile_external_return_copy_joint:
  compile_external_return (SOME op) F F (AbiCopy m) n F nkey ut iv st =
    (x,st') /\
  fn_has_code st st' func /\ (!y. op = Var y ==> not_fresh_at st y) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  alloca_inv s /\ alloca_room ctx func s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME p /\ op_taint tn op = {} /\
  m <= n /\ n < dimword (:256) /\
  (0 < m ==> w2n p + m <= s.vs_alloca_next) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = n) /\
  (0 < m ==> ?src. op = Var src /\ ptr_covers G tn src s m) /\
  (!i. w2n p <= i /\ i < w2n p + m ==> i NOTIN tn.t_mem) ==>
  ?ss G' tn'.
    ss.vs_returndata = read_memory (w2n p) m s /\
    ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient = s.vs_transient /\
    ss.vs_immutables = s.vs_immutables /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions /\
    !D. stor_taint_ok_at D tn s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Halt ss,G',tn')
Proof
  cheat
QED
