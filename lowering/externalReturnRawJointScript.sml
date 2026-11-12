(* A raw external return keeps one terminal state and ghost pair for every
   dead mask. Only the actual length prefix and payload must be clean. *)
Theory externalReturnRawJoint
Ancestors
  rawReturnHalt rawReturnMem bodyPtrDefs fragGasOriginPtrExec
  fragGasOriginPtr fragGasPathPtr fragGasPathMem ptrSafeRun ptrDiscipline
  loweringHalt compileEnv venomState venomExecSemantics venomInst
  words finite_map

Theorem compile_external_return_raw_joint:
  compile_external_return (SOME (Var src)) prim T ei msz F nkey ut iv st =
    (x, st') /\
  fn_has_code st st' func /\ not_fresh_at st src /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var src) s = SOME p /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  read_memory (w2n (p + 32w)) (LENGTH bs) s = bs /\
  LENGTH bs < dimword (:256) /\
  w2n p + 32 + LENGTH bs <= dimword (:256) /\
  w2n p + 32 + LENGTH bs <= s.vs_alloca_next /\
  ptr_covers G tn src s (32 + LENGTH bs) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==>
       i NOTIN tn.t_mem) ==>
  ?ss G' tn'.
    ss.vs_returndata = bs /\
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
