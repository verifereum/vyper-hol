(* Exact modular calldata address used by a dynamic registration head. *)
Theory defaultConcreteBytesRegistration
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  defaultBytesRegistration vyperCalldata abiDecoderContract words list

Theorem default_registration_dynamic_decode:
  4 <= off /\ off < dimword (:256) /\ tv_abi_dynamic tv /\
  calldata_decode_args s.vs_call_ctx.cc_calldata [tv] (off-4) = SOME [x] ==>
  4 <= w2n ((4w + abi_decode_load CALLDATALOAD
    ((4w+n2w(off-4)):bytes32) s):bytes32) /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32)) = SOME x
Proof
  strip_tac >>
  `4 + (off-4) = off` by decide_tac >>
  `((4w + n2w (off-4)):bytes32) = n2w off` by
    (simp[word_add_n2w]) >>
  gvs[calldata_decode_args_def, AllCaseEqs()] >>
  gvs[abi_decode_load_def, abi_decode_source_def, cd_word_def,
       cd_bytes_def, word_add_def, w2n_n2w]
QED

Theorem default_registration_bytes_owner:
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var dst) (type_memory_size tv)) /\
  val_wf tv x /\ val_in_memory tv x s.vs_alloca_next t.vs_memory /\
  eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
  ptr_covers H u dst t (type_memory_size tv) /\
  FLOOKUP t.vs_allocas st.cs_next_id =
    SOME (s.vs_alloca_next,type_memory_size tv) /\
  t.vs_alloca_next = s.vs_alloca_next + type_memory_size tv /\
  s.vs_alloca_next + type_memory_size tv < dimword (:256) /\
  st.cs_next_id < st1.cs_next_id /\ not_fresh_at st1 dst /\
  MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
  ins.inst_outputs = [dst] /\ ins.inst_id = st.cs_next_id ==>
  default_registration_owner fn ce st1 t H u ((name,ty),tv)
    (x,Var dst,s.vs_alloca_next,st.cs_next_id)
Proof
  simp[default_registration_owner_def] >> strip_tac >>
  qexists `ins` >> simp[]
QED
