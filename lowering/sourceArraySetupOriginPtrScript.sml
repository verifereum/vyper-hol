Theory sourceArraySetupOriginPtr
Ancestors decoderArraySetupPtr

(* Compatibility boundary: preserve the constructive setup witnesses, including
   the joint path under the explicit runtime and memory-frontier premises. *)
Theorem source_array_setup_origin_ptr:
  !q src root di abi_sz mem_sz st ops ready initial slot j sb G tn d total t cx ctx PG R.
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz st = (ops,ready) /\
  lookup_var q initial = SOME (n2w slot) /\ slot + 32 < dimword (:256) /\
  mload slot initial = n2w j /\ j < dimword (:256) /\
  eval_operand src initial = SOME (n2w sb) /\
  ptr_covers G tn q initial 32 /\
  (!a. slot <= a /\ a < slot + 32 ==> a NOTIN tn.t_mem) /\
  lookup_var root initial = SOME (n2w d) /\ ptr_covers G tn root initial total /\
  not_fresh_at st q /\ not_fresh_at st root /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  32 + j * mem_sz + mem_sz <= total /\
  d + 32 + j * mem_sz < dimword (:256) /\ mem_sz < dimword (:256) /\
  ~initial.vs_halted /\
  run_inst_seq (emitted_insts st ready) initial = OK t ==>
  ?H u child. SND (SND ops) = Var child /\
    ptr_covers H u child
      (t with vs_inst_idx := LENGTH (emitted_insts st ready) + initial.vs_inst_idx) mem_sz /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    frag_exec_ptr cx ctx PG st ready
      (\g z v. g = G /\ z = tn /\ v = initial)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts st ready) + initial.vs_inst_idx)) R /\
    t.vs_memory = initial.vs_memory /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = initial.vs_allocas /\ u.t_imm = tn.t_imm /\
    (!D lower ctx' func.
      fn_has_code st ready func /\ allocas_from lower initial /\ ~ctx_has_dalloca ctx' /\
      initial.vs_current_bb = st.cs_current_bb /\
      initial.vs_inst_idx = LENGTH st.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH ready.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn initial) /\
    (!D lower explicit ctx' func.
      fn_has_code st ready func /\ allocas_from lower initial /\ ~ctx_has_dalloca ctx' /\
      ~initial.vs_halted /\ slot + 32 <= initial.vs_alloca_next /\
      initial.vs_current_bb = st.cs_current_bb /\
      initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx',func,PG) (initial,G,tn) []
        (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),H,u))
Proof
  MATCH_ACCEPT_TAC calldata_array_element_setup_endpoint_ptr_origin_core
QED
