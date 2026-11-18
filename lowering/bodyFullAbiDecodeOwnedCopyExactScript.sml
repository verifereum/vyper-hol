Theory bodyFullAbiDecodeOwnedCopyExact
Ancestors
  bodyFullAbiDecodeOwnedCopyEffect

(* Identical syntactic owned-state interface; no new logical definition. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

Theorem abi_decode_owned_mcopy_joint_exact:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa input /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  abi_decoder_operand_live sa.cs_next_var count_op /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var dst s = SOME (n2w b) /\ lookup_var src s = SOME (n2w a) /\
  eval_operand count_op s = SOME (n2w n) /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) /\
  a < dimword (:256) /\ b < dimword (:256) /\ n < dimword (:256) /\
  output_base <= b /\ b+n <= output_base+output_cap /\ b+n <= s.vs_alloca_next /\
  a+n <= s.vs_alloca_next /\
  (w2n input_word+LENGTH input_bytes <= b \/ b+n <= w2n input_word) /\
  EVERY (\(aid,p,base,k,bytes). base+k <= b \/ b+n <= base) live /\
  EVERY (\(base,bytes). base+LENGTH bytes <= b \/ b+n <= base) protected ==>
  ?t Gf tnf.
    t = (mcopy b a n s) with vs_inst_idx := SUC s.vs_inst_idx /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> disch_tac >>
  mp_tac (BETA_RULE abi_decode_owned_mcopy_joint_effect) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` assume_tac))) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED
