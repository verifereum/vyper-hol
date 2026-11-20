Theory bodyFullAbiDecodeArrayBulkRobust
Ancestors
  bodyFullAbiDecodeArrayBulk bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeArrayBulkWindow abiStaticAggregateProps
  abiDecoderBulk abiDecoderReentry fragGasOriginPtr fragGasPath
  bodyPtrDefs loweringStateRelDefs venomInst words finite_map pred_set

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
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val bulk_entry = ``
  abi_decode_bulk_payload (Var dp) src cnt msz MLOAD (Var input) sa = ((),sf) /\
  fn_has_code sa sf fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ (?H. V H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  lookup_var dp s = SOME (n2w d) /\ ptr_covers G tn dp s (32+n*msz) /\
  eval_operand src s = SOME (n2w off) /\ eval_operand cnt s = SOME (n2w n) /\
  op_prov G src = NONE /\ op_prov G cnt = NONE /\
  op_taint tn src = {} /\ op_taint tn cnt = {} /\
  abi_decoder_operand_live sa.cs_next_var (Var dp) /\
  abi_decoder_operand_live sa.cs_next_var (Var input) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  off+32+n*msz <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d+32 \/ d+32+n*msz <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= d+32 \/ d+32+n*msz <= b) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d+32 \/ d+32+n*msz <= a) protected``;

val bulk_post = ``\t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!obs. fn_has_code sa sf obs ==> gas_path ctx obs s 0 (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (^owned_decoder_state) sf t Gf tnf /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    mem_bytes_at (d+32) (n*msz) t.vs_memory =
      mem_bytes_at (w2n input_word+(off+32)) (n*msz) s.vs_memory /\
    (!a k. a+k <= d+32 \/ d+32+n*msz <= a ==>
         mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)``;

val input_origin = ``\s.
  (?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
     ib <= w2n (input_word:256 word) /\
     w2n input_word+LENGTH (input_bytes:word8 list) <= ib+isz) \/
  (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word+LENGTH input_bytes <= ib+isz)``;

val protected_containment = ``
  EVERY (\(a,bytes). output_base <= a /\
    a+LENGTH (bytes:word8 list) <= output_base+output_cap) protected``;

val length_certificate = ``\s tn.
  mem_word_at d s.vs_memory = n2w n /\
  (!i. d <= i /\ i < d+32 ==> i NOTIN tn.t_mem)``;

(* The same execution triple witnesses the frame and typed robustness. *)
Theorem abi_decode_array_bulk_robust_conditional:
  ^bulk_entry /\ msz = type_memory_size tv /\ ^protected_containment /\
  (^input_origin) s /\ (^length_certificate) s tn ==>
  ?t Gf tnf. (^bulk_post) t Gf tnf /\ ^protected_containment /\
    (^input_origin) t /\ (^length_certificate) t tnf /\
    (!i. output_base <= i /\ i < output_base+output_cap /\
         i IN tnf.t_mem ==> i IN tn.t_mem) /\
    (!k. k < n ==> !v.
      val_wf tv v /\ val_in_memory tv v (d+32+k*msz) t.vs_memory ==>
      !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
            val_in_memory tv v (d+32+k*msz) mem)
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (fn th => ASSUME_TAC th >> mp_tac (MATCH_MP (BETA_RULE
       bodyFullAbiDecodeArrayBulkPayloadTheory.abi_decode_array_bulk_joint_effect) th))
    (map_every ASSUME_TAC o CONJUNCTS)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every ASSUME_TAC o CONJUNCTS)))) >>
  `(^input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`sa`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  `mem_word_at d t.vs_memory = n2w n` by
    (qpat_assum `mem_word_at d s.vs_memory = _`
       (assume_tac o REWRITE_RULE[mem_word_at_bytes]) >>
     asm_rewrite_tac[mem_word_at_bytes]) >>
  `!i. i IN tnf.t_mem ==> i IN tn.t_mem` by simp[IN_DIFF] >>
  `!i. d <= i /\ i < d+32 ==> i NOTIN tnf.t_mem` by metis_tac[] >>
  `!i. d+32 <= i /\ i < d+32+n*msz ==> i NOTIN tnf.t_mem` by
    simp[IN_DIFF] >>
  `!i. output_base <= i /\ i < output_base+output_cap /\
       i IN tnf.t_mem ==> i IN tn.t_mem` by metis_tac[] >>
  `!k. k < n ==> !v.
     val_wf tv v /\ val_in_memory tv v (d+32+k*msz) t.vs_memory ==>
     !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory tv v (d+32+k*msz) mem` by
    (rpt strip_tac >> irule abi_decode_bulk_clean_elements >>
     metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED
