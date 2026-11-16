Theory bodyFullAbiDecodeFiniteCases
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeClamp
  bodyFullAbiDecodeBytesCase bodyFullAbiDecodeInterface
  abiEncoder compileEnv words list rich_list finite_map

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
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

val owned_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/ write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val owned_decoder_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val owned_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h /\ h <= LENGTH input_bytes) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d (type_memory_size tv) s G tn``;

val owned_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^owned_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==> (^owned_decoder_post) start finish s G tn``;

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/ write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
       off < dimword (:256) /\ h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d (type_memory_size tv) s G tn``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==> (^owned_decoder_post) start finish s G tn``;

Theorem abi_decode_leaf_cases_joint:
  (!dst src opc base_op hi clamp.
    (^owned_to_buf_motive) dst src opc base_op hi (DecPrimWord clamp)) /\
  (!dst src opc base_op hi n.
    (^owned_to_buf_motive) dst src opc base_op hi (DecBytestring n))
Proof
  conj_tac
  >- (BETA_TAC >> match_mp_tac (BETA_RULE abi_decode_word_case_joint_conditional) >>
      metis_tac[abi_decode_clamp_joint]) >>
  ACCEPT_TAC abi_decode_bytes_case_joint
QED

Theorem abi_decode_guarded_leaf_cases_joint:
  (!dst src opc base_op hi clamp.
    (^guarded_to_buf_motive) dst src opc base_op hi (DecPrimWord clamp)) /\
  (!dst src opc base_op hi n.
    (^guarded_to_buf_motive) dst src opc base_op hi (DecBytestring n))
Proof
  reverse conj_tac >- ACCEPT_TAC abi_decode_bytes_guarded_joint >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _`
    (qx_choose_then `off` (qx_choose_then `h` strip_assume_tac)) >>
  `off + abi_member_head_size (vyper_to_abi_type env ty) <= h` by
    (qpat_x_assum `(?clamp'. _) ==> _` mp_tac >> simp[]) >>
  `off <= h` by decide_tac >>
  irule (BETA_RULE (CONJUNCT1 abi_decode_leaf_cases_joint)) >>
  rpt (FIRST [conj_tac, first_assum ACCEPT_TAC]) >>
  qexistsl_tac [`base_op`, `clamp`, `d`, `dst`, `env`, `hi`, `opc`, `sf`, `src`, `tv`, `ty`] >>
  rpt (FIRST [conj_tac, first_assum ACCEPT_TAC]) >>
  qexistsl_tac [`off`, `h`] >> simp[]
QED
