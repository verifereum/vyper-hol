(* Fetched execution keeps the registered resource function separate from code. *)
Theory exprSimAbiDecodeArrayFetched
Ancestors
  exprSimAbiDecodeArraySetup exprSimAbiDecodeArrayBulk
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderSequenceReach
  abiDecoderSiteEffect abiDecoderContract instIdxIndep
  abiDecoderIndexInit abiEncoder compileEnv emitHelper
  venomExecSemantics venomState venomInst valueEncoding
  vyperABI vyperValue contractABI words list rich_list

Theorem abi_decode_array_setup_fetched_outcome:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr opc guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  eval_operand dst s = SOME(n2w d) /\ d < dimword(:256) /\
  abi_decode_load opc (n2w (b+pos):bytes32) s = n2w n /\
  n = w2n (mem_word_at (b+pos) s.vs_memory) /\
  bs = mem_bytes_at (b+pos) (h-pos) s.vs_memory /\
  pos < dimword(:256) /\ h < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_member_head_size at < dimword(:256)) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx func s /\
  fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas output = SOME(root,outsz) /\
  d = root+off /\ off+32 <= outsz /\ output <> header_st.cs_next_id /\
  q+len <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (q,len) (d,32) /\
  (!b sz. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st loop_st fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (n <= maxn /\ pos+32+n*abi_member_head_size at <= h /\
   ?t p. decoder_straight_prefix fn s t /\
     t.vs_current_bb = loop_st.cs_current_bb /\
     t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
     eval_operand ip t = SOME(n2w p) /\ eval_operand cnt t = SOME(n2w n) /\
     mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
     fresh_vars_wrt loop_st t /\
     decode_site_effect ctx func st.cs_next_var
       ({a | d <= a /\ a < d+32} UNION {a | p <= a /\ a < p+32}) s t /\
     FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
     mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory /\
     venomMemDefs$regions_disjoint (root,outsz) (p,32) /\ ~t.vs_halted) \/
  (?encoded ix. run_inst_seq (emitted_insts st loop_st) s = Abort Revert_abort encoded /\
    run_from 0 ctx fn s = Abort Revert_abort (encoded with vs_inst_idx := ix) /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_array_loop_init dst src opc base_op hi maxn
     (abi_member_head_size at) st = ((ip,cnt),loop_st)` by
    simp[abi_decode_array_loop_init_def, comp_bind_def, comp_return_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_setup_site_outcome >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac)
  >- (disj1_tac >> simp[] >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexistsl [`t'`, `p`] >>
      gvs[fresh_vars_wrt_def, eval_op_inst_idx, mload_def]) >>
  disj2_tac >> drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  metis_tac[]
QED
