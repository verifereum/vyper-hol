Theory bodyFullAbiDecodeMemberCasesObserved
Ancestors
  robustCopyTransportPtr exprSimProps exprSimMemoryTransport
  abiCanonicalHeadSize bodyPtrDefs pred_set
  bodyFullAbiDecodeCutComplexBind
  bodyFullAbiDecodeComplexPrefixObserved bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeMemberLayout bodyFullAbiDecodeMemberPrefix valueEncodingTyping
  fragGasOriginPtrLoop fragGasPath fragExec externalEntryShape abiDecodePtrPrims
  abiDecoderMemberInfos abiDecoderCoherence abiEncoder
  compileEnv words list rich_list finite_map bodyFullAbiDecodeCutMemberBind

(* These quotations extend the old member and guarded entries at their
   recursive boundary. The path certificates share the result and ghosts. *)
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

val input_origin = ``\s.
  ((?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
    ib <= w2n (input_word:256 word) /\
    w2n input_word+LENGTH (input_bytes:word8 list) <= ib+isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
    ib <= w2n input_word /\ w2n input_word+LENGTH input_bytes <= ib+isz))``;

val protected_contained = ``\(protected:(num # word8 list) list).
  EVERY (\(a,bytes). output_base <= a /\
    a+LENGTH bytes <= output_base+output_cap) protected``;

val member_common_pre = ``\start finish dst src opc base_op hi d write_start size s G tn check.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\ check (
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
  (^owned_decoder_state) start s G tn)``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
  abi_decoder_coherent ce env sf ty tv /\
  info = type_to_abi_dec_info sf ce ty /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes /\
     ((?clamp. info = DecPrimWord clamp) ==>
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
  compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
  (^member_common_pre) start finish dst src opc base_op hi d d (type_memory_size tv) s G tn
    (\rest. (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\ h <= LENGTH input_bytes) /\
     hi <> Lit 0w /\ rest)``;

val bounded_member_entry = ``\dst src opc base_op hi elems ao vo env sf pretys pretvs tys tvs live protected start finish s G tn d.
  LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
  LENGTH pretys = LENGTH pretvs /\
  elems = abi_decoder_member_infos sf ce tys /\
  ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  hi <> Lit 0w /\
  (?off h. eval_operand src s = SOME (n2w off) /\
    eval_operand hi s = SOME (n2w h) /\
    off+ao+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
    h <= LENGTH input_bytes) /\
  compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start = ((),finish) /\
  eval_operand dst s = SOME (n2w d) /\
  (^member_common_pre) start finish dst src opc base_op hi d (d+vo)
    (SUM (MAP (type_memory_bytes ce) tys)) s G tn
    (\rest. (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\ rest)``;

val robust_at = ``\tv d t tn.
  !v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
    !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem``;

val observed_decoder_post = ``\start finish s G tn robust.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
       (^input_origin) t /\
       (!i. output_base <= i /\ i < output_base+output_cap /\
         i IN tn'.t_mem ==> i IN tn.t_mem) /\
       robust t tn') \/
     (?t. r = Abort Revert_abort t))``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d /\ (^protected_contained) protected /\ (^input_origin) s ==>
    (^observed_decoder_post) start finish s G tn ((^robust_at) tv d)``;

val bounded_complex_elems_motive = ``\dst src opc base_op hi elems ao vo.
  !env sf pretys pretvs tys tvs live protected start finish s G tn d.
    (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
      pretys pretvs tys tvs live protected start finish s G tn d /\
    (^protected_contained) protected /\ (^input_origin) s ==>
    (^observed_decoder_post) start finish s G tn
      (\t tn. !k. k < LENGTH tvs ==> (^robust_at) (EL k tvs)
        (d+vo+SUM (TAKE k (MAP type_memory_size tvs))) t tn)``;

Theorem abi_decode_complex_observed_conditional:
  (^bounded_complex_elems_motive) dst src opc base_op hi infos 0 0 ==>
  (^guarded_to_buf_motive) dst src opc base_op hi (DecComplex dyn infos)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_tac >>
  MATCH_MP_TAC (PURE_REWRITE_RULE [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP]
    (BETA_RULE (Q.INST
    [`Good` |-> `\(b:compile_state) (v:venom_state). T`,
     `Bad` |-> `\(v:venom_state). T`,
     `Span` |-> `\(a:compile_state) (b:compile_state). T`]
     abi_decode_complex_marked_bind))) >>
  conj_tac
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE abi_decode_complex_prefix_observed)) >>
  first_assum ACCEPT_TAC
QED

Theorem abi_decode_member_observed_conditional:
  ((elems = []) \/
   (?ei asz msz rest. elems = (ei,asz,msz)::rest /\
     (!elem_dst elem_src.
       (^guarded_to_buf_motive) elem_dst elem_src opc base_op hi ei) /\
     (^bounded_complex_elems_motive) dst src opc base_op hi rest
       (ao+asz) (vo+msz))) ==>
  (^bounded_complex_elems_motive) dst src opc base_op hi elems ao vo
Proof
  let
    val norm = REDEPTH_CONV BETA_CONV THENC REWRITE_CONV [CONJ_ASSOC, AND_CLAUSES]
    val th = CONV_RULE norm (Q.INST
      [`Good` |-> `\a s. T`, `Bad` |-> `\s. T`, `Span` |-> `\a b. T`]
      abi_decode_member_marked_bind)
  in
    CONV_TAC norm >> disch_tac >> MATCH_MP_TAC th >>
    (reverse conj_tac >- first_assum ACCEPT_TAC) >>
    rpt gen_tac >>
    MATCH_ACCEPT_TAC (CONV_RULE norm abi_decode_member_prefix_joint_observed)
  end
QED
