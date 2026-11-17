Theory bodyFullAbiDecodeLoopBody
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLoopSetup
  bodyFullAbiDecodeLoopBackedge gasOriginPtrLabels abiDecoderCoherence
  abiDecoderMemberInfos abiDecoderReentry abiDecoderOffset abiEncoder compileEnv
  venomInst venomExecSemantics venomState loweringStateRelDefs
  words list rich_list finite_map arithmetic valueEncodingProps ptrDiscipline

(* Interface's state quotation, with the two snapshot lists explicit. *)
val owned_decoder_state = ``\live protected st s G tn.
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

(* No PC or compiler equation is part of this runtime invariant. *)
val loop_resource = ``\anchor j s G tn.
  (^owned_decoder_state) live protected anchor s G tn /\ allocas_from lo s /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  eval_operand src s = SOME (n2w srcoff) /\
  eval_operand hi s = SOME (n2w h) /\
  srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  mem_word_at (w2n input_word+srcoff) s.vs_memory = n2w n /\
  lookup_var counter s = SOME (n2w cell) /\
  FLOOKUP s.vs_allocas aid = SOME (cell,32) /\ aid < anchor.cs_next_id /\
  ptr_covers G tn counter s 32 /\ mem_word_at cell s.vs_memory = n2w j /\
  cell+32 <= s.vs_alloca_next /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  (?ci cp. MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
    ci.inst_outputs = [cp] /\ ci.inst_id = aid /\ not_local_ptr ce es.scopes cp) /\
  lo <= cell /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var counter) = {} /\ j <= n /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+32+n*msz <= w2n input_word) /\
  (cell+32 <= d \/ d+32+n*msz <= cell) /\
  (cell+32 <= w2n input_word \/ w2n input_word+LENGTH input_bytes <= cell) /\
  EVERY (\(id,p,b,k,bytes). id <> aid /\ (b+k <= cell \/ cell+32 <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) protected /\
  EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\
    (b+k <= d \/ d+32+n*msz <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+32+n*msz <= a) protected``;

(* Select snapshots at the actual entry state, before either finite Setup
   or the child. No claims about the newly decoded element are needed. *)
Theorem abi_decode_loop_body_push[local]:
  (^loop_resource) anchor j s G tn /\
  not_fresh_at anchor counter ==>
  (^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) anchor s G tn
Proof
  BETA_TAC >> strip_tac >> asm_rewrite_tac[EVERY_DEF] >> simp[] >> metis_tac[]
QED

Theorem abi_decode_loop_body_state_mono[local]:
  (^owned_decoder_state) live protected a s G tn /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id ==>
  (^owned_decoder_state) live protected b s G tn
Proof
  BETA_TAC >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >-
    (irule EVERY_MONOTONIC >> qexists_tac
      `\(aid,p,base,k,bytes). aid < a.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (base,k) /\
        lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s k /\
        op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
        mem_bytes_at base k s.vs_memory = bytes /\ base+k <= s.vs_alloca_next` >>
     asm_rewrite_tac[] >> gen_tac >> PairCases_on `x` >> simp[] >>
     rpt strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
  conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- decide_tac >>
  irule EVERY_MONOTONIC >>
  qexists_tac `\(aid,p,base,k,bytes). not_fresh_at a p` >>
  asm_rewrite_tac[] >> gen_tac >> PairCases_on `x` >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

(* Projection at the child's same physical endpoint. Counter cleanliness is
   not inferred from its saved bytes: the subsequent MSTORE establishes it. *)
Theorem abi_decode_loop_body_pop[local]:
  (^owned_decoder_state)
    ((aid,counter,cell,32,cb)::live) ((d,pb)::protected) st t G tn /\
  cb = mem_bytes_at cell 32 s.vs_memory /\
  LENGTH pb = 32+j*msz /\ mem_word_at cell s.vs_memory = n2w j ==>
  (^owned_decoder_state) live protected st t G tn /\
  FLOOKUP t.vs_allocas aid = SOME (cell,32) /\
  lookup_var counter t = SOME (n2w cell) /\ ptr_covers G tn counter t 32 /\
  op_taint tn (Var counter) = {} /\ cell+32 <= t.vs_alloca_next /\
  mem_word_at cell t.vs_memory = n2w j /\
  mem_bytes_at d (32+j*msz) t.vs_memory = pb
Proof
  BETA_TAC >> strip_tac >>
  gvs[EVERY_DEF] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  metis_tac[exprSimMemoryTransportTheory.memory_window_word]
QED

(* These are the unchanged Interface child pre/post, with explicit lists. *)
val owned_decoder_post = ``\live protected start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) live protected finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val guarded_decoder_pre = ``\live protected start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) live protected start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) live protected start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==>
    (^owned_decoder_post) live protected start finish s G tn``;

Theorem abi_decode_loop_body_joint:
  abi_decoder_coherent ce env sf ty tv /\
  ei = type_to_abi_dec_info sf ce ty /\
  asz = abi_embedded_static_size ce.ce_struct_fields ty /\
  msz = type_memory_size tv /\ n < dimword (:256) /\ hi <> Lit 0w /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (?H. V H) /\ ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce anchor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  abi_decoder_operand_live anchor.cs_next_var (Var dst) /\
  abi_decoder_operand_live anchor.cs_next_var (Var counter) /\
  abi_decoder_operand_live anchor.cs_next_var (Var input) /\
  anchor.cs_next_var <= loop_body.cs_next_var /\ anchor.cs_next_id <= loop_body.cs_next_id /\
  abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD
    (Var input) hi ei asz msz loop_body = ((idx,child_src,child_dst),child) /\
  compile_abi_decode_to_buf child_dst child_src MLOAD (Var input) hi ei child =
    ((),returned) /\
  fn_has_code loop_body child fn /\ fn_has_code child returned fn /\
  idx = Var iv /\ loop_body.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= returned.cs_next_var /\ ~not_fresh_at returned nv /\
  lookup_block returned.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := returned.cs_current_bb; bb_instructions :=
      returned.cs_current_insts ++
        abi_decode_backedge_insts returned.cs_next_id iv nv (Var counter) hdr|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  (^guarded_to_buf_motive) child_dst child_src MLOAD (Var input) hi ei /\
  (^loop_resource) anchor j s G tn /\ j<n /\ ~s.vs_halted /\
  s.vs_current_bb = loop_body.cs_current_bb /\
  s.vs_inst_idx = LENGTH loop_body.cs_current_insts ==>
  (?t Gf tnf. !H. V H ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
  (?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (^loop_resource) anchor (SUC j) t Gf tnf /\
    (!x. not_fresh_at anchor x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)))
Proof
  strip_tac >>
  `not_fresh_at anchor counter /\ not_fresh_at anchor input` by
    (qpat_assum `abi_decoder_operand_live _ (Var counter)` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var input)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  `(^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) anchor s G tn` by
    (drule_all abi_decode_loop_body_push >> simp[]) >>
  `(^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) loop_body s G tn` by
    (irule abi_decode_loop_body_state_mono >> qexists_tac `anchor` >>
     asm_rewrite_tac[]) >>
  qpat_assum `(^loop_resource) anchor j s G tn`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `local_ptrs_reserved ce loop_body /\ not_fresh_at loop_body input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x)` by
    (qpat_assum `local_ptrs_reserved ce anchor` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> _` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> _` mp_tac >>
     qpat_assum `not_fresh_at anchor input` mp_tac >>
     qpat_assum `origin.cs_next_var <= anchor.cs_next_var` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `abi_decoder_operand_live loop_body.cs_next_var src /\
   abi_decoder_operand_live loop_body.cs_next_var hi /\
   abi_decoder_operand_live loop_body.cs_next_var (Var dst) /\
   abi_decoder_operand_live loop_body.cs_next_var (Var counter)` by
    (qpat_assum `abi_decoder_operand_live _ src` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ hi` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var dst)` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var counter)` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
  `dec_info_needs_offset ei ==> 32 <= asz` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `ei = _` mp_tac >> qpat_assum `asz = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule abi_decoder_coherent_header >>
     drule abiDecoderDynamicTheory.abi_decoder_coherent_dynamic >>
     gvs[abi_decoder_header_def, abi_decoder_needs_offset_iff,
       abiDecodeRangesTheory.abi_member_head_size_def]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >>
     strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def] >>
     metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >>
  `cell < dimword (:256)` by decide_tac >>
  `asz < dimword (:256)` by
    (qpat_assum `srcoff+32+n*asz <= h` mp_tac >>
     qpat_assum `h <= LENGTH input_bytes` mp_tac >>
     qpat_assum `w2n input_word+LENGTH input_bytes < dimword (:256)` mp_tac >>
     qpat_assum `j<n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `n` >> simp[ADD1, RIGHT_ADD_DISTRIB] >> decide_tac) >>
  `lookup_var dst s = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var dst) s = SOME (n2w d)` mp_tac >>
     pure_rewrite_tac[eval_operand_def] >> disch_then irule) >>
  qpat_assum `(^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) loop_body s G tn`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  mp_tac (Q.INST [
    `sa` |-> `loop_body`, `sb` |-> `child`,
    `live` |-> `(aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live`,
    `protected` |-> `(d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected`]
    (SPEC_ALL abi_decode_loop_setup_joint)) >>
  (impl_tac >- (asm_rewrite_tac[] >> BETA_TAC >> asm_rewrite_tac[] >>
    qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes)
      ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected)` mp_tac >>
    simp[])) >>
  strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[]) >>
  rename1 `child_dst = Var child_ptr` >>
  `FLOOKUP Gu child_ptr = SOME (output_base,output_cap)` by
    asm_rewrite_tac[] >>
  `asz = abi_member_head_size (vyper_to_abi_type env ty)` by
    (drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def]) >>
  `local_ptrs_reserved ce child /\
   abi_decoder_operand_live child.cs_next_var (Var input)` by
    (qpat_assum `local_ptrs_reserved ce loop_body` mp_tac >>
     qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var input)` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       abi_decoder_operand_live_mono, LESS_EQ_TRANS]) >>
  `op_prov Gu hi = NONE /\ op_taint tnu hi = {} /\
   op_taint tnu (Var input) = {}` by
    (`eval_operand hi u = eval_operand hi s /\
      op_taint tnu hi = op_taint tn hi /\ op_prov Gu hi = op_prov G hi` by
       (irule decoderArraySetupPtrTheory.old_operand_ghost_frame >>
        reverse conj_tac >- asm_rewrite_tac[] >>
        qexists_tac `loop_body` >>
        conj_tac >-
          (rpt strip_tac >>
           qpat_assum `abi_decoder_operand_live loop_body.cs_next_var hi` mp_tac >>
           qpat_assum `hi = Var x` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
           rpt strip_tac >> gvs[abi_decoder_operand_live_def,
             abi_decoder_older_vars_def, not_fresh_at_def]) >>
        asm_rewrite_tac[]) >>
     `op_taint tn (Var input) = {}` by
       (qpat_assum `abi_decode_ptr_window G tn s input _ _` mp_tac >>
        pure_rewrite_tac[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
          bodyPtrDefsTheory.ptr_covers_def] >> strip_tac >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >>
     qpat_assum `!x. not_fresh_at loop_body x ==> _` drule >> simp[]) >>
  `(^guarded_to_buf_entry) child_dst child_src MLOAD (Var input) hi ei env sf ty tv
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected)
    child returned u Gu tnu (d+32+j*msz)` by
    (qpat_assum `(\st s'' G tn. _) child u Gu tnu`
       (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
     BETA_TAC >> asm_rewrite_tac[] >>
     qpat_assum `msz = type_memory_size tv` (fn th => rewrite_tac[GSYM th]) >>
     conj_tac >- (qexistsl_tac [`q`,`h`] >> asm_rewrite_tac[] >>
       rpt strip_tac >>
       qpat_assum `q + asz <= h` mp_tac >>
       qpat_assum `asz = abi_member_head_size _` (fn th => rewrite_tac[th])) >>
     conj_tac >- (qexists_tac `H` >> asm_rewrite_tac[]) >>
     conj_tac >- (qexists_tac `child_ptr` >>
       pure_rewrite_tac[SUB_EQUAL_0, ADD_CLAUSES] >>
       conj_tac >- REFL_TAC >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
       first_assum MATCH_ACCEPT_TAC) >>
     conj_tac >- (qexistsl_tac [`q`,`h`] >> asm_rewrite_tac[]) >>
     conj_tac >-
       (qpat_assum `abi_decoder_operand_live loop_body.cs_next_var hi` mp_tac >>
        qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
     `j*msz+msz <= n*msz` by
       (qpat_assum `j<n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        once_rewrite_tac[MULT_COMM] >> once_rewrite_tac[ADD_COMM] >>
        rewrite_tac[GSYM MULT_SUC, LE_MULT_LCANCEL] >> decide_tac) >>
     conj_tac >- (simp[]) >> conj_tac >- rewrite_tac[LESS_EQ_REFL] >>
     conj_tac >-
       (qpat_assum `d+32+n*msz <= output_base+output_cap` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     conj_tac >-
       (qpat_assum `w2n input_word + LENGTH input_bytes <= d \/ _` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     conj_tac >-
       (qpat_assum `EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\ _) live` mp_tac >>
        qpat_assum `cell+32 <= d \/ _` mp_tac >>
        qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < child.cs_next_id /\ _) (_::live)` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[EVERY_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >>
        rpt strip_tac >>
        rpt (first_x_assum (drule_then strip_assume_tac)) >>
        asm_rewrite_tac[] >> decide_tac) >>
     qpat_assum `EVERY (\(a,bytes). a+LENGTH bytes <= d \/ _) protected` mp_tac >>
     qpat_assum `j*msz+msz <= n*msz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  qpat_x_assum `(\dst src opc base_op hi info. _) child_dst child_src MLOAD (Var input) hi ei`
    (fn ih => qpat_assum `(\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d. _)
       child_dst child_src MLOAD (Var input) hi ei env sf ty tv _ _ child returned u Gu tnu _`
       (mp_tac o MATCH_MP (BETA_RULE ih) o BETA_RULE)) >>
  reverse strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`,`G'`,`tn'`] >>
      qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
      qpat_assum `!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _` mp_tac >>
      qpat_assum `r = Abort _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  `(^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) returned t G' tn'` by
    (BETA_TAC >> asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[]) >>
  drule abi_decode_loop_body_pop >>
  disch_then (qspecl_then [`s`,`msz`,`j`] mp_tac) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >>
  strip_tac >>
  `eval_operand (Var iv) t = SOME (n2w j) /\
   op_prov G' (Var iv) = NONE /\ op_taint tn' (Var iv) = {}` by
    (qpat_assum `!x. not_fresh_at child x ==> _`
       (qspec_then `iv` mp_tac) >>
     qpat_assum `abi_decoder_operand_live child.cs_next_var idx` mp_tac >>
     qpat_assum `eval_operand idx u = SOME (n2w j)` mp_tac >>
     qpat_assum `op_prov Gu idx = NONE` mp_tac >>
     qpat_assum `op_taint tnu idx = {}` mp_tac >>
     qpat_assum `idx = Var iv` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def, op_prov_def] >> metis_tac[]) >>
  `t.vs_labels = u.vs_labels` by
    (qpat_assum `!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _` mp_tac >>
     qpat_assum `V H` mp_tac >> qpat_assum `r = OK t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `!x. not_fresh_at anchor x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at child x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at loop_body x ==> _` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >>
     rpt strip_tac >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell` by
    (qpat_assum `!name b k. local_region ce es.scopes s name b k ==> cell+32 <= b \/ b+k <= cell` mp_tac >>
     qpat_assum `!x. not_fresh_at anchor x ==> _` mp_tac >>
     qpat_assum `local_ptrs_reserved ce anchor` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `local_region ce es.scopes s name b k` by
       (gvs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `local_ptrs_rel fn ce es.scopes t` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
       (qspec_then `H` mp_tac) >>
     qpat_assum `V H` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
  qabbrev_tac `snapshots =
    (w2n input_word,input_bytes)::
    (d,mem_bytes_at d (32+j*msz) s.vs_memory)::
    (MAP (\(id,p,b,k,bytes). (b,bytes)) live ++ protected)` >>
  `EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) snapshots` by
    (simp[Abbr `snapshots`, EVERY_DEF, EVERY_APPEND, EVERY_MAP,
       LENGTH_mem_bytes_at] >>
     conj_tac >-
       (qpat_assum `cell+32 <= d \/ _` mp_tac >>
        qpat_assum `j<n` mp_tac >> qpat_assum `msz = type_memory_size tv` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        gvs[] >> `j*type_memory_size tv <= n*type_memory_size tv` by simp[] >> decide_tac) >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). id <> aid /\ _) live` mp_tac >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). _ /\ FLOOKUP s.vs_allocas id = SOME (b,k) /\ _) live` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots` by
    (simp[Abbr `snapshots`, EVERY_DEF, EVERY_APPEND, EVERY_MAP,
       LENGTH_mem_bytes_at] >>
     qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) (_::protected)` mp_tac >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). _ /\ FLOOKUP t.vs_allocas id = SOME (b,k) /\ _) (_::live)` mp_tac >>
     qpat_assum `msz = type_memory_size tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  drule_at (Pat `eval_operand (Var iv) s = SOME (n2w j)`) abi_decode_loop_backedge_joint >>
  FAIL_TAC "backedge premises"
QED
