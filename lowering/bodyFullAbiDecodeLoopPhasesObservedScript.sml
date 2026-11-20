Theory bodyFullAbiDecodeLoopPhasesObserved
Ancestors
  bodyFullAbiDecodeLoopBackedge bodyFullAbiDecodeInputOrigin
  abiDecoderHeaderGasPath fragExec pred_set words finite_map venomState
  bodyFullAbiDecodeLoopHeaderExact bodyFullAbiDecodeLoopSetupExact
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

val input_origin = ``\s.
  (?aid ib isz.
     aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
     ib <= w2n (input_word:256 word) /\ w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
  (?name ib isz.
     local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz)``;

(* Keep the HeaderExact witnesses; only the input-origin frame is new. *)
Theorem abi_decode_loop_header_observed:
  emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
  compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
  emit_op MLOAD [addr] sc = (count_op,sd) /\
  emit_op LT [Var idx;count_op] sd = (lt,se) /\
  emit_op ISZERO [lt] se = (done,sf) /\
  emit_inst JNZ [done;Label exit_lbl;Label body_lbl] [] sf = ((),sg) /\
  fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ sa.cs_current_insts = [] /\
  s.vs_inst_idx = 0 /\ allocas_from lo s /\
  (^owned_decoder_state) live protected sa s G tn /\
  not_fresh_at sa input /\ not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  mem_word_at cell s.vs_memory = n2w j /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  cell+32 <= s.vs_alloca_next /\ cell < dimword (:256) /\
  eval_operand src s = SOME (n2w srcoff) /\ op_taint tn src = {} /\
  eval_operand hi s = SOME (n2w h) /\
  srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  mem_word_at (w2n input_word+srcoff) s.vs_memory = n2w n /\
  j <= n /\ n < dimword (:256) ==>
  (^input_origin) s ==>
  ?t Gf tnf.
    (^input_origin) t /\
    (!obs. fn_has_code sa sg obs ==> gas_path ctx obs s 0 (OK t)) /\
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) live protected sg t Gf tnf /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j = n then exit_lbl else body_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    eval_operand src t = SOME (n2w srcoff) /\
    eval_operand hi t = SOME (n2w h) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. output_base <= i /\ i < output_base+output_cap /\
       i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_loop_header_joint_exact)) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  reverse conj_tac >- (asm_rewrite_tac[] >> simp[]) >>
  irule abi_decode_input_origin_transport >> qexistsl_tac [`s`,`sa`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_decode_loop_setup_observed:
  abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD
    (Var input) hi ei asz msz sa = ((idx,child_src,child_dst),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) live protected sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w srcoff) /\
  eval_operand hi s = SOME (n2w h) /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var counter s = SOME (n2w cell) /\
  ptr_covers G tn counter s 32 /\ mem_word_at cell s.vs_memory = n2w j /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  cell+32 <= s.vs_alloca_next /\ cell < dimword (:256) /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  j<n /\ n<dimword (:256) /\ asz<dimword (:256) /\
  hi <> Lit 0w /\ srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (dec_info_needs_offset ei ==> 32 <= asz) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  abi_decoder_operand_live sa.cs_next_var (Var dst) /\
  abi_decoder_operand_live sa.cs_next_var (Var counter) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var counter) = {} /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) ==>
  (^input_origin) s ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
  (?u Gu tnu q child.
    (^input_origin) u /\
    child_dst = Var child /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gu,tnu)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) live protected sb u Gu tnu /\
    eval_operand idx u = SOME (n2w j) /\
    op_prov Gu idx = NONE /\ op_taint tnu idx = {} /\
    abi_decoder_operand_live sb.cs_next_var idx /\
    eval_operand child_src u = SOME (n2w q) /\
    q < dimword (:256) /\ q+asz <= h /\
    op_prov Gu child_src = NONE /\ op_taint tnu child_src = {} /\
    abi_decoder_operand_live sb.cs_next_var child_src /\
    eval_operand hi u = SOME (n2w h) /\
    eval_operand child_dst u = SOME (n2w (d+32+j*msz)) /\
    ptr_covers Gu tnu child u msz /\
    FLOOKUP Gu child = SOME (output_base,output_cap) /\
    op_taint tnu child_dst = {} /\
    abi_decoder_operand_live sb.cs_next_var child_dst /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    tnu.t_mem = tn.t_mem /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x)) /\
    (!name b k. local_region ce es.scopes u name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    (!i. output_base <= i /\ i < output_base+output_cap /\
       i IN tnu.t_mem ==> i IN tn.t_mem))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_loop_setup_joint_exact)) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`u`,`Gu`,`tnu`,`q`,`child`] >>
  reverse conj_tac >- (asm_rewrite_tac[] >> simp[]) >>
  irule abi_decode_input_origin_transport >> qexistsl_tac [`s`,`sa`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* The completed backedge block is shared by all compatible observers.
   Its jump does not require any facts about the observer's target block. *)
Theorem abi_decode_loop_backedge_observed:
  fn_inst_ids_distinct fn /\
  MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
  ci.inst_outputs = [counter_owner] /\ ci.inst_id = aid /\
  not_local_ptr ce es.scopes counter_owner /\
  FLOOKUP s.vs_allocas aid = SOME (cell,32) /\ lo <= cell /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < n /\ n < dimword (:256) /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) /\
  (!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
    stmt_state_rel H ctx fn ce cx es s) /\
  EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) snapshots /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) snapshots /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var counter) hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~not_fresh_at sa nv /\ not_fresh_at sa counter /\ not_fresh_at sa input /\
  origin.cs_next_var <= sa.cs_next_var /\
  cell+32 < dimword (:256) /\ cell+32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!obs. fn_has_code start end_st obs ==>
    lookup_block s.vs_current_bb obs.fn_blocks = SOME bb) ==>
  (w2n input_word+LENGTH input_bytes <= cell \/ cell+32 <= w2n input_word) ==>
  (^input_origin) s ==>
  ?t Gf tnf.
    t = jump_to hdr (mstore cell (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) /\
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!obs. fn_has_code start end_st obs ==> gas_path ctx obs s 0 (OK t)) /\
    mem_word_at cell t.vs_memory = n2w (SUC j) /\
    EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf counter t 32 /\
    DISJOINT {a | cell <= a /\ a < cell+32} tnf.t_mem /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (^input_origin) t /\
    (!i. output_base <= i /\ i < output_base+output_cap /\
       i IN tnf.t_mem ==> i IN tn.t_mem) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    (!H. V H ==>
      abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes) /\
      ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
      stmt_state_rel H ctx fn ce cx es t)
Proof
  strip_tac >> ntac 2 disch_tac >>
  drule_all abi_decode_loop_backedge_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!obs. fn_has_code start end_st obs ==> gas_path ctx obs s 0 (OK t)` by
    (rpt strip_tac >>
     `lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` by metis_tac[] >>
     `eval_operand (Var counter) s = SOME (n2w cell) /\ Var counter <> Var nv` by
       (simp[eval_operand_def] >> metis_tac[]) >>
     qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     `cell < dimword (:256)` by decide_tac >>
     `cell = w2n (n2w cell:256 word)` by simp[w2n_n2w] >>
     pop_assum SUBST1_TAC >>
     irule abi_decode_backedge_gas_path >>
     simp[] >> conj_tac >- (qexists_tac `n` >> simp[]) >>
     qexistsl_tac [`id`,`Var counter`,`iv`,`prefix`] >> simp[]) >>
  `(^input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`sa`] >> fs[] >> metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  asm_rewrite_tac[] >> fs[SUBSET_DEF]
QED
