Theory bodyFullAbiDecodeLoopResource
Ancestors
  bodyFullAbiDecodeInterface decoderGhostFramePtr exprSimMemoryTransport
  abiDecoderReentry loweringStateRelDefs ptrDiscipline words list rich_list
  finite_map arithmetic pred_set

(* Verbatim explicit-list quotations from LoopBody. *)
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

Theorem abi_decode_loop_resource_reconstruct:
  (^loop_resource) anchor j s G tn /\ j < n /\
  (^owned_decoder_state) live protected returned t Gr tnr /\
  local_ptrs_reserved ce anchor /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  abi_decoder_operand_live anchor.cs_next_var (Var dst) /\
  abi_decoder_operand_live anchor.cs_next_var (Var counter) /\
  (!x. not_fresh_at anchor x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tnu (Var x) = op_taint tn (Var x)) /\
  u.vs_labels = s.vs_labels /\
  u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
  alloca_history fn u /\ allocas_from lo u /\
  FLOOKUP t.vs_allocas aid = SOME (cell,32) /\ cell+32 <= t.vs_alloca_next /\
  mem_word_at cell u.vs_memory = n2w (SUC j) /\
  DISJOINT {a | cell <= a /\ a < cell+32} tnu.t_mem /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) u.vs_memory = bytes)
    ((w2n input_word,input_bytes)::
      (MAP (\(id,p,b,k,bytes). (b,bytes)) live ++ protected)) /\
  abi_decode_ptr_window Gu tnu u input input_word (LENGTH input_bytes) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gu tnu u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gu tnu) ==>
  (^loop_resource) anchor (SUC j) u Gu tnu
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p. not_fresh_at anchor p ==>
    lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
    op_taint tnu (Var p) = op_taint tn (Var p)` by simp[] >>
  `!p k. not_fresh_at anchor p /\ ptr_covers G tn p s k ==>
    ptr_covers Gu tnu p u k` by
    (rpt strip_tac >> irule ptr_covers_frame >> metis_tac[]) >>
  `!op. abi_decoder_operand_live anchor.cs_next_var op ==>
    eval_operand op u = eval_operand op s /\
    op_prov Gu op = op_prov G op /\ op_taint tnu op = op_taint tn op` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, venomStateTheory.eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[not_fresh_at_def, op_taint_def]) >>
  `!name b k. local_region ce es.scopes u name b k <=>
    local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `EVERY _ (_::_)` mp_tac >>
  simp[EVERY_APPEND, EVERY_MAP] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_word_at (w2n input_word+srcoff) u.vs_memory = n2w n` by
    (qpat_x_assum `mem_word_at (w2n input_word+srcoff) s.vs_memory = _`
       (fn th => rewrite_tac[GSYM th]) >>
     irule memory_window_word >>
     irule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     qexists `LENGTH input_bytes` >>
     simp[] >> decide_tac) >>
  `not_fresh_at anchor dst /\ not_fresh_at anchor counter` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       GSYM not_fresh_at_def] >>
  simp[] >> rpt conj_tac >> asm_rewrite_tac[]
  >- (simp[EVERY_MEM] >> qx_gen_tac `entry` >> strip_tac >>
      PairCases_on `entry` >>
      qpat_assum `EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\
        FLOOKUP s.vs_allocas id = SOME (b,k) /\ _) live`
        (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then drule >> simp[] >> strip_tac >>
      qpat_assum `EVERY (\(id,p,b,k,bytes). id < returned.cs_next_id /\ _) live`
        (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then drule >> simp[] >> strip_tac >>
      qpat_assum `EVERY (\(id,p,b,k,bytes). not_fresh_at anchor p) live`
        (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then drule >> simp[] >> strip_tac >>
      qpat_assum `EVERY (\x. _ (_ x)) live`
        (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then drule >> simp[] >> strip_tac >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
        (qspec_then `H` mp_tac) >> simp[])
  >- (qpat_x_assum `!p k. not_fresh_at anchor p /\ ptr_covers G tn p s k ==> _`
        irule >> simp[] >>
      qpat_x_assum `ptr_covers G tn dst s _` mp_tac >>
      simp[MULT_COMM, ADD_COMM])
  >- (qpat_x_assum `mem_word_at (w2n input_word+srcoff) u.vs_memory = _`
        mp_tac >> simp[ADD_COMM]) >>
  qpat_x_assum `DISJOINT _ tnu.t_mem` mp_tac >>
  simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED
