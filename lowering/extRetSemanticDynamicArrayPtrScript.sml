Theory extRetSemanticDynamicArrayPtr
Ancestors
  extRetDynamicExitPtr extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr
  extRetDynamicArrayPhasePtr extRetDynamicArrayInitFramePtr
  extRetDynamicArrayEntryPtr extRetDynamicArrayCountPtr
  extRetSemanticDynamicLoopPtr abiEncoderArrayLoopLayout
  abiEncoderArrayHeader fragGasSeqPtr extRetRecursiveResourcePtr
  extRetScratchResourcePtr extRetFramedChildPtr extRetDynamicBodyPtr
  extRetRecursiveFramePtr robustCopyTransportPtr valueEncodingProps
  allocaSiteResource extRetScratchInitPtr fragGasPathPtr fragExec
  emitHelperProps exprLoweringProps emitHelper compileEnv
  loweringStateRelDefs bodyPtrDefs ptrDiscipline venomState
  venomExecSemantics venomMemDefs venomMemProps valueEncoding words
  finite_map pred_set arithmetic

(* The final four instructions of the outer array encoder.  The parent
   cursor is local scratch, initialized to zero before the array loop. *)
Theorem encoder_dynamic_parent_finish_counted_ptr:
  emit_op MLOAD [Var parent] sa = (Var old,sb) /\
  emit_op ADD [Var old;Var encoded] sb = (Var sumv,sc) /\
  emit_void MSTORE [Var parent;Var sumv] sc = ((),sd) /\
  emit_op MLOAD [Var parent] sd = (Var out,se) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa parent /\ not_fresh_at sa encoded /\
  lookup_var parent s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn parent s 32 /\ mload p s = 0w /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  lookup_var encoded s = SOME (n2w n) /\ op_taint tn (Var encoded) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w n) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore p (n2w n) s).vs_memory /\
    (!i. i < p \/ p+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `(!v. not_fresh_at sa v ==> not_fresh_at sb v) /\
   (!v. not_fresh_at sb v ==> not_fresh_at sc v) /\
   (!v. not_fresh_at sc v ==> not_fresh_at sd v)` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def,
         not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!i. w2n (n2w p : bytes32) <= i /\
     i < w2n (n2w p : bytes32)+32 ==> i NOTIN tn.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var old) sf = SOME 0w /\
   eval_operand (Var encoded) sf = SOME (n2w n) /\
   op_taint tnf (Var encoded) = {}` by
    simp[eval_operand_def, w2n_n2w, LESS_MOD] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `lookup_var parent sf' = SOME (n2w p) /\
   ptr_covers Gf' tnf' parent sf' 32 /\
   eval_operand (Var sumv) sf' = SOME (n2w n)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var parent sf'' = SOME (n2w p) /\
   ptr_covers Gf' tnf'' parent sf'' 32 /\
   mload p sf'' = n2w n /\
   (!i. w2n (n2w p : bytes32) <= i /\
     i < w2n (n2w p : bytes32)+32 ==> i NOTIN tnf''.t_mem)` by
    (gvs[ptr_covers_def, w2n_n2w, LESS_MOD] >>
     metis_tac[mload_def, mload_mstore_same]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf'' (OK sf'')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  qexistsl_tac [`Gf''`,`tnf'''`,`sf'''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf''`,`tnf''`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

(* The initializer ends before the first JMP, rather than at the header.
   Recover that edge from the actual compiled header's code boundary. *)
Theorem encoder_dynamic_initial_jump_counted_ptr:
  abi_encode_array_header ip count_op sh = ((hdr,body_lbl,exit_lbl),sa) /\
  fn_has_code sh sa fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sh.cs_current_bb /\
  s.vs_inst_idx = LENGTH sh.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to hdr s))
Proof
  strip_tac >> drule_all abi_encode_array_header_code >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block sh.cs_current_bb fn.fn_blocks = SOME bb` >>
  qabbrev_tac `sj = sh with cs_current_insts := bb.bb_instructions` >>
  `fn_has_code sh sj fn` by
    (simp[fn_has_code_def, Abbr `sj`, emitted_blocks_def] >>
     qexists_tac `bb` >> simp[Abbr `bb`]) >>
  irule emit_jump_path_ptr >> simp[allocas_from_def] >>
  qexistsl [`sh`,`sj`] >> simp[Abbr `sj`, Abbr `bb`]
QED

(* Run the real initialization and its entry edge together.  The same
   witnesses retain the exact memory, allocation and ambient frames. *)
Theorem encoder_dynamic_init_to_header_counted_ptr:
  abi_encode_array_dynamic_init count_op 32 si = ((Var ip,Var cursor),sh) /\
  abi_encode_array_header (Var ip) count_op sh = ((hdr,body_lbl,exit_lbl),sa) /\
  fn_has_code si sh fn /\ fn_has_code sh sa fn /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  si.cs_next_id IN sites /\ si.cs_next_id+2 IN sites /\
  eval_operand count_op s = SOME (n2w N) /\ op_taint tn count_op = {} /\
  (!v. count_op = Var v ==> not_fresh_at si v) ==>
  ?p c Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w p) /\ ptr_covers Gf tnf ip sf 32 /\
    lookup_var cursor sf = SOME (n2w c) /\ ptr_covers Gf tnf cursor sf 32 /\
    p+32 < dimword(:256) /\ c+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas si.cs_next_id = SOME (p,32) /\
    FLOOKUP sf.vs_allocas (si.cs_next_id+2) = SOME (c,32) /\
    mload p sf = 0w /\ mload c sf = n2w (32*N) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem) /\
    (!i. c <= i /\ i < c+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (a,sz)) /\
    mem_agree_outside ({i | p <= i /\ i < p+32} UNION
      {i | c <= i /\ i < c+32}) sf.vs_memory s.vs_memory /\
    (!i. ~(p <= i /\ i < p+32) /\ ~(c <= i /\ i < c+32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at si v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >> drule_all abi_array_dynamic_init_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG Gf tnf sf 0 Gf tnf (OK (jump_to hdr sf))` by
    (irule encoder_dynamic_initial_jump_counted_ptr >> metis_tac[]) >>
  qexistsl [`ia`,`ca`,`Gf`,`tnf`,`jump_to hdr sf`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `encoder_resource ctx fn sites q len protected (jump_to hdr sf)` by
    (irule encoder_resource_fields >> qexists_tac `sf` >> simp[jump_to_def]) >>
  `mload ca sf = n2w (32*N)` by metis_tac[MULT_COMM] >>
  fs[lookup_var_def, mload_def, ptr_covers_def, encoder_ambient_frame_def] >>
  asm_simp_tac (srw_ss()) [jump_to_def, lookup_var_def, mload_def,
                         ptr_covers_def, encoder_ambient_frame_def] >>
  fs[jump_to_def] >> metis_tac[]
QED

Theorem encoder_dynamic_initialized_entry_counted_ptr:
  abi_encode_array_dynamic_init (Var cv) 32 si = ((Var ip,Var cursor),sh) /\
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sa) /\
  fn_has_code si sh fn /\ fn_has_code sh sa fn /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites a scap protected s /\
  si.cs_next_id IN sites /\ si.cs_next_id+2 IN sites /\
  not_fresh_at si src /\ not_fresh_at si dst /\ not_fresh_at si cv /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  lookup_var cv s = SOME (n2w N) /\
  ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  val_wf tv v /\ val_footprint tv v <= scap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem) /\
  MEM (did,dbase,dsize) protected /\ dbase <= b /\ b+dcap <= dbase+dsize /\
  32 <= dcap /\ (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) ==>
  ?p c Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\
    encoder_dynamic_loop_inv ctx fn sites protected
      ip cursor src dst cv p c a b scap dcap tv v N ns 0 Gf tnf sf /\
    encoder_dynamic_effect si sites b dcap G tn s Gf tnf sf /\
    FLOOKUP sf.vs_allocas si.cs_next_id = SOME (p,32) /\
    FLOOKUP sf.vs_allocas (si.cs_next_id+2) = SOME (c,32) /\
    p+32 < dimword(:256) /\ c+32 < dimword(:256) /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w N) /\
   (!x. Var cv = Var x ==> not_fresh_at si x)` by simp[eval_operand_def] >>
  drule_all encoder_dynamic_init_to_header_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `mem_agree_outside writes sf.vs_memory s.vs_memory` >>
  `!i. a <= i /\ i < a+val_footprint tv v ==> i NOTIN writes` by
    (qpat_assum `encoder_resource ctx fn sites a scap protected sf` mp_tac >>
     pure_rewrite_tac [encoder_resource_def, scratch_resource_def] >> strip_tac >>
     gen_tac >> strip_tac >> `scap <> 0` by decide_tac >>
     `regions_disjoint (a,scap) (p,32) /\ regions_disjoint (a,scap) (c,32)` by
       metis_tac[] >>
     qpat_x_assum `regions_disjoint (a,scap) (p,32)` mp_tac >>
     qpat_x_assum `regions_disjoint (a,scap) (c,32)` mp_tac >>
     simp_tac (srw_ss()) [regions_disjoint_def, Abbr `writes`] >> decide_tac) >>
  `!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (simp[Abbr `writes`] >> metis_tac[]) >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==> val_in_memory tv v a mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl [`s.vs_memory`,`sf.vs_memory`,`tn.t_mem`,`tnf.t_mem`,`writes`] >>
     simp[mem_agree_outside_def] >> metis_tac[mem_agree_outside_def]) >>
  `lookup_var src sf = SOME (n2w a) /\ lookup_var dst sf = SOME (n2w b) /\
   lookup_var cv sf = SOME (n2w N) /\ op_taint tnf (Var cv) = {} /\
   op_prov Gf (Var cv) = NONE /\ ptr_covers Gf tnf src sf scap /\
   ptr_covers Gf tnf dst sf dcap` by
    (qpat_assum `!v. not_fresh_at si v ==> _` (qspec_then `src` mp_tac) >>
     qpat_assum `!v. not_fresh_at si v ==> _` (qspec_then `dst` mp_tac) >>
     qpat_assum `!v. not_fresh_at si v ==> _` (qspec_then `cv` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[ptr_covers_def, op_prov_def]) >>
  `encoder_dynamic_loop_inv ctx fn sites protected
     ip cursor src dst cv p c a b scap dcap tv v N ns 0 Gf tnf sf` by
    (irule encoder_dynamic_loop_inv_init >> simp[]) >>
  `writes SUBSET encoder_write_envelope sites sf b dcap` by
    (simp[SUBSET_DEF, Abbr `writes`, encoder_write_envelope_def,
          encoder_scratch_span_def] >> metis_tac[]) >>
  `encoder_dynamic_effect si sites b dcap G tn s Gf tnf sf` by
    (irule encoder_dynamic_effect_from_footprint >> metis_tac[]) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN writes` by
    (drule_all encoder_resource_protected >>
     pure_rewrite_tac [scratch_resource_def] >> strip_tac >>
     `dsize <> 0` by decide_tac >>
     `regions_disjoint (dbase,dsize) (p,32) /\
      regions_disjoint (dbase,dsize) (c,32)` by metis_tac[] >>
     qpat_x_assum `regions_disjoint (dbase,dsize) (p,32)` mp_tac >>
     qpat_x_assum `regions_disjoint (dbase,dsize) (c,32)` mp_tac >>
     simp_tac (srw_ss()) [regions_disjoint_def, Abbr `writes`] >> decide_tac) >>
  qexistsl [`p`,`c`,`Gf`,`tnf`,`sf`] >> simp[] >> metis_tac[]
QED
