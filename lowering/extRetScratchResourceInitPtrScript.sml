(* Scratch initialization threads physical resources through allocation and store,
   including registered-site reuse, independently of semantic state relations. *)
Theory extRetScratchResourceInitPtr
Ancestors
  extRetScratchResourcePtr extRetScratchInitPtr extRetAbiArrayInitPtr
  allocaSiteResource allocaFootprint abiBuiltinAllocation allocationPtr
  localPtrsProps loweringHalt fragExecPtr fragGasPathPtr fragGasSeqPtr
  exprLoweringProps compileEnv emitHelper context codegenRel loweringPosts
  ptrDiscipline bodyPtrDefs venomState venomInst venomExecSemantics
  venomMemProps venomMemDefs valueEncodingProps words finite_map pred_set
  arithmetic list rich_list emitHelperProps fragExec extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr typedCopyPtr

Theorem scratch_resource_allocate_state[local]:
  scratch_resource ctx fn sites q len s /\ id IN sites /\
  MEM (mk_inst id ALLOCA [Lit 32w] [ip]) (fn_insts fn) ==>
  ?addr. scratch_resource ctx fn sites q len (abi_builtin_allocate_state id 32 s) /\
    FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id = SOME (addr,32) /\
    addr+32 < dimword(:256) /\
    s.vs_alloca_next <= (abi_builtin_allocate_state id 32 s).vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> venomMemDefs$regions_disjoint (q,len) (addr,32))
Proof
  strip_tac >>
  `?t addr. exec_alloca (mk_inst id ALLOCA [Lit 32w] [ip]) s (32w:bytes32) = OK t /\
    scratch_resource ctx fn sites q len t /\
    FLOOKUP t.vs_allocas id = SOME (addr,32) /\
    lookup_var ip t = SOME (n2w addr) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> venomMemDefs$regions_disjoint (q,len) (addr,32))` by
    (mp_tac (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit 32w] [ip]`, `out` |-> `ip`]
       scratch_resource_alloca) >> simp[mk_inst_def] >> strip_tac >>
     qexistsl_tac [`t`, `b`] >> simp[]) >>
  `t.vs_allocas = (abi_builtin_allocate_state id 32 s).vs_allocas /\
   t.vs_alloca_next = (abi_builtin_allocate_state id 32 s).vs_alloca_next` by
    (Cases_on `FLOOKUP s.vs_allocas id` >>
     gvs[exec_alloca_def, mk_inst_def, abi_builtin_allocate_state_def,
         update_var_def, AllCaseEqs(), dimword_def]) >>
  qexists_tac `addr` >>
  `scratch_resource ctx fn sites q len (abi_builtin_allocate_state id 32 s)` by
    (irule scratch_resource_fields >> qexists_tac `t` >> simp[]) >>
  `addr+32 < dimword(:256)` by
    (`alloca_inv t` by
       (qpat_x_assum `scratch_resource _ _ _ _ _ t` mp_tac >>
        simp_tac std_ss [scratch_resource_def]) >>
     `alloca_room ctx fn t` by
       (qpat_x_assum `scratch_resource _ _ _ _ _ t` mp_tac >>
        simp_tac std_ss [scratch_resource_def]) >>
     drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Theorem scratch_word_init_resource_counted_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ scratch_resource ctx fn sites q source_len s /\
  sa.cs_next_id IN sites /\ eval_operand init s = SOME w /\ op_taint tn init = {} /\
  (!v. init = Var v ==> not_fresh_at sa v) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    mload addr sf = w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    scratch_resource ctx fn sites q source_len sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (source_len <> 0 ==> venomMemDefs$regions_disjoint (q,source_len) (addr,32)) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    alloca_inv sf /\ sf.vs_labels = s.vs_labels /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (buf.buf_operand,sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `?ip. buf.buf_operand = Var ip /\
    sm.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
     qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> gvs[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]) (fn_insts fn)` by
    (qpat_x_assum `fn_has_code sa sm fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]) bb.bb_instructions` by
       gvs[IS_PREFIX_APPEND] >> metis_tac[lookup_block_fn_insts]) >>
  drule_all scratch_resource_allocate_state >> strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (Var ip,sm)` by simp[] >>
  drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `scratch_resource ctx fn sites q source_len sf` by
    (irule scratch_resource_fields >>
     qexists_tac `abi_builtin_allocate_state sa.cs_next_id 32 s` >> simp[]) >>
  `eval_operand init sf = SOME w /\ op_taint tnf init = {}` by
    (Cases_on `init` >> gvs[eval_operand_def, op_taint_def]) >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  gvs[] >> drule_all scratch_store_state_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`addr`, `Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> metis_tac[]) >>
  `addr < dimword(:256)` by decide_tac >>
  `sf'.vs_allocas = sf.vs_allocas /\ sf'.vs_alloca_next = sf.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  `scratch_resource ctx fn sites q source_len sf'` by
    (irule scratch_resource_fields >> qexists_tac `sf` >> simp[]) >>
  `alloca_inv sf'` by
    (qpat_x_assum `scratch_resource _ _ _ _ _ sf'` mp_tac >>
     simp_tac std_ss [scratch_resource_def]) >>
  `sf'.vs_memory = (mstore addr w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  `mload addr sf' = w` by
    (qspecl_then [`addr`, `w`, `s`] mp_tac mload_mstore_same >> simp[mload_def]) >>
  `mem_agree_outside {i | addr <= i /\ i < addr+32} sf'.vs_memory s.vs_memory` by
    metis_tac[mstore_memory_frame] >>
  `ptr_covers Gf tnf' ip sf' 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[] >>
  simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  metis_tac[]
QED
