(* Preserve an enclosing encoder's clean cursor across the actual inner loop. *)
Theory extRetAbiArrayParentPtr
Ancestors
  extRetAbiArrayStaticCountedPtr abiBuiltinAllocation abiEncoder
  bodyPtrDefs fragGasPathPtr fragExec compileEnv venomState ptrDiscipline
  valueEncodingProps valueEncodingProofs words finite_map list pred_set arithmetic

Theorem compile_abi_encode_dyn_static_loop_parent_counted_ptr:
  compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei asz msz (Var cv) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  lookup_var cv s = SOME (n2w (LENGTH avs)) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) (w2n a) scap mem') /\
  mem_bytes_at (w2n b) 32 s.vs_memory = header /\ LENGTH header = 32 /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= dcap /\
  32+LENGTH avs*asz <= dcap /\ LENGTH avs < dimword(:256) /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id = SOME (addr,32) /\
  addr+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
  not_fresh_at sa parent_dyn_ptr /\ lookup_var parent_dyn_ptr s = SOME q /\
  ptr_covers G tn parent_dyn_ptr s 32 /\
  (!i. w2n q <= i /\ i < w2n q+32 ==> i NOTIN tn.t_mem) /\
  DISJOINT {i | w2n q <= i /\ i < w2n q+32}
    ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32}) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\ sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+LENGTH avs*asz)) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) sf.vs_memory = header ++ FLAT (MAP (enc ty) avs) /\
    (!i. w2n b <= i /\ i < w2n b+32+LENGTH avs*asz ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) (w2n a) scap mem') /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    (!site region. FLOOKUP s.vs_allocas site = SOME region ==>
      FLOOKUP sf.vs_allocas site = SOME region) /\
    mem_agree_outside
      ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | addr <= i /\ i < addr+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
      {i | addr <= i /\ i < addr+32}) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    lookup_var parent_dyn_ptr sf = SOME q /\ ptr_covers Gf tnf parent_dyn_ptr sf 32 /\
    mload (w2n q) sf = mload (w2n q) s /\
    (!i. w2n q <= i /\ i < w2n q+32 ==> i NOTIN tnf.t_mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_abi_encode_dyn_static_loop_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var parent_dyn_ptr sf = SOME q /\
   ptr_covers Gf tnf parent_dyn_ptr sf 32` by
    (qpat_assum `!x. not_fresh_at sa x ==> _`
       (qspec_then `parent_dyn_ptr` mp_tac) >>
     asm_simp_tac bool_ss [] >>
     qpat_x_assum `ptr_covers G tn parent_dyn_ptr s 32` mp_tac >>
     simp_tac bool_ss [ptr_covers_def] >> asm_simp_tac bool_ss []) >>
  `!i. w2n q <= i /\ i < w2n q+32 ==>
    i NOTIN ({i | w2n b <= i /\ i < w2n b+dcap} UNION
      {i | addr <= i /\ i < addr+32})` by
    (qpat_x_assum `DISJOINT _ _` mp_tac >> simp_tac (srw_ss()) [DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `!i. w2n q <= i /\ i < w2n q+32 ==> i NOTIN tnf.t_mem` by metis_tac[] >>
  `mem_bytes_at (w2n q) 32 sf.vs_memory = mem_bytes_at (w2n q) 32 s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (w2n q+x) 1 sf.vs_memory = mem_bytes_at (w2n q+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ sf.vs_memory _` mp_tac >>
        simp_tac bool_ss [mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        first_x_assum irule >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[] >>
  qpat_x_assum `mem_bytes_at (w2n q) 32 sf.vs_memory = _` mp_tac >>
  simp[valueEncodingTheory.mem_bytes_at_def, mload_def, read_memory_def]
QED
