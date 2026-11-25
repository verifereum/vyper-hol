(* Run the ordinary source window once, in the registered observer. *)
Theory entryCreateEncodeObserverRun
Ancestors
  abiEncodeValuesSource exprSimAbiEncodeRegistration exprSimAbiEncodeResources
  exprLoweringProps ptrDiscipline venomInstIdsProps list arithmetic

Theorem create_encode_observer_resources[local]:
  obs.fn_name = func.fn_name /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\
       MEM i.inst_opcode [ALLOCA; INVOKE; DALLOCA] ==> MEM i (fn_insts func)) /\
  alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) ==>
  alloca_room (ctx with ctx_functions := [obs]) obs s /\
  (ctx_has_dalloca (ctx with ctx_functions := [obs]) ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size obs s <= w2n s.vs_initial_fmp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))` by
    (irule FILTER_ALL_DISTINCT >>
     drule fn_inst_ids_distinct_all_distinct >> metis_tac[ALL_DISTINCT_MAP]) >>
  conj_tac
  >- (irule abi_encode_registered_alloca_room >> simp[] >>
      qexists_tac `func` >> simp[] >> metis_tac[MEM]) >>
  `pending_alloca_size obs s <= pending_alloca_size func s` by
    (irule abi_encode_pending_credit >> simp[]) >>
  simp[ctx_has_dalloca_def, EXISTS_MEM] >> strip_tac >>
  `MEM func ctx.ctx_functions` by
    metis_tac[alloca_room_def, venomInstTheory.lookup_function_MEM] >>
  `ctx_has_dalloca ctx` by
    (simp[ctx_has_dalloca_def, EXISTS_MEM] >> qexists_tac `func` >>
     simp[] >> metis_tac[MEM]) >>
  qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
  simp[] >> decide_tac
QED

Theorem create_encode_registered_source_window:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en obs /\ fn_inst_ids_distinct obs /\
  obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\
       MEM i.inst_opcode [ALLOCA; INVOKE; DALLOCA] ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    eval_operand out t = SOME (n2w (LENGTH bs)) /\
    window_phase (ctx with ctx_functions := [obs]) obs st en
      (window_alloca_sites obs (frag_ids st en)) [(d,LENGTH bs)] s t /\
    abi_encode_exec_frame obs s t /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) /\
      (!id b sz. id IN window_alloca_sites obs (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx with ctx_functions := [obs],obs,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all create_encode_observer_resources >> strip_tac >>
  irule abi_encode_values_source_window_input >> asm_rewrite_tac[] >>
  qexistsl_tac [`cap`, `dst`, `ei`, `sb`, `src`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `MEM inst (fn_insts func)` by (first_x_assum irule >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED
