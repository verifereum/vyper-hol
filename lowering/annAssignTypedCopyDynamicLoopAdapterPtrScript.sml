(* Compiler-relative unequal-layout dynamic payload execution. *)
Theory annAssignTypedCopyDynamicLoopAdapterPtr
Ancestors
  annAssignTypedCopyDynamicLoopPtr annAssignTypedCopyDynamicTestPtr
  annAssignTypedCopyFixedControlPtr typedNormalizeDynarrayLoop
  typedMemoryCopy bodyPtrDefs compileEnv emitHelper fragExec exprLoweringProps
  venomState venomInst venomExecSemantics words arithmetic list rich_list

Theorem annassign_dynamic_entry_locations[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts+7) =
      SOME (mk_inst (sa.cs_next_id+7) ASSIGN [Lit 0w]
        ["%" ++ toString (sa.cs_next_var+5)]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+8) =
      SOME (mk_inst (sa.cs_next_id+8) JMP
        [Label (fresh_label_output "typed_dyn_cond" sa.cs_next_label)] [])
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  qexists_tac `initial` >> simp[get_instruction_def] >>
  conj_tac
  >- (qpat_x_assum `DROP _ initial.bb_instructions = _`
        (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_DROP]) >>
  qpat_x_assum `DROP _ initial.bb_instructions = _`
    (mp_tac o Q.AP_TERM `EL 1`) >> simp[EL_DROP, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_entry[local]:
  !ce dst dt cap src st sa sb fn s ctr cond off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME 0w /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\ typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_entry_locations >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> ctr` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var+5` mp_tac) >> simp[]) >>
  irule annassign_dynamic_entry_resources >> simp[] >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  qexists_tac `sa.cs_next_id+7` >> simp[ADD1, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_test[local]:
  !ce dst dt cap src st sa sb fn s ctr bound lt done cond body exit
    k count off size G tn ctx D PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    bound = "%" ++ toString sa.cs_next_var /\
    lt = "%" ++ toString (sa.cs_next_var+6) /\
    done = "%" ++ toString (sa.cs_next_var+7) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    body = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    exit = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    k <= count /\ count < dimword (:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = (if k<count then body else exit) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_dynarray_child_states >> strip_tac >>
  `ALL_DISTINCT [ctr;lt;done] /\ bound <> lt /\ bound <> done /\
   (!x. not_fresh_at sa x ==> x <> lt /\ x <> done)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
      ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  irule annassign_dynamic_test_resources >> simp[] >>
  qexists_tac `sa.cs_next_id+9` >>
  gvs[get_instruction_def, ADD_ASSOC]
QED

Theorem annassign_dynamic_compiler_backedge[local]:
  !sa se fn back ctr tmp cond s k off size G tn ctx D PG.
    cs_extends sa se /\ sa.cs_next_var+12 <= se.cs_next_var /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    tmp = "%" ++ toString se.cs_next_var /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = se.cs_current_insts ++
      typed_sa_backedge_insts se.cs_next_id ctr tmp cond /\
    s.vs_current_bb = se.cs_current_bb /\
    s.vs_inst_idx = LENGTH se.cs_current_insts /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    FLOOKUP G ctr = NONE ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w (k+1)) /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\ typed_copy_state_frame sa off size s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr /\ x <> tmp ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ctr <> tmp /\ (!x. not_fresh_at sa x ==> x <> ctr /\ x <> tmp)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  irule annassign_dynamic_backedge_resources >> simp[] >>
  qexists_tac `se.cs_next_id` >>
  simp[get_instruction_def, typedArrayLoopControlMemTheory.typed_sa_backedge_insts_def, EL_APPEND_EQN,
    ADD_ASSOC, ADD1]
QED
