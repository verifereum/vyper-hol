(* Code installation for the stopped observer used by staged memory stores. *)
Theory entryStageStoreObserverCode
Ancestors
  createSizeTypedCopyCode createSizeCutCode createSizeCutRegion typedCopyGasOps pair
  fragObserverCodeProps exprSimAbiGasBridge externalEntryShape
  exprSimAbiEncodeObliviousCode
  context compileEnv emitHelper fragExec fragFuel venomInst venomExecSemantics
  venomExecProofs exprLoweringProps loweringShapeDefs list rich_list arithmetic

val store_ops = ``[ADD; MLOAD; AND; MCOPY; NOT; MSTORE; INVALID; ASSIGN; JMP;
                    LT; ISZERO; JNZ; MUL; GT; ASSERT]``;

Theorem stage_store_opcode_inventory[local]:
  compile_store_memory ce (Var xs) (Var xd) dt st a = ((),b) /\
  ~is_word_type dt /\ (is_bytestring_type dt ==> is_bytestring_type st) ==>
  EVERY (\i. MEM i.inst_opcode ^store_ops) (frag_code a b)
Proof
  strip_tac >>
  `!ce dst dt src st.
     code_action (\opc. MEM opc ^store_ops) (compile_store_memory_typed ce dst dt src st)` by
    (qspec_then `\opc. MEM opc ^store_ops` mp_tac typed_copy_code_family >> simp[]) >>
  `!n. code_action (\opc. MEM opc ^store_ops) (compile_copy_memory (Var xd) (Var xs) n)` by
    (Cases >> simp[compile_copy_memory_def, code_action_return, code_action_emit_void]) >>
  `compile_store_memory_typed ce (Var xd) dt (Var xs) st a = ((),b) \/
   compile_copy_memory (Var xd) (Var xs) (type_memory_bytes ce dt) a = ((),b)` by
    (Cases_on `is_bytestring_type dt`
     >- (`is_bytestring_type st` by metis_tac[] >>
         disj1_tac >> fs[compile_store_memory_def] >>
         asm_simp_tac (srw_ss()) [Once compile_store_memory_typed_def]) >>
     qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_def] >> IF_CASES_TAC >> simp[]) >>
  fs[code_action_def] >>
  first_x_assum drule >> simp[code_step_def]
QED

Theorem stage_observer_end_fresh[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) ==>
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b))
Proof
  simp[all_blocks_def, MAP_REVERSE, ALL_DISTINCT_APPEND, MEM_REVERSE, MEM_MAP] >>
  metis_tac[emitted_blocks_def, MEM_TAKE]
QED

Theorem stage_observer_label_layout[local]:
  cs_extends a b /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) /\
  MEM l (added_labels a b) ==>
  l <> a.cs_current_bb /\
  (l = b.cs_current_bb \/ MEM l (MAP (\bb. bb.bb_label) (emitted_blocks a b)))
Proof
  strip_tac >>
  `~MEM a.cs_current_bb (added_labels a b)` by
    (drule cs_extends_labels >> strip_tac >>
     gvs[ALL_DISTINCT_APPEND, all_blocks_def] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `cs_extends a b` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  drule emitted_blocks_append >> strip_tac >>
  Cases_on `new = []`
  >- gvs[added_labels_def, all_blocks_def, DROP_LENGTH_TOO_LONG] >>
  `?front last. new = front ++ [last]` by metis_tac[APPEND_FRONT_LAST] >>
  gvs[added_labels_def, all_blocks_def, REVERSE_APPEND, MAP_APPEND, MAP_REVERSE,
      DROP_LENGTH_APPEND, DROP_APPEND, LENGTH_MAP, MEM_REVERSE,
      DROP_LENGTH_TOO_LONG, DECIDE ``x - (y + x) = 0n``, ADD1] >>
  metis_tac[]
QED

Theorem stage_observer_fetch_agreement[local]:
  fn_has_code a b f /\
  (lbl,idx) <> frag_observer_cut b /\
  lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME i ==>
  ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i
Proof
  strip_tac >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `idx < LENGTH b.cs_current_insts` by
        (fs[get_instruction_def, frag_observer_cut_def] >> decide_tac) >>
      fs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem stage_observer_fetch_region[local]:
  cs_extends a b /\ fn_has_code a b obs /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b /\
  lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (s.vs_current_bb = b.cs_current_bb ==> s.vs_inst_idx <= LENGTH b.cs_current_insts) ==>
  create_cut_region a b s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `s.vs_current_bb = b.cs_current_bb`
  >- (simp[create_cut_region_def] >>
      strip_tac >> drule frag_extends_emitted_shape >>
      fs[frag_observer_region_def] >> metis_tac[]) >>
  `MEM bb (emitted_blocks a b)` by
    (fs[frag_observer_region_def, MEM_MAP, fn_has_code_def] >> gvs[] >>
     first_x_assum drule >> simp[]) >>
  `emitted_blocks a b <> []` by (strip_tac >> gvs[]) >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> decide_tac) >>
  Cases_on `bb = LAST (emitted_blocks a b)`
  >- (simp[create_cut_region_def] >> disj1_tac >>
      drule frag_extends_emitted_shape >> simp[] >>
      fs[frag_observer_region_def] >> metis_tac[lookup_block_label]) >>
  simp[create_cut_region_def] >> disj2_tac >> qexists_tac `bb` >> simp[] >>
  `emitted_blocks a b = FRONT (emitted_blocks a b) ++ [LAST (emitted_blocks a b)]` by
    simp[APPEND_FRONT_LAST] >>
  conj_tac >- metis_tac[MEM_APPEND, MEM] >>
  metis_tac[lookup_block_label]
QED

Theorem stage_store_observer_code:
  compile_store_memory ce (Var xs) (Var xd) dt st a = ((),b) /\
  ~is_word_type dt /\ (is_bytestring_type dt ==> is_bytestring_type st) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\ no_phi_fn f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) ==>
  ?id. (!i. MEM i (fn_insts f) ==> i.inst_id <> id) /\
    fn_has_code a b (frag_observer a b f id) /\
    fn_inst_ids_distinct (frag_observer a b f id) /\
    no_phi_fn (frag_observer a b f id) /\
    create_cut_code {} a b /\
    (a.cs_current_bb,LENGTH a.cs_current_insts) IN frag_observer_region a b /\
    (!lbl idx bb i. (lbl,idx) IN frag_observer_region a b /\
       (lbl,idx) <> frag_observer_cut b /\
       lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
       get_instruction bb idx = SOME i ==>
       MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\
       MEM i.inst_opcode ^store_ops /\
       ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i) /\
    (!i l. MEM i (frag_code a b) /\
       MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
       l <> a.cs_current_bb /\ (l,0) IN frag_observer_region a b /\
       ?bb real. lookup_block l (frag_observer a b f id).fn_blocks = SOME bb /\
                 lookup_block l f.fn_blocks = SOME real /\
                 phi_prefix_length bb.bb_instructions = 0 /\
                 phi_prefix_length real.bb_instructions = 0)
Proof
  strip_tac >>
  `create_cut_code {} a b` by metis_tac[create_store_memory_cut_code, SND] >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b))` by
    metis_tac[stage_observer_end_fresh] >>
  qspecl_then [] strip_assume_tac (Q.INST [`fn` |-> `f`] frag_observer_fresh_id) >>
  qexists_tac `id` >>
  `fn_has_code a b (frag_observer a b f id)` by metis_tac[reject_observer_has_code] >>
  `fn_inst_ids_distinct (frag_observer a b f id)` by
    metis_tac[frag_observer_ids_distinct_from_labels] >>
  `no_phi_fn (frag_observer a b f id)` by metis_tac[abi_dyn_observer_no_phi] >>
  simp[frag_observer_start_region] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qabbrev_tac `s = ARB with <|vs_current_bb := lbl; vs_inst_idx := idx|>` >>
      `lbl = b.cs_current_bb ==> idx <= LENGTH b.cs_current_insts` by
        (strip_tac >> gvs[frag_observer_cut_lookup, get_instruction_def, AllCaseEqs()]) >>
      `create_cut_region a b s` by
        (irule stage_observer_fetch_region >> simp[Abbr `s`] >> metis_tac[]) >>
      `MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b` by
        (qpat_assum `fn_has_code a b (frag_observer a b f id)`
           (mp_then (Pat `fn_has_code _ _ _`) mp_tac create_cut_region_rules) >>
         simp[] >>
         disch_then (qspecl_then [`s`, `bb`, `i`] mp_tac o cj 2) >>
         fs[Abbr `s`, frag_observer_cut_def]) >>
      drule_all stage_store_opcode_inventory >> simp[EVERY_MEM] >>
      metis_tac[stage_observer_fetch_agreement]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM l (added_labels a b)` by (fs[create_cut_code_def] >> metis_tac[]) >>
  drule_all stage_observer_label_layout >> strip_tac >>
  simp[frag_observer_region_def] >>
  `(?blk. MEM blk (emitted_blocks a b) /\ blk.bb_label = l) \/ l = b.cs_current_bb` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `!fn. no_phi_fn fn ==> !blk. lookup_block l fn.fn_blocks = SOME blk ==>
                              phi_prefix_length blk.bb_instructions = 0` by
    (simp[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED
