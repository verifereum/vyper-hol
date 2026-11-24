(* Code installation for the stopped observer used by a typed IfExp store. *)
Theory entryCreateIfExpTypedObserverCode
Ancestors
  typedCopyGasOps createSizeTypedCopyCode createSizeCutCode createSizeCutRegion
  entryStageStoreObserverCode entryCreateIntervalLayout
  fragObserverCodeProps exprSimAbiGasBridge externalEntryShape
  exprSimAbiEncodeObliviousCode
  context compileEnv emitHelper fragExec fragFuel venomInst venomExecSemantics
  venomExecProofs venomState loweringShapeDefs list rich_list arithmetic pair

val typed_store_ops = ``[ADD; MLOAD; AND; MCOPY; NOT; MSTORE; INVALID; ASSIGN; JMP;
                         LT; ISZERO; JNZ; MUL; GT; ASSERT]``;

Theorem typed_store_observer_label_layout[local]:
  cs_extends a b /\ create_layout a b /\ MEM l (added_labels a b) ==>
  l <> a.cs_current_bb /\
  (l = b.cs_current_bb \/ MEM l (MAP (\bb. bb.bb_label) (emitted_blocks a b)))
Proof
  strip_tac >>
  `~MEM a.cs_current_bb (added_labels a b)` by
    (qpat_x_assum `cs_extends a b`
       (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     drule emitted_blocks_append >> strip_tac >>
     Cases_on `new = []`
     >- gvs[loweringShapeDefsTheory.added_labels_def,
            loweringShapeDefsTheory.all_blocks_def,
            DROP_LENGTH_TOO_LONG] >>
     `?front last. new = front ++ [last]` by metis_tac[APPEND_FRONT_LAST] >>
     `last.bb_label = a.cs_current_bb` by
       (gvs[LAST_APPEND_NOT_NIL]) >>
     `ALL_DISTINCT (b.cs_current_bb ::
         MAP (\bb. bb.bb_label) (emitted_blocks a b))` by
       fs[create_layout_def] >>
     gvs[loweringShapeDefsTheory.added_labels_def,
         loweringShapeDefsTheory.all_blocks_def, REVERSE_APPEND,
         MAP_APPEND, MAP_REVERSE, DROP_LENGTH_APPEND, DROP_APPEND,
         LENGTH_MAP, MEM_REVERSE, DROP_LENGTH_TOO_LONG,
         DECIDE ``x - (y + x) = 0n``, ADD1] >>
     fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `cs_extends a b`
    (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  drule emitted_blocks_append >> strip_tac >>
  Cases_on `new = []`
  >- gvs[added_labels_def, all_blocks_def, DROP_LENGTH_TOO_LONG] >>
  `?front last. new = front ++ [last]` by metis_tac[APPEND_FRONT_LAST] >>
  gvs[added_labels_def, all_blocks_def, REVERSE_APPEND, MAP_APPEND, MAP_REVERSE,
      DROP_LENGTH_APPEND, DROP_APPEND, LENGTH_MAP, MEM_REVERSE,
      DROP_LENGTH_TOO_LONG, DECIDE ``x - (y + x) = 0n``, ADD1] >>
  metis_tac[]
QED

Theorem ifexp_typed_store_observer_code:
  compile_store_memory_typed ce (Var xd) dt (Var xs) st a = ((),b) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\ no_phi_fn f /\
  create_layout a b ==>
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
       MEM i.inst_opcode ^typed_store_ops /\
       ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i) /\
    (!i l. MEM i (frag_code a b) /\
       MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
       l <> a.cs_current_bb /\ (l,0) IN frag_observer_region a b /\
       ?ob real. lookup_block l (frag_observer a b f id).fn_blocks = SOME ob /\
                 lookup_block l f.fn_blocks = SOME real /\
                 phi_prefix_length ob.bb_instructions = 0 /\
                 phi_prefix_length real.bb_instructions = 0)
Proof
  strip_tac >>
  `!cenv dst dty src sty.
     code_action (\opc. MEM opc ^typed_store_ops)
       (compile_store_memory_typed cenv dst dty src sty)` by
    (qspec_then `\opc. MEM opc ^typed_store_ops` mp_tac typed_copy_code_family >> simp[]) >>
  `create_cut_code {} a b` by metis_tac[create_store_memory_typed_cut_code, SND] >>
  `EVERY (\i. MEM i.inst_opcode ^typed_store_ops) (frag_code a b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     fs[create_store_memory_typed_cut_code, create_cut_code_def] >>
     qpat_x_assum `!cenv dst dty src sty. code_action _ _` mp_tac >>
     pure_rewrite_tac[code_action_def] >> strip_tac >>
     disch_tac >> first_x_assum drule >> simp[code_step_def]) >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b))` by
    (fs[create_layout_def, create_cut_code_def] >> metis_tac[]) >>
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
      drule_all stage_observer_fetch_agreement >>
      disch_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM l (added_labels a b)` by (fs[create_cut_code_def] >> metis_tac[]) >>
  drule_all typed_store_observer_label_layout >> strip_tac >>
  simp[frag_observer_region_def] >>
  `(?blk. MEM blk (emitted_blocks a b) /\ blk.bb_label = l) \/ l = b.cs_current_bb` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `!fn. no_phi_fn fn ==> !blk. lookup_block l fn.fn_blocks = SOME blk ==>
                              phi_prefix_length blk.bb_instructions = 0` by
    (simp[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED
