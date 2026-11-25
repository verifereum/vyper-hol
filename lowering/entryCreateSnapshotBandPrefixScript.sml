(* Synchronize a computed traversal with the marks of its successful run. *)
Theory entryCreateSnapshotBandPrefix
Ancestors
  createCtorSegmentArrival entryCreateFocusSpec createSizePrefixReplay
  createMarkedPath fragGasOrigin fragExec venomExecProofs venomExecSemantics
  venomInst venomState relation list option

Theorem snapshot_computed_successor[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  ctor_segment_fetch func s = SOME i /\ i.inst_opcode <> INVOKE /\
  ctor_segment_next func s i = SOME v /\
  gas_origin_edge mem explicit ctx func s marks (OK t) ==> v = t
Proof
  strip_tac >>
  `!lbl bb. lookup_block lbl func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lookup_block_MEM] >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  rw[gas_origin_edge_def, exit_result_def] >>
  gvs[ctor_segment_fetch_def, step_inst_non_invoke, ctor_segment_next_def,
      ctor_segment_entry_def] >>
  gvs[AllCaseEqs(), exit_result_def] >>
  rename1 `eval_phis _ dest.bb_instructions` >>
  `phi_prefix_length dest.bb_instructions = 0` by metis_tac[] >>
  gvs[eval_phis_no_phi, jump_to_def]
QED

Theorem snapshot_empty_path_uncons[local]:
  gas_origin_path mem explicit ctx func s [] (OK t) /\ s <> t ==>
  ?v. gas_origin_edge mem explicit ctx func s [] (OK v) /\
      gas_origin_path mem explicit ctx func v [] (OK t)
Proof
  simp[Once gas_origin_path_cases, exit_result_def] >> metis_tac[]
QED

Theorem snapshot_edge_forget_memory[local]:
  gas_origin_edge mem explicit ctx func s marks r ==>
  gas_origin_edge F explicit ctx func s marks r
Proof
  pure_rewrite_tac[gas_origin_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fuel`,`bb`,`inst`,`middle`]
      (map_every assume_tac o CONJUNCTS))) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`fuel`,`bb`,`inst`,`middle`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Theorem snapshot_computed_empty_prefix:
  RTC C s u /\ gas_origin_path mem explicit ctx func s [] (OK u) /\
  create_operand_at sc u /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!a b. C a b ==> ~create_operand_at sc a /\
    ?i. ctor_segment_fetch func a = SOME i /\ i.inst_id IN frag_ids sm sc /\
        i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b) ==>
  create_expr_prefix sm sc explicit ctx func s [] u
Proof
  `(!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
   (!a b. C a b ==> ~create_operand_at sc a /\
     ?i. ctor_segment_fetch func a = SOME i /\ i.inst_id IN frag_ids sm sc /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b) ==>
   !s u. RTC C s u ==> gas_origin_path mem explicit ctx func s [] (OK u) /\
     create_operand_at sc u ==> create_expr_prefix sm sc explicit ctx func s [] u`
    suffices_by metis_tac[] >>
  strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >> conj_tac
  >- simp[create_expr_prefix_marked] >>
  map_every qx_gen_tac [`a`,`b`,`u`] >> rpt strip_tac >>
  qpat_assum `!a b. C a b ==> _` (drule_then strip_assume_tac) >>
  `a <> u` by metis_tac[] >>
  drule_all snapshot_empty_path_uncons >> strip_tac >>
  `v = b` by metis_tac[snapshot_computed_successor] >> gvs[] >>
  `create_expr_prefix sm sc explicit ctx func b [] u` by metis_tac[] >>
  drule_then assume_tac snapshot_edge_forget_memory >>
  `create_prefix_step sm sc explicit ctx func a [] b` by
    gvs[create_prefix_step_def, create_operand_at_def, ctor_segment_fetch_def,
        AllCaseEqs()] >>
  fs[create_expr_prefix_marked] >> irule (cj 2 RTC_RULES) >>
  qexists_tac `(b,[])` >> simp[create_marked_edge_def]
QED
