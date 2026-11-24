(* Install a stopped observer on the actual encoder band. Old instructions
   retained before its entry contribute allocation sites, not encoder steps. *)
Theory entryCreateEncodeObserverCode
Ancestors
  entryStageStoreObserverCode
  createSizeEncodeCoreCode createSizeCutCode createSizeCutRegion
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiGasBridge fragObserverCodeProps externalEntryShape
  loweringShapeDefs compileEnv fragExec fragFuel abiEncoderProps
  venomInst venomExecProofs list rich_list arithmetic pair

Theorem encode_added_label[local]:
  cs_extends a b /\ ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\ MEM l (added_labels a b) ==>
  l <> a.cs_current_bb /\
  (l = b.cs_current_bb \/ ?bb. MEM bb (emitted_blocks a b) /\ bb.bb_label = l)
Proof
  strip_tac >>
  qpat_assum `cs_extends a b` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  Cases_on `new = []` >- gvs[added_labels_def, all_blocks_def, DROP_LENGTH_TOO_LONG] >>
  `?front last. new = front ++ [last]` by metis_tac[APPEND_FRONT_LAST] >>
  gvs[added_labels_def, all_blocks_def, REVERSE_APPEND, MAP_APPEND, MAP_REVERSE,
      DROP_LENGTH_APPEND, DROP_APPEND, LENGTH_MAP, MEM_REVERSE,
      DROP_LENGTH_TOO_LONG, DECIDE ``x - (y + x) = 0n``, ADD1,
      ALL_DISTINCT_APPEND, MEM_MAP, LAST_APPEND] >>
  metis_tac[]
QED

Theorem encode_observer_landing[local]:
  create_cut_code {} a b /\ ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\
  fn_has_code a b f /\ fn_has_code a b obs /\ no_phi_fn f /\ no_phi_fn obs /\
  MEM i (frag_code a b) /\ MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
  (l,0) IN frag_observer_region a b /\
  ?ob real. lookup_block l obs.fn_blocks = SOME ob /\
    lookup_block l f.fn_blocks = SOME real /\
    phi_prefix_length ob.bb_instructions = 0 /\ phi_prefix_length real.bb_instructions = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a b /\ MEM l (added_labels a b)` by (fs[create_cut_code_def] >> metis_tac[]) >>
  drule_all encode_added_label >> strip_tac >>
  simp[frag_observer_region_def, MEM_MAP] >>
  `!fn. no_phi_fn fn ==> !bb. lookup_block l fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (simp[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem encode_observer_fetch[local]:
  create_cut_code {} a b /\ fn_has_code a b f /\ fn_has_code a b (frag_observer a b f id) /\
  (lbl,idx) IN frag_observer_region a b /\ (lbl,idx) <> frag_observer_cut b /\
  lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME i ==>
  MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\
  ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `lbl = b.cs_current_bb ==> idx <= LENGTH b.cs_current_insts` by
    (strip_tac >> gvs[frag_observer_cut_lookup, get_instruction_def, AllCaseEqs()]) >>
  qabbrev_tac `s = ARB with <|vs_current_bb := lbl; vs_inst_idx := idx|>` >>
  `create_cut_region a b s` by
    (irule stage_observer_fetch_region >> simp[Abbr `s`] >> metis_tac[]) >>
  `MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b` by
    (qpat_assum `fn_has_code a b (frag_observer a b f id)`
       (mp_then (Pat `fn_has_code _ _ _`) mp_tac create_cut_region_rules) >>
     simp[] >> disch_then (qspecl_then [`s`, `bb`, `i`] mp_tac o cj 2) >>
     fs[Abbr `s`, frag_observer_cut_def]) >>
  metis_tac[stage_observer_fetch_agreement]
QED

Theorem create_encode_observer_code:
  compile_abi_encode_to_buf dst src ei a = (out,b) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\ no_phi_fn f /\ ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)) ==>
  ?id. (!i. MEM i (fn_insts f) ==> i.inst_id <> id) /\
    fn_has_code a b (frag_observer a b f id) /\
    fn_inst_ids_distinct (frag_observer a b f id) /\
    (frag_observer a b f id).fn_name = f.fn_name /\
    create_cut_code {} a b /\
    (a.cs_current_bb,LENGTH a.cs_current_insts) IN frag_observer_region a b /\
    (!i. MEM i (fn_insts (frag_observer a b f id)) /\ i.inst_opcode <> STOP ==>
      MEM i (fn_insts f)) /\
    (!lbl idx bb i. (lbl,idx) IN frag_observer_region a b /\
      (lbl,idx) <> frag_observer_cut b /\
      lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
      get_instruction bb idx = SOME i ==>
      MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\ encode_window_opcode i.inst_opcode /\
      ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i) /\
    (!i l. MEM i (frag_code a b) /\ MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
      (l,0) IN frag_observer_region a b /\
      ?ob real. lookup_block l (frag_observer a b f id).fn_blocks = SOME ob /\
        lookup_block l f.fn_blocks = SOME real /\
        phi_prefix_length ob.bb_instructions = 0 /\ phi_prefix_length real.bb_instructions = 0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_cut_code {} a b` by metis_tac[create_encode_to_buf_cut_code, SND] >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b))` by fs[] >>
  mp_tac (Q.INST [`fn` |-> `f`] frag_observer_fresh_id) >>
  disch_then (qx_choose_then `id` assume_tac) >> qexists_tac `id` >>
  `fn_has_code a b (frag_observer a b f id)` by metis_tac[reject_observer_has_code] >>
  `fn_inst_ids_distinct (frag_observer a b f id)` by metis_tac[frag_observer_ids_distinct_from_labels] >>
  `no_phi_fn (frag_observer a b f id)` by metis_tac[abi_dyn_observer_no_phi] >>
  `!i. MEM i (frag_code a b) ==> encode_window_opcode i.inst_opcode` by
    (drule (cj 2 encode_window_code_action_mutual |> SRULE [code_action_def, code_step_def]) >>
     simp[EVERY_MEM]) >>
  `(frag_observer a b f id).fn_name = f.fn_name` by simp[frag_observer_def] >>
  asm_simp_tac std_ss [frag_observer_start_region] >> conj_tac
  >- metis_tac[frag_observer_nonstop_inclusion] >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all encode_observer_fetch >> strip_tac >> metis_tac[]) >>
  metis_tac[encode_observer_landing]
QED
