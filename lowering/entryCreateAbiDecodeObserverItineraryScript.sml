(* Read the regular STOP observer without executing its artificial endpoint. *)
Theory entryCreateAbiDecodeObserverItinerary
Ancestors
  entryCreateIntervalLayout entryCreatePathScope entryCreateOperandReplay
  entryCreateFocusSpec createSizePrefixReplay createMarkedPath
  createSizeCutRegion createSizeCutCode bodyFullIfExpReach fragObserverCodeProps
  exprSimAbiGasBridge fragFuel fragExec fragGasPath fragGasOrigin venomExecSemantics
  venomExecProofs venomInst venomState list rich_list relation pred_set arithmetic

Theorem decode_cut_region_observer[local]:
  cs_extends a b /\ create_layout a b /\ create_cut_region a b s ==>
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emitted_blocks a b = []`
  >- fs[create_cut_region_def, frag_observer_region_def, FRONT_DEF] >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  `MEM (LAST (emitted_blocks a b)) (emitted_blocks a b)` by
    simp[MEM_LAST_NOT_NIL] >>
  `~MEM a.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))` by
    (qpat_x_assum `create_layout a b` mp_tac >>
     simp[create_layout_def] >>
     qspec_then `emitted_blocks a b` mp_tac APPEND_FRONT_LAST >>
     simp[] >> disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  fs[create_cut_region_def, frag_observer_region_def, create_layout_def, MEM_MAP] >>
  metis_tac[MEM_FRONT_NOT_NIL]
QED

Theorem decode_observer_block[local]:
  fn_has_code a b f /\
  lookup_block lbl (frag_observer a b f id).fn_blocks = SOME ob ==>
  ?bb. lookup_block lbl f.fn_blocks = SOME bb
Proof
  strip_tac >> drule frag_observer_lookup_cases >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem decode_observer_edge[local]:
  cs_extends a b /\ fn_has_code a b f /\ frag_gas_free a b /\ no_phi_fn f /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b /\
  gas_path_edge ctx (frag_observer a b f id) s 0 r /\ (!h. r <> Halt h) ==>
  ~create_operand_at b s /\ gas_path_edge ctx f s 0 r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~create_operand_at b s` by
    (strip_tac >>
     qpat_x_assum `gas_path_edge _ _ _ _ _` mp_tac >>
     fs[create_operand_at_def, gas_path_edge_def, frag_observer_cut_lookup,
        frag_observer_cut_instruction] >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs, exit_result_def]) >>
  simp[] >>
  `(s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut b` by
    fs[create_operand_at_def, frag_observer_cut_def] >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[gas_path_edge_def]) >>
  drule_all frag_observer_instruction_agrees >> strip_tac >>
  rewrite_tac[gas_path_edge_def] >> asm_simp_tac std_ss [] >>
  qexists_tac `fuel` >>
  asm_simp_tac std_ss [] >> TRY (metis_tac[]) >>
  rename1 `lookup_block mid.vs_current_bb (frag_observer a b f id).fn_blocks = SOME target` >>
  `no_phi_fn (frag_observer a b f id)` by metis_tac[abi_dyn_observer_no_phi] >>
  `phi_prefix_length target.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  drule_all decode_observer_block >> strip_tac >>
  rename1 `lookup_block mid.vs_current_bb f.fn_blocks = SOME real_target` >>
  `phi_prefix_length real_target.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  gvs[eval_phis_no_phi] >> metis_tac[eval_phis_no_phi]
QED

Theorem decode_prefix_prepend[local]:
  create_prefix_step a b explicit ctx f s [] t /\
  create_expr_prefix a b explicit ctx f t [] u ==>
  create_expr_prefix a b explicit ctx f s [] u
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule (cj 2 RTC_RULES) >> qexists_tac `(t,[])` >>
  simp[create_marked_edge_def]
QED

Theorem decode_observer_itinerary_region[local]:
  !ctx obs s n r. gas_path ctx obs s n r ==>
  !a b f id explicit tops ce cx.
    obs = frag_observer a b f id /\ n = 0 /\
    body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
    fn_has_code a b f /\ create_cut_code {} a b /\ frag_gas_free a b /\
    create_layout a b /\ create_cut_region a b s /\
    ((?t. r = OK t /\ create_operand_at b t) \/ (?v. r = Abort Revert_abort v)) ==>
    (?t. r = OK t /\ create_operand_at b t /\ create_expr_prefix a b explicit ctx f s [] t) \/
    (?v u. r = Abort Revert_abort v /\ create_expr_prefix a b explicit ctx f s [] u /\
           ~create_operand_at b u /\ gas_origin_edge F explicit ctx f u [] r)
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[create_expr_prefix_nil]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[] >>
      rename1 `gas_path_edge ctx (frag_observer a b f id) s 0 (OK mid)` >>
      `cs_extends a b` by fs[create_cut_code_def] >>
      `no_phi_fn f` by
        (simp[no_phi_fn_def, EVERY_MEM] >> metis_tac[body_inv_no_phi]) >>
      `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b` by
        metis_tac[decode_cut_region_observer] >>
      `~create_operand_at b s /\ gas_path_edge ctx f s 0 (OK mid)` by
        (irule decode_observer_edge >> simp[] >> qexistsl_tac [`a`, `id`] >> simp[]) >>
      `gas_origin_edge F explicit ctx f s [] (OK mid)` by
        metis_tac[gas_path_edge_zero_origin] >>
      `create_prefix_step a b explicit ctx f s [] mid /\ create_cut_region a b mid` by
        (irule operand_cut_region_edge >> simp[] >>
         metis_tac[create_operand_at_def]) >>
      metis_tac[decode_prefix_prepend])
  >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[exit_result_def] >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `no_phi_fn f` by
    (simp[no_phi_fn_def, EVERY_MEM] >> metis_tac[body_inv_no_phi]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b` by
    metis_tac[decode_cut_region_observer] >>
  rename1 `gas_path_edge ctx (frag_observer a b f id) s 0 (Abort Revert_abort v)` >>
  `~create_operand_at b s /\ gas_path_edge ctx f s 0 (Abort Revert_abort v)` by
    (irule decode_observer_edge >> simp[] >> qexistsl_tac [`a`, `id`] >> simp[]) >>
  qexists_tac `s` >> simp[create_expr_prefix_nil, gas_path_edge_zero_origin]
QED

Theorem create_regular_observer_itinerary:
  let obs = frag_observer a b f id in
    body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
    fn_has_code a b f /\ create_cut_code {} a b /\ frag_gas_free a b /\
    create_layout a b /\ create_operand_at a s /\ gas_path ctx obs s 0 r /\
    ((?t. r = OK t /\ create_operand_at b t) \/ (?v. r = Abort Revert_abort v)) ==>
    (?t. r = OK t /\ create_operand_at b t /\ create_expr_prefix a b explicit ctx f s [] t) \/
    (?v u. r = Abort Revert_abort v /\ create_expr_prefix a b explicit ctx f s [] u /\
           ~create_operand_at b u /\ gas_origin_edge F explicit ctx f u [] r)
Proof
  simp_tac std_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule decode_observer_itinerary_region >> disch_then irule >>
  simp[] >> metis_tac[create_cut_region_rules, create_operand_at_def]
QED
