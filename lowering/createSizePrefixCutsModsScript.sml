Theory createSizePrefixCutsMods
Ancestors
  createSizePrefixCuts createExprSizeExitDefsMods
  abiEncoderProps fragExec venomExecSemantics venomInst relation list words pair
  builtinCreate arithmetic createSizeDispatch exprLowering vfmConstants createSizeCutRegion
  createSizeCutEntry createSizeCutCode compilerInstructionSuffix externalEntryShape
  compileEnv createSizeItinerary exprLoweringProps fragFuel rich_list createSizeOperandCode
  createSizeCtorCutSpine createSizeFixedPreparation createSizeConcreteSnapshots
  createSizeLocationCode createSizeEncodeCode context integer_word bodySim
  createExprSizeExitDefs createSizePrefixReplay createSizePrefixReplayMods

Theorem create_size_prefix_cut_walk_mods[local]:
  !mods exps src cuts a u marks.
    cs_extends sa a /\ LAST (a::cuts) = sc /\
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    LIST_REL create_cut_first (FRONT (a::cuts)) cuts /\
    cs_extends sc sb /\ fn_has_code sa sb func /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME db /\
    get_instruction db (LENGTH sc.cs_current_insts) = SOME dispatch /\
    dispatch.inst_id = sc.cs_next_id /\ MEM dispatch.inst_opcode [CREATE;CREATE2] /\
    emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
    compile_check_create_result created rof sd = (result,sb) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix sa sb explicit ctx func u marks s ==>
    ?states chunks.
      HD states = u /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
      LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                      v.vs_inst_idx = LENGTH c.cs_current_insts) (a::cuts) states /\
      (!i. i < LENGTH cuts ==>
        create_expr_prefix (EL i (a::cuts)) (EL i cuts) explicit ctx func
          (EL i states) (EL i chunks) (EL (SUC i) states)) /\
      marks = FLAT chunks
Proof
  ntac 3 gen_tac >> Induct
  >- (pure_rewrite_tac[LAST_CONS, FRONT_CONS, LIST_REL_def] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `a = sc` SUBST_ALL_TAC >>
      drule_all create_dispatch_no_return_mods >> strip_tac >>
      qexistsl_tac [`[u]`,`[]`] >> gvs[]) >>
  pure_rewrite_tac[FRONT_CONS, LAST_CONS, LIST_REL_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `create_cut_code {} a m` >>
  `!cs x. LIST_REL (create_cut_code {}) (FRONT (x::cs)) cs ==>
          create_cut_code {} x (LAST (x::cs))` by
    (Induct >- simp[] >> simp[FRONT_CONS_NOT_NIL] >> metis_tac[create_cut_code_join]) >>
  `create_cut_code {} m sc` by (first_x_assum drule >> simp[]) >>
  `?inner. LIST_REL create_cut_first (m::inner) (inner ++ [sc])` by
    (Cases_on `cuts` >- (qexists_tac `[]` >> gvs[]) >>
     rename1 `LAST (m::n::ns) = sc` >>
     qexists_tac `FRONT (n::ns)` >>
     `FRONT (n::ns) ++ [sc] = n::ns` by
       metis_tac[LAST_CONS, APPEND_FRONT_LAST, NOT_CONS_NIL] >>
     fs[FRONT_CONS]) >>
  `cs_extends a m /\ cs_extends m sc /\ m.cs_next_id <= sc.cs_next_id` by
    fs[create_cut_code_def] >>
  `cs_extends sa m /\ cs_extends m sb` by metis_tac[cs_extends_trans] >>
  `?v left right.
    v.vs_current_bb = m.cs_current_bb /\ v.vs_inst_idx = LENGTH m.cs_current_insts /\
    create_expr_prefix a m explicit ctx func u left v /\
    create_expr_prefix sa sb explicit ctx func v right s /\ marks = left ++ right` by
    (`fn_has_code a m func` by metis_tac[fn_has_code_mid] >>
     `fn_has_code m sb func` by metis_tac[fn_has_code_split] >>
     drule_all create_cut_region_rules >> strip_tac >>
     `!bb. lookup_block m.cs_current_bb func.fn_blocks = SOME bb ==>
           phi_prefix_length bb.bb_instructions <= LENGTH m.cs_current_insts` by
       (rpt strip_tac >> drule_all create_pre_dispatch_phi_bound >> simp[]) >>
     irule create_size_prefix_first_cut >> reverse conj_tac >- simp[] >>
     qexists_tac `create_cut_region a m` >>
     `create_cut_region a m u` by metis_tac[] >>
     simp[] >> reverse conj_tac
     >- (CCONTR_TAC >> pop_assum
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE [DE_MORGAN_THM, NOT_CLAUSES]) >>
         `dispatch.inst_id IN frag_ids a m` by metis_tac[] >> fs[frag_ids_def]) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     fs[create_prefix_step_def] >> metis_tac[]) >>
  qpat_x_assum `!a u marks. _` (qspecl_then [`m`,`v`,`right`] mp_tac) >>
  simp[] >>
  disch_then (qx_choosel_then [`rest_states`,`rest_chunks`]
    (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `rest_states`
  >- (qpat_x_assum `?v ys. [] = v::ys /\ _` mp_tac >> simp[]) >>
  rename1 `LAST (head::stk) = s` >>
  qexistsl_tac [`u::head::stk`,`left::rest_chunks`] >>
  fs[] >> gen_tac >> Cases_on `i` >> gvs[]
QED

Theorem create_size_itinerary_at_emit_mods[local]:
  create_itinerary_code sa cuts sc /\
  emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?out states chunks.
    created = Var out /\ inst = mk_inst sc.cs_next_id opc ops [out] /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac create_itinerary_code_relations >>
  drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
  drule_all create_size_identify_emit >> strip_tac >>
  `s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts` by
    metis_tac[create_dispatch_pc_unique] >>
  `inst.inst_id = sc.cs_next_id` by simp[mk_inst_def] >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     metis_tac[ci_mono_def,ci_mono_emit_op,compile_check_create_result_labels,pairTheory.SND]) >>
  `cs_extends sa sa` by simp[cs_extends_refl] >>
  drule_all create_size_prefix_cut_walk_mods >> strip_tac >>
  rpt (goal_assum (drule_at Any))
QED

Theorem create_size_prefix_cuts_from_code_mods:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_call_itinerary_run >> strip_tac
  >- (drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
      drule added_insts_emit_inst >> strip_tac >>
      `~MEM inst.inst_opcode [CREATE;CREATE2]` suffices_by simp[] >>
      irule (BETA_RULE (Q.INST [`P` |-> `\i. ~MEM i.inst_opcode [CREATE;CREATE2]`]
         added_insts_function_property)) >>
      qexistsl_tac [`func`,`sa`,`sb`] >> fs[mk_inst_def,ci_mono_def,frag_ids_def]) >>
  Cases_on `salt` >>
  qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
      [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
  `MEM CREATE [CREATE;CREATE2] /\ MEM CREATE2 [CREATE;CREATE2]` by simp[] >>
  drule_all create_size_itinerary_at_emit_mods >> strip_tac >>
  rename1 `marks = FLAT all_chunks` >>
  qexistsl_tac [`cuts`,`value`] >>
  (FIRST [rename1 `create_call_itinerary _ _ _ _ _ _ _ (SOME salt_op) _ _` >>
          qexists_tac `SOME salt_op`, qexists_tac `NONE`]) >>
  qexistsl_tac [`bufop`,`len`,`sc`,`sd`,`created`,`out`,`states`,`all_chunks`] >>
  asm_rewrite_tac[optionTheory.option_case_def] >> simp[]
QED

Theorem create_size_prefix_cuts_mods:
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  `create_itinerary_suppliers` by
    (simp[create_itinerary_suppliers_def, create_operand_cut_code,
          create_vv_snapshot_cut_code, create_unwrap_cut_code,
          create_encode_values_cut_code, cj 1 create_fixed_preparation_intervals,
          cj 4 create_fixed_preparation_intervals, cj 5 create_fixed_preparation_intervals] >>
     rpt gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
     irule create_cut_code_bind >>
     conj_tac >- (irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
     simp[]) >>
  `create_itinerary_rows_supplier` by
    (rw[create_itinerary_rows_supplier_def, create_itinerary_ctor_rows_def] >>
     irule create_ctor_cut_spine >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule create_size_prefix_cuts_from_code_mods >> simp[] >>
  rpt (goal_assum (drule_at Any))
QED
