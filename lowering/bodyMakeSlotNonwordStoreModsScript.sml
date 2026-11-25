(* Execute one MakeArray nonword store at the cursor after unwrap. *)
Theory bodyMakeSlotNonwordStoreMods
Ancestors
  bodyMakeElementsContractMods bodyMakeElementStoreMods
  bodyStructFieldChildFrameMods bodyStructFieldCutsMods
  bodyStructFieldSmallStoreMods bodyStructFieldBytesStoreMods
  bodyFullPathHistory bodyInvCodeProps stateRelProj exprBodyPreProps
  exprSimAggregateChildren exprSimFullBundleProps typedMemoryCopy
  bodyFullShadowBodyInv exprSimHypsDefs vyperStorageFootprint
  fragGasOriginPtr gasOutcomeFullMods ptrDiscipline venomMemDefs[qualified]
  venomState finite_map words arithmetic

val _ = Parse.hide "base";
val make_element_transfer_statement =
  concl bodyMakeElementStoreModsTheory.make_element_transfer_mods;
val make_element_transfer_contract =
  boolSyntax.list_mk_forall
    (free_vars make_element_transfer_statement, make_element_transfer_statement);

Theorem make_slot_nonword_store_run[local]:
  ^make_element_transfer_contract ==>
  compile_store_memory ce op (Var dst) dty sty sc = ((),sb) /\
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,base+off) (sc,gz,tz,z) /\
  ~is_word_type dty /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  FLOOKUP z.vs_allocas aid = SOME (base,cap) /\
  off + type_memory_size dtv <= cap /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  alloca_history func z /\ venomMemDefs$alloca_inv z /\ ~z.vs_halted /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?t gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,gz,tz) [] (OK t,gf,tf)) /\
    struct_store_effects func (sc,gz,tz,z) (sb,gf,tf,t) (base+off,dtv,v) /\
    value_has_type dtv v /\ val_wf dtv v
Proof
  disch_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type dtv v /\ val_wf dtv v` by fs[struct_operand_mods_def] >>
  simp[] >>
  Cases_on `type_memory_size stv = 0`
  >- (irule struct_field_small_store_mods >> simp[] >>
      qexistsl [`ce`,`dst`,`dty`,`op`,`stv`,`sty`,`tenv`] >> simp[]) >>
  `0 < type_memory_size stv` by decide_tac >>
  Cases_on `is_bytestring_type dty`
  >- (irule struct_field_bytes_store_mods >> simp[] >>
      qexistsl [`ce`,`dst`,`dty`,`op`,`stv`,`sty`,`tenv`] >>
      asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[struct_operand_mods_def] >>
  `~is_bytestring_type sty` by metis_tac[type_widens_from_bytestring] >>
  `val_footprint stv v = type_memory_size stv` by
    (irule evaluated_nonbytes_footprint >> qexistsl [`tenv`,`sty`] >> simp[]) >>
  `base + off < dimword (:256)` by decide_tac >>
  `w2n ((n2w (base+off)):256 word) = base+off` by simp[wordsTheory.w2n_n2w, LESS_MOD] >>
  gvs[eval_operand_def] >>
  first_x_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP z.vs_allocas aid = SOME _`)) >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `!mem. mem_agree_outside _ _ mem ==> val_in_memory _ _ _ mem`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sb func`)) >>
  disch_then (drule_at (Pat `allocas_from lo z`)) >>
  disch_then (fn step =>
    qpat_assum `evaluate_type tenv dty = SOME dtv`
      (mp_then (Pat `evaluate_type _ dty = SOME _`) mp_tac step)) >>
  disch_then (fn step =>
    qpat_assum `lookup_var dst z = SOME _`
      (mp_then (Pat `lookup_var dst _ = SOME _`) mp_tac step)) >>
  disch_then (fn step =>
    qpat_assum `ptr_covers gz tz dst z _`
      (mp_then (Pat `ptr_covers _ _ dst _ _`) mp_tac step)) >>
  disch_then (qspecl_then [`PG`,`explicit`,`ctx`,`off`] mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w, LESS_MOD] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE decide_tac))) >>
  disch_then (qx_choosel_then [`t`,`gf`,`tf`] strip_assume_tac) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `t.vs_alloca_next = z.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[Once venom_state_component_equality]) >>
  qexistsl [`t`,`gf`,`tf`] >>
  simp[struct_store_effects_def, expr_sim_full_endpoint_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem make_slot_nonword_store_mods:
  ^make_element_transfer_contract ==>
  make_slot_entry_mods mods exps src tops cenv cx env
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
    h xs dty dtv ps off sa sb sha shb (es,s,G,tn) /\
  ~is_word_type dty /\
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sc mid z gz tz /\
  storage_trace_domain cx st0 mid.storage_trace /\
  bind (eval_expr cx h) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  expr_body_pre_mods mods cenv cx env h es /\ value_runtime_typed env (expr_type h) v /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx h es sa sc s mid v op z) /\
  ptr_val_ok cx (post_value_type cenv h) v op gz tz z /\
  (~is_word_type (post_value_type cenv h) ==> ptr_buf_ok cenv h op gz z) /\
  (~is_word_type (post_value_type cenv h) ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  (!x. op = Var x ==> not_fresh_at sc x) /\
  aid < sa.cs_next_id /\ not_fresh_at sc dst /\
  lookup_var dst z = SOME (n2w (base+off)) /\ ptr_covers gz tz dst z (type_memory_size dtv) /\
  compile_store_memory cenv op (Var dst) dty (lowered_value_type cenv h) sc = ((),sb) /\
  fn_has_code sc sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) ==>
  ?t gf tf.
    (!D. gas_origin_ptr_path
      (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (z,gz,tz) [] (OK t,gf,tf)) /\
    struct_store_effects func (sc,gz,tz,z) (sb,gf,tf,t) (base+off,dtv,v) /\
    value_has_type dtv v /\ val_wf dtv v
Proof
  disch_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_x_assum `make_slot_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [make_slot_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_entry_mods`
    (strip_assume_tac o PURE_REWRITE_RULE [make_elements_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_static_mods`
    (strip_assume_tac o PURE_REWRITE_RULE [make_elements_static_mods_def]) >>
  qpat_x_assum `make_elements_cut_mods DF lo d ctx func cenv cx st0 _ _ sc mid z gz tz`
    (strip_assume_tac o PURE_REWRITE_RULE [make_elements_cut_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ mid z /\ _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (drule_then (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def])
      expr_body_pre_mods_inv >> conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!name p k. local_region _ _ _ name p k ==> regions_disjoint _ _ p k`
    (assume_tac o PURE_REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      struct_field_store_input_mods) >>
  disch_then (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP z.vs_allocas aid = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers gz tz dst z _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME dtv`)) >>
  disch_then (qspecl_then [`off`,`mods`,`env`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  drule_at (Pat `^make_element_transfer_contract`) make_slot_nonword_store_run >>
  disch_then irule >> asm_simp_tac bool_ss [] >>
  conj_tac >- (qexistsl [`aid`,`cap`] >> simp[]) >>
  qexistsl [`cenv`,`dst`,`dty`,`op`,`stv`,`lowered_value_type cenv h`,`get_tenv cx`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
