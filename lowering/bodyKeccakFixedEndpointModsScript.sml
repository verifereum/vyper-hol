(* The fixed-width hash shares the scratch run with MethodId, but its
   result is the full digest, as certified by the ordinary Keccak post. *)
Theory bodyKeccakFixedEndpointMods
Ancestors
  bodyKeccakFixedMods bodyMethodIdHashFixedMods bodyMethodIdScratchFrameMods
  bodyFullHashKeccakFixed bodyFullPostsMods bodyFullShadowBodyInv bodyMemoryDefs
  exprSimHash exprSimVVFrame exprSimWordArgs ghostPcTransportPtr
  bodyInvSplit bodyPtrDefs ptrDiscipline loweringStateRelDefs exprLoweringProps
  builtinHashing compileEnv vyperTypeSystem vyperValue vyperStorageTrace
  finite_map pred_set venomInst venomState vyperStorageFootprint
  loweringPosts freshWrites

Theorem fixed_hash_immutable_pc[local]:
  immutable_frame_mods func cenv cx es (s with vs_inst_idx := pc) <=>
  immutable_frame_mods func cenv cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       local_region_def, lookup_var_def]
QED

Theorem fixed_hash_ghost_pc[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn (s with vs_inst_idx := pc) <=>
  ghost_inv_at_mods D lo d cenv cx es G tn s
Proof
  Cases_on `d` >>
  simp[ghost_inv_at_mods_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_at_def, allocas_from_def, lookup_var_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

val fixed_keccak_expr = ``Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e]``;
val fixed_keccak_val = ``Value (BytesV (Keccak_256_w64 bs))``;
val fixed_keccak_stack = ``StackValue (BaseT (BytesT (Fixed 32))) op``;

Theorem keccak_fixed_endpoint_mods:
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m))) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  return_buf_frame d cenv sa s0 /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  storage_trace_domain cx st0 mid.storage_trace /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid (BytesV bs) x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) x G tn s) ==>
  ?raw u Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK raw /\
    u = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
      vv_post H ctx func cenv cx ^fixed_keccak_expr es sa sb s0 mid
        ^fixed_keccak_val ^fixed_keccak_stack u /\
      immutable_frame_mods func cenv cx mid u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gf tf u /\
      ghost_kept_at lo cenv mid sm G tn s Gf tf)
Proof
  strip_tac >>
  qabbrev_tac `J = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 J mid.storage_trace` by fs[Abbr `J`, storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) x s /\
    immutable_frame_mods func cenv cx mid s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) x G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_mods_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `J` (drule_then strip_assume_tac)) >>
  `LENGTH bs = m` by fs[vyperTypingTheory.value_has_type_def] >>
  `m <= 32` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sm s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     qpat_assum `expr_post J _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  suspend "scratch"
QED

Resume keccak_fixed_endpoint_mods[scratch]:
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `compile_method_id_hash (expr_type e) x sm = (op,sb)` by
    simp[compile_method_id_hash_def] >>
  `is_bytes_or_string_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    simp[is_bytes_or_string_type_def, is_bytestring_type_def] >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) x s /\
    ghost_inv_at (DF H) 0 d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) x G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_then assume_tac method_id_ghost_at_zero >> simp[]) >>
  drule_all method_id_hash_fixed_scratch_run >>
  suspend "scratch_apply"
QED

Resume keccak_fixed_endpoint_mods[scratch_apply]:
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sb) s = OK raw` >>
  rename1 `u = (raw with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  rename1 `op_taint tf op = {}` >> rename1 `op_prov Gf op = NONE` >>
  `ghost_kept_at lo cenv mid sm G tn s Gf tf` by
    (simp[ghost_kept_at_def] >>
     qpat_assum `tf.t_mem SUBSET tn.t_mem` (assume_tac o REWRITE_RULE[SUBSET_DEF]) >>
     rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl_tac [`raw`,`u`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `J` (drule_then strip_assume_tac)) >>
  conj_tac >-
    (qpat_assum `stmt_state_rel J _ _ _ _ mid u`
       (mp_then Any mp_tac stmt_state_rel_allocas_below_fmp) >> asm_rewrite_tac[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\
    immutable_frame_mods _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  `vv_post H ctx func cenv cx ^fixed_keccak_expr es sa sb s0 mid
    ^fixed_keccak_val ^fixed_keccak_stack raw` by
    (drule_all keccak_fixed_post_run >> strip_tac >> gvs[]) >>
  simp[vv_post_inst_idx] >> suspend "linked_post"
QED

Resume keccak_fixed_endpoint_mods[linked_post]:
  simp[fixed_hash_immutable_pc, fixed_hash_ghost_pc] >>
  qabbrev_tac `site = mk_inst sm.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  `site.inst_opcode = ALLOCA /\ site.inst_id = sm.cs_next_id` by
    simp[Abbr `site`, mk_inst_def] >>
  `compile_keccak256_bytesm x (LENGTH bs) sm = (op,sb)` by simp[] >>
  qpat_assum `u = (raw with vs_inst_idx := _)` (fn th =>
    rule_assum_tac (SIMP_RULE (srw_ss()) [th, lookup_var_def, ghost_inv_at_inst_idx])) >>
  `!p. not_fresh_at sm p ==> lookup_var p raw = lookup_var p s /\
                           FLOOKUP Gf p = FLOOKUP G p /\
                           FLOOKUP tf.t_var p = FLOOKUP tn.t_var p` by
    (rpt strip_tac >> gvs[lookup_var_def] >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  `FLOOKUP raw.vs_allocas site.inst_id = SOME (b,32)` by simp[] >>
  drule_all keccak_fixed_suffix_mods >> simp[]
QED

Finalise keccak_fixed_endpoint_mods
