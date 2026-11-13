(* Physical observations retained at the actual decoder endpoint. *)
Theory abiDecodePtrSuccessPost
Ancestors
  abiDecodePtrResultPost abiDecodePtrOutcome abiDecodePtrMemberInterface
  abiDecoderVarExtend execEquivParamDefs venomState compileEnv finite_map
  bodyPtrBopHashFrame freshWrites abiDecoderContract loweringPosts
  abiBuiltinDecodeHeader loweringHalt exprLoweringProps exprSimProps fragExec
  rich_list

Theorem abi_decode_extend_same_lookup:
  abi_decoder_vars_extend s.vs_vars u v /\ lookup_var x u = lookup_var x s ==>
  lookup_var x v = lookup_var x s
Proof
  simp_tac bool_ss [abi_decoder_vars_extend_def, abi_decoder_var_map_def,
    lookup_var_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_vars x`
  >- (fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP v.vs_vars x` >> fs[] >>
      first_x_assum drule >> simp[]) >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Theorem abi_decode_actual_member_effects:
  abi_decode_member_frame ready G tn u H tf uf a k /\
  abi_decoder_vars_extend s.vs_vars uf v /\
  sa.cs_next_var <= ready.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  abi_decode_frame a k u v /\ v.vs_allocas = u.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s)
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >> strip_tac >>
  `uf.vs_allocas = u.vs_allocas /\ uf.vs_call_ctx = u.vs_call_ctx /\
   uf.vs_data_section = u.vs_data_section` by
    (fs[abi_decode_member_frame_def, venom_state_component_equality]) >>
  simp[] >> conj_tac
  >- (simp[abi_decode_frame_def] >> rpt strip_tac >>
      irule abi_decode_member_frame_bytes >>
      goal_assum (drule_at Any) >> decide_tac) >>
  rpt strip_tac >> irule abi_decode_extend_same_lookup >>
  goal_assum (drule_at Any) >>
  `not_fresh_at ready x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  fs[abi_decode_member_frame_def]
QED

Theorem abi_decode_success_frame_posts:
  wb_frame cenv es0 es sc s0 s /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  abi_decode_member_frame ready G tn u H tf uf a k /\
  abi_decoder_vars_extend s.vs_vars uf v /\
  sa.cs_next_var <= ready.cs_next_var /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint a k b n) /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    regions_disjoint a k b n) ==>
  wb_frame cenv es0 es sc s0 v /\ v.vs_allocas = u.vs_allocas /\
  (!name b n. local_region cenv es.scopes v name b n ==>
    regions_disjoint a k b n) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
    FLOOKUP v.vs_allocas aid = SOME e) /\
  (!off len. regions_disjoint off len a k ==>
    mem_bytes_at off len v.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule_all abi_decode_actual_member_effects >> strip_tac >>
  `!name b n. local_region cenv es.scopes v name b n <=>
    local_region cenv es.scopes s name b n` by
    (rpt gen_tac >> irule bop_local_region_readonly_frame >>
     qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (irule abi_decode_result_wb_frame >>
      simp[] >> qexistsl_tac [`k`, `a`, `s`, `sa`, `u`] >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `v.vs_allocas = _` SUBST1_TAC >>
      first_x_assum irule >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp[abi_decode_frame_def] >> strip_tac >>
  qpat_x_assum `u.vs_memory = s.vs_memory` (fn th => rewrite_tac[th]) >>
  first_x_assum irule >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem abi_decode_operand_success_posts:
  expr_post ctx func cenv cx e es0 sc sa s0 es (BytesV bs) (Var p) s /\
  ptr_val_ok cx (expr_type e) (BytesV bs) (Var p) G tn s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  fn_has_code sa ready func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ abi_decoder_operand_live sa.cs_next_var (Var p) /\
  mn <= LENGTH bs /\ LENGTH bs <= mx /\ mx < dimword (:256) /\
  ghost_inv ret cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ outsz < dimword (:256) /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  outsz = SUM (MAP (type_memory_bytes ce) tys) /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs] =
    INL (ArrayV (TupleV vs)) /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD src len
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) ready = ((),sb) /\
  fn_has_code ready sb func /\ fn_has_code sa sb func /\
  wb_frame cenv es0 es sc s0 s /\ local_ptrs_reserved cenv sc /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes ==>
  ?v H tf dst d. buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tf (OK v) /\
    v.vs_current_bb = sb.cs_current_bb /\ v.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret cenv cx es H tf v /\ stmt_state_rel ctx func cenv cx es v /\
    lookup_var dst v = SOME d /\ ptr_covers H tf dst v outsz /\
    (!mem'. mem_agree_outside tf.t_mem v.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem') /\
    ghost_kept cenv es sa G tn s H tf /\ wb_frame cenv es0 es sc s0 v /\
    FLOOKUP v.vs_allocas sh.cs_next_id = SOME (w2n d,outsz) /\
    sc.cs_next_id <= sh.cs_next_id /\ sh.cs_next_id < sb.cs_next_id /\
    (!name b n. local_region cenv es.scopes v name b n ==>
      regions_disjoint (w2n d) outsz b n) /\
    (pure_frame cenv func es0 sc s0 s ==> pure_frame cenv func es0 sc s0 v)
Proof
  strip_tac >> drule_all abi_decode_operand_success_handoff >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `abi_decode_member_frame ready G2 tn2 u H tf uf (w2n d) outsz` >>
  `sa.cs_next_var <= ready.cs_next_var /\ sa.cs_next_id <= sh.cs_next_id` by
    (drule abi_builtin_decode_header_shape >> strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `ready.cs_next_id <= sb.cs_next_id` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`buf.buf_operand`, `Lit 0w`, `MLOAD`, `src`, `len`,
       `DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)`, `ready`] mp_tac) >>
     simp[ci_mono_def]) >>
  drule_all abi_decode_success_frame_posts >> strip_tac >>
  `MEM (mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
      [STRING #"%" (toString sh.cs_next_var)]) (fn_insts func)` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     qpat_x_assum `fn_has_code sa ready func`
       (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND]) >>
  `pure_frame cenv func es0 sc s0 s ==> pure_frame cenv func es0 sc s0 v` by
    (strip_tac >>
     `sc.cs_next_id <= sh.cs_next_id` by decide_tac >>
     `!n lb lsz. local_region cenv es0.scopes s0 n lb lsz ==>
        regions_disjoint (w2n d) outsz lb lsz` by
       (rpt strip_tac >>
        `local_region cenv es.scopes v n lb lsz` by
          (irule local_region_frame_fwd >>
           qexistsl_tac [`s0`, `sc`, `es0.scopes`] >> fs[wb_frame_def]) >>
        qpat_x_assum `!name b n. local_region cenv es.scopes v _ _ _ ==> _` drule >>
        simp[]) >>
     `(mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
         [STRING #"%" (toString sh.cs_next_var)]).inst_opcode = ALLOCA /\
      (mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
         [STRING #"%" (toString sh.cs_next_var)]).inst_id = sh.cs_next_id` by
       simp[venomInstTheory.mk_inst_def] >>
     qpat_x_assum `outsz = SUM _` kall_tac >>
     mp_tac (pure_frame_buffer_tail |> Q.SPECL [`cenv`, `func`, `es0`, `sc`, `s0`,
       `s`, `v`, `mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
         [STRING #"%" (toString sh.cs_next_var)]`, `w2n (d:256 word)`, `outsz`]) >>
     impl_tac
     >- (rpt conj_tac >|
         [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC, first_assum ACCEPT_TAC,
          simp[], simp[], simp[], first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]) >>
     simp[]) >>
  qexistsl_tac [`v`, `H`, `tf`, `dst`, `d`] >> simp[] >> gvs[]
QED
