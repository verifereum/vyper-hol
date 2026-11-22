(* Transfer the saved-list witness to the observed encoder cut. *)
Theory createCtorEncoderActualLength
Ancestors
  createMarkedPath createCtorEncoderLength createCtorEncoderFinish
  createCtorEncoderCutOccurrence createCtorSegmentArrival createCtorOversizedSink
  abiEncoderProps bodyFullExtCallDirectState fragGasOrigin fragGasOriginPtr
  fragExec venomExecProofs relation arithmetic pair
Libs pairLib horizonTypeLib

(* All later segments project to one relation with the same lower ID bound. *)
Theorem ctor_marked_suffix_project[local]:
  !n. (!k. k < n ==>
      (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      RTC (create_marked_edge (\p ms q. ?bb i.
        (p.vs_current_bb,p.vs_inst_idx) <>
          ((c (SUC k)).cs_current_bb,LENGTH (c (SUC k)).cs_current_insts) /\
        lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb p.vs_inst_idx = SOME i /\
        i.inst_id IN frag_ids (c k) (c (SUC k)) /\
        gas_origin_edge F explicit ctx func p ms (OK q)))
        (r k,[]) (r (SUC k),chunk k)) ==>
    (c 0).cs_next_id <= (c n).cs_next_id /\
    RTC (\p q. ?bb i ms.
      lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\
      (c 0).cs_next_id <= i.inst_id /\
      gas_origin_edge F explicit ctx func p ms (OK q)) (r 0) (r n)
Proof
  Induct >- simp[] >>
  disch_tac >> qpat_x_assum `(_ ==> _ /\\ _)` mp_tac >>
  (impl_tac >- (rpt gen_tac >> disch_tac >>
                `k < SUC n` by decide_tac >> first_x_assum drule >> simp[])) >>
  strip_tac >>
  qpat_assum `!k. k < SUC n ==> _` (qspec_then `n` mp_tac) >>
  simp_tac bool_ss [prim_recTheory.LESS_SUC_REFL] >> strip_tac >>
  conj_tac >- metis_tac[LESS_EQ_TRANS] >>
  irule RTC_TRANS >> qexists_tac `r n` >> simp[] >>
  drule_then irule ctor_marked_project >>
  simp[frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem ctor_marked_cut_identify[local]:
  RTC (create_marked_edge (\p ms q. ?bb i.
    (p.vs_current_bb,p.vs_inst_idx) <> (en.cs_current_bb,LENGTH en.cs_current_insts) /\
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids st en /\
    gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (t,encmarks) /\
  c 0 = en /\ r 0 = t /\ r n = bad /\
  (!k. k < n ==>
    (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
    RTC (create_marked_edge (\p ms q. ?bb i.
      (p.vs_current_bb,p.vs_inst_idx) <>
        ((c (SUC k)).cs_current_bb,LENGTH (c (SUC k)).cs_current_insts) /\
      lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\
      i.inst_id IN frag_ids (c k) (c (SUC k)) /\
      gas_origin_edge F explicit ctx func p ms (OK q)))
      (r k,[]) (r (SUC k),chunk k)) /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  (z.vs_current_bb,z.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\
  lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
  get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
  ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value; off; sz]) \/
   (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value; off; sz; salt])) /\
  eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w /\
  gas_origin_path T explicit ctx func u marks (OK z) ==>
  z = t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `A = \p q. (p.vs_current_bb,p.vs_inst_idx) <>
    (en.cs_current_bb,LENGTH en.cs_current_insts) /\
    ?ms. gas_origin_edge F explicit ctx func p ms (OK q)` >>
  qabbrev_tac `B = \p q. ?bb i ms.
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\
    en.cs_next_id <= i.inst_id /\ gas_origin_edge F explicit ctx func p ms (OK q)` >>
  `RTC A u t` by
    (drule_then irule ctor_marked_project >> simp[Abbr `A`] >> metis_tac[]) >>
  `RTC B t bad` by
    (drule_then (mp_tac o cj 2) ctor_marked_suffix_project >>
     asm_rewrite_tac[] >> simp[Abbr `B`]) >>
  `!p q. A p q \/ B p q ==> ?ms. gas_origin_edge F explicit ctx func p ms (OK q)` by
    (simp[Abbr `A`, Abbr `B`] >> metis_tac[]) >>
  `!ms q. ~gas_origin_edge T explicit ctx func bad ms (OK q)` by
    (drule_all ctor_oversized_no_ok >> simp[]) >>
  `ctor_segment_fetch func bad = SOME dispatch /\ dispatch.inst_opcode <> PHI` by
    (simp[ctor_segment_fetch_def] >> fs[]) >>
  `?i. ctor_segment_fetch func t = SOME i /\ i.inst_opcode <> PHI` by
    (qpat_assum `RTC B t bad` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
     >- gvs[] >>
     qpat_x_assum `B t _` mp_tac >> simp[Abbr `B`, ctor_segment_fetch_def] >>
     rw[gas_origin_edge_def, exit_result_def] >> metis_tac[step_inst_ok_imp_not_phi]) >>
  `?i. ctor_segment_fetch func z = SOME i /\ i.inst_opcode <> PHI` by
    (fs[ctor_segment_fetch_def] >> metis_tac[]) >>
  `RTC A z t \/ RTC B t z` by
    (drule_all_then (strip_assume_tac) ctor_path_split_at_sink >> simp[]) >>
  drule_all_then (qx_choosel_then [`end_bb`,`pred`,`last`] strip_assume_tac)
    ctor_encoder_finish_position >>
  irule ctor_encoder_cut_occurrence >>
  qexistsl_tac [`A`,`B`,`end_bb`,`ctx`,`explicit`,`func`,`en.cs_next_id`,`last`,`pred`] >>
  asm_rewrite_tac[] >> simp[Abbr `A`, Abbr `B`]
QED

Theorem ctor_encoder_length_at_marked_cut:
  body_inv tops ctx ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
      H (INL vs) ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  rows = ZIP (svs,MAP (lowered_value_type ce) args) /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-dst_offset /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\
  RTC (create_marked_edge (\p ms q. ?bb i.
    (p.vs_current_bb,p.vs_inst_idx) <> (en.cs_current_bb,LENGTH en.cs_current_insts) /\
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids st en /\
    gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (t,encmarks) /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  c 0 = en /\ r 0 = t /\ r n = bad /\
  (!k. k < n ==>
    (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
    RTC (create_marked_edge (\p ms q. ?bb i.
      (p.vs_current_bb,p.vs_inst_idx) <>
        ((c (SUC k)).cs_current_bb,LENGTH (c (SUC k)).cs_current_insts) /\
      lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\
      i.inst_id IN frag_ids (c k) (c (SUC k)) /\
      gas_origin_edge F explicit ctx func p ms (OK q)))
      (r k,[]) (r (SUC k),chunk k)) /\
  lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
  get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
  ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value; off; sz]) \/
   (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value; off; sz; salt])) /\
  eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w ==>
  ?Gt tt.
    (pure_frame ce func ee se u t /\ wb_frame ce ee ee se u t) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en t Gt tt /\
    eval_operand alen t = SOME (n2w (LENGTH bytes)) /\ op_taint tt alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) t.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tt.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)))
    ctor_encoder_length_witness >>
  `(z.vs_current_bb,z.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts)` by
    (qhdtm_assum `abi_encode_saved_state`
       (mp_tac o REWRITE_RULE[abi_encode_saved_state_def]) >> simp[]) >>
  `gas_origin_path T explicit ctx func u [] (OK z)` by
    (qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ _ _`
       (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_projections)) >> simp[]) >>
  `z = t` by (drule_all ctor_marked_cut_identify >> simp[]) >>
  qpat_x_assum `z = t` SUBST_ALL_TAC >>
  qexistsl_tac [`Gz`,`tz`] >> asm_rewrite_tac[]
QED
