(* Decoder instruction credits bound aggregate cardinalities. *)
Theory extcallDecoderBudgetBounds
Ancestors
  abiDecoderAllocation abiDecoderComplexGuard abiDecoderMemberCode
  abiDecoderMemberInfos abiDecoderComplexHead abiDecoderRange
  abiDecoderMemberSetup abiDecoderTypedContract abiDecoderContract
  abiEncoder exprLowering compileEnv emitHelper venomInst vyperAST
  emitHelperProps exprLoweringProps finite_map pred_set arithmetic list words pair

Theorem decoder_registered_sites_bound[local]:
  FINITE (ids:num set) /\
  (!i. i IN ids ==> ?p. FLOOKUP m i = SOME (p,32) /\ p < top) /\
  (!i j p q. i IN ids /\ j IN ids /\ i <> j /\
    FLOOKUP m i = SOME (p,32) /\ FLOOKUP m j = SOME (q,32) ==>
    p + 32 <= q \/ q + 32 <= p) ==>
  CARD ids <= top
Proof
  strip_tac >>
  `INJ (\i. FST (THE (FLOOKUP m i))) ids (count top)` by
    (simp[INJ_DEF] >> conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!i. i IN ids ==> _` drule >> strip_tac >> simp[]) >>
     rpt strip_tac >>
     rename1 `FST (THE (FLOOKUP m x)) = FST (THE (FLOOKUP m y))` >>
     `?p. FLOOKUP m x = SOME (p,32) /\ p < top` by metis_tac[] >>
     `?q. FLOOKUP m y = SOME (q,32) /\ q < top` by metis_tac[] >>
     gvs[] >> Cases_on `x = y` >> simp[] >>
     qpat_x_assum `!i j p q. _` (qspecl_then [`x`, `y`, `p`, `p`] mp_tac) >> simp[]) >>
  drule INJ_CARD >> simp[]
QED

Theorem extcall_decoder_budget_ids_bound:
  abi_decoder_budget first last b cap s ==>
  CARD (abi_decoder_ids first last) < dimword(:256)
Proof
  rw[abi_decoder_budget_def] >>
  qabbrev_tac `present = abi_decoder_ids first last INTER FDOM s.vs_allocas` >>
  `CARD present <= s.vs_alloca_next` by
    (irule (Q.INST [`m` |-> `s.vs_allocas`] decoder_registered_sites_bound) >>
     simp_tac std_ss [Abbr `present`, FINITE_INTER, FDOM_FINITE,
       abi_decoder_ids_finite, IN_INTER] >>
     qexists_tac `s` >> conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `?p sz. FLOOKUP s.vs_allocas i = SOME (p,sz)` by
       metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME, pairTheory.pair_CASES] >>
     qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` (qspecl_then [`i`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >>
     qexists_tac `p` >> simp[] >> decide_tac) >>
  `CARD (abi_decoder_missing first last s) =
   CARD (abi_decoder_ids first last) - CARD present` by
    simp[abi_decoder_missing_def, Abbr `present`, CARD_DIFF] >>
  `CARD present <= CARD (abi_decoder_ids first last)` by
    (irule CARD_SUBSET >> simp[Abbr `present`, INTER_SUBSET]) >>
  decide_tac
QED

Theorem extcall_decoder_ids_cardinality:
  CARD (abi_decoder_ids first last) = last - first
Proof
  `abi_decoder_ids first last = count last DIFF count first` by
    (simp[abi_decoder_ids_def, EXTENSION] >> decide_tac) >>
  simp[CARD_DIFF] >>
  Cases_on `first <= last`
  >- (`count last INTER count first = count first` by
        (simp[EXTENSION] >> decide_tac) >> simp[]) >>
  `count last INTER count first = count last` by
    (simp[EXTENSION] >> decide_tac) >> simp[]
QED

Theorem extcall_decoder_members_id_bound:
  !infos dst src opc base_op hi ao vo st fin.
  compile_abi_decode_complex_elems dst src opc base_op hi infos ao vo st = ((),fin) /\
  abi_decode_source_opcode opc ==>
  LENGTH infos <= fin.cs_next_id - st.cs_next_id
Proof
  Induct
  >- simp[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  Cases_on `h` >> Cases_on `r` >>
  simp[abi_decode_complex_member_phases, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `abi_decode_member_setup dst src opc base_op hi _ ao vo st = (ops,setup)` >>
  rename1 `compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi q setup = ((),child)` >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `setup.cs_next_id <= child.cs_next_id` by
    metis_tac[CONJUNCT1 ci_mono_compile_abi_decode, ci_mono_def, SND] >>
  `child.cs_next_id <= fin.cs_next_id` by
    metis_tac[CONJUNCT1 (CONJUNCT2 ci_mono_compile_abi_decode), ci_mono_def, SND] >>
  `LENGTH infos <= fin.cs_next_id - child.cs_next_id` by metis_tac[] >>
  decide_tac
QED
Theorem extcall_decoder_guard_id_strict:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\ hi <> Lit 0w ==>
  st.cs_next_id < fin.cs_next_id
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem extcall_decoder_complex_id_bound:
  compile_abi_decode_to_buf dst src opc base_op hi (DecComplex dyn infos) st = ((),fin) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w ==>
  LENGTH infos + abi_decoder_entry_floor st <= fin.cs_next_id
Proof
  simp[abi_decode_complex_phases, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `compile_abi_decode_complex_elems dst src opc base_op hi infos 0 0 middle = ((),fin)` >>
  `middle.cs_next_id <= fin.cs_next_id` by
    metis_tac[CONJUNCT1 (CONJUNCT2 ci_mono_compile_abi_decode), ci_mono_def, SND] >>
  drule_all extcall_decoder_guard_id_strict >>
  drule_all extcall_decoder_members_id_bound >>
  simp[abi_decoder_entry_floor_def] >> decide_tac
QED

Theorem extcall_decoder_tuple_budget_bound:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce (TupleT tys)) st = ((),fin) /\
  hi <> Lit 0w /\ abi_decoder_budget first last b cap s /\
  first <= abi_decoder_entry_floor st /\ fin.cs_next_id <= last ==>
  LENGTH tys < dimword(:256)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[abi_decoder_tuple_infos] >> strip_tac >>
  drule extcall_decoder_complex_id_bound >>
  simp[abi_decode_source_opcode_def, abi_decoder_member_infos_def] >> strip_tac >>
  drule extcall_decoder_budget_ids_bound >>
  simp[extcall_decoder_ids_cardinality] >> decide_tac
QED

