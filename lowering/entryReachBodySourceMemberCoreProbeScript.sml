(* Checked source-cursor adapters for the metadata-independent member engine.
   This is not a proof of recursive source decoder closure. *)
Theory entryReachBodySourceMemberCoreProbe
Ancestors
  entryReachBodyMemberExecutionCore entryReachBodySourceAggregateInputs
  entryReachBodySourceMemberEntry entryReachBodyMemberSetup
  abiDecoderCoherence abiDecoderEmpty abiDecoderOffset abiDecoderDynamic
  abiDecoderComplexHead abiDecoderContract abiEncoder compileEnv
  valueEncoding list arithmetic words

Definition entry_source_probe_cursor_def:
  entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d
    pre tys (st:compile_state) s <=>
    ?pretvs preavs prevs tvs avs vs.
      fulltys = pre ++ tys /\ fulltvs = pretvs ++ tvs /\
      fullavs = preavs ++ avs /\ fullvs = prevs ++ vs /\
      entry_source_members ce env sf pre pretvs preavs prevs /\
      entry_source_members ce env sf tys tvs avs vs /\
      mem_bytes_at sb
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)))
        (abi_decode_source CALLDATALOAD s) =
        enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs) /\
      tuple_in_memory prevs pretvs d s.vs_memory
End

Theorem source_probe_head_sizes[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) =
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys))
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def] >> rpt strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >> simp[] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem source_probe_cursor_offsets:
  entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d pre tys st s ==>
  SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre) =
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pre))
Proof
  simp_tac bool_ss [entry_source_probe_cursor_def] >> strip_tac >>
  irule source_probe_head_sizes >> goal_assum (drule_at Any)
QED

(* The empty dynamic case supplies its value for every memory, without
   a child producer or a dynamic-offset navigation premise. *)
Theorem source_probe_empty_value[local]:
  entry_source_probe_cursor ce env sf fulltys fulltvs fullavs fullvs sb d
    pre (ty::tys) st s /\ type_to_abi_dec_info sf ce ty = DecComplex T [] ==>
  ?tv av v tvs avs vs.
    entry_source_members ce env sf tys tvs avs vs /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_source_metadata ce env sf ty tv (DecComplex T []) av v /\
    type_memory_bytes ce ty = 0 /\ type_memory_size tv = 0 /\
    (!cell mem. val_in_memory tv v cell mem)
Proof
  simp_tac bool_ss [entry_source_probe_cursor_def] >> strip_tac >>
  Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  gvs[entry_source_members_def, Excl "enc_def"] >>
  drule_all entry_source_empty_descriptor_value >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]
QED

(* Typechecked instantiation of the engine with source-only semantic input.
   The callback is deliberately left as a premise: recursive closure is a
   later obligation, not something this probe assumes has been established. *)
Theorem source_probe_execution:
  entry_members_callback
    (entry_source_probe_cursor ce env sf tys tvs avs vs sb d)
    cert sf ce ctx fn oid root extent sites b cap site limit_st dst src sb d outsz /\
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  entry_source_probe_cursor ce env sf tys tvs avs vs sb d [] tys st s /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys) 0 0 st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
  oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. tuple_in_memory vs tvs d t.vs_memory /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz last t /\
    canonical_members_effect ctx fn sites d outsz st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,outsz)] s t
Proof
  strip_tac >> drule_all entry_members_execution >> strip_tac >>
  qpat_x_assum `entry_source_probe_cursor _ _ _ _ _ _ _ _ _ tys [] last t`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_source_probe_cursor_def]) >>
  `tvs' = [] /\ avs' = [] /\ vs' = []` by
    metis_tac[entry_source_members_lengths, LENGTH_NIL] >>
  gvs[APPEND_NIL, Excl "enc_def"] >> qexists_tac `t` >> asm_rewrite_tac[]
QED
