(* Empty sequential members execute without touching the actual state. *)
Theory ctorAbiActualMembers
Ancestors
  ctorAbiActualReentry abiDecoderMemberInfos abiDecoderMembers
  abiDecoderLoop abiEncoderRegisteredEffect abiEncoder exprLowering compileEnv
  valueEncoding venomState list

Theorem ctor_actual_members_nil:
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi
    (abi_decoder_member_infos sf ce []) ao vo st = ((),st') /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory [] [] (d+vo) actual.vs_memory /\
    abi_encoder_registered_effect (frag_ids st st') [(d,n)] initial actual /\
    (alloca_inv actual <=> alloca_inv initial) /\
    (alloca_frontier_inv ctx func site actual <=>
      alloca_frontier_inv ctx func site initial) /\
    (fresh_vars_wrt limit_st actual <=> fresh_vars_wrt limit_st initial) /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    (!x. lookup_var x actual = lookup_var x initial) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def] >> strip_tac >> gvs[] >>
  qexists `initial` >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl,
    abi_decode_sim_refl]
QED
