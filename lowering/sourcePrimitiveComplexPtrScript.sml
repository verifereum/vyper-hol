(* Finite canonical complex decoders: compiler and prefix frame boundaries. *)
Theory sourcePrimitiveComplexPtr
Ancestors canonicalMemberTraversalPtr robustCopyTransportPtr abiDecoderFrameCompose
  abiEncoderInput valueTypingMemoryProps exprSim abiDecoderMemberSetup
  emitHelperProps compileEnv abiDecoderContract bodyPtrDefs
  list rich_list arithmetic pred_set abiDecoderMemberCons abiEncoder
  abiDecoderCode fragExec

Theorem member_setup_entry_freshness[local]:
  abi_decode_member_setup dst src opc hi dyn ao vo sa = (ops,mid) /\
  fresh_vars_wrt sa s ==> fresh_vars_wrt mid s
Proof
  strip_tac >> drule abi_decode_member_setup_counters >> strip_tac >>
  irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[] >>
  Cases_on `dyn` >> simp[] >> Cases_on `hi = Lit 0w` >> simp[]
QED

Theorem decoded_tuple_prefix_robust_frame:
  LIST_REL value_has_type tvs vs /\ k <= LENGTH tvs /\
  abi_decode_frame (d + SUM (MAP type_memory_size (TAKE k tvs))) C s t /\
  u.t_mem SUBSET tn.t_mem /\
  (!i. i < k ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
  !i. i < k ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)
Proof
  rpt strip_tac >>
  `i < LENGTH tvs /\ value_has_type (EL i tvs) (EL i vs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `val_wf (EL i tvs) (EL i vs)` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint (EL i tvs) (EL i vs) <= type_memory_size (EL i tvs)` by
    metis_tac[val_footprint_le] >>
  `SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
    SUM (MAP type_memory_size (TAKE k tvs))` by
    (qspec_then `type_memory_size` mp_tac abi_encoder_prefix_sum_bound >>
     disch_then (qspecl_then [`TAKE k tvs`, `i`] mp_tac) >>
     simp[TAKE_TAKE, EL_TAKE, MIN_DEF]) >>
  `mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
    (val_footprint (EL i tvs) (EL i vs)) t.vs_memory =
    mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
      (val_footprint (EL i tvs) (EL i vs)) s.vs_memory` by
    (gvs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (metis_tac[calldata_member_robust_window_frame]) >>
  simp[] >> first_x_assum irule >> simp[mem_agree_outside_def]
QED

Theorem complex_member_phase_code[local]:
  compile_abi_decode_complex_elems dst src opc hi ((ei,az,mz)::rest)
    ao vo sa = ((),sb) /\ abi_decode_source_opcode opc /\
  fn_has_code sa sb fn /\ fresh_vars_wrt sa s ==>
  ?ops mid en.
    abi_decode_member_setup dst src opc hi (dec_info_needs_offset ei)
      ao vo sa = (ops,mid) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc hi ei mid = ((),en) /\
    compile_abi_decode_complex_elems dst src opc hi rest (ao+az) (vo+mz) en = ((),sb) /\
    fn_has_code sa mid fn /\ fn_has_code mid en fn /\ fn_has_code en sb fn /\
    cs_extends sa mid /\ cs_extends mid en /\ cs_extends en sb /\
    fresh_vars_wrt mid s
Proof
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup dst src opc hi _ ao vo sa = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ opc hi ei mid = ((),en)` >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code sa mid fn /\ fn_has_code mid en fn` by
    (metis_tac[fn_has_code_split]) >>
  `fresh_vars_wrt mid s` by metis_tac[member_setup_entry_freshness] >>
  simp[]
QED
