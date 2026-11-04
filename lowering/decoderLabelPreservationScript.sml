(* Label provenance for recursive ABI decoder compilation. *)
Theory decoderLabelPreservation
Ancestors
  entryLabelPreservation abiDecoderAppend abiEncoder fragExec compileEnv
  emitHelper loweringShapeDefs context list

Theorem added_labels_same_blocks[local]:
  s.cs_blocks = t.cs_blocks /\ s.cs_current_bb = t.cs_current_bb ==>
  added_labels s t = []
Proof
  strip_tac >>
  simp[added_labels_def, all_blocks_def, DROP_APPEND, LENGTH_MAP,
       DROP_LENGTH_TOO_LONG]
QED

Theorem label_preserving_fresh_var[local]:
  !s r t. fresh_var s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rpt strip_tac >>
  `cs_extends s t` by metis_tac[cs_extends_fresh_var] >>
  `added_labels s t = []` by
    (irule added_labels_same_blocks >> gvs[fresh_var_def]) >> simp[]
QED

Theorem label_preserving_fresh_id[local]:
  !s r t. fresh_id s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rpt strip_tac >>
  `cs_extends s t` by metis_tac[cs_extends_fresh_id] >>
  `added_labels s t = []` by
    (irule added_labels_same_blocks >> gvs[fresh_id_def]) >> simp[]
QED

Theorem label_preserving_emit[local]:
  !s r t. emit inst s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rpt strip_tac >>
  `cs_extends s t` by metis_tac[cs_extends_emit] >>
  `added_labels s t = []` by
    (irule added_labels_same_blocks >> gvs[emit_def]) >> simp[]
QED

val label_simps = [label_preserving_return, label_preserving_fresh_var,
  label_preserving_fresh_id, label_preserving_emit, label_preserving_emit_inst];
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt strip_tac >> metis_tac label_simps) >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (rpt strip_tac >> metis_tac label_simps);

Theorem label_preserving_emit_op[local]:
  !s r t. emit_op opc ops s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[emit_op_def] >> ntac 2 LABEL_BIND >> LABEL_IGNORE >>
  rpt strip_tac >> metis_tac label_simps
QED

Theorem label_preserving_emit_void[local]:
  !s r t. emit_void opc ops s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[emit_void_def] >> LABEL_BIND >>
  rpt strip_tac >> metis_tac label_simps
QED

val label_simps = label_simps @ [label_preserving_emit_op, label_preserving_emit_void];
val LABEL_BIND = ho_match_mp_tac label_preserving_bind >> conj_tac
  >- (rpt strip_tac >> metis_tac label_simps) >> gen_tac;
val LABEL_IGNORE = ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (rpt strip_tac >> metis_tac label_simps);

Theorem label_preserving_abi_clamp:
  !c v s r t. compile_abi_clamp_basetype v c s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  Cases >> simp_tac pure_ss [compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def] >>
  gen_tac >>
  rpt (IF_CASES_TAC >> simp_tac pure_ss [LET_THM])
  >- metis_tac[label_preserving_return] >>
  simp_tac pure_ss [LET_THM] >> ntac 2 LABEL_BIND >> rpt strip_tac >> metis_tac label_simps
QED

Theorem label_preserving_abi_static:
  (!v s r t. clamp v s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) ==>
  !s r t. compile_abi_decode_static src dst opc clamp s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  LABEL_BIND >> LABEL_IGNORE >> rpt strip_tac >> metis_tac label_simps
QED

Theorem label_preserving_abi_alloc_buffer:
  !s r t. compile_alloc_buffer n s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> LABEL_BIND >>
  rpt strip_tac >> metis_tac label_simps
QED

Theorem label_preserving_abi_member_pointer:
  !s r t. compile_getelemptr_abi src dyn off opc hi s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> LABEL_BIND >>
  Cases_on `dyn` >> simp_tac bool_ss []
  >- (ntac 2 LABEL_BIND >>
      ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
      >- (IF_CASES_TAC
          >- (rpt strip_tac >> metis_tac label_simps) >>
          ntac 2 LABEL_BIND >> rpt strip_tac >> metis_tac label_simps) >>
      rpt strip_tac >> metis_tac label_simps) >>
  rpt strip_tac >> metis_tac label_simps
QED

Theorem label_preserving_abi_array_pointer:
  !s r t. compile_abi_decode_dyn_elem_ptr opc src data hi sz s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >> ntac 2 LABEL_BIND >>
  ho_match_mp_tac label_preserving_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (rpt strip_tac >> metis_tac label_simps) >>
      ntac 2 LABEL_BIND >> LABEL_IGNORE >> ntac 3 LABEL_BIND >>
      rpt strip_tac >> metis_tac label_simps) >>
  rpt strip_tac >> metis_tac label_simps
QED
