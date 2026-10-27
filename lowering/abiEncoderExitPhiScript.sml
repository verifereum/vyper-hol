(* Nonempty exit prefixes close PHI provenance in arbitrary containing functions. *)
Theory abiEncoderExitPhi
Ancestors
  abiEncoderPhi abiEncoderAppend fragExec abiEncoder compileEnv emitHelper
  emitHelperProps context venomExecSemantics list rich_list pair

Definition abi_encoder_exit_nonempty_def:
  abi_encoder_exit_nonempty (m : 'a compiler) <=>
    !st out st'. m st = (out,st') ==> st'.cs_current_insts <> []
End

Definition abi_encoder_empty_preserving_def:
  abi_encoder_empty_preserving (m : 'a compiler) <=>
    !st out st'. m st = (out,st') /\ st'.cs_current_insts = [] ==>
      st.cs_current_insts = [] /\ st.cs_blocks = st'.cs_blocks
End

Theorem abi_encoder_exit_nonempty_bind:
  (!v. abi_encoder_exit_nonempty (f v)) ==>
  abi_encoder_exit_nonempty (comp_bind m f)
Proof
  simp[abi_encoder_exit_nonempty_def, comp_bind_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_encoder_exit_nonempty_ignore:
  abi_encoder_exit_nonempty f ==>
  abi_encoder_exit_nonempty (comp_ignore_bind m f)
Proof
  simp[comp_ignore_bind_def, abi_encoder_exit_nonempty_bind]
QED

Theorem abi_encoder_exit_nonempty_emit:
  (!opc ops. abi_encoder_exit_nonempty (emit_op opc ops)) /\
  (!opc ops. abi_encoder_exit_nonempty (emit_void opc ops))
Proof
  simp[abi_encoder_exit_nonempty_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def]
QED

Theorem abi_encoder_nonempty_preserving:
  abi_encoder_exit_nonempty m ==> abi_encoder_empty_preserving m
Proof
  simp[abi_encoder_exit_nonempty_def, abi_encoder_empty_preserving_def] >>
  metis_tac[]
QED

Theorem abi_encoder_empty_preserving_bind:
  abi_encoder_empty_preserving m /\ (!v. abi_encoder_empty_preserving (f v)) ==>
  abi_encoder_empty_preserving (comp_bind m f)
Proof
  simp[abi_encoder_empty_preserving_def, comp_bind_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_encoder_empty_preserving_ignore:
  abi_encoder_empty_preserving m /\ abi_encoder_empty_preserving f ==>
  abi_encoder_empty_preserving (comp_ignore_bind m f)
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule abi_encoder_empty_preserving_bind >> simp[]
QED

Theorem abi_encoder_empty_preserving_return:
  abi_encoder_empty_preserving (comp_return v)
Proof
  simp[abi_encoder_empty_preserving_def, comp_return_def]
QED

fun exit_nonempty_tac g =
  (FIRST [FIRST_PROVE [simp[abi_encoder_exit_nonempty_emit]],
    ho_match_mp_tac abi_encoder_exit_nonempty_bind >> gen_tac >> exit_nonempty_tac,
    ho_match_mp_tac abi_encoder_exit_nonempty_ignore >> exit_nonempty_tac]) g;

Theorem abi_encoder_empty_preserving_prims:
  (!opc ops. abi_encoder_empty_preserving (emit_op opc ops)) /\
  (!opc ops. abi_encoder_empty_preserving (emit_void opc ops)) /\
  abi_encoder_empty_preserving fresh_var /\
  abi_encoder_empty_preserving fresh_id /\
  (!sfx. abi_encoder_empty_preserving (fresh_label sfx))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> irule abi_encoder_nonempty_preserving >>
      simp[abi_encoder_exit_nonempty_emit])
  >- (rpt gen_tac >> irule abi_encoder_nonempty_preserving >>
      simp[abi_encoder_exit_nonempty_emit]) >>
  simp[abi_encoder_empty_preserving_def, fresh_var_def, fresh_id_def,
    fresh_label_def]
QED

fun empty_preserving_tac extra g =
  (FIRST [irule abi_encoder_nonempty_preserving >> exit_nonempty_tac,
    FIRST_PROVE [simp (extra @ [abi_encoder_empty_preserving_prims,
      abi_encoder_empty_preserving_return, LET_THM])],
    first_x_assum irule,
    ho_match_mp_tac abi_encoder_empty_preserving_bind >> conj_tac
      >- empty_preserving_tac extra >> gen_tac >> empty_preserving_tac extra,
    ho_match_mp_tac abi_encoder_empty_preserving_ignore >> conj_tac >> empty_preserving_tac extra,
    IF_CASES_TAC >> fs[] >> empty_preserving_tac extra]) g;

Theorem abi_encoder_empty_preserving_alloc:
  abi_encoder_empty_preserving (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> empty_preserving_tac []
QED

Theorem abi_encoder_empty_preserving_static:
  abi_encoder_empty_preserving (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >> empty_preserving_tac []
QED

Theorem abi_encoder_empty_preserving_mutual:
  (!dst src ei dyn off ptr.
    abi_encoder_empty_preserving (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei.
    abi_encoder_empty_preserving (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    abi_encoder_empty_preserving (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    abi_encoder_empty_preserving (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  empty_preserving_tac [abi_encoder_empty_preserving_alloc,
    abi_encoder_empty_preserving_static]
QED

Theorem abi_encoder_core_exit_nonempty:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  st.cs_blocks <> st'.cs_blocks ==> st'.cs_current_insts <> []
Proof
  mp_tac (cj 2 abi_encoder_empty_preserving_mutual) >>
  simp_tac bool_ss [abi_encoder_empty_preserving_def] >> metis_tac[]
QED

Theorem abi_encoder_nonempty_prefix_phi:
  isPREFIX prefix insts /\ prefix <> [] /\ phi_prefix_length prefix = 0 ==>
  phi_prefix_length insts = 0
Proof
  Cases_on `prefix` >> simp[] >>
  Cases_on `insts` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
QED

Theorem abi_encoder_core_containing_exit_phi:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  fn_has_code st st' func ==>
  st.cs_blocks = st'.cs_blocks \/
  (!bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> Cases_on `st.cs_blocks = st'.cs_blocks` >> simp[] >>
  `st'.cs_current_insts <> []` by (drule_all abi_encoder_core_exit_nonempty >> simp[]) >>
  `phi_prefix_length st'.cs_current_insts = 0` by
    (drule abi_encoder_core_exit_phi >> simp[]) >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp_tac bool_ss [fn_has_code_def] >> strip_tac >>
  rpt strip_tac >> gvs[] >> irule abi_encoder_nonempty_prefix_phi >>
  qexists_tac `st'.cs_current_insts` >> simp[]
QED
