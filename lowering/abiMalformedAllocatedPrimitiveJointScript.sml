(* Invalid primitive payloads take the actual checked assertion-revert path. *)
Theory abiMalformedAllocatedPrimitiveJoint
Ancestors
  abiMalformedConstructorContract abiMalformedRecursiveInterface
  abiDecoderCoherence abiDecoderWordTyped abiDecoderClampedWord
  abiDecoderContract abiDecoderReentry abiDecoderReentryPointer
  abiDecodePtrWordJoint abiDecodePtrMemberFrame abiDecodePtrRejectChecks
  abiValidAllocatedObservations
  loweringStateRelDefs exprLoweringProps bodyPtrDefs ptrDiscipline
  compileEnv venomState venomExecSemantics words list arithmetic

Theorem abi_malformed_allocated_primitive_joint:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecPrimWord clamp) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d 32 s /\
  p+32 <= L /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 (DROP p xs)) /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) (TAKE 32 (DROP p xs)))) /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s 32 /\ op_taint tn pos = {} /\
  allocas_from lo s ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?av. has_type (vyper_to_abi_type env ty) av` strip_assume_tac >>
  `?u. run_inst_seq (emitted_insts st en) s = Abort Revert_abort u` by
    (drule_all (abi_malformed_primitive_reflected_run |>
       Q.INST [`outsz` |-> `32`] |> SRULE [PULL_EXISTS]) >>
     strip_tac >- metis_tac[] >>
     fs[abi_malformed_reflected_post_def]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decode_revert_witness >> strip_tac >>
  drule_all abi_valid_allocated_revert_observations >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all abi_malformed_allocated_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `B+L < dimword(:256)` by fs[abi_malformed_allocated_window_def] >>
  `B < dimword(:256) /\ d < dimword(:256)` by decide_tac >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[EVERY_DEF, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >>
  `lookup_var output s = SOME (n2w d)` by fs[eval_operand_def] >>
  fs[] >>
  mp_tac (abi_decode_word_abort_joint |>
    Q.INST [`d` |-> `destination_word`] |> Q.INST
      [`sa` |-> `st`, `sb` |-> `en`, `src` |-> `source`,
       `dst` |-> `output`, `b` |-> `n2w B`, `h` |-> `L`,
       `destination_word` |-> `n2w d`, `u` |-> `u`, `s` |-> `s`,
       `a` |-> `Revert_abort`]) >>
  (impl_tac >- simp[w2n_n2w]) >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := j`, `G'`, `tn'`] >> simp[]
QED
