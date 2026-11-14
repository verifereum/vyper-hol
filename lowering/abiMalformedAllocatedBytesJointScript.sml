(* Malformed bytestrings replay the fresh abort certificate on the actual state. *)
Theory abiMalformedAllocatedBytesJoint
Ancestors
  abiMalformedBulkConstructor abiMalformedRecursiveInterface
  abiDecodePtrBytesAbort abiDecodeBytesMem abiDecodePtrBytesJoint
  abiDecodePtrReentry abiDecodePtrReentryGhost abiDecodeMemReentry
  abiDecodePtrMemberFrame abiDecodePtrRejectChecks
  abiDecoderAbortReentry abiDecoderReentry abiDecoderReentryPointer abiDecoderVarExtend
  abiValidAllocatedObservations abiDecoderBytes abiDecoderBytesFrame abiDecoderContract
  fragGasCopyLoop fragGasOriginPtrDead fragGasSeqPtr fragExecMem
  loweringStateRelDefs exprLoweringProps bodyPtrDefs ptrDiscipline
  compileEnv venomState venomExecSemantics words list arithmetic contractABI

Theorem abi_malformed_allocated_bytes_joint:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecBytestring n) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP p xs) /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) (DROP p xs))) /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\ allocas_from lo s ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ps = abi_decoder_prune_vars st.cs_next_var s` >>
  drule abi_malformed_entry_prune >> strip_tac >>
  `abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) ps` by
    simp[Abbr `ps`] >>
  `fresh_vars_wrt ceiling ps` by
    fs[Abbr `ps`, fresh_vars_wrt_def, abi_decoder_prune_vars_def,
       finite_mapTheory.FDOM_DRESTRICT] >>
  `?clean. run_inst_seq (emitted_insts st en) ps = Abort Revert_abort clean` by
    (drule_all (abi_malformed_bytestring_reentry |> Q.INST
       [`s` |-> `ps`, `outsz` |-> `type_memory_bytes ce ty`,
        `base_op` |-> `Var source`] |> SRULE []) >> metis_tac[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  mp_tac (abi_decoder_sequence_revert_reentry |> Q.INST
    [`initial` |-> `s`, `next` |-> `st.cs_next_var`,
     `insts` |-> `emitted_insts st en`, `clean` |-> `clean`]) >>
  (impl_tac >- simp[Abbr `ps`]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = Abort Revert_abort actual` >>
  `abi_decode_reject_witness (emitted_insts st en) s actual` by
    (irule abi_decode_revert_witness >> simp[]) >>
  drule_all abi_valid_allocated_revert_observations >> strip_tac >>
  qpat_assum `abi_malformed_entry H0 ctx func cenv cx es st _ dstid live
      (Var source) hi pos (Var output) B L xs p d _ s`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all abi_malformed_allocated_bounds >> strip_tac >>
  drule_all (abi_malformed_bytestring_capacity |>
    Q.INST [`outsz` |-> `type_memory_bytes ce ty`] |> SRULE []) >> strip_tac >>
  `B+L < dimword(:256)` by fs[abi_malformed_allocated_window_def] >>
  `B < dimword(:256) /\ d < dimword(:256) /\ n+31 < dimword(:256)` by
    decide_tac >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[EVERY_DEF, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >>
  `lookup_var output s = SOME (n2w d)` by fs[eval_operand_def] >>
  `abi_decode_ptr_window G tn ps source (n2w B) L /\
   ptr_covers G tn output ps (type_memory_bytes ce ty) /\
   allocas_from lo ps /\ fresh_vars_wrt st ps /\
   lookup_var output ps = SOME (n2w d) /\
   eval_operand pos ps = SOME (n2w p) /\ eval_operand hi ps = SOME (n2w L)` by
    (fs[abi_decode_ptr_window_def] >>
     simp[Abbr `ps`, abi_decode_ptr_prune_covers, abi_decoder_prune_fresh,
       abi_decoder_prune_eval, abi_decoder_prune_vars_def,
       eval_operand_def, lookup_var_def, allocas_from_def,
       finite_mapTheory.FLOOKUP_DRESTRICT] >>
     fs[allocas_from_def, abi_decoder_older_vars_def, not_fresh_at_def,
        lookup_var_def] >> metis_tac[]) >>
  mp_tac (abi_decode_bytes_member_abort_ptr |>
    Q.INST [`d` |-> `destination_word`] |> Q.INST
      [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
          d_imm := K {}; d_ret := K {}|>`,
       `sa` |-> `st`, `sb` |-> `en`, `src` |-> `source`, `dst` |-> `output`,
       `b` |-> `n2w B`, `h` |-> `L`, `destination_word` |-> `n2w d`,
       `cap` |-> `type_memory_bytes ce ty`, `s` |-> `ps`, `u` |-> `clean`,
       `a` |-> `Revert_abort`]) >>
  (impl_tac >- (simp[Abbr `ps`, abi_decoder_prune_vars_def, w2n_n2w,
     contractABITheory.ceil32_def] >> decide_tac)) >>
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) ps` by
    (mp_tac (abi_decode_bytes_member_checked_mem_ok |>
       Q.INST [`d` |-> `destination_word`] |> Q.INST
         [`s` |-> `ps`, `src` |-> `source`, `dst` |-> `output`,
          `b` |-> `n2w B`, `destination_word` |-> `n2w d`, `h` |-> `L`]) >>
     (impl_tac >- (simp[Abbr `ps`, abi_decoder_prune_vars_def, w2n_n2w,
        contractABITheory.ceil32_def] >>
        fs[abi_decoder_prune_vars_def, abi_decode_ptr_window_def,
           lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
           abi_decoder_older_vars_def, not_fresh_at_def] >>
        metis_tac[])) >> simp[]) >>
  `abi_decoder_vars_extend s.vs_vars ps s` by
    simp[Abbr `ps`, abi_decoder_prune_extension] >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule abi_decode_sequence_mem_reentry_result >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      0 ctx func PG G tn (emitted_insts st en) s Gf tnf` by
    (mp_tac (Q.SPECL [`emitted_insts st en`, `s.vs_vars`, `ps`, `s`, `clean`,
       `G`, `tn`, `Gf`, `tnf`] (abi_decode_ptr_sequence_reentry_result |>
         Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
             d_imm := K {}; d_ret := K {}|>`, `lo` |-> `0`, `fn` |-> `func`])) >>
     (impl_tac >- fs[EVERY_CONJ]) >> simp[]) >>
  drule_all abi_decode_bytes_joint_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      lo ctx func PG G tn (emitted_insts st en) s Gf tnf` by
    (irule (inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
     simp[] >> fs[EVERY_MEM]) >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (actual with vs_inst_idx := j),Gf,tnf)` by
    (gen_tac >> qpat_assum `!D lo explicit PG G tn HG th. _`
       (qspecl_then
         [`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
          `lo`, `explicit`, `PG`, `G`, `tn`, `Gf`, `tnf`] irule) >> simp[]) >>
  qexistsl_tac [`actual with vs_inst_idx := j`, `Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED
