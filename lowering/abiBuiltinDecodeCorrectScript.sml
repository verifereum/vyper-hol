Theory abiBuiltinDecodeCorrect
Ancestors
  abiBuiltinDecodeSetup abiDecoderAppend abiDecoderCounters abiDecoderCode abiDecoderContract
  abiEncoder builtinAbi fragExec compileEnv list arithmetic abiBuiltinCanonicalPre
  abiBuiltinSetupReach abiBuiltinAllocation abiBuiltinDecodeEffect abiDecoderCoherentCorrect
  abiDecoderEffect abiDecoderAllocation abiDecoderReentry abiDecoderCoherence
  abiDecoderTypedContract abiDecoderLoop valueEncoding vyperABI contractABI venomState
  venomExecSemantics words

(* Containment and counters for the actual builtin setup and decoder body. *)
Theorem lower_abi_decode_setup_trace:
  lower_abi_decode data info min_size max_size outsz st = (out,final) ==>
  ?ops ready.
    abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (FST (SND ops)) MLOAD (SND (SND ops)) info ready =
      ((),final) /\ out = FST ops
Proof
  simp_tac bool_ss [lower_abi_decode_setup, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready)` >>
  qexistsl_tac [`ops`, `ready`] >> simp[]
QED

Theorem abi_builtin_decode_code:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  compile_abi_decode_to_buf (FST ops) (FST (SND ops)) MLOAD (SND (SND ops)) info ready =
    ((),final) /\ fn_has_code st final func ==>
  fn_has_code st ready func /\ fn_has_code ready final func /\
  ready.cs_blocks = st.cs_blocks /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= final.cs_next_var /\
  st.cs_next_id <= abi_builtin_decode_output_site st min_size max_size /\
  abi_builtin_decode_output_site st min_size max_size < ready.cs_next_id /\
  ready.cs_next_id <= final.cs_next_id
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st ready` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_to_buf_code >> simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  asm_simp_tac bool_ss [abi_builtin_decode_output_site_def] >> decide_tac
QED

(* Canonical-success execution of the complete lower_abi_decode action.
   The incoming metadata, bytes and allocation bounds are pure predicates;
   setup and recursive body execution are both proved below. *)
Theorem lower_abi_decode_canonical:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_canonical_pre ce env sf ty tv av v start first last data min_size max_size
    src_base d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  qpat_assum `abi_builtin_canonical_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_canonical_pre_def]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ src_base < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `p` |-> `n2w src_base:bytes32`,
    `outsz` |-> `type_memory_bytes ce ty`,
    `cnt` |-> `LENGTH (enc (vyper_to_abi_type env ty) av)`] abi_builtin_decode_setup_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST (SND ops)) prepared = SOME (n2w (src_base + 32)) /\
   eval_operand (SND (SND ops)) prepared =
     SOME (n2w (src_base + 32 + LENGTH (enc (vyper_to_abi_type env ty) av)))`
    by asm_simp_tac (srw_ss()) [word_add_n2w] >>
  drule_all abi_builtin_canonical_pre_ready >> strip_tac >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `final`, `opc` |-> `MLOAD`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`,
    `sb` |-> `src_base + 32`, `initial` |-> `prepared:venom_state`] abi_decoder_decode) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w d)` by fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`st` |-> `start`,
    `site` |-> `abi_builtin_decode_output_site start min_size max_size`,
    `outsz` |-> `type_memory_bytes ce ty`] abi_builtin_decode_effect_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
