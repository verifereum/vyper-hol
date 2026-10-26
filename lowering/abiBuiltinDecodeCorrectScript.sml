(* Canonical-success execution of the complete lower_abi_decode action.
   The incoming metadata, bytes and allocation bounds are pure predicates;
   setup and recursive body execution are both proved below. *)
Theory abiBuiltinDecodeCorrect
Ancestors
  abiBuiltinCanonicalPre abiBuiltinDecodeCode abiBuiltinSetupReach abiBuiltinSetupExecute
  abiBuiltinDecodeSetup abiBuiltinAllocationState abiBuiltinDecodeEffect
  abiDecoderCoherentCorrect abiDecoderEffect abiDecoderAllocation abiDecoderReentry
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderLoop
  abiEncoder builtinAbi fragExec compileEnv valueEncoding vyperABI contractABI
  venomState venomExecSemantics words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_DECODE_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin canonical decoding not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinDecodeCorrect");
