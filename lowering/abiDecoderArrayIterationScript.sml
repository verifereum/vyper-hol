(* A generated primitive body advances the invariant at any valid cursor. *)
Theory abiDecoderArrayIteration
Ancestors
  abiDecoderArrayInvariant abiDecoderArrayAdvance abiDecoderPrimitiveLoopFragment
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderLoopSetup exprLoweringProps emitHelperProps compileEnv valueEncoding
  abiDecoderPrimitiveLoopFragment fragExec instIdxIndep
  vyperABI vyperTyping venomState contractABI words list rich_list arithmetic

Theorem abi_decoder_array_memory_inst_idx[simp]:
  abi_decoder_array_memory opc aty avs tv vs sb d j (s with vs_inst_idx := ix) <=>
  abi_decoder_array_memory opc aty avs tv vs sb d j s
Proof
  simp[abi_decoder_array_memory_def, abi_decode_source_def, Excl "enc_def"]
QED

Theorem abi_decoder_primitive_array_iteration:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d j initial /\
  j < LENGTH vs /\ abi_decode_source_opcode opc /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= d \/
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= sb) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var ip /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d (SUC j) actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame (d + 32 + j * 32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_dynarray_values >> strip_tac >>
  drule_all abi_decoder_primitive_array_sizes >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  qpat_assum `abi_decoder_array_memory _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_array_memory_def]) >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`, `av` |-> `EL j (avs:abi_value list)`,
    `post` |-> `DROP (SUC j) (avs:abi_value list)`, `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    abi_decoder_primitive_loop_body) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  `elems_in_memory (TAKE j vs ++ [EL j vs]) (d + 32) tv actual.vs_memory` by metis_tac[] >>
  `d + 32 + j * 32 + 32 <= d + (32 + maxn * 32)` by
    (mp_tac (Q.SPECL [`j`, `LENGTH (vs:vyperValue$value list)`, `maxn`, `d`]
       abi_decoder_array_cell_bound) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d (SUC j) actual` by
    (mp_tac (Q.INST [`before` |-> `initial:venom_state`, `after` |-> `actual:venom_state`,
       `aty` |-> `vyper_to_abi_type env ty`,
       `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
       abi_decoder_array_memory_advance) >>
     impl_tac >- gvs[Excl "enc_def"] >> simp[]) >>
  `eval_operand ip actual = SOME p` by metis_tac[] >>
  qexists_tac `actual` >> gvs[Excl "enc_def"]
QED

Theorem abi_decoder_primitive_array_iteration_from_state:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d j initial /\
  j < LENGTH vs /\ abi_decode_source_opcode opc /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= d \/
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= sb) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var ip /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d (SUC j) actual /\
      eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
      fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
      abi_decode_frame (d + 32 + j * 32) 32 initial actual /\
      actual.vs_allocas = initial.vs_allocas /\
      actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_primitive_array_iteration >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx, Excl "enc_def"] >>
  first_assum ACCEPT_TAC
QED
