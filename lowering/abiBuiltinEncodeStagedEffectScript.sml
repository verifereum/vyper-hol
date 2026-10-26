(* Compose a source-producing allocation/write with the complete encoder. *)
Theory abiBuiltinEncodeStagedEffect
Ancestors
  abiBuiltinEncodeEffect abiBuiltinAllocation abiDecoderFrame abiDecoderPrimitiveLoopFrames
  abiDecoderReentry abiDecoderContract compileEnv venomState finite_map words list arithmetic

Definition abi_builtin_encode_staged_effect_def:
  abi_builtin_encode_staged_effect first last st final limit_st sb source_cap p outsz write_size b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(sb,source_cap);(p,outsz);(p+32,write_size);(b,cap)] s t /\
    t.vs_halted = s.vs_halted /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
End

Theorem abi_builtin_allocate_state_outside:
  id <> site ==>
  FLOOKUP (abi_builtin_allocate_state site source_cap s).vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  asm_simp_tac (srw_ss()) [abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_builtin_encode_producer_compose:
  abi_decode_frame sb source_cap initial prepared /\
  prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id source_cap initial).vs_allocas /\
  prepared.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op prepared = SOME w) /\
  abi_builtin_encode_effect first last staged final limit_st p outsz write_size b cap prepared actual /\
  st.cs_next_var <= staged.cs_next_var /\ st.cs_next_id < staged.cs_next_id /\
  staged.cs_next_id <= final.cs_next_id ==>
  abi_builtin_encode_staged_effect first last st final limit_st sb source_cap
    p outsz write_size b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_encode_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_effect_def]) >>
  `abi_decode_footprint_frame [(sb,source_cap);(p,outsz);(p+32,write_size);(b,cap)] initial prepared` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`sb`, `source_cap`] >> simp[]) >>
  `abi_decode_footprint_frame [(sb,source_cap);(p,outsz);(p+32,write_size);(b,cap)] prepared actual` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(p,outsz);(p+32,write_size);(b,cap)]` >> simp[] >>
     qx_genl_tac [`q`, `n`] >> strip_tac >> qexistsl_tac [`q`, `n`] >> gvs[]) >>
  `abi_decode_footprint_frame [(sb,source_cap);(p,outsz);(p+32,write_size);(b,cap)] initial actual` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_builtin_encode_staged_effect_def] >> conj_tac
  >- (rpt strip_tac >>
      `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
      qpat_x_assum `!op w. abi_decoder_operand_live staged.cs_next_var op /\ _ ==> _` irule >>
      asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
      qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qx_gen_tac `id` >> strip_tac >>
  `id <> st.cs_next_id /\ (id < staged.cs_next_id \/ final.cs_next_id <= id)` by decide_tac >>
  `FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (asm_simp_tac bool_ss [] >> irule abi_builtin_allocate_state_outside >> asm_simp_tac bool_ss []) >>
  first_x_assum (qspec_then `id` mp_tac) >> asm_simp_tac bool_ss []
QED
