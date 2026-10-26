(* Whole-action frame includes both the returned buffer and the actual method
   store, which may extend beyond a short nominal output allocation. *)
Theory abiBuiltinEncodeEffect
Ancestors
  abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderEffect abiDecoderFrame
  abiDecoderPrimitiveLoopFrames abiDecoderAllocation abiDecoderReentry abiDecoderContract
  compileEnv venomState finite_map words list arithmetic

Definition abi_builtin_encode_effect_def:
  abi_builtin_encode_effect first last st final limit_st p outsz write_size b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(p,outsz);(p+32,write_size);(b,cap)] s t /\
    t.vs_halted = s.vs_halted /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
End

Theorem abi_builtin_encode_setup_frame_outside:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\ id <> site ==>
  FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_builtin_encode_setup_frame_footprint:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  abi_decode_footprint_frame [(p,outsz);(p+32,write_size);(b,cap)] s t
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
  irule abi_decoder_frame_in_footprint >> qexistsl_tac [`p+32`, `write_size`] >> simp[]
QED

Theorem abi_builtin_encode_body_footprint:
  abi_decode_footprint_frame [(p,outsz);(b,cap)] s t ==>
  abi_decode_footprint_frame [(p,outsz);(p+32,write_size);(b,cap)] s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(p,outsz);(b,cap)]` >> simp[] >> qx_genl_tac [`q`, `n`] >>
  strip_tac >> qexistsl_tac [`q`, `n`] >> gvs[]
QED

Theorem abi_builtin_encode_effect_compose:
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial prepared /\
  abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p outsz b cap prepared actual /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id < ready.cs_next_id /\
  ready.cs_next_id <= final.cs_next_id ==>
  abi_builtin_encode_effect first last st final limit_st p outsz write_size b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  drule abi_builtin_encode_setup_frame_footprint >> disch_then (qspecl_then [`cap`, `b`] assume_tac) >>
  drule abi_builtin_encode_body_footprint >> disch_then (qspec_then `write_size` assume_tac) >>
  `abi_decode_footprint_frame [(p,outsz);(p+32,write_size);(b,cap)] initial actual` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  asm_simp_tac bool_ss [abi_builtin_encode_effect_def] >> conj_tac
  >- (rpt strip_tac >>
      `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
      qpat_x_assum `!op w. abi_decoder_operand_live ready.cs_next_var op /\ _ ==> _` irule >>
      asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
      qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qx_gen_tac `id` >> strip_tac >>
  `id <> st.cs_next_id /\ (id < ready.cs_next_id \/ final.cs_next_id <= id)` by decide_tac >>
  `FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (drule_all abi_builtin_encode_setup_frame_outside >> simp[]) >>
  gvs[abi_decoder_scratch_frame_def]
QED
