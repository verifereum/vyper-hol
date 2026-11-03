(* The complete builtin may allocate its arbitrary-sized output before the
   recursive decoder allocates 32-byte scratch slots. *)
Theory abiBuiltinDecodeEffect
Ancestors
  abiBuiltinAllocation abiDecoderEffect abiDecoderFrame abiDecoderReentry abiDecoderAllocation
  compileEnv venomState finite_map words arithmetic

Definition abi_builtin_decode_effect_def:
  abi_builtin_decode_effect first last st final limit_st d outsz b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,outsz);(b,cap)] s t /\ t.vs_halted = s.vs_halted /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
End

Theorem abi_builtin_decode_effect_compose:
  abi_builtin_allocation_frame st.cs_next_var site outsz initial prepared /\
  abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st d outsz b cap prepared actual /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= site /\
  site < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id ==>
  abi_builtin_decode_effect first last st final limit_st d outsz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_decode_footprint_frame [(d,outsz);(b,cap)] initial actual` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >>
     asm_simp_tac bool_ss [] >>
     mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
       `t` |-> `prepared:venom_state`, `ranges` |-> `[(d,outsz);(b,cap)]`]
       abi_builtin_allocation_frame_footprint) >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_builtin_decode_effect_def] >> conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live ready.cs_next_var op` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
      metis_tac[]) >>
  qx_gen_tac `id` >> strip_tac >>
  `id <> site /\ (id < ready.cs_next_id \/ final.cs_next_id <= id)` by decide_tac >>
  `FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
      `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_outside) >>
     asm_simp_tac bool_ss []) >>
  gvs[abi_decoder_scratch_frame_def]
QED
