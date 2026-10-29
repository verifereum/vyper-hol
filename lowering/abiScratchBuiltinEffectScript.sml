(* Whole-builtin physical effect includes output allocation and method store.
   TOP-LEVEL: abi_scratch_builtin_effect and compose preserve old registers,
   allocator history, allocation rows outside scratch, and observations outside
   the actual physical write regions. *)
Theory abiScratchBuiltinEffect
Ancestors
  abiScratchBuiltinPre abiScratchEncoderContract abiScratchFootprint abiScratchEffect
  abiScratchFrameCompose abiEncoderInputFrame abiEncoderInput abiBuiltinEncodeSetup
  abiBuiltinEncodeEffect abiBuiltinAllocation abiScratchBuiltinOwnership abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderPrimitiveLoopFrames abiDecoderReentry compileEnv
  venomState finite_map pred_set words list arithmetic

Definition abi_scratch_builtin_effect_def:
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state st.cs_next_id outsz s) t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame
      ([(p,outsz);(p+32,write_size)] ++ abi_decoder_child_scratch (abi_decoder_ids first last) b cap
        (abi_builtin_allocate_state st.cs_next_id outsz s)) s t /\
    t.vs_halted = s.vs_halted /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id. ~(id IN abi_decoder_ids first last) ==>
      FLOOKUP t.vs_allocas id =
        FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz s).vs_allocas id)
End

Theorem abi_scratch_builtin_effect_output_row:
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap s t /\
  ~(st.cs_next_id IN abi_decoder_ids first last) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) ==>
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abiBuiltinEncodeOwnershipTheory.abi_builtin_allocate_state_row >> disch_then assume_tac >>
  qpat_assum `abi_scratch_builtin_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_builtin_effect_def]) >>
  qpat_x_assum `!id. ~(id IN abi_decoder_ids first last) ==> _`
    (qspec_then `st.cs_next_id` mp_tac) >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_builtin_whole_frame:
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared /\
  abi_scratch_effect first last lo hi child_next limit_st p outsz b cap prepared actual /\
  first <= lo /\ hi <= last ==>
  abi_decode_footprint_frame
    ([(p,outsz);(p+32,write_size)] ++ abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz initial)) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(p,outsz)] ++ abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)
    prepared actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `child_ids` |-> `abi_decoder_ids lo hi`,
       `fp` |-> `[(p,outsz)]`, `s` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`]
       abi_scratch_frame_subset_append) >>
     impl_tac >- (asm_simp_tac (srw_ss()) [] >> fs[abi_scratch_effect_def]) >> simp[]) >>
  `abi_decode_footprint_frame
    ([(p,outsz);(p+32,write_size)] ++ abi_decoder_child_scratch
      (abi_decoder_ids first last) b cap prepared) prepared actual` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(p,outsz)] ++ abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared` >>
     simp[] >> qx_genl_tac [`q`, `n`] >> strip_tac >> qexistsl_tac [`q`, `n`] >> gvs[]) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz initial)` by
    fs[abi_builtin_encode_setup_frame_def, abi_decoder_child_scratch_def] >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> conj_tac
  >- (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`p+32`, `write_size`] >>
      simp[] >> fs[abi_builtin_encode_setup_frame_def]) >> gvs[]
QED

Theorem abi_scratch_builtin_effect_compose:
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial prepared /\
  abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p outsz b cap prepared actual /\
  first <= ready.cs_next_id /\ final.cs_next_id <= last /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id < ready.cs_next_id /\
  ready.cs_next_id <= final.cs_next_id ==>
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_builtin_whole_frame >> disch_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`,
    `lo` |-> `ready.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `child_next` |-> `ready.cs_next_var`, `d` |-> `p:num`, `sz` |-> `outsz:num`]
    abi_scratch_builtin_allocation_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand op prepared = SOME w` by fs[abi_builtin_encode_setup_frame_def] >>
     `abi_decoder_operand_live ready.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     drule_all abi_scratch_effect_operand >> simp[]) >>
  `(abi_scratch_evolution (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state st.cs_next_id outsz initial) actual <=>
    abi_scratch_evolution (abi_decoder_ids first last) b cap prepared actual)` by
    (irule abi_scratch_evolution_transport >> fs[abi_builtin_encode_setup_frame_def]) >>
  `!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
    FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (qx_gen_tac `id` >> strip_tac >>
     `id <> st.cs_next_id /\ (id < ready.cs_next_id \/ final.cs_next_id <= id)` by decide_tac >>
     `FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id` by
       (drule_all abi_builtin_encode_setup_frame_outside >> simp[]) >>
     fs[abi_scratch_effect_def]) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  asm_simp_tac bool_ss [abi_scratch_builtin_effect_def] >> fs[abi_scratch_effect_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_scratch_builtin_source:
  abi_scratch_builtin_pre ei at av st method_id_opt src sb source_cap p maxlen first last b cap initial /\
  abi_scratch_builtin_effect first last st final limit_st p
    (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
    (case method_id_opt of NONE => 0 | SOME _ => 32) b cap initial actual ==>
  abi_encoder_input ei at av sb source_cap actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_builtin_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_builtin_pre_def, LET_THM]) >>
  qpat_assum `abi_scratch_builtin_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_builtin_effect_def]) >>
  `abi_footprint_disjoint sb source_cap
    ([(p,maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4));
      (p+32,case method_id_opt of NONE => 0 | SOME _ => 32)] ++
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap
        (abi_builtin_allocate_state st.cs_next_id
          (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) initial))` by
    asm_simp_tac (srw_ss()) [abi_scratch_disjoint_cons] >>
  drule_all abi_encoder_input_frame >> simp[]
QED
