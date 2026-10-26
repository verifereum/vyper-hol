(* Dynamic complex constructors execute cursor setup, every member and final load.
   TOP-LEVEL: abi_scratch_encoder_complex_dynamic proves the precise encoder
   contract, including registered parent-cursor writes and allocation evolution. *)
Theory abiScratchComplexDynamic
Ancestors
  abiScratchComplexPrepare abiScratchComplexFinish abiScratchMembersBoundary
  abiScratchMembersCorrect abiScratchMembersContract abiScratchMembersState abiScratchMembersPre
  abiScratchEncoderContract abiScratchEffectCompose abiScratchEffectWiden
  abiEncoderComplexContext abiEncoderMembersDefs abiEncoderInput abiEncoderInputLayout
  abiDecoderReentry abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_complex_compose:
  abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready /\
  abi_scratch_effect first last st.cs_next_id middle.cs_next_id prepared.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id middle.cs_next_var
    limit_st d sz b cap encoded actual /\
  first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  prepared.cs_next_id <= end_st.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `prepared.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap ready encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `middle.cs_next_id`, `st.cs_next_id`, `prepared.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `middle.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial encoded` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `ready` >> simp[]) >>
  conj_tac
  >- (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `encoded` >> simp[]) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

Theorem abi_scratch_encoder_complex_dynamic:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_scratch_encoder (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_scratch_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encoder_complex_dynamic_context >>
  disch_then (qx_choose_then `dyn_ptr` (qx_choose_then `prepared`
    (qx_choose_then `ignored` (qx_choose_then `middle` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `prepared.cs_next_id <= last /\ middle.cs_next_id <= last /\
    prepared.cs_next_var <= limit_st.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var /\
    start.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `st` |-> `prepared`, `end_st` |-> `middle`, `out` |-> `ignored`, `initial` |-> `ready:venom_state`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_scratch_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `so` |-> `abi_encoder_member_span infos`,
    `ho` |-> `SUM (MAP (\(_,asz,_,_). asz) (infos:(abi_enc_info # num # num # bool) list))`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_finish) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`st` |-> `start`, `sz` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_COMPLEX_DYNAMIC_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch dynamic complex encoder not kernel closed: " ^ n)
  end) (DB.thms "abiScratchComplexDynamic");
