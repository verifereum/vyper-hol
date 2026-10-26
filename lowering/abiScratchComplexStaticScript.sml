(* Static complex constructors execute every actual member and return its size.
   TOP-LEVEL: abi_scratch_encoder_complex_static establishes the precise
   recursive encoder contract from the child constructor hypotheses. *)
Theory abiScratchComplexStatic
Ancestors
  abiScratchMembersBoundary abiScratchMembersCorrect abiScratchMembersContract abiScratchMembersState
  abiScratchMembersPre abiScratchEncoderContract abiEncoderComplexStatic abiEncoderComplexCode
  abiEncoderComplexLayout abiEncoderMembersDefs abiEncoderMemberCode abiEncoderMembersInput
  abiEncoderInput abiEncoderInputLayout abiDecoderLoop abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState list words arithmetic

Theorem abi_scratch_encoder_complex_static:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
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
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >> strip_tac >>
  drule_all abi_encoder_complex_static_length >> disch_tac >>
  drule abi_encoder_complex_static_flags >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> disch_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`, `out` |-> `ignored`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_scratch_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [eval_operand_def, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_COMPLEX_STATIC_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch static complex encoder not kernel closed: " ^ n)
  end) (DB.thms "abiScratchComplexStatic");
