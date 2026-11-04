(* Appended constructor arguments leave the assembled program's labels intact. *)
Theory asmDataSuffixProps
Ancestors
  symbolResolve asmWf codegenRel list rich_list finite_map arithmetic pair

Theorem data_suffix_label_offsets:
  !prog bytes.
    SND (compute_label_offsets (prog ++ [AsmDataItem bytes])) =
    SND (compute_label_offsets prog)
Proof
  simp[compute_label_offsets_def, FOLDL_APPEND, UNCURRY]
QED

Theorem data_suffix_assemble:
  !prog bytes.
    assemble (prog ++ [AsmDataItem bytes]) = assemble prog ++ bytes
Proof
  simp[assemble_def, UNCURRY, data_suffix_label_offsets, MAP_APPEND,
       encode_inst_def]
QED

Theorem data_suffix_encoding_wf:
  !prog bytes.
    asm_encoding_wf (prog ++ [AsmDataItem bytes]) <=> asm_encoding_wf prog
Proof
  rpt gen_tac >>
  simp[asm_encoding_wf_def, UNCURRY, data_suffix_label_offsets] >>
  eq_tac
  >- (strip_tac >>
      `!i. i < LENGTH prog ==> i < LENGTH prog + 1` by decide_tac >>
      rpt strip_tac >> metis_tac[EL_APPEND1])
  >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `i < LENGTH prog`
      >- (gvs[EL_APPEND1] >> metis_tac[])
      >> `i = LENGTH prog` by decide_tac >> gvs[EL_APPEND2])
  >- metis_tac[]
  >- (rpt strip_tac >> Cases_on `i < LENGTH prog`
      >- (gvs[EL_APPEND1] >> metis_tac[])
      >> `i = LENGTH prog` by decide_tac >> gvs[EL_APPEND2])
  >> rpt strip_tac >> Cases_on `i < LENGTH prog`
  >- (gvs[EL_APPEND1] >> metis_tac[])
  >> `i = LENGTH prog` by decide_tac >> gvs[EL_APPEND2]
QED

Theorem data_suffix_pc_offset:
  !prog bytes pc.
    pc <= LENGTH prog ==>
    asm_pc_to_offset (prog ++ [AsmDataItem bytes]) pc =
    asm_pc_to_offset prog pc
Proof
  rpt strip_tac >>
  `pc - LENGTH prog = 0` by decide_tac >>
  `TAKE pc (prog ++ [AsmDataItem bytes]) = TAKE pc prog` by
    simp[TAKE_APPEND] >>
  simp[asm_pc_to_offset_def]
QED
