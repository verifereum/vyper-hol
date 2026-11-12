Theory fmpStageFmpStepsCallRoot
Ancestors
  fmpStepLayout list rich_list arithmetic venomInst callLayoutDefs

Theorem call_invoke_after_prefix[local]:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix /\
  k < LENGTH (prefix ++ tail) /\
  (EL k (prefix ++ tail)).inst_opcode = INVOKE ==>
  LENGTH prefix <= k
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `k < LENGTH prefix` by decide_tac >>
  fs[EVERY_EL, EL_APPEND1] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem fmp_install_root_invoke_location:
  blocks = entry::rest /\
  ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
    (users ++ OPTION_TO_LIST oldpc) /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc supply)
    blocks = SOME (out,supply') /\
  lookup_block lbl blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb'. lookup_block lbl out = SOME bb' /\
    k + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0)
      < LENGTH bb'.bb_instructions /\
    EL (k + (if lbl = entry.bb_label then LENGTH (OPTION_TO_LIST root) else 0))
      bb'.bb_instructions = EL k bb.bb_instructions
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >>
  strip_tac >> gvs[] >>
  Cases_on `lbl = entry.bb_label`
  >- (gvs[lookup_block_def, FIND_thm] >>
      `LENGTH (users ++ OPTION_TO_LIST oldpc) <= k` by
        (irule call_invoke_after_prefix >> conj_tac
         >- (qexists_tac `tail` >> gvs[APPEND_ASSOC]) >>
         gvs[]) >>
      `LENGTH (OPTION_TO_LIST newpc) = LENGTH (OPTION_TO_LIST oldpc)` by
        (Cases_on `newpc` >> Cases_on `oldpc` >> gvs[OPTION_TO_LIST_def]) >>
      Cases_on `fn_is_context_entry ctx fn` >>
      simp[lookup_block_def, FIND_thm] >>
      fs[LENGTH_APPEND] >> simp[EL_APPEND_EQN, LENGTH_APPEND]) >>
  gvs[lookup_block_def, FIND_thm] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[lookup_block_def, FIND_thm] >> metis_tac[]
QED
