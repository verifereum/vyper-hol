Theory exprSimAbiEncodeArgsEntry
Ancestors
  exprSimAbiEncodeArgsMaterializePath exprLowering exprSimHypsDefs

(* The first instruction at an empty input cursor has been installed,
   either in a closed block or in the final open block. *)
Definition abi_args_entry_emitted_def:
  abi_args_entry_emitted si sf <=>
    (?bb i rest. MEM bb (emitted_blocks si sf) /\
       bb.bb_label = si.cs_current_bb /\
       bb.bb_instructions = i::rest /\ i.inst_opcode <> PHI) \/
    (sf.cs_current_bb = si.cs_current_bb /\
     ?i rest. sf.cs_current_insts = i::rest /\ i.inst_opcode <> PHI)
End

Theorem abi_args_entry_emitted_phi_zero:
  abi_args_entry_emitted si sf /\ fn_has_code si sf func ==>
  ?bb. lookup_block si.cs_current_bb func.fn_blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  rw[abi_args_entry_emitted_def, fragExecTheory.fn_has_code_def]
  >- (first_x_assum drule >> simp[venomExecSemanticsTheory.phi_prefix_length_def]) >>
  Cases_on `bb.bb_instructions` >>
  gvs[listTheory.isPREFIX, venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem abi_args_nonphi_prefix:
  isPREFIX (i::rest) code /\ i.inst_opcode <> PHI ==>
  ?tail. code = i::tail
Proof
  Cases_on `code` >> simp[]
QED

Theorem abi_args_entry_emitted_mono:
  cs_extends si sm /\ cs_extends sm sf /\
  abi_args_entry_emitted si sm ==>
  abi_args_entry_emitted si sf
Proof
  rw[compileEnvTheory.cs_extends_def, abi_args_entry_emitted_def] >>
  `emitted_blocks si sm = new` by
    metis_tac[fragExecTheory.emitted_blocks_append] >>
  `emitted_blocks si sf = new' ++ new` by
    (irule fragExecTheory.emitted_blocks_append >> simp[]) >>
  gvs[]
  >- metis_tac[listTheory.MEM_APPEND] >>
  Cases_on `new' = []` >> gvs[]
  >- (Cases_on `sf.cs_current_insts` >> gvs[] >> metis_tac[]) >>
  Cases_on `(LAST new').bb_instructions` >> gvs[] >>
  disj1_tac >> metis_tac[rich_listTheory.LAST_MEM, listTheory.MEM_APPEND]
QED
