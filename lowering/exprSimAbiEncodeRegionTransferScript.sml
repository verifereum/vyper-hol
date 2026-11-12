(* Retained-code observer transfer, independent of the encoder recursion. *)
Theory exprSimAbiEncodeRegionTransfer
Ancestors
  abiEncoderObserver fragExec venomInst venomExecSemantics list rich_list

Definition encode_retained_observer_def:
  encode_retained_observer fn sa sb k =
    fn with fn_blocks := emitted_blocks sa sb ++
      [<|bb_label := sb.cs_current_bb;
         bb_instructions := sb.cs_current_insts ++ [mk_inst k STOP [] []]|>]
End

Theorem encode_retained_lookup_member[local]:
  !blocks lbl bb. lookup_block lbl blocks = SOME bb ==>
    MEM bb blocks /\ bb.bb_label = lbl
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem encode_retained_insts_member[local]:
  !blocks i. MEM i (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM i bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem encode_retained_blocks:
  MEM bb (encode_retained_observer fn sa sb k).fn_blocks ==>
  MEM bb (emitted_blocks sa sb) \/
  bb = <|bb_label := sb.cs_current_bb;
         bb_instructions := sb.cs_current_insts ++ [mk_inst k STOP [] []]|>
Proof
  simp[encode_retained_observer_def]
QED

Theorem encode_retained_block_transfer:
  fn_has_code sa sb func /\
  lookup_block lbl (encode_retained_observer fn sa sb k).fn_blocks = SOME bb ==>
  lookup_block lbl func.fn_blocks = SOME bb \/
  (lbl = sb.cs_current_bb /\
   bb.bb_instructions = sb.cs_current_insts ++ [mk_inst k STOP [] []] /\
   ?bb'. lookup_block lbl func.fn_blocks = SOME bb' /\
         isPREFIX sb.cs_current_insts bb'.bb_instructions)
Proof
  strip_tac >> drule encode_retained_lookup_member >> strip_tac >>
  drule encode_retained_blocks >> strip_tac
  >- (gvs[fn_has_code_def] >> metis_tac[]) >>
  gvs[fn_has_code_def] >> metis_tac[]
QED

Theorem encode_retained_opcode_inclusion:
  fn_has_code sa sb func /\
  MEM i (fn_insts (encode_retained_observer fn sa sb k)) /\
  i.inst_opcode <> STOP ==> MEM i (fn_insts func)
Proof
  simp[fn_insts_def, encode_retained_insts_member] >> strip_tac >>
  drule encode_retained_blocks >> strip_tac
  >- (gvs[fn_has_code_def] >> metis_tac[encode_retained_lookup_member]) >>
  gvs[mk_inst_def] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  drule encode_retained_lookup_member >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> metis_tac[MEM_APPEND]
QED

Theorem encode_prefix_phi_extension:
  !pre xs. EXISTS (\i. i.inst_opcode <> PHI) pre /\ isPREFIX pre xs ==>
    phi_prefix_length xs = phi_prefix_length pre /\
    TAKE (phi_prefix_length xs) xs = TAKE (phi_prefix_length pre) pre
Proof
  Induct >> simp[] >> Cases_on `xs` >> simp[isPREFIX] >>
  strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem encode_retained_region_agrees:
  fn_has_code sa sb func /\
  (!idx. (sb.cs_current_bb,idx) IN R /\
         (sb.cs_current_bb,idx) <> cut ==> idx < LENGTH sb.cs_current_insts) /\
  EXISTS (\i. i.inst_opcode <> PHI) sb.cs_current_insts ==>
  region_code_agrees (encode_retained_observer fn sa sb k) func cut R
Proof
  strip_tac >> simp[region_code_agrees_def] >> conj_tac
  >- (rpt strip_tac >> drule_all encode_retained_block_transfer >> strip_tac
      >- metis_tac[] >>
      `idx < LENGTH sb.cs_current_insts` by metis_tac[] >>
      qexists_tac `bb'` >> gvs[IS_PREFIX_APPEND] >>
      qpat_x_assum `!idx. _` (qspec_then `idx` mp_tac) >>
      simp[] >> strip_tac >> simp[get_instruction_def, EL_APPEND_EQN] >>
      gvs[get_instruction_def, EL_APPEND_EQN]) >>
  rpt strip_tac >> drule_all encode_retained_block_transfer >> strip_tac
  >- metis_tac[] >>
  qexists_tac `bb'` >> simp[] >>
  `phi_prefix_length bb'.bb_instructions = phi_prefix_length sb.cs_current_insts /\
   TAKE (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions =
   TAKE (phi_prefix_length sb.cs_current_insts) sb.cs_current_insts` by
    (irule encode_prefix_phi_extension >> simp[]) >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length sb.cs_current_insts /\
   TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions =
   TAKE (phi_prefix_length sb.cs_current_insts) sb.cs_current_insts` by
    (irule encode_prefix_phi_extension >> simp[]) >> gvs[]
QED
