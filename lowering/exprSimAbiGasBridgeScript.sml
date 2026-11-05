(*
 * Counted paths for GAS-free fragments.
 *
 * frag_exec and abi_decode_sim say what running a fragment reaches, as a
 * run_from simulation; the counted expression judgments need an actual
 * gas_marked_path to that state.  For a fragment that runs no GAS, INVOKE
 * or PHI and never jumps back to the block it starts in, the fragment
 * judgment gives such a path, with a count of 0.
 *)

Theory exprSimAbiGasBridge
Ancestors
  fragGasMode fragExec exprLoweringProps abiDecoderLoop abiEncoderObserver
  venomInst venomExecSemantics venomState compileEnv list rich_list
  fragGasPath gasCount arithmetic venomExecProofs venomInstProps venomWf

(* The code a fragment emitted: the instructions after sa's position in the
   block it started, every block it finished after that, and the
   instructions of the block it left open. *)
Definition frag_code_def:
  frag_code (sa:compile_state) (sb:compile_state) =
    let new = emitted_blocks sa sb in
    if NULL new then emitted_insts sa sb
    else DROP (LENGTH sa.cs_current_insts) (LAST new).bb_instructions ++
         FLAT (MAP (\bb. bb.bb_instructions) (FRONT new)) ++
         sb.cs_current_insts
End

(* The fragment runs no GAS, INVOKE, PHI, STOP or RETURN, never jumps back
   to the block it starts in, and leaves open a block of a label it did not
   finish. *)
Definition frag_gas_free_def:
  frag_gas_free (sa:compile_state) (sb:compile_state) <=>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\
               i.inst_opcode <> RETURN /\
               ~MEM (Label sa.cs_current_bb) i.inst_operands)
          (frag_code sa sb) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb))
End

(* Proof-only observer. Filtering the supplied blocks retains instruction-id
   uniqueness even when the emitted-block list repeats a label. *)
Definition frag_observer_def:
  frag_observer sa sb fn id =
    fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> ::
      FILTER (\bb. MEM bb (emitted_blocks sa sb)) fn.fn_blocks
End

Definition frag_observer_cut_def:
  frag_observer_cut sb = (sb.cs_current_bb, LENGTH sb.cs_current_insts)
End

Definition frag_observer_region_def:
  frag_observer_region sa sb =
    {(lbl,idx) | (lbl = sa.cs_current_bb ==> LENGTH sa.cs_current_insts <= idx) /\
       (lbl = sb.cs_current_bb \/
        MEM lbl (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)))}
End

Theorem frag_observer_cut_lookup:
  lookup_block sb.cs_current_bb (frag_observer sa sb fn id).fn_blocks =
    SOME <|bb_label := sb.cs_current_bb;
           bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>
Proof
  simp[frag_observer_def, lookup_block_def, listTheory.FIND_thm]
QED

Theorem frag_observer_cut_instruction:
  get_instruction
    <|bb_label := sb.cs_current_bb;
      bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>
    (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] [])
Proof
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem frag_observer_lookup_filter[local]:
  !blocks lbl bb keep.
    lookup_block lbl blocks = SOME bb /\ keep bb ==>
    lookup_block lbl (FILTER keep blocks) = SOME bb
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  Cases_on `keep h` >> gvs[FIND_thm, lookup_block_def]
QED

Theorem frag_observer_has_code:
  fn_has_code sa sb fn /\ frag_gas_free sa sb ==>
  fn_has_code sa sb (frag_observer sa sb fn id)
Proof
  rw[fn_has_code_def]
  >- (rename1 `MEM emitted (emitted_blocks sa sb)` >>
      `emitted.bb_label <> sb.cs_current_bb` by
        (fs[frag_gas_free_def, MEM_MAP] >> metis_tac[]) >>
      simp[frag_observer_def, lookup_block_def, FIND_thm] >>
      rewrite_tac[GSYM lookup_block_def] >>
      irule frag_observer_lookup_filter >> simp[]) >>
  qexists_tac `<|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` >>
  simp[frag_observer_cut_lookup, IS_PREFIX_APPEND]
QED

Theorem frag_observer_start_region:
  cs_extends sa sb ==>
  (sa.cs_current_bb, LENGTH sa.cs_current_insts) IN
    frag_observer_region sa sb
Proof
  rw[cs_extends_def, frag_observer_region_def] >>
  drule emitted_blocks_append >> strip_tac >>
  Cases_on `new = []` >> gvs[] >>
  disj2_tac >> simp[MEM_MAP] >>
  qexists_tac `LAST (emitted_blocks sa sb)` >> simp[MEM_LAST_NOT_NIL]
QED

Theorem frag_observer_excludes_old_prefix:
  (sa.cs_current_bb,idx) IN frag_observer_region sa sb ==>
  LENGTH sa.cs_current_insts <= idx
Proof
  simp[frag_observer_region_def]
QED

Theorem frag_code_same_blocks:
  sa.cs_blocks = sb.cs_blocks ==>
  frag_code sa sb = DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts
Proof
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem frag_observer_final_label_fresh:
  frag_gas_free sa sb ==>
  !bb. MEM bb (FILTER (\bb. MEM bb (emitted_blocks sa sb)) fn.fn_blocks) ==>
    bb.bb_label <> sb.cs_current_bb
Proof
  rw[frag_gas_free_def, MEM_FILTER, MEM_MAP] >> metis_tac[]
QED

(* The arbitrary old prefix really is excluded, even if it cannot run.
   This also tests an empty emitted suffix and a cut at its first position. *)
Theorem frag_observer_old_unsafe_prefix_probe:
  let sa = st with cs_current_insts :=
    [mk_inst 0 STOP [] []; mk_inst 1 INVOKE [] []] in
  frag_gas_free sa sa /\
  (sa.cs_current_bb,2) IN frag_observer_region sa sa /\
  ~((sa.cs_current_bb,0) IN frag_observer_region sa sa) /\
  ~((sa.cs_current_bb,1) IN frag_observer_region sa sa) /\
  get_instruction
    <|bb_label := sa.cs_current_bb;
      bb_instructions := sa.cs_current_insts ++ [mk_inst 2 STOP [] []]|> 2 =
    SOME (mk_inst 2 STOP [] [])
Proof
  simp[frag_gas_free_def, frag_code_def, emitted_blocks_def,
       emitted_insts_def, frag_observer_region_def, get_instruction_def]
QED

Theorem frag_observer_extract_labels[local]:
  !ops labels. extract_labels ops = SOME labels ==>
  !lbl. MEM lbl labels ==> MEM (Label lbl) ops
Proof
  Induct >- simp[extract_labels_def] >>
  Cases_on `h` >> simp[extract_labels_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[]
QED

Theorem frag_observer_jump_no_reentry:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  ~MEM (Label lbl) inst.inst_operands /\
  step_inst_base inst s = OK u ==>
  u.vs_current_bb <> lbl
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
  drule frag_observer_extract_labels >>
  metis_tac[MEM_EL]
QED

Theorem frag_observer_emitted_empty_end_probe:
  let old = [mk_inst 0 STOP [] []; mk_inst 1 INVOKE [] []];
      jump = mk_inst 2 JMP [Label "bridge-end"] [];
      sa = st with <|cs_current_bb := "bridge-start";
                    cs_current_insts := old|>;
      bb = <|bb_label := "bridge-start"; bb_instructions := old ++ [jump]|>;
      sb = sa with <|cs_blocks := bb :: sa.cs_blocks;
                    cs_current_bb := "bridge-end"; cs_current_insts := []|> in
  cs_extends sa sb /\ frag_gas_free sa sb /\ frag_code sa sb = [jump] /\
  ("bridge-start",2) IN frag_observer_region sa sb /\
  ("bridge-end",0) IN frag_observer_region sa sb
Proof
  simp[cs_extends_def, frag_gas_free_def, frag_code_def,
       emitted_blocks_def, frag_observer_region_def, mk_inst_def] >>
  qexists_tac `[<|bb_label := "bridge-start";
    bb_instructions := [mk_inst 0 STOP [] []; mk_inst 1 INVOKE [] [];
                        mk_inst 2 JMP [Label "bridge-end"] []]|>]` >>
  simp[mk_inst_def, IS_PREFIX_APPEND]
QED

Theorem frag_observer_lookup_cases:
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  (lbl = sb.cs_current_bb /\
   bb = <|bb_label := sb.cs_current_bb;
          bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>) \/
  (lbl <> sb.cs_current_bb /\ MEM bb (emitted_blocks sa sb) /\
   bb.bb_label = lbl)
Proof
  Cases_on `lbl = sb.cs_current_bb`
  >- simp[frag_observer_cut_lookup] >>
  simp[frag_observer_def, lookup_block_def, FIND_thm] >> strip_tac >>
  drule FIND_MEM >> simp[MEM_FILTER] >> strip_tac >>
  drule FIND_P >> simp[]
QED

Theorem frag_extends_emitted_shape:
  cs_extends sa sb ==>
  if emitted_blocks sa sb = [] then
    sa.cs_blocks = sb.cs_blocks /\ sa.cs_current_bb = sb.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts
  else
    (LAST (emitted_blocks sa sb)).bb_label = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts
      (LAST (emitted_blocks sa sb)).bb_instructions
Proof
  rw[cs_extends_def] >> drule emitted_blocks_append >> strip_tac >> gvs[]
QED

Theorem frag_instruction_drop_member[local]:
  get_instruction bb idx = SOME inst /\ n <= idx ==>
  MEM inst (DROP n bb.bb_instructions)
Proof
  simp[get_instruction_def] >> strip_tac >> gvs[] >>
  simp[MEM_EL] >> qexists_tac `idx - n` >> simp[EL_DROP]
QED

Theorem frag_emitted_front_member[local]:
  new <> [] /\ MEM bb new /\ bb <> LAST new ==> MEM bb (FRONT new)
Proof
  strip_tac >>
  `new = FRONT new ++ [LAST new]` by simp[APPEND_FRONT_LAST] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem frag_emitted_start_block[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\
  MEM bb (emitted_blocks sa sb) /\ bb.bb_label = sa.cs_current_bb ==>
  bb = LAST (emitted_blocks sa sb)
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by (strip_tac >> gvs[]) >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  fs[fn_has_code_def] >>
  `MEM (LAST (emitted_blocks sa sb)) (emitted_blocks sa sb)` by
    simp[MEM_LAST_NOT_NIL] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem frag_observer_code_provenance:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  MEM inst (frag_code sa sb)
Proof
  strip_tac >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[frag_observer_cut_def, frag_observer_region_def] >>
      fs[get_instruction_def, EL_APPEND_EQN] >>
      `idx < LENGTH sb.cs_current_insts` by decide_tac >>
      gvs[] >>
      Cases_on `emitted_blocks sa sb = []`
      >- (drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
          simp[frag_code_def, emitted_insts_def] >>
          simp[MEM_EL] >> qexists_tac `idx - LENGTH sa.cs_current_insts` >>
          fs[EL_DROP]) >>
      simp[frag_code_def, NULL_EQ, MEM_APPEND] >>
      disj2_tac >> simp[MEM_EL] >> metis_tac[]) >>
  Cases_on `bb.bb_label = sa.cs_current_bb`
  >- (drule_all frag_emitted_start_block >> strip_tac >> gvs[] >>
      fs[frag_observer_region_def] >>
      `emitted_blocks sa sb <> []` by (strip_tac >> gvs[]) >>
      simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj1_tac >>
      irule frag_instruction_drop_member >> goal_assum (drule_at Any) >> simp[]) >>
  `emitted_blocks sa sb <> []` by (strip_tac >> gvs[]) >>
  `bb <> LAST (emitted_blocks sa sb)` by
    (drule frag_extends_emitted_shape >> simp[] >> metis_tac[]) >>
  `MEM bb (FRONT (emitted_blocks sa sb))` by
    metis_tac[frag_emitted_front_member] >>
  simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj2_tac >>
  `MEM inst bb.bb_instructions` by
    metis_tac[frag_instruction_drop_member, DROP_0, ZERO_LESS_EQ] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem frag_observer_off_cut_opcodes:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\
  inst.inst_opcode <> RETURN /\
  ~MEM (Label sa.cs_current_bb) inst.inst_operands
Proof
  strip_tac >> drule_all frag_observer_code_provenance >>
  fs[frag_gas_free_def, EVERY_MEM] >> metis_tac[]
QED

Theorem frag_successful_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem frag_observer_region_closed:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb ==>
  observer_region_closed ctx (frag_observer sa sb fn id)
    (frag_observer_cut sb) (frag_observer_region sa sb)
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump] >>
  `middle.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`, `s`] >> metis_tac[step_inst_non_invoke]) >>
  drule frag_observer_lookup_cases >> strip_tac >>
  fs[frag_observer_region_def, MEM_MAP] >> metis_tac[]
QED

(* The general transfer interface asks for PHI agreement even at the cut.
   A zero-length same-block fragment need not provide that agreement. *)
Theorem frag_observer_empty_phi_agreement_probe:
  let sa = st with cs_current_insts := [];
      original = fn with fn_blocks :=
        [<|bb_label := sa.cs_current_bb;
           bb_instructions := [mk_inst 0 PHI [] []]|>] in
  cs_extends sa sa /\ fn_has_code sa sa original /\ frag_gas_free sa sa /\
  ~region_code_agrees (frag_observer sa sa original 1) original
    (frag_observer_cut sa) (frag_observer_region sa sa)
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  conj_tac >- simp[cs_extends_same_block] >>
  conj_tac
  >- (simp[fn_has_code_def, emitted_blocks_def, lookup_block_def, FIND_thm]) >>
  conj_tac
  >- simp[frag_gas_free_def, frag_code_def, emitted_blocks_def, emitted_insts_def] >>
  simp[frag_observer_def, emitted_blocks_def] >>
  strip_tac >> fs[region_code_agrees_def] >>
  qpat_x_assum `!lbl bb. _` (qspec_then `st.cs_current_bb` mp_tac) >>
  simp[lookup_block_def, FIND_thm, phi_prefix_length_def, mk_inst_def,
       frag_observer_region_def, emitted_blocks_def]
QED

Theorem frag_observer_instruction_agrees:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
             get_instruction original idx = SOME inst
Proof
  strip_tac >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `idx < LENGTH sb.cs_current_insts` by
        (fs[get_instruction_def, frag_observer_cut_def] >> decide_tac) >>
      fs[fn_has_code_def] >>
      fs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem frag_observer_end_nonphi:
  cs_extends sa sb /\ frag_gas_free sa sb /\
  sb.cs_current_bb <> sa.cs_current_bb ==>
  EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (strip_tac >> drule frag_extends_emitted_shape >> gvs[]) >>
  fs[frag_gas_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
  metis_tac[]
QED

Theorem frag_observer_end_phi_zero:
  cs_extends sa sb /\ frag_gas_free sa sb ==>
  sa.cs_blocks = sb.cs_blocks \/
  !bb. lookup_block sb.cs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `sa.cs_blocks = sb.cs_blocks` >- simp[] >>
  `sb.cs_current_bb <> sa.cs_current_bb` by
    (drule frag_extends_emitted_shape >>
     Cases_on `emitted_blocks sa sb = []` >> gvs[] >>
     fs[frag_gas_free_def, MEM_MAP] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  drule_all frag_observer_end_nonphi >> strip_tac >>
  simp[frag_observer_cut_lookup] >>
  Cases_on `sb.cs_current_insts` >> fs[phi_prefix_length_def, mk_inst_def]
QED

Theorem frag_observer_phi_agrees:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
    phi_prefix_length original.bb_instructions = phi_prefix_length bb.bb_instructions /\
    TAKE (phi_prefix_length original.bb_instructions) original.bb_instructions =
    TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
        metis_tac[frag_observer_end_nonphi] >>
      fs[fn_has_code_def] >>
      Cases_on `sb.cs_current_insts`
      >- (gvs[phi_prefix_length_def, mk_inst_def] >>
          fs[cs_extends_def]) >>
      Cases_on `bb.bb_instructions` >>
      gvs[phi_prefix_length_def]) >>
  fs[fn_has_code_def] >> qexists_tac `bb` >> simp[] >> metis_tac[]
QED

Definition frag_entry_code_agrees_def:
  frag_entry_code_agrees start fn fn' cut region <=>
    (!lbl idx bb inst.
      (lbl,idx) IN region /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
            get_instruction bb' idx = SOME inst) /\
    (!lbl bb. lbl <> start /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      (lbl,phi_prefix_length bb.bb_instructions) IN region ==>
      ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
        phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
        TAKE (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions =
        TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
End

Theorem frag_observer_entry_code_agrees:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
  frag_entry_code_agrees sa.cs_current_bb (frag_observer sa sb fn id) fn
    (frag_observer_cut sb) (frag_observer_region sa sb)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rewrite_tac[frag_entry_code_agrees_def] >> conj_tac
  >- (rpt strip_tac >> irule frag_observer_instruction_agrees >> metis_tac[]) >>
  rpt strip_tac >> irule frag_observer_phi_agrees >> metis_tac[]
QED

Theorem frag_observer_step_transfer:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  abi_observer_step ctx fn (frag_observer_cut sb) s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `frag_entry_code_agrees sa.cs_current_bb (frag_observer sa sb fn id) fn
     (frag_observer_cut sb) (frag_observer_region sa sb)` by
    (irule frag_observer_entry_code_agrees >> simp[]) >>
  fs[abi_observer_step_def, frag_entry_code_agrees_def] >>
  qpat_assum `!lbl idx bb inst. _` (drule_all_then strip_assume_tac) >>
  simp[abi_observer_step_def] >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump] >>
  `middle.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`, `s`] >> metis_tac[step_inst_non_invoke]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  qpat_x_assum `!lbl bb. _`
    (qspecl_then [`middle.vs_current_bb`, `target`] mp_tac) >>
  impl_tac
  >- (simp[] >> drule frag_observer_lookup_cases >> strip_tac >>
      fs[frag_observer_region_def, MEM_MAP] >> metis_tac[]) >>
  strip_tac >> rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target'` >>
  qexistsl_tac [`target'`, `entered`] >> simp[] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >>
  asm_rewrite_tac[] >> simp[eval_phis_prefix]
QED

Theorem frag_observer_prefix_transfer:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id.
  observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  local_prefix ctx fn cut s t
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 local_prefix_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s middle` >>
  irule (cj 2 local_prefix_rules) >> qexists_tac `middle` >> conj_tac
  >- (irule frag_observer_step_transfer >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[observer_region_closed_def, frag_observer_region_closed]
QED

Theorem frag_distinct_flat_filter[local]:
  !xs f keep. ALL_DISTINCT (FLAT (MAP f xs)) ==>
    ALL_DISTINCT (FLAT (MAP f (FILTER keep xs)))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `keep h` >> gvs[ALL_DISTINCT_APPEND] >>
  gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem frag_distinct_flat_extract[local]:
  !xs f keep chosen.
  ALL_DISTINCT (FLAT (MAP f xs)) /\ MEM chosen xs /\ ~keep chosen ==>
  ALL_DISTINCT (f chosen ++ FLAT (MAP f (FILTER keep xs)))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `chosen = h` >> gvs[ALL_DISTINCT_APPEND]
  >- (conj_tac
      >- metis_tac[frag_distinct_flat_filter] >>
      gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  Cases_on `keep h` >> gvs[ALL_DISTINCT_APPEND] >>
  gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem frag_fn_insts_blocks_member[local]:
  !blocks inst. MEM inst (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

Theorem frag_observer_fresh_id:
  ?id. !inst. MEM inst (fn_insts fn) ==> inst.inst_id <> id
Proof
  qexists_tac `SUC (SUM (MAP (\i. i.inst_id) (fn_insts fn)))` >>
  rpt strip_tac >> drule SUM_MAP_MEM_bound >>
  disch_then (qspec_then `\i. i.inst_id` mp_tac) >> simp[]
QED

Theorem frag_observer_ids_distinct:
  fn_has_code sa sb fn /\ frag_gas_free sa sb /\ fn_inst_ids_distinct fn /\
  (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <> id) ==>
  fn_inst_ids_distinct (frag_observer sa sb fn id)
Proof
  strip_tac >> fs[fn_has_code_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `~MEM bb (emitted_blocks sa sb)` by
    (drule lookup_block_label >> strip_tac >>
     fs[frag_gas_free_def, MEM_MAP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions ++
     FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
       (FILTER (\bb. MEM bb (emitted_blocks sa sb)) fn.fn_blocks)))` by
    (qspecl_then [`fn.fn_blocks`, `\bb. MAP (\i. i.inst_id) bb.bb_instructions`]
       mp_tac frag_distinct_flat_extract >>
     fs[fn_inst_ids_distinct_def] >> metis_tac[]) >>
  gvs[IS_PREFIX_APPEND] >>
  `~MEM id (MAP (\i. i.inst_id) sb.cs_current_insts)` by
    (simp[MEM_MAP] >>
     fs[fn_insts_def, frag_fn_insts_blocks_member] >> metis_tac[MEM_APPEND]) >>
  `~MEM id (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (FILTER (\bb. MEM bb (emitted_blocks sa sb)) fn.fn_blocks)))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, MEM_FILTER] >>
     fs[fn_insts_def, frag_fn_insts_blocks_member] >> metis_tac[]) >>
  fs[fn_inst_ids_distinct_def, frag_observer_def, MAP_APPEND, ALL_DISTINCT_APPEND,
     mk_inst_def] >> metis_tac[]
QED

Theorem frag_observer_nonstop_inclusion:
  fn_has_code sa sb fn /\
  MEM inst (fn_insts (frag_observer sa sb fn id)) /\ inst.inst_opcode <> STOP ==>
  MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def, frag_observer_def, frag_fn_insts_blocks_member] >> gvs[]
  >- (fs[MEM_APPEND, fn_has_code_def] >>
      `MEM inst bb.bb_instructions` by
        metis_tac[IS_PREFIX_APPEND, MEM_APPEND] >>
      drule lookup_block_MEM >> strip_tac >> metis_tac[]) >>
  fs[MEM_FILTER] >> metis_tac[]
QED

(* SINK is permitted by the frozen opcode filter, but is a Halt step.
   Thus the existing observer_region_safe interface is strictly too strong. *)
Theorem frag_observer_sink_safety_probe:
  let sa = st with cs_current_insts := [];
      sb = sa with cs_current_insts := [mk_inst 0 SINK [] []] in
  cs_extends sa sb /\ frag_gas_free sa sb /\
  ~observer_region_safe (frag_observer sa sb fn 1)
    (frag_observer_cut sb) (frag_observer_region sa sb)
Proof
  simp[cs_extends_same_block, frag_gas_free_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def] >>
  simp[observer_region_safe_def, frag_observer_cut_def,
       frag_observer_region_def, frag_observer_def, lookup_block_def,
       FIND_thm, get_instruction_def, mk_inst_def, emitted_blocks_def] >>
  qexists_tac `0` >>
  simp[mk_inst_def, step_inst_base_opcode_eqs] >>
  qexists_tac `s with vs_halted := F` >> simp[]
QED

(* Select one dispatch equation before simplifying an opcode branch. *)
fun frag_opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

Theorem frag_halt_preserves_position:
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt h ==>
  h.vs_current_bb = s.vs_current_bb /\ h.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  qpat_assum `inst.inst_opcode = _`
    (fn eq => fs[frag_opcode_eq (rhs (concl eq))]) >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      AllCaseEqs(), halt_state_def, set_returndata_def] >>
  gvs[exec_alloca_def, exec_ext_call_def, exec_delegatecall_def,
      exec_create_not_Halt, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem frag_cut_run_prefix_aux[local]:
  !fuel n s bb h.
    (!bb. lookup_block (FST cut) fn.fn_blocks = SOME bb ==>
      ?id. get_instruction bb (SND cut) = SOME (mk_inst id STOP [] [])) /\
    (!lbl idx bb inst. (lbl,idx) IN region /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==> inst.inst_opcode <> INVOKE) /\
    observer_region_closed ctx fn cut region /\
    (s.vs_current_bb,s.vs_inst_idx) IN region /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx fn s = Halt h /\
    (h.vs_current_bb,h.vs_inst_idx) = cut ==>
    ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = cut`
  >- (qexists_tac `s` >> conj_tac
      >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
      `FST cut = s.vs_current_bb /\ SND cut = s.vs_inst_idx` by
        (Cases_on `cut` >> gvs[]) >>
      `?id. get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        metis_tac[] >>
      `run_from fuel ctx fn s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def]) >> gvs[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac >> gs[]
  >- (rename1 `step_inst_base inst s = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary") >>
  metis_tac[frag_halt_preserves_position]
QED

Resume frag_cut_run_prefix_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx fn cut s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut region`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `h`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Resume frag_cut_run_prefix_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def] >>
  rename1 `run_blocks (SUC remaining) ctx fn middle = Halt h` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx fn cut s
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut region`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `h`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `entered with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[]
QED

Finalise frag_cut_run_prefix_aux

Theorem frag_observer_halt_cut_prefix:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\ run_from fuel ctx (frag_observer sa sb fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
      stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks`
  >- gvs[run_from_def] >>
  irule frag_cut_run_prefix_aux >>
  simp[] >> conj_tac
  >- (simp[frag_observer_cut_def, frag_observer_cut_lookup] >>
      rpt strip_tac >> gvs[] >> metis_tac[frag_observer_cut_instruction]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `frag_observer_region sa sb` >> simp[] >> conj_tac
  >- metis_tac[frag_observer_off_cut_opcodes] >>
  metis_tac[frag_observer_region_closed]
QED

Theorem frag_observer_halt_cut_prefix_transfer:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\ run_from fuel ctx (frag_observer sa sb fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx fn (frag_observer_cut sb) s u /\ stop_view u = h
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_observer_halt_cut_prefix >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  irule frag_observer_prefix_transfer >> metis_tac[]
QED

Theorem abi_observer_step_zero_edge:
  abi_observer_step ctx fn cut s t /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst ==>
     inst.inst_opcode <> GAS) ==>
  gas_path_edge ctx fn s 0 (OK t)
Proof
  rw[abi_observer_step_def, gas_path_edge_def] >> gvs[] >>
  qexists_tac `0` >> simp[gas_count_step_def] >> metis_tac[]
QED

Theorem frag_observer_step_zero_edge:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  gas_path_edge ctx fn s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_observer_step ctx fn (frag_observer_cut sb) s t` by
    (irule frag_observer_step_transfer >> metis_tac[]) >>
  irule abi_observer_step_zero_edge >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `abi_observer_step ctx (frag_observer sa sb fn id) _ s t`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  drule_all frag_observer_instruction_agrees >> strip_tac >> gvs[] >>
  metis_tac[frag_observer_off_cut_opcodes]
QED

Theorem frag_observer_prefix_zero_path:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id.
  observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  gas_path ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s middle` >>
  `gas_path_edge ctx fn s 0 (OK middle)` by
    (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  `gas_path ctx fn middle 0 (OK t)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_region_closed_def, frag_observer_region_closed]) >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem frag_observer_exit_zero_edge:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = r /\ exit_result r ==>
  gas_path_edge ctx fn s 0 r
Proof
  rpt strip_tac >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  drule_all frag_observer_instruction_agrees >> strip_tac >>
  simp[gas_path_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def]
QED

Theorem frag_observer_exit_path_aux[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
  !fuel n s bb r.
    (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx (frag_observer sa sb fn id) s = r /\
    exit_result r /\ (!h. r <> Halt h) ==>
    gas_path ctx fn s 0 r
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
                bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        (gvs[frag_observer_cut_def, frag_observer_cut_lookup]) >>
      `get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >>
         gvs[mk_inst_def]) >> metis_tac[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ s = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_observer_off_cut_opcodes] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx (frag_observer sa sb fn id) s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac
  >- (rename1 `step_inst_base inst s = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary")
  >- suspend "abort"
  >- suspend "intret" >>
  metis_tac[exit_result_def]
QED

Resume frag_observer_exit_path_aux[abort]:
  irule (cj 3 gas_path_rules) >> simp[] >>
  metis_tac[frag_observer_exit_zero_edge]
QED

Resume frag_observer_exit_path_aux[intret]:
  irule (cj 3 gas_path_rules) >> simp[] >>
  metis_tac[frag_observer_exit_zero_edge]
QED

Resume frag_observer_exit_path_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `gas_path_edge ctx fn s 0 (OK (middle with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  `(s.vs_current_bb,SUC s.vs_inst_idx) IN frag_observer_region sa sb` by
    (drule_all frag_observer_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >>
     simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `r`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  metis_tac[gas_path_rules, ADD]
QED

Resume frag_observer_exit_path_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_observer sa sb fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_observer_exit_path_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  `gas_path_edge ctx fn s 0
     (OK (entered with vs_inst_idx := phi_prefix_length target.bb_instructions))` by
    (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
     frag_observer_region sa sb` by
    (drule_all frag_observer_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >>
     simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  `run_from remaining ctx (frag_observer sa sb fn id)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = r` by
    simp[run_from_def] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Finalise frag_observer_exit_path_aux

Theorem frag_observer_exit_path:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = r /\
  exit_result r /\ (!h. r <> Halt h) ==>
  gas_path ctx fn s 0 r
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks`
  >- (gvs[Once run_from_def, exit_result_def]) >>
  irule frag_observer_exit_path_aux >> metis_tac[]
QED

Theorem local_prefix_endpoint:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
    ~s.vs_halted /\ ~t.vs_halted /\
    (t.vs_current_bb,t.vs_inst_idx) = cut
Proof
  ho_match_mp_tac local_prefix_ind >>
  simp[abi_observer_step_def] >> metis_tac[]
QED

Theorem local_prefix_zero_path:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
    !region. observer_region_closed ctx fn cut region /\
    (s.vs_current_bb,s.vs_inst_idx) IN region /\
    (!lbl idx bb inst.
      (lbl,idx) IN region /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      inst.inst_opcode <> GAS) ==>
    gas_path ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt strip_tac >>
  rename1 `abi_observer_step ctx fn cut s successor` >>
  `gas_path_edge ctx fn s 0 (OK successor)` by
    (irule abi_observer_step_zero_edge >>
     reverse conj_tac >- (qexists_tac `cut` >> simp[]) >>
     fs[abi_observer_step_def] >> metis_tac[]) >>
  `gas_path ctx fn successor 0 (OK t)` by
    (first_x_assum irule >> qexists_tac `region` >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  metis_tac[gas_path_rules, ADD]
QED

Theorem stop_view_recover:
  ~u.vs_halted /\ ~t.vs_halted /\ stop_view u = stop_view t ==>
  u = t with vs_returndata := u.vs_returndata
Proof
  simp[stop_view_def, halt_state_def, venom_state_component_equality]
QED

Theorem stop_view_closed_post:
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
  ~u.vs_halted /\ ~t.vs_halted /\ stop_view u = stop_view t /\ Q t ==>
  Q u
Proof
  strip_tac >> drule_all stop_view_recover >>
  disch_then SUBST1_TAC >> simp[]
QED

(* The run_from simulation of frag_exec, taken in a function where the
   fragment's end is followed by STOP, is an actual path in every function
   that has the fragment's code.  Q may not depend on vs_returndata, which
   that STOP clears; R accepts no Halt, so that the STOP is never mistaken
   for an exit of the fragment. *)
Theorem frag_exec_gas_path:
  !ctx sa sb P Q R fn s.
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_has_code sa sb (frag_observer sa sb fn 0)` by
    metis_tac[frag_observer_has_code] >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[frag_exec_def]) >>
  disch_then (qspecl_then [`frag_observer sa sb fn 0`, `s`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume frag_exec_gas_path[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_observer sa sb fn 0) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst 0 STOP [] []]|>`, `0`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn 0) s = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn 0) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `gas_path ctx fn s 0 (OK u)` by
    (drule frag_observer_prefix_zero_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  disj1_tac >> qexists_tac `u` >>
  simp[gas_marked_path_def] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED

Resume frag_exec_gas_path[exit]:
  disj2_tac >> qexists_tac `run_from fuel ctx (frag_observer sa sb fn 0) s` >>
  simp[gas_marked_path_def] >>
  irule frag_observer_exit_path >> metis_tac[]
QED

Finalise frag_exec_gas_path

(* The same for a fragment proved in the abi_decode_sim form, such as the
   ABI encoder and decoder executions. *)
Theorem abi_decode_sim_gas_path:
  !ctx sa sb Q fn s.
    (!fn'. fn_has_code sa sb fn' /\ fn_inst_ids_distinct fn' /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP ==>
            MEM i (fn_insts fn)) /\
       (sa.cs_blocks = sb.cs_blocks \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' s t) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?id. !inst. MEM inst (fn_insts fn) ==> inst.inst_id <> id` by
    metis_tac[frag_observer_fresh_id] >>
  qpat_x_assum `!fn'. _` (qspec_then `frag_observer sa sb fn id` mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[frag_observer_has_code]
      >- metis_tac[frag_observer_ids_distinct]
      >- metis_tac[frag_observer_nonstop_inclusion] >>
      metis_tac[frag_observer_end_phi_zero]) >>
  strip_tac >> rename1 `Q t` >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `gas_path ctx fn s 0 (OK u)` by
    (drule frag_observer_prefix_zero_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  qexists_tac `u` >> simp[gas_marked_path_def] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED
