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
  instIdxIndep

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

(* ===== Relabeled entry block ===== *)

(* The entry block renamed to L, with its pre-fragment instructions
   replaced by NOPs with the IDs ids. *)
Definition start_relabel_def:
  start_relabel L ids (sa:compile_state) =
    sa with <| cs_current_bb := L;
               cs_current_insts := MAP (\id. mk_inst id NOP [] []) ids |>
End

(* What a fragment run from start_relabel L ids sa ends in, given that
   the run from sa ends in sb. *)
Definition start_swap_def:
  start_swap (sa:compile_state) L ids (sb:compile_state) =
    let pre = MAP (\id. mk_inst id NOP [] []) ids in
    let p = LENGTH sa.cs_current_insts in
    let new = emitted_blocks sa sb in
    if NULL new then
      sb with <| cs_current_bb := L;
                 cs_current_insts := pre ++ DROP p sb.cs_current_insts |>
    else
      sb with cs_blocks :=
        FRONT new ++
        [LAST new with <| bb_label := L;
                          bb_instructions := pre ++ DROP p (LAST new).bb_instructions |>] ++
        DROP (LENGTH new) sb.cs_blocks
End

(* A fragment's code does not depend on its entry block's label or on the
   instructions already in it. *)
Definition frag_start_oblivious_def:
  frag_start_oblivious (m : compile_state -> 'a # compile_state) <=>
    !sa x sb L ids.
      m sa = (x,sb) /\ LENGTH ids = LENGTH sa.cs_current_insts ==>
      m (start_relabel L ids sa) = (x, start_swap sa L ids sb)
End

(* frag_gas_free's opcode conditions alone. *)
Definition frag_ops_free_def:
  frag_ops_free (sa:compile_state) (sb:compile_state) <=>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\
               i.inst_opcode <> RETURN) (frag_code sa sb)
End

Theorem start_swap_emitted_blocks:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks ==>
  emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb) =
    FRONT (emitted_blocks sa sb) ++
    [LAST (emitted_blocks sa sb) with
      <|bb_label := L;
        bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++
          DROP (LENGTH sa.cs_current_insts)
            (LAST (emitted_blocks sa sb)).bb_instructions|>]
Proof
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  `new <> []` by (strip_tac >> gvs[]) >>
  simp[start_swap_def, start_relabel_def, NULL_EQ] >>
  irule emitted_blocks_append >> simp[DROP_LENGTH_APPEND]
QED

Theorem start_swap_fields:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks ==>
  (start_swap sa L ids sb).cs_current_bb = sb.cs_current_bb /\
  (start_swap sa L ids sb).cs_current_insts = sb.cs_current_insts
Proof
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  `new <> []` by (strip_tac >> gvs[]) >>
  simp[start_swap_def, NULL_EQ]
QED

Theorem start_relabel_extends:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks ==>
  cs_extends (start_relabel L ids sa) (start_swap sa L ids sb)
Proof
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  `new <> []` by (strip_tac >> gvs[]) >>
  simp[start_swap_def, start_relabel_def, NULL_EQ, cs_extends_def,
       DROP_LENGTH_APPEND] >>
  qexists_tac `FRONT new ++
    [LAST new with <|bb_label := L;
      bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++
        DROP (LENGTH sa.cs_current_insts) (LAST new).bb_instructions|>]` >>
  simp[IS_PREFIX_APPEND]
QED

Theorem start_swap_emitted_shape:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks ==>
  emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb) <> [] /\
  FRONT (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) =
    FRONT (emitted_blocks sa sb) /\
  LAST (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) =
    (LAST (emitted_blocks sa sb) with
      <|bb_label := L;
        bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++
          DROP (LENGTH sa.cs_current_insts)
            (LAST (emitted_blocks sa sb)).bb_instructions|>)
Proof
  strip_tac >> drule_all start_swap_emitted_blocks >> simp[FRONT_APPEND]
QED

Theorem start_relabel_frag_code:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  frag_code (start_relabel L ids sa) (start_swap sa L ids sb) = frag_code sa sb
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule_all start_swap_emitted_shape >> strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  simp[frag_code_def, NULL_EQ] >>
  simp[start_relabel_def, DROP_APPEND]
QED

Theorem start_relabel_gas_free:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts /\ frag_ops_free sa sb /\
  L <> sb.cs_current_bb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) ==>
  frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb)
Proof
  strip_tac >>
  drule_all start_relabel_frag_code >> strip_tac >>
  drule_all start_swap_emitted_blocks >> strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  simp[frag_gas_free_def] >>
  simp[start_relabel_def] >>
  gvs[frag_ops_free_def, EVERY_MEM] >> metis_tac[]
QED

Theorem frag_fresh_label:
  !labels:string list. ?L. ~MEM L labels
Proof
  gen_tac >>
  qexists_tac `REPLICATE (SUC (SUM (MAP LENGTH labels))) #"x"` >>
  strip_tac >> drule SUM_MAP_MEM_bound >>
  disch_then (qspec_then `LENGTH` mp_tac) >> simp[]
QED

Theorem frag_relabel_fresh_label:
  ?L. L <> sb.cs_current_bb /\
      ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
      EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)
Proof
  qspec_then `sb.cs_current_bb ::
    MAP (\bb. bb.bb_label) (emitted_blocks sa sb) ++
    FLAT (MAP (\i. MAP (\op. case op of Label l => l | _ => "")
      i.inst_operands) (frag_code sa sb))` mp_tac frag_fresh_label >>
  simp[MEM_FLAT, MEM_MAP, EVERY_MEM] >> strip_tac >>
  qexists_tac `L` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!l. _` (qspec_then
    `MAP (\op. case op of Label l => l | _ => "") i.inst_operands` mp_tac) >>
  simp[MEM_MAP] >> conj_tac
  >- (qexists_tac `i` >> simp[]) >>
  qexists_tac `Label L` >> simp[]
QED

Theorem frag_relabel_fresh_ids:
  !code:instruction list. !n.
    ?ids id. LENGTH ids = n /\ ALL_DISTINCT ids /\ ~MEM id ids /\
      (!i. MEM i code ==> ~MEM i.inst_id ids /\ i.inst_id <> id)
Proof
  rpt gen_tac >>
  qexistsl_tac [`GENLIST (\k. SUC (SUM (MAP (\i. i.inst_id) code)) + k) n`,
    `SUC (SUM (MAP (\i. i.inst_id) code)) + n`] >>
  simp[ALL_DISTINCT_GENLIST, MEM_GENLIST] >> rpt strip_tac >>
  drule SUM_MAP_MEM_bound >>
  disch_then (qspec_then `\i. i.inst_id` mp_tac) >> simp[]
QED

Definition frag_relabel_observer_def:
  frag_relabel_observer sa sb L ids fn id =
    fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> ::
      emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)
End

Theorem frag_relabel_observer_cut:
  lookup_block sb.cs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks =
  SOME <|bb_label := sb.cs_current_bb;
         bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>
Proof
  simp[frag_relabel_observer_def, lookup_block_def, FIND_thm]
QED

Theorem frag_blocks_consistent_lookup[local]:
  !blocks bb.
    MEM bb blocks /\
    (!b. MEM b blocks /\ b.bb_label = bb.bb_label ==> b = bb) ==>
    lookup_block bb.bb_label blocks = SOME bb
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  simp[Once lookup_block_def, FIND_thm] >>
  Cases_on `h.bb_label = bb.bb_label`
  >- (`h = bb` by metis_tac[MEM] >> simp[]) >>
  simp[] >> rewrite_tac[GSYM lookup_block_def] >>
  first_x_assum irule >> metis_tac[MEM]
QED

Theorem start_swap_blocks_consistent:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb fn /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) ==>
  !b c.
    MEM b (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) /\
    MEM c (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) /\
    b.bb_label = c.bb_label ==> b = c
Proof
  strip_tac >> drule_all start_swap_emitted_blocks >> strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  `!b. MEM b (FRONT (emitted_blocks sa sb)) ==>
       MEM b (emitted_blocks sa sb)` by
    (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
        [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
     metis_tac[MEM_APPEND]) >>
  fs[fn_has_code_def] >>
  `!b c. MEM b (FRONT (emitted_blocks sa sb)) /\
          MEM c (FRONT (emitted_blocks sa sb)) /\
          b.bb_label = c.bb_label ==> b = c` by
    (rpt strip_tac >>
     `lookup_block b.bb_label fn.fn_blocks = SOME b` by metis_tac[] >>
     `lookup_block c.bb_label fn.fn_blocks = SOME c` by metis_tac[] >>
     metis_tac[optionTheory.SOME_11]) >>
  simp[MEM_APPEND, MEM] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_observer_has_code:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb fn /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  L <> sb.cs_current_bb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) ==>
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb)
    (frag_relabel_observer sa sb L ids fn id)
Proof
  strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  `!bb. MEM bb (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) ==>
    bb.bb_label <> sb.cs_current_bb` by
    (drule_all start_swap_emitted_blocks >> simp[MEM_APPEND, MEM] >>
     rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
  simp[fn_has_code_def] >> conj_tac
  >- (rpt strip_tac >>
      simp[frag_relabel_observer_def, Once lookup_block_def, FIND_thm] >>
      rewrite_tac[GSYM lookup_block_def] >>
      irule frag_blocks_consistent_lookup >>
      metis_tac[start_swap_blocks_consistent]) >>
  qexists_tac `<|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` >>
  simp[frag_relabel_observer_cut, IS_PREFIX_APPEND]
QED

Theorem frag_relabel_ids_reorder[local]:
  ALL_DISTINCT (a ++ b ++ c) /\ ALL_DISTINCT ids /\ ~MEM id ids /\
  (!x. MEM x (a ++ b ++ c) ==> ~MEM x ids /\ x <> id) ==>
  ALL_DISTINCT (c ++ [id] ++ b ++ ids ++ a)
Proof
  simp[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[]
QED

Theorem frag_relabel_observer_id_layout:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks ==>
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (frag_relabel_observer sa sb L ids fn id).fn_blocks) =
  MAP (\i. i.inst_id) sb.cs_current_insts ++ [id] ++
  MAP (\i. i.inst_id)
    (FLAT (MAP (\bb. bb.bb_instructions) (FRONT (emitted_blocks sa sb)))) ++
  ids ++ MAP (\i. i.inst_id)
    (DROP (LENGTH sa.cs_current_insts) (LAST (emitted_blocks sa sb)).bb_instructions)
Proof
  strip_tac >> drule_all start_swap_emitted_blocks >> strip_tac >>
  simp[frag_relabel_observer_def, MAP_APPEND, FLAT_APPEND, MAP_FLAT,
       MAP_MAP_o, combinTheory.o_DEF, mk_inst_def, APPEND_ASSOC]
QED

Theorem frag_relabel_observer_ids:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ALL_DISTINCT ids /\ ~MEM id ids /\
  (!i. MEM i (frag_code sa sb) ==> ~MEM i.inst_id ids /\ i.inst_id <> id) ==>
  fn_inst_ids_distinct (frag_relabel_observer sa sb L ids fn id)
Proof
  strip_tac >> drule_all frag_relabel_observer_id_layout >> strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  simp[fn_inst_ids_distinct_def] >>
  irule frag_relabel_ids_reorder >>
  gvs[frag_code_def, NULL_EQ, MAP_APPEND] >>
  simp[MEM_MAP, MEM_APPEND] >> metis_tac[]
QED

Theorem frag_relabel_observer_name[simp]:
  (frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name
Proof
  simp[frag_relabel_observer_def]
QED

Theorem frag_relabel_observer_phi_zero:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb ==>
  !bb. lookup_block sb.cs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
    (fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
     metis_tac[]) >>
  simp[frag_relabel_observer_cut] >>
  Cases_on `sb.cs_current_insts` >> fs[phi_prefix_length_def, mk_inst_def]
QED

Theorem frag_relabel_observer_provenance:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb fn /\
  MEM inst (fn_insts (frag_relabel_observer sa sb L ids fn id)) /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> NOP ==>
  MEM inst (fn_insts fn)
Proof
  strip_tac >> drule_all start_swap_emitted_blocks >> strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  fs[fn_insts_def, frag_relabel_observer_def, frag_fn_insts_blocks_member,
     MEM_APPEND, MEM_MAP] >> gvs[]
  >- (fs[fn_has_code_def] >>
      `MEM inst bb.bb_instructions` by
        metis_tac[IS_PREFIX_APPEND, MEM_APPEND] >>
      drule lookup_block_MEM >> metis_tac[])
  >- (`MEM bb (emitted_blocks sa sb)` by
        (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
           [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
         metis_tac[MEM_APPEND]) >>
      fs[fn_has_code_def] >>
      `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by metis_tac[] >>
      drule lookup_block_MEM >> metis_tac[])
  >- gvs[MEM_MAP, mk_inst_def] >>
  `MEM inst (LAST (emitted_blocks sa sb)).bb_instructions` by
    metis_tac[TAKE_DROP, MEM_APPEND] >>
  fs[fn_has_code_def] >>
  `lookup_block (LAST (emitted_blocks sa sb)).bb_label fn.fn_blocks =
    SOME (LAST (emitted_blocks sa sb))` by metis_tac[MEM_LAST_NOT_NIL] >>
  drule lookup_block_MEM >> metis_tac[]
QED

Theorem frag_relabel_observer_no_invoke:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb ==>
  !i. MEM i (fn_insts (frag_relabel_observer sa sb L ids fn id)) ==>
      i.inst_opcode <> INVOKE
Proof
  strip_tac >> drule_all start_swap_emitted_blocks >> strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
  simp[fn_insts_def, frag_fn_insts_blocks_member, frag_relabel_observer_def,
       FLAT_APPEND, MAP_APPEND, MEM_FLAT, MEM_MAP, MEM_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[MEM_APPEND, MEM_MAP, mk_inst_def] >>
  qpat_x_assum `!i. _ ==> _` (qspec_then `i` mp_tac) >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_observer_exists:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) ==>
  ?L ids id.
    LENGTH ids = LENGTH sa.cs_current_insts /\ L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb) /\
    fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb)
      (frag_relabel_observer sa sb L ids fn id) /\
    fn_inst_ids_distinct (frag_relabel_observer sa sb L ids fn id) /\
    (!i. MEM i (fn_insts (frag_relabel_observer sa sb L ids fn id)) /\
         i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
    (!i. MEM i (fn_insts (frag_relabel_observer sa sb L ids fn id)) ==>
         i.inst_opcode <> INVOKE) /\
    (!bb. lookup_block sb.cs_current_bb
       (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `?L. L <> sb.cs_current_bb /\
       ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
       EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)` by
    metis_tac[frag_relabel_fresh_label] >>
  `?ids id. LENGTH ids = LENGTH sa.cs_current_insts /\ ALL_DISTINCT ids /\
       ~MEM id ids /\ (!i. MEM i (frag_code sa sb) ==>
         ~MEM i.inst_id ids /\ i.inst_id <> id)` by
    metis_tac[frag_relabel_fresh_ids] >>
  qexistsl_tac [`L`, `ids`, `id`] >> simp[] >> rpt conj_tac
  >- metis_tac[start_relabel_gas_free]
  >- metis_tac[frag_relabel_observer_has_code]
  >- metis_tac[frag_relabel_observer_ids]
  >- metis_tac[frag_relabel_observer_provenance]
  >- metis_tac[frag_relabel_observer_no_invoke] >>
  metis_tac[frag_relabel_observer_phi_zero]
QED

Theorem frag_relabel_observer_lookup_cases:
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  (lbl = sb.cs_current_bb /\
   bb = <|bb_label := sb.cs_current_bb;
          bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>) \/
  (lbl <> sb.cs_current_bb /\
   MEM bb (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) /\
   bb.bb_label = lbl)
Proof
  Cases_on `lbl = sb.cs_current_bb`
  >- simp[frag_relabel_observer_cut] >>
  simp[frag_relabel_observer_def, lookup_block_def, FIND_thm] >> strip_tac >>
  drule FIND_MEM >> strip_tac >> drule FIND_P >> simp[]
QED

Theorem frag_relabel_entry_instruction:
  LENGTH ids = LENGTH old /\ isPREFIX old bb.bb_instructions /\ LENGTH old <= idx ==>
  get_instruction
    (bb with <|bb_label := L;
      bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++
        DROP (LENGTH old) bb.bb_instructions|>) idx = get_instruction bb idx
Proof
  strip_tac >> fs[IS_PREFIX_APPEND] >>
  simp[get_instruction_def, DROP_LENGTH_APPEND, EL_APPEND_EQN]
QED

Theorem frag_relabel_instruction_agrees:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb fn /\
  LENGTH ids = LENGTH sa.cs_current_insts /\ L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  (lbl = L ==> LENGTH sa.cs_current_insts <= idx) /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  ?original. lookup_block (if lbl = L then sa.cs_current_bb else lbl) fn.fn_blocks =
               SOME original /\ get_instruction original idx = SOME inst
Proof
  strip_tac >> drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `idx < LENGTH sb.cs_current_insts` by
        (fs[get_instruction_def, frag_observer_cut_def] >> decide_tac) >>
      fs[fn_has_code_def] >>
      fs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >>
  fs[MEM_APPEND] >> gvs[]
  >- (`MEM bb (emitted_blocks sa sb)` by
        (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
           [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
         metis_tac[MEM_APPEND]) >>
      `bb.bb_label <> L` by (fs[MEM_MAP] >> metis_tac[]) >>
      fs[fn_has_code_def] >> metis_tac[]) >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  qexists_tac `LAST (emitted_blocks sa sb)` >>
  conj_tac >- (fs[fn_has_code_def] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  drule_all frag_relabel_entry_instruction >>
  disch_then (qspec_then `L` mp_tac) >> simp[]
QED

Theorem frag_relabel_code_provenance:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  (lbl = L ==> LENGTH sa.cs_current_insts <= idx) /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  MEM inst (frag_code sa sb)
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `idx < LENGTH sb.cs_current_insts` by
        (fs[get_instruction_def, frag_observer_cut_def] >> decide_tac) >>
      simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj2_tac >>
      fs[get_instruction_def, EL_APPEND_EQN] >> metis_tac[MEM_EL]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >>
  fs[MEM_APPEND] >> gvs[]
  >- (simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj2_tac >>
      `MEM inst bb.bb_instructions` by
        metis_tac[frag_instruction_drop_member, DROP_0, ZERO_LESS_EQ] >>
      simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj1_tac >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  drule_all frag_relabel_entry_instruction >>
  disch_then (qspec_then `L` mp_tac) >> strip_tac >>
  irule frag_instruction_drop_member >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem frag_relabel_front_nonphi:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  MEM bb (FRONT (emitted_blocks sa sb)) ==>
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM i (FLAT (MAP (\bb. bb.bb_instructions) (FRONT (emitted_blocks sa sb))))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_MEM] >> metis_tac[]
QED

Theorem frag_relabel_target_phis:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ lbl <> L /\
  (sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
    phi_prefix_length original.bb_instructions = 0 /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  (`emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
        (fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
         metis_tac[]) >>
      fs[fn_has_code_def, IS_PREFIX_APPEND] >>
      Cases_on `sb.cs_current_insts` >>
      fs[phi_prefix_length_def, mk_inst_def]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >> fs[MEM_APPEND] >> gvs[] >>
  `MEM bb (emitted_blocks sa sb)` by
    (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
       [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
     metis_tac[MEM_APPEND]) >>
  drule_all frag_relabel_front_nonphi >> strip_tac >>
  qexists_tac `bb` >> conj_tac >- (fs[fn_has_code_def] >> metis_tac[]) >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def])
QED

Theorem frag_relabel_jump_no_reentry:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  (lbl = L ==> LENGTH sa.cs_current_insts <= idx) /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst /\
  (!i. MEM i (frag_code sa sb) ==> ~MEM (Label L) i.inst_operands) /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base inst s = OK u ==>
  u.vs_current_bb <> L
Proof
  strip_tac >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  irule frag_observer_jump_no_reentry >> metis_tac[]
QED

Theorem frag_relabel_position_boundaries:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  L <> sb.cs_current_bb /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (s with vs_current_bb := L).vs_inst_idx =
    LENGTH (start_relabel L ids sa).cs_current_insts /\
  (if (s with vs_current_bb := L).vs_current_bb = L
   then sa.cs_current_bb else (s with vs_current_bb := L).vs_current_bb) =
    s.vs_current_bb /\
  (if sb.cs_current_bb = L then sa.cs_current_bb else sb.cs_current_bb) =
    sb.cs_current_bb /\
  frag_observer_cut (start_swap sa L ids sb) = frag_observer_cut sb
Proof
  strip_tac >> drule_all start_swap_fields >> strip_tac >>
  simp[start_relabel_def, frag_observer_cut_def]
QED

Definition frag_relabel_state_def:
  frag_relabel_state L entry u v <=>
    ?p. v = u with
      <|vs_current_bb := (if u.vs_current_bb = L then entry else u.vs_current_bb);
        vs_prev_bb := p|>
End

Theorem frag_relabel_state_initial:
  s.vs_current_bb = entry ==>
  frag_relabel_state L entry (s with vs_current_bb := L) s
Proof
  simp[frag_relabel_state_def] >> strip_tac >>
  qexists_tac `s.vs_prev_bb` >> simp[venom_state_component_equality]
QED

Theorem frag_relabel_state_fields:
  frag_relabel_state L entry u v ==>
  v.vs_inst_idx = u.vs_inst_idx /\ v.vs_halted = u.vs_halted /\
  v.vs_current_bb = (if u.vs_current_bb = L then entry else u.vs_current_bb)
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> simp[]
QED

Theorem frag_relabel_state_cut:
  frag_relabel_state L entry u v /\ u.vs_current_bb <> L ==>
  v = u with vs_prev_bb := v.vs_prev_bb
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> simp[]
QED

Theorem frag_relabel_state_post:
  frag_relabel_state L entry u v /\ u.vs_current_bb <> L /\ Q u /\
  (!t p. Q t ==> Q (t with vs_prev_bb := p)) ==> Q v
Proof
  strip_tac >> drule_all frag_relabel_state_cut >> strip_tac >> metis_tac[]
QED

Theorem frag_relabel_state_abort_post:
  frag_relabel_state L entry u v /\ R (Abort a u) /\
  (!a t b p. R (Abort a t) ==>
     R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) ==>
  R (Abort a v)
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> simp[]
QED

Theorem frag_relabel_state_intret_post:
  frag_relabel_state L entry u v /\ R (IntRet vals u) /\
  (!vals t b p. R (IntRet vals t) ==>
     R (IntRet vals (t with <| vs_current_bb := b; vs_prev_bb := p |>))) ==>
  R (IntRet vals v)
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> simp[]
QED

Theorem frag_eval_operand_control[local]:
  !op s b p.
    eval_operand op (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem frag_eval_operands_control[local]:
  !ops s b p.
    eval_operands ops (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, frag_eval_operand_control]
QED

Theorem frag_pure1_control[local]:
  exec_pure1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure1 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_pure1_def, frag_eval_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_pure2_control[local]:
  exec_pure2 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure2 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `rest`
  >- (simp[exec_pure2_def, frag_eval_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_pure3_control[local]:
  exec_pure3 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure3 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `rest` ["", "d tail"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `tail`
  >- (simp[exec_pure3_def, frag_eval_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand d s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_call_request_control[local]:
  venom_call_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    addr value off sz static = venom_call_request s addr value off sz static
Proof
  simp[venomCallOracleDefsTheory.venom_call_request_def, read_memory_def]
QED

Theorem frag_create_request_control[local]:
  venom_create_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt = venom_create_request s value off sz salt
Proof
  simp[venomCallOracleDefsTheory.venom_create_request_def, read_memory_def]
QED

Theorem frag_consume_call_control[local]:
  consume_call_outcome rq ro rs (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (consume_call_outcome rq ro rs s),
     SND (consume_call_outcome rq ro rs s) with
       <|vs_prev_bb := p; vs_current_bb := b|>)
Proof
  simp[venomCallOracleDefsTheory.consume_call_outcome_eq,
       write_memory_with_expansion_def]
QED

Theorem frag_consume_create_control[local]:
  consume_create_outcome rq (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (consume_create_outcome rq s),
     SND (consume_create_outcome rq s) with
       <|vs_prev_bb := p; vs_current_bb := b|>)
Proof
  simp[venomCallOracleDefsTheory.consume_create_outcome_eq]
QED

Theorem frag_ext_call_control[local]:
  exec_ext_call inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr value ao az ro rz static =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_ext_call inst s gas addr value ao az ro rz static)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_ext_call_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_ext_call_def, frag_call_request_control,
       venomCallOracleDefsTheory.consume_call_outcome_eq,
       write_memory_with_expansion_def, update_var_def,
       instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_create_control[local]:
  exec_create inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_create inst s value off sz salt)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_create_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_create_def, frag_create_request_control,
       venomCallOracleDefsTheory.consume_create_outcome_eq,
       update_var_def, halt_state_def, set_returndata_def,
       instIdxIndepTheory.exec_result_map_def] >>
  IF_CASES_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_delegate_state_control[local]:
  make_venom_delegatecall_state
    (s with <|vs_prev_bb := p; vs_current_bb := b|>) target gas data code static =
  make_venom_delegatecall_state s target gas data code static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem frag_extract_control[local]:
  extract_venom_result (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    output ro rz result =
  OPTION_MAP (\v. (FST v, SND v with <|vs_prev_bb := p; vs_current_bb := b|>))
    (extract_venom_result s output ro rz result)
Proof
  Cases_on `result` >- simp[extract_venom_result_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[extract_venom_result_def] >>
  namedCases_on `pair1.contexts` ["", "ctxt rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >>
  PairCases_on `ctxt` >>
  Cases_on `pair0` >> simp[write_memory_with_expansion_def] >>
  qmatch_goalsub_rename_tac `case outcome of NONE => _ | SOME _ => _` >>
  Cases_on `outcome` >>
  simp[write_memory_with_expansion_def]
QED

Theorem frag_delegatecall_control[local]:
  exec_delegatecall inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr ao az ro rz =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  simp[exec_delegatecall_def, read_memory_def, frag_delegate_state_control,
       frag_extract_control] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  rename1 `_ = SOME pair` >> PairCases_on `pair` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >> simp[instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem frag_read0_control[local]:
  f (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f s ==>
  exec_read0 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read0 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem frag_read1_control[local]:
  (!v. f v (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f v s) ==>
  exec_read1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read1 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_read1_def, frag_eval_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_write2_control[local]:
  (!v w. f v w (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
     f v w s with <|vs_prev_bb := p; vs_current_bb := b|>) ==>
  exec_write2 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_write2 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `rest`
  >- (simp[exec_write2_def, frag_eval_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >>
      simp[instIdxIndepTheory.exec_result_map_def]) >>
  simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_relabel_base_ordinary:
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[is_pseudo_def, is_terminator_def] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_pure1_control, frag_pure2_control, frag_pure3_control,
       frag_ext_call_control, frag_create_control, frag_delegatecall_control,
       frag_read0_control, frag_read1_control, frag_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def,
       instIdxIndepTheory.exec_result_map_def] >>
  simp[frag_eval_operand_control, frag_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def,
       update_var_def, exec_alloca_def, exec_gas_def,
       instIdxIndepTheory.exec_result_map_def] >>
  gvs[exec_alloca_def, exec_gas_def, AllCaseEqs(), update_var_def]
QED

Theorem frag_relabel_base_nonphi[local]:
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `is_pseudo inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >>
      fs[is_pseudo_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> simp[update_var_def]) >>
  metis_tac[frag_relabel_base_ordinary]
QED

Theorem frag_relabel_ordinary_edge[local]:
  frag_relabel_state L entry u v /\ ~u.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst u = OK middle /\ ~middle.vs_halted ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L entry
         (middle with vs_inst_idx := SUC u.vs_inst_idx) v'
Proof
  strip_tac >>
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  drule_all frag_relabel_base_nonphi >>
  disch_then (qspecl_then
    [`p`, `if u.vs_current_bb = L then entry else u.vs_current_bb`] assume_tac) >>
  qexists_tac `middle with <|vs_current_bb :=
     (if u.vs_current_bb = L then entry else u.vs_current_bb);
     vs_prev_bb := p; vs_inst_idx := SUC u.vs_inst_idx|>` >>
  gvs[] >> conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def]) >>
  qexists_tac `p` >> simp[venom_state_component_equality]
QED

Theorem frag_relabel_jump_control[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst u = OK middle ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)
Proof
  simp[MEM] >> strip_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_eval_operand_control] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[jump_to_def, venom_state_component_equality]
QED

Definition frag_relabel_context_def:
  frag_relabel_context sa sb L ids fn <=>
    cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
    fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0)
End

Theorem frag_relabel_region_entry_bound[local]:
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)
Proof
  simp[frag_observer_region_def, start_relabel_def] >> metis_tac[]
QED

Theorem frag_relabel_off_cut_opcodes[local]:
  frag_relabel_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN
Proof
  strip_tac >> fs[frag_relabel_context_def] >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    metis_tac[frag_relabel_region_entry_bound] >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM]
QED

Theorem frag_relabel_region_closed[local]:
  frag_relabel_context sa sb L ids fn ==>
  observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all frag_relabel_off_cut_opcodes >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (`(s.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= s.vs_inst_idx)` by
       (fs[frag_relabel_context_def] >> metis_tac[frag_relabel_region_entry_bound]) >>
     `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
     fs[frag_relabel_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >>
  fs[frag_relabel_context_def] >> drule_all start_swap_fields >> strip_tac >>
  gvs[frag_observer_region_def, start_relabel_def, MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_step_edge[local]:
  frag_relabel_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all frag_relabel_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_context_def] >> metis_tac[frag_relabel_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- (irule frag_relabel_ordinary_edge >> goal_assum (drule_at Any) >>
      gvs[]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (fs[frag_relabel_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  `?original_target. lookup_block middle.vs_current_bb fn.fn_blocks = SOME original_target /\
      phi_prefix_length original_target.bb_instructions = 0 /\
      phi_prefix_length target.bb_instructions = 0` by
    (fs[frag_relabel_context_def] >> metis_tac[frag_relabel_target_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
       (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_prev_bb := p|>) =
    OK (entered with vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb))` by
    metis_tac[frag_relabel_jump_control, MEM] >>
  qexists_tac `entered with <|vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_inst_idx := 0|>` >>
  gvs[] >> (conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >>
      disj1_tac >>
      once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]) >>
  qexists_tac `SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)` >>
  simp[venom_state_component_equality])
QED

Theorem frag_relabel_base_abort[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = Abort a t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    Abort a (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_pure1_control, frag_pure2_control, frag_pure3_control,
       frag_ext_call_control, frag_create_control, frag_delegatecall_control,
       frag_read0_control, frag_read1_control, frag_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def,
       instIdxIndepTheory.exec_result_map_def] >>
  simp[frag_eval_operand_control, frag_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  qpat_x_assum `_ = Abort _ _` mp_tac >> pairarg_tac >> simp[]
QED

Theorem frag_mcopy_control[local]:
  mcopy dst src sz (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (mcopy dst src sz s) with <|vs_prev_bb := p; vs_current_bb := b|>
Proof
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def]
QED

Theorem frag_pack_dret_control[local]:
  !pairs cursor s b p.
  pack_dret_dynamic cursor pairs (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     (SND (SND (pack_dret_dynamic cursor pairs s))) with
       <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[pack_dret_dynamic_def, frag_mcopy_control] >>
  first_x_assum (fn th => rewrite_tac[th]) >>
  pairarg_tac >> simp[]
QED

Theorem frag_relabel_base_intret[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = IntRet vals t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    IntRet vals (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_pure1_control, frag_pure2_control, frag_pure3_control,
       frag_ext_call_control, frag_create_control, frag_delegatecall_control,
       frag_read0_control, frag_read1_control, frag_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def,
       instIdxIndepTheory.exec_result_map_def] >>
  simp[frag_eval_operand_control, frag_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  rewrite_tac[frag_pack_dret_control] >>
  qpat_x_assum `_ = IntRet _ _` mp_tac >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem frag_relabel_base_exit[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r
Proof
  Cases_on `r` >> simp[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  (rpt strip_tac)
  >- (irule (SRULE [] frag_relabel_base_abort) >> simp[])
  >> irule (SRULE [] frag_relabel_base_intret) >> simp[]
QED

Theorem frag_relabel_exit_edge[local]:
  frag_relabel_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  frag_relabel_state L sa.cs_current_bb u v /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  ?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> drule_all frag_relabel_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_context_def] >> metis_tac[frag_relabel_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexistsl_tac [`if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb`, `p`] >>
  `step_inst_base inst (u with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) = exec_result_map (\t. t with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) (step_inst_base inst u)` by
    (irule frag_relabel_base_exit >> simp[]) >>
  gvs[] >> simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def] >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_relabel_prefix_path[local]:
  !ctx observed cut u t. local_prefix ctx observed cut u t ==>
  !sa sb L ids fn id v.
    observed = frag_relabel_observer sa sb L ids fn id /\
    cut = frag_observer_cut sb /\
    frag_relabel_context sa sb L ids fn /\
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?t'. gas_path ctx fn v 0 (OK t') /\
         frag_relabel_state L sa.cs_current_bb t t'
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `v` >> simp[] >>
      irule (cj 1 gas_path_rules) >>
      drule frag_relabel_state_fields >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule_all frag_relabel_step_edge >> strip_tac >>
  `observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))` by
      (irule frag_relabel_region_closed >> simp[]) >>
  `?t'. gas_path ctx fn v' 0 (OK t') /\
        frag_relabel_state L sa.cs_current_bb t t'` by
    (first_x_assum irule >> simp[] >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem frag_relabel_exit_path_aux[local]:
  frag_relabel_context sa sb L ids fn ==>
  !fuel n u bb r v.
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    ~u.vs_halted /\
    lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - u.vs_inst_idx = n /\
    run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
    exit_result r /\ (!h. r <> Halt h) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?b p. gas_path ctx fn v 0
      (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> completeInduct_on `fuel` >> completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
                bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        gvs[frag_observer_cut_def, frag_relabel_observer_cut] >>
      `get_instruction bb u.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = Halt (stop_view u)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >> gvs[mk_inst_def]) >>
      metis_tac[]) >>
  Cases_on `get_instruction bb u.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ u = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_relabel_off_cut_opcodes] >>
  Cases_on `step_inst_base inst u` >>
  qpat_x_assum `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >> strip_tac
  >- (rename1 `step_inst_base inst u = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary")
  >- suspend "abort"
  >- suspend "intret" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_exit_path_aux[abort]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_exit_path_aux[intret]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_exit_path_aux[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (middle with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  drule_all frag_relabel_step_edge >> strip_tac >>
  `(u.vs_current_bb,SUC u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC u.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC u.vs_inst_idx`, `bb`, `r`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`b`, `p`] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Resume frag_relabel_exit_path_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_relabel_observer sa sb L ids fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_exit_path_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  drule_all frag_relabel_step_edge >> strip_tac >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >>
  `run_from remaining ctx (frag_relabel_observer sa sb L ids fn id)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = r` by
    simp[run_from_def] >>
  qpat_x_assum `gas_path _ _ v' _ _` mp_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`b`, `p`] >>
  qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Finalise frag_relabel_exit_path_aux

Theorem frag_relabel_exit_path[local]:
  frag_relabel_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~u.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
  exit_result r /\ (!h. r <> Halt h) /\
  frag_relabel_state L sa.cs_current_bb u v ==>
  ?b p. gas_path ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[Once run_from_def, exit_result_def] >>
  irule frag_relabel_exit_path_aux >> metis_tac[]
QED

Theorem frag_relabel_halt_prefix[local]:
  frag_relabel_context sa sb L ids fn /\
  (s.vs_current_bb,s.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
       (frag_observer_cut sb) s u /\ stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[run_from_def] >>
  irule frag_cut_run_prefix_aux >> simp[] >> conj_tac
  >- (simp[frag_observer_cut_def, frag_relabel_observer_cut] >>
      rpt strip_tac >> gvs[] >> metis_tac[frag_observer_cut_instruction]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`u` |-> `s with <|vs_current_bb := lbl; vs_inst_idx := idx|>`]
        (cj 2 frag_relabel_off_cut_opcodes)) >> simp[]) >>
  metis_tac[frag_relabel_region_closed]
QED

Theorem frag_exec_gas_path_relabel:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    fn_has_code sa sb fn /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `frag_relabel_context sa sb L ids fn` by simp[frag_relabel_context_def] >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `( (s with vs_current_bb := L).vs_current_bb,
     (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume frag_exec_gas_path_relabel[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_relabel_observer sa sb L ids fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule frag_relabel_prefix_path >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  disj1_tac >> qexists_tac `v` >>
  gvs[gas_marked_path_def, frag_observer_cut_def]
QED

Resume frag_exec_gas_path_relabel[exit]:
  qmatch_asmsub_abbrev_tac `R r` >>
  `!h. r <> Halt h` by metis_tac[] >>
  `?b p. gas_path ctx fn s 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)` by
    (irule frag_relabel_exit_path >>
     simp[Abbr `r`] >>
     qpat_assum `frag_relabel_context _ _ _ _ _`
       (irule_at (Pat `frag_relabel_context _ _ _ _ _`)) >>
     qexistsl_tac [`s with vs_current_bb := L`, `id`, `fuel`] >> gvs[]) >>
  disj2_tac >>
  qexists_tac `exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r` >>
  simp[gas_marked_path_def] >>
  Cases_on `r` >> gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  metis_tac[]
QED

Finalise frag_exec_gas_path_relabel

Theorem abi_decode_sim_gas_path_relabel:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' (s with vs_current_bb := L) t) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
    fn_has_code sa sb fn /\
    (sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `frag_relabel_context sa sb L ids fn` by simp[frag_relabel_context_def] >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `((s with vs_current_bb := L).vs_current_bb,
    (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `Q t` >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule frag_relabel_prefix_path >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  qexists_tac `v` >> gvs[gas_marked_path_def, frag_observer_cut_def]
QED
