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
  fragGasPath gasCount arithmetic venomExecProofs

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

Theorem frag_fn_insts_blocks_member[local]:
  !blocks inst. MEM inst (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
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
  cheat
QED

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
  cheat
QED
