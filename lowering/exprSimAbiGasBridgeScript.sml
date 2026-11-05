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
