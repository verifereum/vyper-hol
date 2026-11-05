(* Concrete nested encoder producer probe; retained entry prefix is not executed. *)
Theory exprSimAbiEncodeRegion
Ancestors
  exprSimAbiEncodeRegistration abiEncoderObserver builtinAbi vyperCompiler
  venomWf fragExec venomExecSemantics venomInst list opcodeClass venomStepProps
  venomInstProps venomExecProofs

Definition encode_probe_start_def:
  encode_probe_start =
    (initial_compile_state "entry") with
      <| cs_next_id := 1;
         cs_current_insts := [mk_inst 0 INVOKE [Label "callee"] []] |>
End

Definition encode_probe_info_def:
  encode_probe_info =
    AbiDynArray (AbiDynArray AbiPrimWord 32 32 F) 32 32 T
End

Definition encode_probe_result_def:
  encode_probe_result =
    lower_abi_encode F (SOME 0w) (Lit 4096w) encode_probe_info 4096
      encode_probe_start
End

Theorem encode_probe_shape:
  LENGTH (SND encode_probe_result).cs_blocks = 6
Proof
  EVAL_TAC
QED

Theorem encode_probe_summary:
  (MAP (\bb. (bb.bb_label, LENGTH bb.bb_instructions))
     (SND encode_probe_result).cs_blocks,
   (SND encode_probe_result).cs_current_bb,
   LENGTH (SND encode_probe_result).cs_current_insts,
   (SND encode_probe_result).cs_next_id) =
  ([("@enc_dyn_exit_5",13); ("@enc_dyn_body_4",12);
    ("@enc_dyn_hdr_3",4); ("@enc_dyn_body_1",16);
    ("@enc_dyn_hdr_0",4); ("entry",15)], "@enc_dyn_exit_2",9,73)
Proof
  EVAL_TAC
QED

Definition encode_probe_observer_def:
  encode_probe_observer fn =
    fn with fn_blocks :=
      emitted_blocks encode_probe_start (SND encode_probe_result) ++
      [<| bb_label := (SND encode_probe_result).cs_current_bb;
          bb_instructions := (SND encode_probe_result).cs_current_insts ++
            [mk_inst 73 STOP [] []] |>]
End

Definition encode_probe_cut_def:
  encode_probe_cut = ("@enc_dyn_exit_2",9)
End

Theorem encode_probe_embedding:
  fn_has_code encode_probe_start (SND encode_probe_result)
    (encode_probe_observer fn)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem encode_probe_ids:
  fn_inst_ids_distinct (encode_probe_observer fn)
Proof
  EVAL_TAC
QED

Theorem encode_probe_name:
  (encode_probe_observer fn).fn_name = fn.fn_name
Proof
  simp[encode_probe_observer_def]
QED

Definition encode_probe_region_def:
  encode_probe_region =
    {(lbl,idx) | (lbl = "entry" /\ 1 <= idx /\ idx < 15) \/
       (lbl = "@enc_dyn_hdr_0" /\ idx < 4) \/
       (lbl = "@enc_dyn_body_1" /\ idx < 16) \/
       (lbl = "@enc_dyn_hdr_3" /\ idx < 4) \/
       (lbl = "@enc_dyn_body_4" /\ idx < 12) \/
       (lbl = "@enc_dyn_exit_5" /\ idx < 13) \/
       (lbl = "@enc_dyn_exit_2" /\ idx <= 9)}
End

Theorem encode_probe_entry:
  (encode_probe_start.cs_current_bb,
   LENGTH encode_probe_start.cs_current_insts) IN encode_probe_region
Proof
  EVAL_TAC >> simp[]
QED

Theorem encode_probe_stop:
  ?bb. lookup_block (FST encode_probe_cut)
      (encode_probe_observer fn).fn_blocks = SOME bb /\
    get_instruction bb (SND encode_probe_cut) = SOME (mk_inst 73 STOP [] [])
Proof
  EVAL_TAC >> simp[]
QED


Definition encode_probe_positions_def:
  encode_probe_positions =
    GENLIST (\i. ("entry",i+1)) 14 ++
    GENLIST (\i. ("@enc_dyn_hdr_0",i)) 4 ++
    GENLIST (\i. ("@enc_dyn_body_1",i)) 16 ++
    GENLIST (\i. ("@enc_dyn_hdr_3",i)) 4 ++
    GENLIST (\i. ("@enc_dyn_body_4",i)) 12 ++
    GENLIST (\i. ("@enc_dyn_exit_5",i)) 13 ++
    GENLIST (\i. ("@enc_dyn_exit_2",i)) 10
End

Theorem encode_probe_positions_region:
  MEM (lbl,idx) encode_probe_positions <=>
  (lbl,idx) IN encode_probe_region
Proof
  simp_tac std_ss [encode_probe_positions_def, encode_probe_region_def,
    MEM_APPEND, MEM_GENLIST, pred_setTheory.GSPECIFICATION, pairTheory.PAIR_EQ] >>
  `(?i:num. i < 14 /\ idx = i + 1) <=> 1 <= idx /\ idx < 15`
    by (eq_tac >- (rpt strip_tac >> decide_tac) >>
        strip_tac >> qexists_tac `idx - 1` >> decide_tac) >>
  simp_tac std_ss [pairTheory.EXISTS_PROD, pairTheory.PAIR_EQ,
    GSYM CONJ_ASSOC, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
  simp_tac arith_ss [AC DISJ_ASSOC DISJ_COMM, AC CONJ_ASSOC CONJ_COMM] >>
  `idx < 10 <=> idx <= 9` by (pop_assum kall_tac >> decide_tac) >>
  simp_tac std_ss [LEFT_EXISTS_AND_THM] >> metis_tac[]
QED

Definition encode_probe_opcode_check_def:
  encode_probe_opcode_check blocks p <=>
    p = encode_probe_cut \/
    (case lookup_block (FST p) blocks of
       NONE => F
     | SOME bb => case get_instruction bb (SND p) of
         NONE => F
       | SOME inst =>
           MEM inst.inst_opcode [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; JMP; JNZ])
End

Theorem encode_probe_opcode_table:
  EVERY (encode_probe_opcode_check (encode_probe_observer fn).fn_blocks)
    encode_probe_positions
Proof
  CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV EVAL))) >> EVAL_TAC
QED

Theorem encode_probe_opcode_inventory:
  (lbl,idx) IN encode_probe_region /\ (lbl,idx) <> encode_probe_cut /\
  lookup_block lbl (encode_probe_observer fn).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  MEM inst.inst_opcode [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; JMP; JNZ]
Proof
  strip_tac >>
  mp_tac encode_probe_opcode_table >>
  rewrite_tac[EVERY_MEM] >>
  disch_then (qspec_then `(lbl,idx)` mp_tac) >>
  simp[encode_probe_positions_region, encode_probe_opcode_check_def]
QED

Theorem encode_probe_safe:
  observer_region_safe (encode_probe_observer fn)
    encode_probe_cut encode_probe_region
Proof
  rw[observer_region_safe_def]
  >- (mp_tac encode_probe_stop >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all encode_probe_opcode_inventory >> strip_tac >>
  rpt conj_tac
  >- gvs[]
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      drule step_inst_base_halt_opcodes >> gvs[]) >>
  rpt strip_tac >> drule step_inst_base_ok_halted >> simp[]
QED

Definition encode_probe_target_check_def:
  encode_probe_target_check blocks lbl <=>
    MEM (lbl,0) encode_probe_positions /\
    (case lookup_block lbl blocks of NONE => F | SOME bb =>
      phi_prefix_length bb.bb_instructions = 0)
End

Definition encode_probe_control_check_def:
  encode_probe_control_check blocks p <=>
    p = encode_probe_cut \/
    (case lookup_block (FST p) blocks of NONE => F | SOME bb =>
     case get_instruction bb (SND p) of NONE => F | SOME inst =>
       if is_terminator inst.inst_opcode then
         (case inst.inst_operands of [] => F | a::rest =>
           (case rest of
              [] => (case a of Label lbl => inst.inst_opcode = JMP /\
                       encode_probe_target_check blocks lbl | _ => F)
            | b::tail => (case tail of [] => F | c::remaining =>
                (case remaining of
                   [] => (case b of Label yes =>
                            (case c of Label no => inst.inst_opcode = JNZ /\
                               encode_probe_target_check blocks yes /\
                               encode_probe_target_check blocks no | _ => F)
                          | _ => F)
                 | d::ds => F))))
       else MEM (FST p,SUC (SND p)) encode_probe_positions)
End

Theorem encode_probe_control_table:
  EVERY (encode_probe_control_check (encode_probe_observer fn).fn_blocks)
    encode_probe_positions
Proof
  CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV EVAL))) >> EVAL_TAC
QED

Theorem encode_probe_control_at:
  p IN encode_probe_region ==>
  encode_probe_control_check (encode_probe_observer fn).fn_blocks p
Proof
  Cases_on `p` >> strip_tac >>
  mp_tac encode_probe_control_table >> rewrite_tac[EVERY_MEM] >>
  disch_then irule >> simp[encode_probe_positions_region]
QED


Theorem encode_probe_control_jump:
  encode_probe_control_check blocks p /\ p <> encode_probe_cut /\
  lookup_block (FST p) blocks = SOME bb /\
  get_instruction bb (SND p) = SOME inst /\ is_terminator inst.inst_opcode ==>
  (?lbl. inst.inst_opcode = JMP /\ inst.inst_operands = [Label lbl] /\
         encode_probe_target_check blocks lbl) \/
  (?v yes no. inst.inst_opcode = JNZ /\
    inst.inst_operands = [v; Label yes; Label no] /\
    encode_probe_target_check blocks yes /\ encode_probe_target_check blocks no)
Proof
  strip_tac >> gvs[encode_probe_control_check_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[] >>
  namedCases_on `rest` ["", "b tail"]
  >- (Cases_on `a` >> gvs[]) >>
  namedCases_on `tail` ["", "c remaining"] >> gvs[] >>
  Cases_on `remaining` >> gvs[] >>
  Cases_on `b` >> gvs[] >> Cases_on `c` >> gvs[]
QED

Theorem encode_probe_control_next:
  encode_probe_control_check blocks p /\ p <> encode_probe_cut /\
  lookup_block (FST p) blocks = SOME bb /\
  get_instruction bb (SND p) = SOME inst /\ ~is_terminator inst.inst_opcode ==>
  (FST p,SUC (SND p)) IN encode_probe_region
Proof
  Cases_on `p` >> strip_tac >> gvs[encode_probe_control_check_def,
    encode_probe_positions_region]
QED

Theorem encode_probe_target:
  encode_probe_target_check blocks lbl ==>
  (lbl,0) IN encode_probe_region /\
  ?bb. lookup_block lbl blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `lookup_block lbl blocks` >>
  simp[encode_probe_target_check_def, encode_probe_positions_region]
QED

Theorem encode_probe_closed:
  observer_region_closed ctx (encode_probe_observer fn)
    encode_probe_cut encode_probe_region
Proof
  rw[observer_region_closed_def, abi_observer_step_def]
  >- (drule encode_probe_control_at >> disch_then (qspec_then `fn` assume_tac) >>
      drule encode_probe_control_next >> simp[] >>
      strip_tac >>
      drule step_preserves_control_flow >> simp[] >> strip_tac >> gvs[]) >>
  drule encode_probe_control_at >> disch_then (qspec_then `fn` assume_tac) >>
  drule encode_probe_control_jump >> simp[] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(),
      venomStateTheory.eval_operand_def, venomStateTheory.jump_to_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  metis_tac[encode_probe_target, optionTheory.SOME_11]
QED

Theorem encode_probe_blocks:
  !bb. MEM bb (encode_probe_observer fn).fn_blocks ==>
    MEM bb (emitted_blocks encode_probe_start (SND encode_probe_result)) \/
    bb = <| bb_label := (SND encode_probe_result).cs_current_bb;
            bb_instructions := (SND encode_probe_result).cs_current_insts ++
              [mk_inst 73 STOP [] []] |>
Proof
  simp[encode_probe_observer_def]
QED

Theorem encode_probe_final_phi:
  (SND encode_probe_result).cs_current_insts <> [] /\
  phi_prefix_length (SND encode_probe_result).cs_current_insts = 0
Proof
  EVAL_TAC
QED

Theorem encode_probe_lookup_member[local]:
  !blocks lbl bb. lookup_block lbl blocks = SOME bb ==>
    MEM bb blocks /\ bb.bb_label = lbl
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem encode_probe_prefix_phi[local]:
  pre <> [] /\ phi_prefix_length pre = 0 /\ isPREFIX pre xs ==>
  phi_prefix_length xs = 0
Proof
  Cases_on `pre` >> simp[] >> Cases_on `xs` >>
  simp[phi_prefix_length_def, isPREFIX] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >> gvs[]
QED

Theorem encode_probe_block_transfer:
  fn_has_code encode_probe_start (SND encode_probe_result) func /\
  lookup_block lbl (encode_probe_observer fn).fn_blocks = SOME bb ==>
  lookup_block lbl func.fn_blocks = SOME bb \/
  (lbl = (SND encode_probe_result).cs_current_bb /\
   bb.bb_instructions = (SND encode_probe_result).cs_current_insts ++
      [mk_inst 73 STOP [] []] /\
   ?bb'. lookup_block lbl func.fn_blocks = SOME bb' /\
         isPREFIX (SND encode_probe_result).cs_current_insts bb'.bb_instructions)
Proof
  strip_tac >> drule encode_probe_lookup_member >> strip_tac >>
  drule encode_probe_blocks >> strip_tac
  >- (gvs[fn_has_code_def] >> metis_tac[]) >>
  gvs[fn_has_code_def] >> metis_tac[]
QED

Theorem encode_probe_final_bound:
  (lbl,idx) IN encode_probe_region /\ (lbl,idx) <> encode_probe_cut /\
  lbl = (SND encode_probe_result).cs_current_bb ==>
  idx < LENGTH (SND encode_probe_result).cs_current_insts
Proof
  mp_tac encode_probe_summary >> simp[] >> strip_tac >>
  strip_tac >> gvs[encode_probe_region_def, encode_probe_cut_def]
QED

Theorem encode_probe_agrees:
  fn_has_code encode_probe_start (SND encode_probe_result) func ==>
  region_code_agrees (encode_probe_observer fn) func
    encode_probe_cut encode_probe_region
Proof
  strip_tac >> simp[region_code_agrees_def] >> conj_tac
  >- (rpt strip_tac >> drule_all encode_probe_block_transfer >> strip_tac
      >- metis_tac[] >>
      drule_all encode_probe_final_bound >> strip_tac >>
      qexists_tac `bb'` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
      gvs[get_instruction_def, EL_APPEND_EQN]) >>
  rpt strip_tac >> drule_all encode_probe_block_transfer >> strip_tac
  >- metis_tac[] >>
  qexists_tac `bb'` >> simp[] >>
  `phi_prefix_length bb'.bb_instructions = 0` by
    (irule encode_probe_prefix_phi >>
     qexists_tac `(SND encode_probe_result).cs_current_insts` >>
     simp[encode_probe_final_phi]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (irule encode_probe_prefix_phi >>
     qexists_tac `(SND encode_probe_result).cs_current_insts` >>
     simp[encode_probe_final_phi]) >> gvs[]
QED

Theorem encode_probe_insts_member[local]:
  !blocks i. MEM i (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM i bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem encode_probe_opcode_inclusion:
  fn_has_code encode_probe_start (SND encode_probe_result) func /\
  MEM i (fn_insts (encode_probe_observer fn)) /\ i.inst_opcode <> STOP ==>
  MEM i (fn_insts func)
Proof
  simp[fn_insts_def, encode_probe_insts_member] >> strip_tac >>
  drule encode_probe_blocks >> strip_tac
  >- (gvs[fn_has_code_def] >> metis_tac[encode_probe_lookup_member]) >>
  gvs[mk_inst_def] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  drule encode_probe_lookup_member >> strip_tac >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[MEM_APPEND]
QED

Theorem encode_probe_allocas_distinct:
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA)
    (fn_insts (encode_probe_observer fn)))
Proof
  EVAL_TAC
QED

Theorem encode_probe_labels_distinct:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (encode_probe_observer fn).fn_blocks)
Proof
  EVAL_TAC
QED

Theorem encode_probe_resource_inclusion:
  fn_has_code encode_probe_start (SND encode_probe_result) func ==>
  !i. MEM i (fn_insts (encode_probe_observer func)) /\
      (i.inst_opcode = ALLOCA \/ i.inst_opcode = INVOKE \/
       i.inst_opcode = DALLOCA) ==> MEM i (fn_insts func)
Proof
  rpt strip_tac >> irule encode_probe_opcode_inclusion >> simp[] >>
  metis_tac[]
QED
