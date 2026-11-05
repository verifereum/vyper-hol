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
         (case inst.inst_operands of
            [Label lbl] => inst.inst_opcode = JMP /\
              encode_probe_target_check blocks lbl
          | [v; Label yes; Label no] => inst.inst_opcode = JNZ /\
              encode_probe_target_check blocks yes /\
              encode_probe_target_check blocks no
          | _ => F)
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

