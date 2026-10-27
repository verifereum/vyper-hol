(* Compiler observer construction probes. No recursive execution proof. *)
Theory abiEncoderObserverCode
Ancestors
  abiEncoderObserver abiEncoderLeafCode abiEncoderArrayLoopLayout
  abiEncoderArrayHeader
  abiEncoder abiDecoderContract fragExec emitHelperProps exprLoweringProps
  compileEnv emitHelper
  venomInst venomExecSemantics venomState list rich_list arithmetic

Definition abi_word_observer_def:
  abi_word_observer fn lbl old id src dst tmp =
    fn with fn_blocks :=
      [<|bb_label := lbl; bb_instructions := old ++
        [mk_inst id MLOAD [src] [tmp];
         mk_inst (id+1) MSTORE [dst; Var tmp] [];
         mk_inst (id+2) STOP [] []]|>]
End

Definition abi_word_region_def:
  abi_word_region lbl n = {(lbl,n); (lbl,n+1); (lbl,n+2)}
End

Theorem abi_word_observer_safe:
  observer_region_safe (abi_word_observer fn lbl old id src dst tmp)
    (lbl,LENGTH old+2) (abi_word_region lbl (LENGTH old))
Proof
  rw[observer_region_safe_def, abi_word_observer_def, abi_word_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      EL_APPEND_EQN] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def, exec_write2_def] >>
  rpt strip_tac >>
  gvs[Once step_inst_base_def, mk_inst_def, exec_read1_def, exec_write2_def,
      AllCaseEqs(), mstore_def, update_var_def]
QED

Theorem abi_word_observer_closed:
  observer_region_closed ctx (abi_word_observer fn lbl old id src dst tmp)
    (lbl,LENGTH old+2) (abi_word_region lbl (LENGTH old))
Proof
  rw[observer_region_closed_def, abi_observer_step_def,
     abi_word_observer_def, abi_word_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      EL_APPEND_EQN] >>
  gvs[mk_inst_def, is_terminator_def] >>
  drule venomInstProofsTheory.step_preserves_control_flow >>
  simp[is_terminator_def]
QED

Theorem abi_word_compiler_shape:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  out = Lit 32w /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id MLOAD [src] [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE
       [dst; Var (STRING #"%" (toString st.cs_next_var))] []]
Proof
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[APPEND_ASSOC]
QED

Theorem abi_word_observer_has_code:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  fn_has_code st st'
    (abi_word_observer fn st.cs_current_bb st.cs_current_insts st.cs_next_id
      src dst (STRING #"%" (toString st.cs_next_var)))
Proof
  strip_tac >> drule abi_word_compiler_shape >> strip_tac >>
  simp[fn_has_code_def, emitted_blocks_def, abi_word_observer_def,
       lookup_block_def, listTheory.FIND_thm, IS_PREFIX_APPEND] >>
  qexists_tac `[mk_inst (st.cs_next_id+2) STOP [] []]` >> simp[]
QED

Theorem abi_word_phi_prefix_suffix[local]:
  !old tail tail'.
  phi_prefix_length (old ++ mk_inst id MLOAD [src] [tmp] :: tail) =
    phi_prefix_length (old ++ mk_inst id MLOAD [src] [tmp] :: tail') /\
  TAKE (phi_prefix_length (old ++ mk_inst id MLOAD [src] [tmp] :: tail))
    (old ++ mk_inst id MLOAD [src] [tmp] :: tail) =
  TAKE (phi_prefix_length (old ++ mk_inst id MLOAD [src] [tmp] :: tail'))
    (old ++ mk_inst id MLOAD [src] [tmp] :: tail')
Proof
  Induct >- simp[phi_prefix_length_def, mk_inst_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`tail`, `tail'`] strip_assume_tac) >>
  Cases_on `h.inst_opcode = PHI` >>
  asm_simp_tac std_ss [APPEND, phi_prefix_length_def, TAKE_def] >>
  metis_tac[]
QED

Theorem abi_word_observer_agrees:
  region_code_agrees (abi_word_observer fn lbl old id src dst tmp)
    (fn with fn_blocks := [<|bb_label := lbl; bb_instructions := old ++
      [mk_inst id MLOAD [src] [tmp];
       mk_inst (id+1) MSTORE [dst; Var tmp] []] ++ suffix|>])
    (lbl,LENGTH old+2) (abi_word_region lbl (LENGTH old))
Proof
  rw[region_code_agrees_def, abi_word_observer_def, abi_word_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      EL_APPEND_EQN] >>
  qspecl_then [`old`,
    `[mk_inst (id+1) MSTORE [dst; Var tmp] []; mk_inst (id+2) STOP [] []]`,
    `mk_inst (id+1) MSTORE [dst; Var tmp] [] :: suffix`] mp_tac
    abi_word_phi_prefix_suffix >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[]
QED

(* The actual loop header shape, with both branch targets observed at the body
   cut. The exit trampoline is outside the header's emitted-code obligation. *)
Definition abi_header_observer_def:
  abi_header_observer fn old id ip count_op iv cmp done =
    fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions := old ++
          [mk_inst id JMP [Label "header"] []]|>;
       <|bb_label := "header"; bb_instructions :=
          abi_encode_array_header_insts (id+1) ip count_op iv cmp done "body" "exit"|>;
       <|bb_label := "body"; bb_instructions := [mk_inst (id+5) STOP [] []]|>;
       <|bb_label := "exit"; bb_instructions := [mk_inst (id+6) JMP [Label "body"] []]|>]
End

Definition abi_header_region_def:
  abi_header_region n =
    {("entry",n); ("header",0); ("header",1); ("header",2); ("header",3);
     ("body",0); ("exit",0)}
End

Theorem abi_header_observer_safe:
  observer_region_safe (abi_header_observer fn old id ip count_op iv cmp done)
    ("body",0) (abi_header_region (LENGTH old))
Proof
  rw[observer_region_safe_def, abi_header_observer_def, abi_header_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def, EL_APPEND_EQN,
      abi_encode_array_header_insts_def] >>
  simp[mk_inst_def] >>
  simp[step_inst_base_opcode_eqs] >>
  rpt strip_tac >>
  gvs[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
      exec_pure1_def, exec_pure2_def, AllCaseEqs(), jump_to_def, update_var_def]
QED

Theorem abi_header_observer_closed:
  observer_region_closed ctx (abi_header_observer fn old id ip count_op iv cmp done)
    ("body",0) (abi_header_region (LENGTH old))
Proof
  rw[observer_region_closed_def, abi_observer_step_def,
     abi_header_observer_def, abi_header_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      EL_APPEND_EQN, abi_encode_array_header_insts_def] >>
  gvs[mk_inst_def, is_terminator_def, step_inst_non_invoke,
      step_inst_base_opcode_eqs, jump_to_def, AllCaseEqs(),
      eval_phis_def, phi_prefix_length_def, exec_read1_def,
      exec_pure1_def, exec_pure2_def, update_var_def, mload_def,
      AllCaseEqs()]
QED

Theorem abi_header_observer_agrees:
  region_code_agrees
    (abi_header_observer fn old id ip count_op iv cmp done)
    (fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions := old ++
          [mk_inst id JMP [Label "header"] []]|>;
       <|bb_label := "header"; bb_instructions :=
          abi_encode_array_header_insts (id+1) ip count_op iv cmp done "body" "exit"|>;
       <|bb_label := "body"; bb_instructions := mk_inst k NOP [] [] :: suffix|>;
       <|bb_label := "exit"; bb_instructions := [mk_inst (id+6) JMP [Label "body"] []]|>])
    ("body",0) (abi_header_region (LENGTH old))
Proof
  rw[region_code_agrees_def, abi_header_observer_def, abi_header_region_def] >>
  gvs[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
      EL_APPEND_EQN, abi_encode_array_header_insts_def,
      phi_prefix_length_def, mk_inst_def]
QED

(* Proposed general bridge interface (not asserted as a theorem here):
   compile_abi_encode_to_buf dst src ei st = (op,st') /\
   abi_enc_admissible ei
   ==> ?observed R.
       fn_has_code st st' observed /\
       observer_region_safe observed (st'.cs_current_bb,LENGTH st'.cs_current_insts) R /\
       observer_region_closed ctx observed
         (st'.cs_current_bb,LENGTH st'.cs_current_insts) R /\
       (st.cs_current_bb,LENGTH st.cs_current_insts) IN R.
   Transfer additionally needs region_code_agrees with the actual containing
   function, with a validated PHI-prefix boundary at the cut block. The header
   probe above has no PHIs: eval_phis is empty on its actual emitted targets.
   The separate generic JMP/PHI probes test predecessor/parallel-PHI semantics,
   not the compiler's use of PHIs. Tuple/member recursion, child-generated
   blocks, array back edges, distinct fresh labels, and the final continuation
   boundary are NOT established by these bounded probes. The exit trampoline
   is an explicit test harness, not a claim about the full encoder's exit.
   None of these code facts establishes exact allocated-write confinement. *)
