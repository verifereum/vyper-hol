(* Confinement of the concrete control runs in the actual array layout.
   Each extension starts at the supplied occurrence of its PC. *)
Theory entryCreateEncoderArraySteps
Ancestors
  abiEncoderArrayLoopCode abiEncoderArrayHeader abiDecoderExecution entryCreateEncoderArrayLinear
  entryCreateAdminSequence entryCreatePathScope createSizePrefixReplay
  entryCreateCompletedCut entryCreateFocusSpec
  createMarkedPath createExprSizeExitDefs abiEncoderProps
  fragExec fragGasOrigin gasEvents exprLoweringProps entrySinkExtraction
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list pred_set relation arithmetic

Theorem array_control_edge[local]:
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  ~s.vs_halted /\ i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  is_terminator i.inst_opcode /\ step_inst_base i s = OK (jump_to lbl s) ==>
  create_expr_prefix a b E C fn s [] (jump_to lbl s)
Proof
  strip_tac >>
  `s.vs_current_bb <> b.cs_current_bb \/
   s.vs_inst_idx <> LENGTH b.cs_current_insts` by
    (CCONTR_TAC >> gvs[] >> metis_tac[]) >>
  `gas_origin_edge F E C fn s [] (OK (jump_to lbl s))` by
    (simp[gas_origin_edge_def, step_inst_non_invoke, gas_events_step_def] >>
     metis_tac[]) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def, create_prefix_step_def] >> metis_tac[]
QED

(* Reuse the straight-line administrative run theorem at the two exact
   local PCs. These records describe slices of the same installed block;
   the function and context are never changed. *)
Theorem array_linear_piece[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ code ++ rest /\ s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  ~s.vs_halted /\ run_inst_seq code s = OK u ==>
  create_expr_prefix a b E C fn s [] (u with vs_inst_idx := LENGTH (pre ++ code))
Proof
  strip_tac >>
  qabbrev_tac `p = a with <|cs_current_bb := s.vs_current_bb;
    cs_current_insts := pre|>` >>
  qabbrev_tac `q = b with <|cs_blocks := a.cs_blocks;
    cs_current_bb := s.vs_current_bb; cs_current_insts := pre ++ code|>` >>
  `fn_has_code p q fn` by
    (simp[fn_has_code_def, emitted_blocks_def, Abbr `p`, Abbr `q`] >>
     qexists_tac `bb` >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]) >>
  `emitted_insts p q = code` by
    simp[emitted_insts_def, Abbr `p`, Abbr `q`, DROP_LENGTH_APPEND] >>
  `create_operand_full_scope p q E C fn s []
    (OK (u with vs_inst_idx := LENGTH (pre ++ code)))` by
    (`LENGTH (pre ++ code) = LENGTH q.cs_current_insts` by simp[Abbr `q`] >>
     pop_assum SUBST1_TAC >> irule create_admin_sequence_scope >>
     simp[Abbr `p`, Abbr `q`, frag_ids_def, create_operand_at_def] >>
     fs[frag_ids_def]) >>
  irule create_expr_prefix_lift >>
  qexistsl_tac [`p`, `q`] >>
  fs[create_operand_full_scope_def, frag_ids_def, Abbr `p`, Abbr `q`]
QED

(* The enclosing row must identify its installed exit fetch (if any).
   Bare fn_has_code does not constrain instructions after its final PC. *)
Definition encoder_array_band_def:
  encoder_array_band a b fn owner bend <=>
    a.cs_next_id <= owner.cs_next_id /\ bend.cs_next_id + 3 <= b.cs_next_id /\
    (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
      i.inst_id NOTIN frag_ids a b)
End

Theorem encoder_array_layout_setup_scoped:
  abi_encoder_array_loop_code fn owner body_st bend exit_st ip count_op labels /\
  encoder_array_band a b fn owner bend /\
  create_operand_at owner s /\ ~s.vs_halted /\
  create_expr_prefix a b E C fn start [] s ==>
  create_expr_prefix a b E C fn start [] (jump_to (FST labels) s)
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def, encoder_array_band_def,
    create_operand_at_def] >> strip_tac >>
  `create_expr_prefix a b E C fn s [] (jump_to (FST labels) s)` by
    (irule array_control_edge >> simp[] >>
     qexists_tac `mk_inst owner.cs_next_id JMP [Label (FST labels)] []` >>
     simp[mk_inst_def, frag_ids_def, is_terminator_def, step_jmp_behavior,
       get_instruction_def, EL_APPEND_EQN] >> decide_tac) >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

Theorem encoder_array_header_segment:
  abi_encoder_array_loop_code fn owner body_st bend exit_st ip count_op labels /\
  encoder_array_band a b fn owner bend /\
  s.vs_current_bb = FST labels /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  iv = STRING #"%" (toString owner.cs_next_var) /\
  cmp = STRING #"%" (toString (owner.cs_next_var+1)) /\
  done = STRING #"%" (toString (owner.cs_next_var+2)) /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w k /\
  k <= n /\ n < dimword (:256) ==>
  create_expr_prefix a b E C fn s []
    (jump_to (if k<n then FST (SND labels) else SND (SND labels))
      (abi_encode_array_header_state iv cmp done k n s))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 3 (abi_encode_array_header_insts (owner.cs_next_id+1)
      ip count_op iv cmp done (FST (SND labels)) (SND (SND labels)))) s =
    OK (abi_encode_array_header_state iv cmp done k n s)` by
    metis_tac[abi_encode_array_header_prefix] >>
  qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_array_loop_code_def] >> strip_tac >>
  fs[encoder_array_band_def] >>
  qabbrev_tac `hd = owner.cs_next_id` >>
  qabbrev_tac `br = mk_inst (hd+4) JNZ
    [Var done; Label (SND (SND labels)); Label (FST (SND labels))] []` >>
  qabbrev_tac `is = [mk_inst (hd+1) MLOAD [ip] [iv];
    mk_inst (hd+2) LT [Var iv; count_op] [cmp];
    mk_inst (hd+3) ISZERO [Var cmp] [done]]` >>
  qabbrev_tac `hblock = <|bb_label := FST labels; bb_instructions := is ++ [br]|>` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hblock /\
   run_inst_seq is s = OK (abi_encode_array_header_state iv cmp done k n s)` by
    (fs[Abbr `hblock`, Abbr `is`, Abbr `br`, abi_encode_array_header_insts_def] >>
     simp[ADD_ASSOC]) >>
  qabbrev_tac `raw = abi_encode_array_header_state iv cmp done k n s` >>
  qabbrev_tac `q = raw with vs_inst_idx := 3` >>
  `create_expr_prefix a b E C fn s [] q` by
    (`q = raw with vs_inst_idx := LENGTH ([] ++ is)` by simp[Abbr `q`, Abbr `is`] >>
     pop_assum SUBST1_TAC >> irule array_linear_piece >>
     simp[] >> conj_tac >- (qexists_tac `[br]` >> simp[Abbr `hblock`]) >>
     simp[Abbr `is`, mk_inst_def, is_terminator_def, frag_ids_def] >> decide_tac) >>
  qabbrev_tac `lbl = if k<n then FST (SND labels) else SND (SND labels)` >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
   eval_operand (Var done) q = SOME (bool_to_word (~(k<n)))` by
    simp[Abbr `q`, Abbr `raw`, abi_encode_array_header_state_def,
      update_var_def, eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `create_expr_prefix a b E C fn q [] (jump_to lbl q)` by
    (`get_instruction hblock q.vs_inst_idx = SOME br` by
       simp[Abbr `q`, Abbr `hblock`, Abbr `is`, get_instruction_def, EL_APPEND_EQN] >>
     `br.inst_id IN frag_ids a b /\ br.inst_opcode <> GAS /\
      br.inst_opcode <> INVOKE /\ is_terminator br.inst_opcode` by
       (simp[Abbr `br`, mk_inst_def, frag_ids_def, is_terminator_def] >> decide_tac) >>
     `step_inst_base br q = OK (jump_to lbl q)` by
       (`(1w:bytes32) <> 0w` by simp[] >> drule step_jnz_behavior >>
        Cases_on `k<n` >>
        asm_simp_tac bool_ss [Abbr `br`, mk_inst_def, Abbr `lbl`, bool_to_word_def]
        >> metis_tac[]) >>
     irule array_control_edge >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`hblock`, `br`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  `jump_to lbl q = jump_to lbl raw` by
    simp[Abbr `q`, Abbr `raw`, jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  `create_expr_prefix a b E C fn s [] (jump_to lbl raw)` by
    metis_tac[create_expr_prefix_append, APPEND_NIL] >>
  gvs[Abbr `lbl`, Abbr `raw`]
QED
(* This is the two-instruction run feeding the JMP in
   window_array_backedge_joint, not an arbitrary zero-mark pointer path. *)
Theorem encoder_array_backedge_segment:
  abi_encoder_array_loop_code fn owner body_st bend exit_st ip count_op labels /\
  encoder_array_band a b fn owner bend /\
  create_operand_at bend s /\ ~s.vs_halted /\
  iv = STRING #"%" (toString body_st.cs_next_var) /\
  nv = STRING #"%" (toString bend.cs_next_var) /\
  run_inst_seq (TAKE 2 (abi_decode_backedge_insts bend.cs_next_id iv nv ip
    (FST labels))) s = OK raw ==>
  create_expr_prefix a b E C fn s [] (jump_to (FST labels) raw)
Proof
  simp_tac bool_ss [abi_encoder_array_loop_code_def, encoder_array_band_def,
    create_operand_at_def] >> strip_tac >>
  qabbrev_tac `is = [mk_inst bend.cs_next_id ADD [Var iv;Lit 1w] [nv];
    mk_inst (bend.cs_next_id+1) MSTORE [ip;Var nv] []]` >>
  qabbrev_tac `j = mk_inst (bend.cs_next_id+2) JMP [Label (FST labels)] []` >>
  qabbrev_tac `backblock = <|bb_label := bend.cs_current_bb;
      bb_instructions := bend.cs_current_insts ++ is ++ [j]|>` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME backblock /\
   run_inst_seq is s = OK raw` by
    (fs[Abbr `backblock`, Abbr `is`, Abbr `j`, abi_decode_backedge_insts_def] >>
     simp[ADD_ASSOC]) >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) is` by
    (simp[Abbr `is`, mk_inst_def, frag_ids_def, is_terminator_def] >> decide_tac) >>
  qabbrev_tac `q = raw with vs_inst_idx := LENGTH (bend.cs_current_insts ++ is)` >>
  `create_expr_prefix a b E C fn s [] q` by
    (simp_tac bool_ss [Abbr `q`] >> irule array_linear_piece >> simp[] >>
     qexists_tac `[j]` >> simp[Abbr `backblock`]) >>
  `q.vs_current_bb = s.vs_current_bb /\ ~q.vs_halted` by
    (imp_res_tac run_inst_seq_preserves_entry_control >> simp[Abbr `q`] >>
     fs[Abbr `is`, mk_inst_def, is_terminator_def]) >>
  `get_instruction backblock q.vs_inst_idx = SOME j` by
    (simp_tac (srw_ss()) [Abbr `q`, Abbr `backblock`] >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  `create_expr_prefix a b E C fn q [] (jump_to (FST labels) q)` by
    (irule array_control_edge >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`backblock`, `j`] >>
     `lookup_block q.vs_current_bb fn.fn_blocks = SOME backblock` by metis_tac[] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (simp[Abbr `j`, mk_inst_def, frag_ids_def, is_terminator_def, step_jmp_behavior] >>
        decide_tac))) >>
  `jump_to (FST labels) q = jump_to (FST labels) raw` by
    simp_tac (srw_ss()) [NoAsms, Abbr `q`, jump_to_def] >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

(* Root initialization, address preparation before the recursive call, and
   publication after it use this same straight-line seam.  The run equation
   is supplied by the concrete phase producer, at its chosen endpoint. *)
Theorem encoder_array_linear_scoped_from_run:
  fn_has_code x y fn /\ y.cs_current_bb = x.cs_current_bb /\
  y.cs_current_insts = x.cs_current_insts ++ code /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  create_operand_at x s /\ ~s.vs_halted /\
  run_inst_seq code s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = LENGTH y.cs_current_insts ==>
  create_expr_prefix a b E C fn s [] t
Proof
  strip_tac >> fs[fn_has_code_def, create_operand_at_def, IS_PREFIX_APPEND] >>
  `t = (t with vs_inst_idx := s.vs_inst_idx) with
      vs_inst_idx := LENGTH (x.cs_current_insts ++ code)` by
    (`LENGTH (x.cs_current_insts ++ code) = t.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> simp[NoAsms, venom_state_fupdselfid]) >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  irule array_linear_piece >>
  first_assum (irule_at Any) >>
  fs[APPEND_ASSOC] >> metis_tac[]
QED

(* One test of the loop. The successful taken-body hypothesis uses the
   three successive actual witnesses: preparation, recursive child, and
   publication of that child's result. At the final test (including n=0)
   none of those hypotheses nor a backedge is needed. *)

Theorem encoder_array_exhausted_test_scoped:
  abi_encoder_array_loop_code fn owner body_st bend exit_st ip count_op labels /\
  encoder_array_band a b fn owner bend /\
  s.vs_current_bb = FST labels /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  iv = STRING #"%" (toString owner.cs_next_var) /\
  cmp = STRING #"%" (toString (owner.cs_next_var+1)) /\
  done = STRING #"%" (toString (owner.cs_next_var+2)) /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w n /\
  n < dimword (:256) /\
  branch = jump_to (SND (SND labels))
    (abi_encode_array_header_state iv cmp done n n s) ==>
  create_expr_prefix a b E C fn s [] branch /\
  create_operand_at exit_st branch /\ ~branch.vs_halted
Proof
  strip_tac >>
  conj_tac
  >- (`n <= n` by simp[] >> drule_all encoder_array_header_segment >> simp[]) >>
  fs[abi_encoder_array_loop_code_def, create_operand_at_def,
    jump_to_def, abi_encode_array_header_state_def, update_var_def]
QED

Theorem encoder_array_control_scoped_from_steps:
  abi_encoder_array_loop_code fn owner body_st bend exit_st ip count_op labels /\
  encoder_array_band a b fn owner bend /\
  s.vs_current_bb = FST labels /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  iv = STRING #"%" (toString owner.cs_next_var) /\
  cmp = STRING #"%" (toString (owner.cs_next_var+1)) /\
  done = STRING #"%" (toString (owner.cs_next_var+2)) /\
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w k /\
  k <= n /\ n < dimword (:256) /\
  create_expr_prefix a b E C fn start [] s /\
  branch = jump_to (if k<n then FST (SND labels) else SND (SND labels))
    (abi_encode_array_header_state iv cmp done k n s) /\
  (k<n ==>
    create_expr_prefix a b E C fn branch [] child_in /\
    create_expr_prefix a b E C fn child_in [] child_out /\
    create_expr_prefix a b E C fn child_out [] before_back /\
    create_operand_at bend before_back /\ ~before_back.vs_halted /\
    run_inst_seq (TAKE 2 (abi_decode_backedge_insts bend.cs_next_id
      (STRING #"%" (toString body_st.cs_next_var))
      (STRING #"%" (toString bend.cs_next_var)) ip (FST labels))) before_back = OK raw) ==>
  create_expr_prefix a b E C fn start []
    (if k<n then jump_to (FST labels) raw else branch)
Proof
  strip_tac >> drule_all encoder_array_header_segment >> strip_tac >>
  `create_expr_prefix a b E C fn start [] branch` by
    metis_tac[create_expr_prefix_append, APPEND_NIL] >>
  reverse (Cases_on `k<n`)
  >- (fs[] >> metis_tac[]) >>
  fs[] >>
  `create_expr_prefix a b E C fn before_back [] (jump_to (FST labels) raw)` by
    (irule encoder_array_backedge_segment >> simp[] >>
     qpat_assum `run_inst_seq (TAKE 2 _) before_back = OK raw` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED
