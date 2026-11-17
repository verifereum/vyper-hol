(* Compiler syntax: weak closure of slots-fragment jump targets. *)
Theory bodyFullStoreSlotsStaticControl
Ancestors
  fragFuelLoopAbiDecDyn exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  context compileEnv emitHelper exprLoweringProps fragExec list pred_set
  venomInst

val slots_J = ``\T i.
  (i.inst_opcode = JMP ==> ?l. i.inst_operands = [Label l] /\ l IN T) /\
  (i.inst_opcode = JNZ ==> ?v l r.
    i.inst_operands = [v; Label l; Label r] /\ l IN T /\ r IN T)``;
val slots_B = ``\a b. {l | (?bb. MEM bb (emitted_blocks a b) /\ l = bb.bb_label) \/
  l = b.cs_current_bb}``;
val slots_closed = ``\T m. !a r b. m a = (r,b) ==>
  entry_shape a b /\ EVERY ((^slots_J) (T UNION (^slots_B) a b)) (frag_code a b)``;
val slots_skel = ``\hdr body exit (p:compile_state -> unit # compile_state)
    (h:compile_state -> unit # compile_state) (q:compile_state -> unit # compile_state).
  do p; new_block hdr; h; new_block body; q; new_block exit; return () od``;

fun slots_sequence_with extra = rpt (FIRST (extra @ [
  CHANGED_TAC BETA_TAC,
  first_assum (MATCH_ACCEPT_TAC o BETA_RULE),
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return),
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_branchless_closed) >>
    simp[code_action_fresh_var] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op) >> simp[] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_inst) >> simp[mk_inst_def] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_void) >> simp[mk_inst_def] >> NO_TAC),
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind),
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_ignore_bind),
  conj_tac, gen_tac]));
val slots_sequence = slots_sequence_with [];

Theorem store_slots_word_loop_skeleton[local]:
  !src dst cnt tr.
  comp_ignore_bind (compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F) (comp_return ()) =
  do lh <- fresh_label "wcopy_cond";
     lb <- fresh_label "wcopy_body";
     le <- fresh_label "wcopy_exit";
     ctr <- fresh_var;
     (^slots_skel) lh lb le
       (do emit_inst ASSIGN [Lit 0w] [ctr]; emit_inst JMP [Label lh] [] od)
       (do done_op <- emit_op EQ [Var ctr; cnt];
           emit_inst JNZ [done_op; Label le; Label lb] [] od)
       (do off <- emit_op MUL [Var ctr; Lit 32w];
           src_off <- emit_op ADD [src; off];
           loaded <- emit_op MLOAD [src_off];
           dst_off <- emit_op ADD [dst; Var ctr];
           emit_void (if tr then TSTORE else SSTORE) [dst_off; loaded];
           nc <- emit_op ADD [Var ctr; Lit 1w];
           emit_inst ASSIGN [nc] [ctr]; emit_inst JMP [Label lh] [] od) od
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp_tac std_ss [compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
    word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
    comp_ignore_bind_def, comp_bind_assoc, fragFuelTheory.comp_bind_return, LET_THM]
QED

Theorem store_slots_primitive_control:
  (!T src dst cnt tr. (^(inst [alpha |-> ``:unit``] slots_closed)) T
    (comp_ignore_bind (compile_word_copy_loop_op src dst cnt LocMemory
      (if tr then LocTransient else LocStorage) F) (comp_return ()))) /\
  (!T src. (^(inst [alpha |-> ``:operand``] slots_closed)) T (compile_bytestring_word_count src)) /\
  (!T src off. (^(inst [alpha |-> ``:operand``] slots_closed)) T (compile_lit_byte_offset src off))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> pure_rewrite_tac[store_slots_word_loop_skeleton] >>
      BETA_TAC >>
      ntac 3 (ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
        conj_tac >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label) >> gen_tac) >>
      ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
      conj_tac >- (MATCH_MP_TAC (BETA_RULE abi_dyn_branchless_closed) >>
        simp[code_action_fresh_var]) >> gen_tac >>
      MATCH_MP_TAC (BETA_RULE abi_dyn_skeleton_closed) >>
      Cases_on `tr` >> slots_sequence)
  >- (rpt gen_tac >> pure_rewrite_tac[compile_bytestring_word_count_def] >>
      slots_sequence) >>
  rpt gen_tac >> pure_rewrite_tac[compile_lit_byte_offset_def] >>
  IF_CASES_TAC >- slots_sequence >> Cases_on `src` >>
  simp_tac std_ss [venomStateTheory.operand_case_def] >> slots_sequence
QED

Theorem store_slots_elements_skeleton[local]:
  !cenv src dst elem cnt tr.
  compile_copy_elements_to_slots cenv src dst elem cnt tr =
  do lh <- fresh_label "dyn_cond";
     lb <- fresh_label "dyn_body";
     le <- fresh_label "dyn_exit";
     ctr <- fresh_var;
     (^slots_skel) lh lb le
       (do emit_inst ASSIGN [Lit 0w] [ctr]; emit_inst JMP [Label lh] [] od)
       (do lt <- emit_op LT [Var ctr; cnt];
           done_op <- emit_op ISZERO [lt];
           emit_inst JNZ [done_op; Label le; Label lb] [] od)
       (do off <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem))];
           se <- emit_op ADD [src; off];
           soff <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem DIV 32))];
           de <- emit_op ADD [dst; soff];
           compile_store_slots cenv se de elem tr;
           nc <- emit_op ADD [Var ctr; Lit 1w];
           emit_inst ASSIGN [nc] [ctr]; emit_inst JMP [Label lh] [] od) od
Proof
  simp_tac std_ss [Once compile_store_slots_def, LET_THM,
    comp_ignore_bind_def, comp_bind_assoc, fragFuelTheory.comp_bind_return]
QED

Theorem store_slots_weak_control_family:
  (!T cenv src dst ty tr. (^(inst [alpha |-> ``:unit``] slots_closed)) T
    (compile_store_slots cenv src dst ty tr)) /\
  (!T cenv src dst members mo so tr. (^(inst [alpha |-> ``:unit``] slots_closed)) T
    (compile_store_slots_members cenv src dst members mo so tr)) /\
  (!T cenv src dst elem cnt tr. (^(inst [alpha |-> ``:unit``] slots_closed)) T
    (compile_copy_elements_to_slots cenv src dst elem cnt tr))
Proof
  CONV_TAC (LAND_CONV (RESORT_FORALL_CONV (fn vs => tl vs @ [hd vs])) THENC
    RAND_CONV (LAND_CONV (RESORT_FORALL_CONV (fn vs => tl vs @ [hd vs])) THENC
      RAND_CONV (RESORT_FORALL_CONV (fn vs => tl vs @ [hd vs])))) >>
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (simp_tac std_ss [Once compile_store_slots_def] >> slots_sequence)
  >- suspend "members"
  >> suspend "elements"
QED

val slots_family_sequence = slots_sequence_with [
  (first_assum (MATCH_MP_TAC o BETA_RULE) >> simp[] >> NO_TAC),
  MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [COND_CLAUSES] (BETA_RULE (Q.INST [`tr` |-> `T`]
    (SPEC_ALL (cj 1 store_slots_primitive_control))))),
  MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [COND_CLAUSES] (BETA_RULE (Q.INST [`tr` |-> `F`]
    (SPEC_ALL (cj 1 store_slots_primitive_control))))),
  MATCH_ACCEPT_TAC (BETA_RULE (cj 1 store_slots_primitive_control)),
  MATCH_ACCEPT_TAC (BETA_RULE (cj 2 store_slots_primitive_control)),
  MATCH_ACCEPT_TAC (BETA_RULE (cj 3 store_slots_primitive_control))];

Resume store_slots_weak_control_family[dispatch]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  pure_rewrite_tac [Once compile_store_slots_def] >>
  simp_tac std_ss [LET_THM] >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty`
  >- (ASM_SIMP_TAC std_ss [] >> Cases_on `type_memory_bytes cenv ty DIV 32 = 1` >>
      ASM_SIMP_TAC std_ss []
      >- (Cases_on `tr` >> simp_tac std_ss [] >> slots_family_sequence) >>
      Cases_on `tr` >>
      simp_tac std_ss [compile_memory_to_storage_def, compile_memory_to_transient_def,
        compile_word_copy_loop_def] >> slots_family_sequence) >>
  ASM_SIMP_TAC std_ss [] >> Cases_on `is_bytestring_type ty`
  >- (ASM_SIMP_TAC std_ss [] >> Cases_on `tr` >> simp_tac std_ss [] >>
      slots_family_sequence) >>
  ASM_SIMP_TAC std_ss [] >> Cases_on `~acyclic_struct_metadata cenv.ce_struct_fields` >>
  ASM_SIMP_TAC std_ss []
  >- slots_family_sequence >>
  Cases_on `ty` >> FULL_SIMP_TAC std_ss [vyperASTTheory.type_case_def,
    vyperASTTheory.type_11, vyperASTTheory.type_distinct]
  >~ [`is_abi_dynamic _ (ArrayT el bd)`]
  >- (Cases_on `bd` >> FULL_SIMP_TAC std_ss [vyperASTTheory.bound_case_def,
        vyperASTTheory.bound_11, vyperASTTheory.bound_distinct] >>
      Cases_on `tr` >> FULL_SIMP_TAC std_ss [] >> slots_family_sequence) >>
  slots_family_sequence
QED
Resume store_slots_weak_control_family[members]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  pure_rewrite_tac [Once compile_store_slots_def] >>
  slots_family_sequence
QED
Resume store_slots_weak_control_family[elements]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  pure_rewrite_tac [store_slots_elements_skeleton] >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
    conj_tac >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label) >> gen_tac) >>
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
  conj_tac >- (MATCH_MP_TAC (BETA_RULE abi_dyn_branchless_closed) >>
    simp[code_action_fresh_var]) >> gen_tac >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_skeleton_closed) >>
  FULL_SIMP_TAC std_ss [] >> slots_family_sequence
QED
Finalise store_slots_weak_control_family
