(* Syntax-directed control certificates for the ABI encoder. *)
Theory stmtSimCustomErrorEncoderControl
Ancestors
  stmtSimCustomErrorControl abiEncoder emitHelper emitHelperProps compileEnv context venomInst abiStaticLoopCode list rich_list pred_set

Definition ce_encoder_action_def:
  ce_encoder_action (action : 'a compiler) <=>
    !a out b. action a = (out,b) ==> ?C. ce_chunks a b C /\ ce_open C
End

Theorem ce_encoder_action_return:
  ce_encoder_action (comp_return v)
Proof
  rw[ce_encoder_action_def, comp_return_def] >>
  qexists_tac `[(a.cs_current_bb,[])]` >> simp[ce_chunks_singleton]
QED

Theorem ce_encoder_action_bind:
  ce_encoder_action action /\ (!v. ce_encoder_action (next v)) ==>
  ce_encoder_action (comp_bind action next)
Proof
  rw[ce_encoder_action_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `ce_splice C' C` >>
  conj_tac >- (irule ce_chunks_splice >> goal_assum (drule_at Any) >> simp[]) >>
  simp[ce_open_splice]
QED

Theorem ce_encoder_action_ignore_bind:
  ce_encoder_action action /\ ce_encoder_action next ==>
  ce_encoder_action (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  ho_match_mp_tac ce_encoder_action_bind >> simp[]
QED

Theorem ce_encoder_action_emit:
  ~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE ==>
  ce_encoder_action (emit_inst opc ops outs)
Proof
  rw[ce_encoder_action_def, emit_inst_def, comp_bind_def, fresh_id_def,
    comp_return_def, emit_def] >>
  qexists_tac `[(a.cs_current_bb,
    [<|inst_id := a.cs_next_id; inst_opcode := opc;
       inst_operands := ops; inst_outputs := outs|>])]` >>
  simp[ce_chunks_singleton, ce_normal_def, mk_inst_def]
QED

Theorem ce_encoder_action_op:
  ~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE ==>
  ce_encoder_action (emit_op opc ops)
Proof
  rw[ce_encoder_action_def, emit_op_def, comp_bind_def, fresh_id_def,
    fresh_var_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists_tac `[(a.cs_current_bb,
    [mk_inst a.cs_next_id opc ops ["%" ++ toString a.cs_next_var]])]` >>
  simp[ce_chunks_singleton, ce_normal_def]
QED

Theorem ce_encoder_action_void:
  ~is_terminator opc /\ opc <> GAS /\ opc <> INVOKE ==>
  ce_encoder_action (emit_void opc ops)
Proof
  simp[emit_void_def, GSYM emit_inst_def, ce_encoder_action_emit]
QED

Theorem ce_encoder_action_alloc:
  ce_encoder_action (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  ho_match_mp_tac ce_encoder_action_bind >> conj_tac
  >- (irule ce_encoder_action_op >> simp[is_terminator_def]) >>
  simp[ce_encoder_action_return]
QED

Theorem ce_encoder_action_static:
  ce_encoder_action (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >>
  ho_match_mp_tac ce_encoder_action_bind >> conj_tac
  >- (irule ce_encoder_action_op >> simp[is_terminator_def]) >>
  gen_tac >> irule ce_encoder_action_ignore_bind >> conj_tac
  >- (irule ce_encoder_action_void >> simp[is_terminator_def]) >>
  simp[ce_encoder_action_return]
QED

Theorem ce_encoder_action_static_info:
  ce_encoder_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    ce_encoder_action_static, ce_encoder_action_return] >>
  irule ce_encoder_action_ignore_bind >> conj_tac
  >- (irule ce_encoder_action_void >> simp[is_terminator_def]) >>
  simp[ce_encoder_action_return]
QED

Theorem ce_encoder_action_static_loop:
  ce_encoder_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rw[ce_encoder_action_def, compile_abi_encode_dyn_static_loop_result] >>
  qexists_tac `[(a.cs_current_bb,
    abi_static_loop_entry a.cs_next_id a.cs_next_var a.cs_next_label);
    (fresh_label_output "enc_dyn_hdr" a.cs_next_label,
      abi_static_loop_header a.cs_next_id a.cs_next_var a.cs_next_label len);
    (fresh_label_output "enc_dyn_body" (a.cs_next_label+1),
      abi_static_loop_body a.cs_next_id a.cs_next_var a.cs_next_label dst src ei asz msz);
    (fresh_label_output "enc_dyn_exit" (a.cs_next_label+2),
      abi_static_loop_exit a.cs_next_id a.cs_next_var src ei asz)]` >>
  conj_tac >- simp[ce_chunks_def, ce_prepend_def, ce_block_def] >>
  Cases_on `ei` >>
  simp[ce_open_def, ce_open_to_def, ce_end_def, ce_normal_def,
    abi_static_loop_entry_def, abi_static_loop_header_def,
    abi_static_loop_body_def, abi_static_loop_body_prefix_def,
    abi_static_loop_exit_def, static_info_insts_def, mk_inst_def,
    is_terminator_def]
QED

Theorem ce_open_to_internal[local]:
  ce_open_to k C /\ k SUBSET set (MAP FST (TL C)) ==> ce_open C
Proof
  strip_tac >>
  `k UNION set (MAP FST (TL C)) = set (MAP FST (TL C))` by ASM_SET_TAC[] >>
  gvs[ce_open_to_def, ce_open_def]
QED

Theorem ce_encoder_loop_compose[local]:
  ce_chunks a m A /\ ce_chunks m n C /\ ce_chunks n b B /\
  ce_open_to k A /\ ce_open C /\ ce_open_to k B /\
  k SUBSET (set (MAP FST (TL A)) UNION set (MAP FST (TL B))) ==>
  ?D. ce_chunks a b D /\ ce_open D
Proof
  strip_tac >>
  `A <> [] /\ B <> [] /\ C <> []` by
    fs[ce_open_to_def, ce_open_def] >>
  `ce_open_to k C` by
    (irule ce_open_to_mono >> qexists_tac `{}` >> simp[GSYM ce_open_def]) >>
  `ce_open_to k (ce_splice A (ce_splice C B))` by
    simp[ce_open_to_splice] >>
  `ce_chunks a b (ce_splice A (ce_splice C B))` by
    (irule ce_chunks_splice >> qexists_tac `m` >> simp[] >>
     irule ce_chunks_splice >> qexists_tac `n` >> simp[]) >>
  qexists_tac `ce_splice A (ce_splice C B)` >> simp[] >>
  irule ce_open_to_internal >> qexists_tac `k` >> simp[] >>
  `ce_splice C B <> []` by metis_tac[ce_open_to_def, ce_open_to_splice] >>
  simp[ce_splice_labels] >> ASM_SET_TAC[]
QED

Theorem ce_end_last[local]:
  xs <> [] /\ ce_normal (FRONT xs) /\
  ((?l. (LAST xs).inst_opcode = JMP /\
        (LAST xs).inst_operands = [Label l] /\ l IN k) \/
   (?c y n. (LAST xs).inst_opcode = JNZ /\
        (LAST xs).inst_operands = [c;Label y;Label n] /\ y IN k /\ n IN k)) ==>
  ce_end k xs
Proof
  strip_tac >> rewrite_tac[ce_end_def] >>
  qexistsl_tac [`FRONT xs`,`LAST xs`] >> simp[APPEND_FRONT_LAST]
QED

Theorem ce_encoder_action_dyn_loop_step:
  (!dst src. ce_encoder_action (compile_abi_encode_to_buf dst src ei)) ==>
  ce_encoder_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  strip_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[ce_encoder_action_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!dst src. _` (mp_tac o SRULE[ce_encoder_action_def]) >>
  disch_then drule >> strip_tac >>
  rename1 `ce_open cc` >>
  qmatch_asmsub_abbrev_tac `ce_chunks mid en cc` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `ce_chunks a fin` >>
  qabbrev_tac `aa = [(a.cs_current_bb,
    DROP (LENGTH a.cs_current_insts) (HD (TL mid.cs_blocks)).bb_instructions);
    ((HD mid.cs_blocks).bb_label,(HD mid.cs_blocks).bb_instructions);
    (mid.cs_current_bb,mid.cs_current_insts)]` >>
  qabbrev_tac `bb = [(en.cs_current_bb,
    DROP (LENGTH en.cs_current_insts) (HD fin.cs_blocks).bb_instructions);
    (fin.cs_current_bb,fin.cs_current_insts)]` >>
  `ce_chunks a mid aa` by
    simp[Abbr `aa`, Abbr `mid`, ce_chunks_def, ce_prepend_def,
      ce_block_def, DROP_LENGTH_APPEND, GSYM APPEND_ASSOC] >>
  `ce_chunks en fin bb` by
    simp[Abbr `bb`, Abbr `fin`, ce_chunks_def, ce_prepend_def,
      ce_block_def, DROP_LENGTH_APPEND, GSYM APPEND_ASSOC] >>
  qabbrev_tac `kk = {fresh_label_output "enc_dyn_hdr" a.cs_next_label;
    fresh_label_output "enc_dyn_body" (a.cs_next_label+1);
    fresh_label_output "enc_dyn_exit" (a.cs_next_label+2)}` >>
  `ce_open_to kk aa` by
    (qunabbrev_tac `aa` >>
     qpat_assum `Abbrev (mid = _)`
       (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     simp_tac std_ss [compile_state_accfupds, basic_block_accfupds,
       HD, TL, APPEND, DROP_LENGTH_APPEND, GSYM APPEND_ASSOC] >>
     simp[Abbr `kk`, ce_open_to_def] >>
     rpt conj_tac >>~-
       ([`ce_end _ _`], irule ce_end_last >>
         simp[ce_normal_def, mk_inst_def, is_terminator_def]) >>
     simp[ce_normal_def, mk_inst_def, is_terminator_def]) >>
  `ce_open_to kk bb` by
    (qunabbrev_tac `bb` >>
     qpat_assum `Abbrev (fin = _)`
       (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     simp_tac std_ss [compile_state_accfupds, basic_block_accfupds,
       HD, TL, APPEND, DROP_LENGTH_APPEND, GSYM APPEND_ASSOC] >>
     simp[Abbr `kk`, ce_open_to_def] >>
     rpt conj_tac >>~-
       ([`ce_end _ _`], irule ce_end_last >>
         simp[ce_normal_def, mk_inst_def, is_terminator_def]) >>
     simp[ce_normal_def, mk_inst_def, is_terminator_def]) >>
  irule ce_encoder_loop_compose >>
  qexistsl_tac [`aa`,`bb`,`cc`,`kk`,`mid`,`en`] >> simp[] >>
  simp[Abbr `kk`, Abbr `aa`, Abbr `bb`, Abbr `mid`, Abbr `fin`, SUBSET_DEF]
QED

fun ce_encoder_compose_tac g =
  (FIRST [
    asm_simp_tac (srw_ss()) [ce_encoder_action_return,
      ce_encoder_action_alloc, ce_encoder_action_static_info,
      ce_encoder_action_static, ce_encoder_action_static_loop] >> NO_TAC,
    first_x_assum (fn th => irule (SRULE[] th) >> simp[] >> NO_TAC),
    irule ce_encoder_action_op >> simp[is_terminator_def] >> NO_TAC,
    irule ce_encoder_action_void >> simp[is_terminator_def] >> NO_TAC,
    ho_match_mp_tac ce_encoder_action_bind >> conj_tac
      >- ce_encoder_compose_tac >> gen_tac >> ce_encoder_compose_tac,
    ho_match_mp_tac ce_encoder_action_ignore_bind >> conj_tac >> ce_encoder_compose_tac,
    IF_CASES_TAC >> fs[] >> ce_encoder_compose_tac]) g;

Theorem ce_encoder_action_mutual:
  (!dst src ei dyn off ptr.
    ce_encoder_action (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. ce_encoder_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    ce_encoder_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    ce_encoder_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`ce_encoder_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule ce_encoder_action_dyn_loop_step >> simp[]) >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> fs[] >> ce_encoder_compose_tac)
  >- ce_encoder_compose_tac
  >- ce_encoder_compose_tac
  >- ce_encoder_compose_tac
  >- (Cases_on `elem_is_dyn` >> fs[] >> ce_encoder_compose_tac)
  >- ce_encoder_compose_tac
  >- (IF_CASES_TAC >> fs[] >> ce_encoder_compose_tac)
  >- ce_encoder_compose_tac >>
  ce_encoder_compose_tac
QED

Theorem custom_error_encoder_control:
  compile_abi_encode_to_buf dst src ei a = (out,b) ==>
  ?C. ce_chunks a b C /\ ce_open C
Proof
  metis_tac[cj 2 ce_encoder_action_mutual, ce_encoder_action_def]
QED
