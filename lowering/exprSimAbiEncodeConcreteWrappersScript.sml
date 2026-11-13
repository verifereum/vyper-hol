Theory exprSimAbiEncodeConcreteWrappers
Ancestors
  exprSimAbiEncodeConcreteCompose abiEncoderWindowMembers
  abiEncoderWindowContract abiEncoderWindowSequence abiEncoderWindowPhase
  venomState words abiEncoderWindowChild fragExec emitHelperProps
  freshWrites exprLoweringProps abiEncoderWindowLookup list

Theorem abi_encode_member_source_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?raw. window_pure_seq st ready s raw /\
    window_phase ctx func st ready {} [] s
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    window_members_inv ctx func infos at ats avs k src dst dp site slot
      sb cap d ready en (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    eval_operand child_src (raw with vs_inst_idx := LENGTH ready.cs_current_insts) =
      SOME (n2w (sb+so)) /\
    (!x. child_src = Var x ==> not_fresh_at ready x)
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st ready s raw` >>
  `window_phase ctx func st ready {} [] s
    (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_pure_seq_phase >> simp[]) >>
  qexists_tac `raw` >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[window_members_inv_pure_phase]) >>
  fs[eval_operand_def, lookup_var_def, word_add_n2w]
QED

(* A constructive child contract: unlike a continuation simulation it retains
   both the raw endpoint and the syntactic facts needed for concatenation. *)
Definition abi_encode_concrete_result_def:
  abi_encode_concrete_result ctx func st en out at av d s r <=>
    inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_strong_result ctx func st en out at av d s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
End

Definition abi_encode_concrete_contract_def:
  abi_encode_concrete_contract ei <=>
    !dst src st out en ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,en) /\
      abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
      st.cs_blocks = en.cs_blocks ==>
      ?r. abi_encode_concrete_result ctx func st en out at av d s r
End

Theorem abi_encode_static_child_concrete:
  abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+ho))) src
    ei at av sb cap (d+ho) s /\
  st.cs_blocks = en.cs_blocks /\ eval_operand dst s = SOME (n2w d) ==>
  ?head ready raw r.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,ready) /\
    compile_abi_encode_to_buf head src ei ready = (out,en) /\
    window_pure_seq st ready s raw /\
    abi_encoder_window_pre ctx func ready en head src ei at av
      sb cap (d+ho) (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_strong_result ctx func ready en out at av (d+ho)
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts)
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all window_static_child_context >> strip_tac >>
  `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st ready s raw` >>
  `window_phase ctx func st ready {} [] s
    (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_pure_seq_phase >> fs[abi_encoder_window_pre_def]) >>
  `raw.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  `abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho)
    (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_static_child_pre >>
     simp[eval_operand_def, lookup_var_def, word_add_n2w] >>
     qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >> simp[]) >>
  `ready.cs_blocks = en.cs_blocks` by fs[window_pure_seq_def, window_seq_def] >>
  qpat_x_assum `abi_encode_concrete_contract ei` mp_tac >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >> strip_tac >>
  fs[abi_encode_concrete_result_def] >>
  `emitted_insts st en = emitted_insts st ready ++ emitted_insts ready en` by
    (irule emitted_insts_append >> simp[] >>
     qpat_assum `window_pure_seq st ready s raw` mp_tac >>
     simp_tac bool_ss [window_pure_seq_def, window_seq_def, inst_extends_def] >>
     strip_tac >> fs[inst_extends_def]) >>
  `?rr. run_inst_seq (emitted_insts st en) s = OK rr /\
    (rr with vs_inst_idx := LENGTH en.cs_current_insts) =
    (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >> simp[] >>
     qexistsl_tac [`LENGTH ready.cs_current_insts`, `raw`] >>
     fs[window_pure_seq_def, window_seq_def]) >>
  qexistsl_tac [`raw`, `rr`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[window_pure_seq_def, window_seq_def, inst_extends_trans] >>
  conj_tac >- fs[window_pure_seq_def, window_seq_def, EVERY_MEM] >>
  rpt strip_tac >>
  `~not_fresh_at ready x` by metis_tac[not_fresh_at_mono] >>
  `lookup_var x (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = lookup_var x s` by
    (irule window_seq_high_vars >> qexistsl_tac [`ready`, `st`] >>
     simp[] >> conj_tac
     >- (irule abi_window_emit_register_bounds >>
         qexistsl_tac [`[dst;Lit (n2w ho)]`, `ADD`, `head`] >> simp[]) >>
     metis_tac[window_pure_seq_def]) >>
  metis_tac[]
QED
