Theory exprSimAbiEncodeConcreteCompose
Ancestors
  exprSimAbiEncodeConcreteLeaves fragExec abiEncoderWindowSequence
  venomState venomExecSemantics venomInst list instIdxIndep exprLoweringProps
  abiEncoderWindowChild abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderWindowLeaves abiEncoderChildCode abiEncoderAppend abiEncoderProps
  emitHelper emitHelperProps compileEnv words freshWrites abiEncoderWindowLookup
  abiEncoderWindowMembers abiEncoderInput abiEncoderAdmissible

Theorem abi_encode_run_append_normalized:
  run_inst_seq xs s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq ys (t with vs_inst_idx := k) = OK u ==>
  ?r. run_inst_seq (xs ++ ys) s = OK r /\
      (r with vs_inst_idx := n) = (u with vs_inst_idx := n)
Proof
  strip_tac >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`t`, `k`] mp_tac) >>
  Cases_on `run_inst_seq ys t` >>
  gvs[exec_result_map_def] >> strip_tac >>
  qpat_assum `run_inst_seq xs s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `ys` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem abi_encode_static_word_child_concrete:
  compile_abi_encode_child dst src AbiPrimWord F ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+ho))) src
    AbiPrimWord at av sb cap (d+ho) s /\
  eval_operand dst s = SOME (n2w d) ==>
  ?head ready raw r.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,ready) /\
    compile_abi_encode_to_buf head src AbiPrimWord ready = (out,en) /\
    window_pure_seq st ready s raw /\
    abi_encoder_window_pre ctx func ready en head src AbiPrimWord at av
      sb cap (d+ho) (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
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
  `abi_encoder_window_pre ctx func ready en head src AbiPrimWord at av sb cap (d+ho)
    (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_static_child_pre >>
     simp[eval_operand_def, lookup_var_def, word_add_n2w] >>
     qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >> simp[]) >>
  drule_all abi_encode_word_concrete >> strip_tac >>
  `inst_extends ready en /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ready en)` by
    (`eval_operand src (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = SOME (n2w sb) /\
      eval_operand head (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = SOME (n2w (d+ho)) /\
      sb < dimword (:256) /\ d+ho < dimword (:256)` by
       (qpat_assum `abi_encoder_window_pre _ _ ready en _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
        asm_rewrite_tac[] >> drule alloca_room_next_lt >> decide_tac) >>
     drule_all window_word_run >> strip_tac >> fs[EVERY_MEM]) >>
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
  qexistsl_tac [`head`, `ready`, `raw`, `rr`] >> asm_rewrite_tac[] >>
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

(* First static member, after the actual source-address preparation. *)
Theorem abi_encode_singleton_word_member_concrete:
  window_members_inv ctx func [(AbiPrimWord,az,ms,F)] at ats avs 0
    src dst dp site slot sb cap d st en s /\
  compile_abi_encode_child dst child_src AbiPrimWord F 0 dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w sb) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?r. run_inst_seq (emitted_insts st en) s = OK r /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `0 < LENGTH [(AbiPrimWord,az,ms,F)]` by simp[] >>
  `abi_encoder_admissible AbiPrimWord` by simp[abi_encoder_admissible_def] >>
  `EL 0 [(AbiPrimWord,az,ms,F)] = (AbiPrimWord,az,ms,F)` by simp[] >>
  `~is_dynamic (EL 0 ats)` by
    (drule_all window_members_inv_source >> simp[] >> metis_tac[]) >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `0 + LENGTH (enc (EL 0 ats) (EL 0 avs)) <= LENGTH (enc at (ListV avs))` by
    (gvs[] >> decide_tac) >>
  `?cc. cc <= ms /\ abi_encoder_window_pre ctx func st en (Lit (n2w (d+0))) child_src
    AbiPrimWord (EL 0 ats) (EL 0 avs) sb cc (d+0) s` by
    (drule window_members_inv_child_pre >>
     simp[abi_encoder_member_span_def] >>
     disch_then (qspecl_then [`0`, `child_src`] mp_tac) >> simp[] >>
     (impl_tac >- fs[]) >> simp[]) >>
  `eval_operand dst s = SOME (n2w d)` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  drule_all abi_encode_static_word_child_concrete >> strip_tac >>
  metis_tac[]
QED
