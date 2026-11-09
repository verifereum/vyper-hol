Theory abiDecodePtrSelectedAbort
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrSelectedMember abiDecodePtrWord
  abiDecodePtrBytesAbort abiDecodePtrSelectionAbort abiDecodePtrContinuation
  abiEncoder compileEnv context bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst words arithmetic list finite_map pred_set

(* Decoder-only failure uses precisely the replay ghosts; there is no
   successful-state invariant at an abort endpoint. *)
Theorem abi_decode_member_decode_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sa = ((),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa out /\
  lookup_var out s = SOME (d+n2w q) /\ ptr_covers G tn out s k /\
  eval_operand v s = SOME w /\ op_prov G v = NONE /\ op_taint tn v = {} /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  (~dec_info_needs_offset ei ==> w = z+n2w off) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf
Proof
  strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_separation >> strip_tac >>
  `q+k <= cap` by fs[abi_decode_member_layout_def] >>
  `w2n (d+n2w q) = w2n d+q` by
    (`w2n d+q < dimword(:256) /\ q < dimword(:256)` by decide_tac >>
     simp[word_add_def, w2n_n2w]) >>
  `w2n (d+n2w q)+k < dimword(:256) /\
   (w2n b+h <= w2n (d+n2w q) \/ w2n (d+n2w q)+k <= w2n b)` by decide_tac >>
  fs[abi_decode_member_layout_def] >> gvs[dec_info_needs_offset_def] >>
  FIRST [
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord _) _ = _` >> suspend "word",
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecBytestring _) _ = _` >> suspend "bytes"]
QED

Resume abi_decode_member_decode_abort[word]:
  markerLib.RESUME_TAC >> (
  `w2n (z+n2w off)+32 <= h` by
    (irule LESS_EQ_TRANS >> qexists_tac `w2n z+off+32` >>
     rewrite_tac[word_add_def, w2n_n2w] >>
     `((w2n z+off MOD dimword(:256)) MOD dimword(:256)) <=
       w2n z+off MOD dimword(:256)` by simp[MOD_LESS_EQ] >>
     `off MOD dimword(:256) <= off` by simp[MOD_LESS_EQ] >> decide_tac) >>
  drule (abi_decode_word_abort_ptr |> Q.INST
    [`p` |-> `w2n (z+n2w off : bytes32)`] |> SRULE []) >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`z`, `off`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> goal_assum (drule_at Any))
QED

Resume abi_decode_member_decode_abort[bytes]:
  markerLib.RESUME_TAC >>
  drule abi_decode_bytes_member_abort_ptr >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`w2n w`, `32+contractABI$ceil32 n`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[w2n_lt]) >> strip_tac >> goal_assum (drule_at Any)
QED

Finalise abi_decode_member_decode_abort
