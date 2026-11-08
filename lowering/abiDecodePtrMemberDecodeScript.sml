Theory abiDecodePtrMemberDecode
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrWord abiDecodePtrBytesFramed abiDecodePtrMemberFrame
  abiDecodePtrBytesRuntimeFrame abiDecodePtrBytesMember abiDecoderBytesPhases
  abiDecodePtrWordRuntimeFrame abiDecoderClampedWord abiDecoderExecution abiDecoderContract
  abiEncoder compileEnv context bodyPtrDefs ptrDiscipline contractABI vyperTypeABI
  venomExecSemantics venomState venomInst words arithmetic list finite_map pred_set
  assignTuplePtrCopyEndpoint exprPtrUnwrapPostFrames exprLoweringProps

Theorem abi_decode_member_decode_success:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sa = ((),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa out /\
  lookup_var out s = SOME (d+n2w q) /\ ptr_covers G tn out s k /\
  eval_operand v s = SOME w /\ op_prov G v = NONE /\ op_taint tn v = {} /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  (~dec_info_needs_offset ei ==> w = z+n2w off) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?H tf t m. t = u with vs_inst_idx := LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf t /\
    abi_decode_member_frame sa G tn s H tf t (w2n d+q) k /\
    32 <= m /\ m <= k /\ abi_decode_ptr_window H tf t out (d+n2w q) m
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
  `!name a j. local_region cenv es.scopes s name a j ==>
     a+j <= w2n (d+n2w q) \/ w2n (d+n2w q)+k <= a` by
    (rpt strip_tac >>
     qpat_x_assum `!name a j. local_region cenv es.scopes s name a j ==> _` drule >>
     decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv vv off'.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off') /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,vv) ==>
     regions_disjoint off' (type_memory_size tv) (w2n (d+n2w q)) k` by
    (rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >> strip_tac >>
     first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  fs[abi_decode_member_layout_def] >> gvs[dec_info_needs_offset_def] >>
  FIRST [
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord _) _ = _` >> suspend "word",
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecBytestring _) _ = _` >> suspend "bytes"]
QED

Resume abi_decode_member_decode_success[word]:
  markerLib.RESUME_TAC >> (
  `w2n (z+n2w off)+32 <= h` by
    (irule LESS_EQ_TRANS >> qexists_tac `w2n z+off+32` >>
     rewrite_tac[word_add_def, w2n_n2w] >>
     `((w2n z+off MOD dimword(:256)) MOD dimword(:256)) <=
       w2n z+off MOD dimword(:256)` by simp[MOD_LESS_EQ] >>
     `off MOD dimword(:256) <= off` by simp[MOD_LESS_EQ] >> decide_tac) >>
  `?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
      ghost_inv ret cenv cx es H tf u /\ stmt_state_rel ctx func cenv cx es u /\
      abi_decode_ptr_window H tf u out (d+n2w q) 32 /\
      abi_decode_member_frame sa G tn s H tf u (w2n d+q) 32 /\
      fresh_vars_wrt sb u` by
    (drule (abi_decode_word_success_framed |> Q.INST
       [`p` |-> `w2n (z+n2w off : bytes32)`] |> SRULE []) >>
     disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
     disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     disch_then (qspecl_then [`z`, `off`, `PG`, `D`] mp_tac) >>
     (impl_tac >- (simp[] >> metis_tac[])) >>
     strip_tac >>
     qexistsl_tac [`H`, `tf`] >>
     simp[abi_decode_member_frame_def] >>
     gen_tac >> strip_tac >> conj_tac
     >- (first_x_assum irule >> decide_tac) >>
     first_x_assum irule >> decide_tac) >>
  drule abi_decode_word_memory_shape >> strip_tac >>
  drule abi_decoder_clamped_word_shape >> simp[abi_decode_source_opcode_def] >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (fs[abi_decode_member_frame_def] >>
     qpat_x_assum `(u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`H`, `tf`, `32`] >> simp[] >>
  conj_tac
  >- (irule abi_decode_member_live_transport >>
      simp[ghost_inv_inst_idx, stmt_state_rel_inst_idx, fresh_vars_wrt_def] >>
      conj_tac >- fs[fresh_vars_wrt_def] >>
      goal_assum (drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexistsl_tac [`w2n d+q`, `32`] >>
      fs[abi_decode_member_frame_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `abi_decode_member_frame _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[abi_decode_member_frame_def, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `abi_decode_ptr_window H tf u out _ _` mp_tac >>
  simp[abi_decode_ptr_window_def, lookup_var_def, ptr_covers_def] >>
  strip_tac >> gvs[] >> metis_tac[])
QED

Resume abi_decode_member_decode_success[bytes]:
  markerLib.RESUME_TAC >>
  drule abi_decode_bytes_success_framed >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w2n w`, `32+contractABI$ceil32 n`, `PG`, `D`] mp_tac) >>
  (impl_tac >- (simp[w2n_lt] >> metis_tac[])) >>
  strip_tac >> suspend "bytes_finish"
QED

Resume abi_decode_member_decode_success[bytes_finish]:
  markerLib.RESUME_TAC >> (
  drule_all abi_decode_bytes_runtime_frame >> strip_tac >>
  drule abi_decode_bytes_position_shape >> simp[abi_decode_source_opcode_def] >> strip_tac >>
  `abi_decode_member_frame sa G tn s H tf u (w2n d+q) (32+contractABI$ceil32 n)` by
    (simp[abi_decode_member_frame_def] >>
     qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`H`, `tf`, `32`] >> simp[] >>
  conj_tac
  >- (irule abi_decode_member_live_transport >>
      simp[ghost_inv_inst_idx, stmt_state_rel_inst_idx, fresh_vars_wrt_def] >>
      conj_tac >- fs[fresh_vars_wrt_def] >>
      goal_assum (drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexistsl_tac [`w2n d+q`, `32+contractABI$ceil32 n`] >>
      fs[abi_decode_member_frame_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `abi_decode_member_frame _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[abi_decode_member_frame_def, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `abi_decode_ptr_window H tf u out _ _` mp_tac >>
  simp[abi_decode_ptr_window_def, lookup_var_def, ptr_covers_def] >>
  strip_tac >> fs[lookup_var_def])
QED

Finalise abi_decode_member_decode_success
