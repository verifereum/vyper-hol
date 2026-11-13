Theory extRetSemanticComplexMembersPtr
Ancestors
  extRetComplexMemberStatePtr extRetComplexStaticMemberPtr
  extRetComplexDynamicMemberPtr extRetComplexMembersInvariantPtr
  extRetDynamicBodyPtr extRetRecursiveFramePtr extRetFramedChildPtr
  extRetBulkCopyCountedPtr bodyPtrDefs compileEnv loweringStateRelDefs
  emitHelper fragExec abiEncoder abiEncoderMemberCode fragGasPathPtr
  ptrDiscipline venomState venomMemDefs list rich_list arithmetic finite_map
  loweringShapeRules loweringShapeDefs reasonCopySourcePtr contractABI
  vyperValue

Definition encoder_complex_infos_def:
  encoder_complex_infos eis hs ms dyn =
    GENLIST (\j. (eis j, EL j hs, EL j ms, EL j dyn)) (LENGTH ms)
End

Theorem encoder_complex_infos_length:
  LENGTH (encoder_complex_infos eis hs ms dyn) = LENGTH ms
Proof
  simp[encoder_complex_infos_def]
QED

Theorem encoder_complex_infos_cons[local]:
  DROP j (encoder_complex_infos eis hs ms dyn) = (ei,az,mz,dy)::rest ==>
  j < LENGTH ms /\ ei = eis j /\ az = EL j hs /\ mz = EL j ms /\
  dy = EL j dyn /\
  DROP (j+1) (encoder_complex_infos eis hs ms dyn) = rest
Proof
  strip_tac >> drule DROP_EQ_CONS >> strip_tac >>
  gvs[encoder_complex_infos_def, EL_GENLIST, ADD1]
QED

Theorem encoder_complex_offset_projections:
  LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms ==>
  encoder_member_offset so ms (LENGTH ms) = so+SUM ms /\
  encoder_member_offset ho hs (LENGTH ms) = ho+SUM hs /\
  encoder_member_offset (ho+SUM hs) tails (LENGTH ms) =
    ho+SUM hs+SUM tails
Proof
  metis_tac[encoder_member_offset_done]
QED

Theorem encoder_complex_effect_restrict[local]:
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  encoder_dynamic_effect sb sites b cap G tn s Gf tnf sf ==>
  encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf
Proof
  simp[encoder_dynamic_effect_def] >> metis_tac[]
QED

Theorem encoder_complex_preparation_effect[local]:
  sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
  sp.vs_allocas = s.vs_allocas /\ sp.vs_alloca_next = s.vs_alloca_next /\
  encoder_ambient_frame tn s tnp sp /\
  (!x. not_fresh_at sa x ==>
    lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
    op_taint tnp (Var x) = op_taint tn (Var x)) ==>
  encoder_dynamic_effect sa sites b cap G tn s Gp tnp sp
Proof
  simp[encoder_dynamic_effect_def, mem_agree_outside_def]
QED

(* The fold's suffix is bookkeeping only: physical and semantic resources
   always refer to the full, immutable member ledger. *)
Definition encoder_complex_fold_adapter_def:
  encoder_complex_fold_adapter ctx fn sites protected
    src dst ip a b scap dcap active cid cursor so ho ms hs tails dyn eis tv v
    entry G tn s j remaining x y st Gp tnp sp <=>
  j <= LENGTH ms /\ remaining = DROP j (encoder_complex_infos eis hs ms dyn) /\
  x = encoder_member_offset so ms j /\
  y = encoder_member_offset ho hs j /\
  (!z. not_fresh_at entry z ==> not_fresh_at st z) /\
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j st Gp tnp sp /\
  encoder_dynamic_effect entry sites b dcap G tn s Gp tnp sp
End

Theorem encoder_complex_fold_adapter_cons[local]:
  encoder_complex_fold_adapter ctx fn sites protected
    src dst ip a b scap dcap active cid cursor so ho ms hs tails dyn eis tv v
    entry G tn s j ((ei,az,mz,dy)::rest) x y st Gp tnp sp /\
  LENGTH hs = LENGTH ms ==>
  j < LENGTH ms /\ ei = eis j /\ az = EL j hs /\ mz = EL j ms /\
  dy = EL j dyn /\ DROP (j+1) (encoder_complex_infos eis hs ms dyn) = rest /\
  x = encoder_member_offset so ms j /\ y = encoder_member_offset ho hs j /\
  x+mz = encoder_member_offset so ms (j+1) /\
  y+az = encoder_member_offset ho hs (j+1)
Proof
  simp[encoder_complex_fold_adapter_def] >> strip_tac >>
  qpat_x_assum `_::rest = _` (mp_tac o SYM) >>
  disch_then (strip_assume_tac o MATCH_MP encoder_complex_infos_cons) >>
  gvs[] >> metis_tac[encoder_member_offset_step, ADD_COMM]
QED

Definition encoder_complex_semantic_children_def:
  encoder_complex_semantic_children env tys tv v eis ms hs tails dyn caps children
    cost so ho a scap b protected cid cursor D ctx fn PG <=>
  !j target es sc sd child_out Gp tnp sp.
    j < LENGTH ms /\
    compile_abi_encode_to_buf (Var target) (Var es) (eis j) sc = (child_out,sd) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var target sp = SOME (n2w (b+(if EL j dyn then
      encoder_member_offset (ho+SUM hs) tails j else encoder_member_offset ho hs j))) /\
    ptr_covers Gp tnp target sp (caps j) /\
    lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
    ptr_covers Gp tnp es sp (EL j ms) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory (tv j) (v j) (a+encoder_member_offset so ms j) mem) /\
    encoder_resource ctx fn (children j) a scap
      (if EL j dyn then (cid,cursor,32)::protected else protected) sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env (tys j) (v j)
      D ctx fn PG sc sd (children j) a scap
      (if EL j dyn then (cid,cursor,32)::protected else protected)
      (b+(if EL j dyn then encoder_member_offset (ho+SUM hs) tails j
          else encoder_member_offset ho hs j))
      (caps j) child_out n (cost j) Gp tnp sp Gm tnm sm
End

Theorem encoder_complex_semantic_member[local]:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v j sa G tn s /\
  not_fresh_at sa es /\
  lookup_var es s = SOME (n2w (a+encoder_member_offset so ms j)) /\
  ptr_covers G tn es s (EL j ms) /\
  (!i. i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap /\
    vyper_to_abi env (tys i) (v i) = SOME (avs i) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env (tys i)) (avs i))) /\
  encoder_complex_semantic_children env tys tv v eis ms hs tails dyn caps children
    cost so ho a scap b protected cid cursor D ctx fn PG /\
  compile_abi_encode_child (Var dst) (Var es) (eis j) (EL j dyn)
    (encoder_member_offset ho hs j) (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s (cost j) Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
      active cid cursor so ho ms hs tails tv v (j+1) sb Gf tnf sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf
Proof
  strip_tac >>
  `!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap` by
    metis_tac[] >>
  `vyper_to_abi env (tys j) (v j) = SOME (avs j) /\
   EL j ns = LENGTH (enc (vyper_to_abi_type env (tys j)) (avs j))` by metis_tac[] >>
  qhdtm_x_assum `encoder_complex_semantic_children`
    (assume_tac o PURE_REWRITE_RULE [encoder_complex_semantic_children_def]) >>
  Cases_on `EL j dyn` >> fs[]
  >- (irule encoder_complex_dynamic_member_counted_ptr >>
      simp[] >>
      qexistsl_tac [`avs j`, `caps`, `children`, `dyn`, `eis j`, `env`, `es`, `ns`, `out`, `tys j`] >>
      simp[] >> rpt gen_tac >> strip_tac >>
      `caps j <= dcap-encoder_member_offset (ho+SUM hs) tails j` by
        (`encoder_member_offset (ho+SUM hs) tails j + caps j <= dcap` by
           metis_tac[encoder_complex_layout_def] >> decide_tac) >>
      `ptr_covers Gp tnp child sp (caps j)` by
        (irule ptr_covers_mono >> metis_tac[]) >>
      qpat_x_assum `!j target es sc sd child_out Gp tnp sp. _`
        (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
      simp[]) >>
  irule encoder_complex_static_member_counted_ptr >>
  simp[] >>
  qexistsl_tac [`avs j`, `caps`, `children`, `Var ip`, `dyn`, `eis j`, `env`, `es`, `ns`, `out`, `tys j`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j target es sc sd child_out Gp tnp sp. _`
    (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  simp[]
QED

Theorem encoder_complex_fold_step[local]:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  (!i. i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap /\
    vyper_to_abi env (tys i) (v i) = SOME (avs i) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env (tys i)) (avs i))) /\
  encoder_complex_semantic_children env tys tv v eis ms hs tails dyn caps children
    cost so ho a scap b protected cid cursor D ctx fn PG /\
  ~ctx_has_dalloca ctx /\
  encoder_complex_fold_adapter ctx fn sites protected
    src dst ip a b scap dcap active cid cursor so ho ms hs tails dyn eis tv v
    entry G tn s j ((ei,az,mz,dy)::rest) x y st G0 tn0 s0 /\
  s0.vs_current_bb = st.cs_current_bb /\
  s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
  emit_op ADD [Var src; Lit (n2w x)] st = (elem_src,prepared) /\
  compile_abi_encode_child (Var dst) elem_src ei dy y (Var ip) prepared =
    (child_out,child_end) /\
  fn_has_code st prepared fn /\ fn_has_code prepared child_end fn ==>
  ?Gp tnp sp G1 tn1 s1.
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 Gp tnp (OK sp) /\
    sp.vs_current_bb = prepared.cs_current_bb /\
    sp.vs_inst_idx = LENGTH prepared.cs_current_insts /\ ~sp.vs_halted /\
    gas_path_ptr D 0 ctx fn PG Gp tnp sp (cost j) G1 tn1 (OK s1) /\
    s1.vs_current_bb = child_end.cs_current_bb /\
    s1.vs_inst_idx = LENGTH child_end.cs_current_insts /\ ~s1.vs_halted /\
    encoder_complex_fold_adapter ctx fn sites protected
      src dst ip a b scap dcap active cid cursor so ho ms hs tails dyn eis tv v
      entry G tn s (j+1) rest (x+mz) (y+az) child_end G1 tn1 s1
Proof
  strip_tac >>
  `LENGTH hs = LENGTH ms` by metis_tac[encoder_complex_layout_def] >>
  drule_all encoder_complex_fold_adapter_cons >> strip_tac >> gvs[] >>
  qhdtm_x_assum `encoder_complex_fold_adapter`
    (strip_assume_tac o PURE_REWRITE_RULE [encoder_complex_fold_adapter_def]) >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ st = (Var es,prepared)` >>
  `!z. not_fresh_at st z ==> not_fresh_at prepared z` by
    metis_tac[not_fresh_at_mono, LESS_EQ_ADD] >>
  drule_all encoder_complex_source_prepare_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_at (Pat `compile_abi_encode_child _ _ _ _ _ _ _ = _`)
    encoder_complex_semantic_member >>
  disch_then (drule_at (Pat `encoder_complex_semantic_children _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `encoder_complex_member_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule >>
  disch_then (qspec_then `avs` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `encoder_dynamic_effect st sites b dcap G0 tn0 s0 Gp tnp sp` by
    (irule encoder_complex_preparation_effect >> simp[]) >>
  `encoder_dynamic_effect st sites b dcap Gp tnp sp Gf tnf sf` by
    (irule encoder_complex_effect_restrict >> metis_tac[]) >>
  `encoder_dynamic_effect st sites b dcap G0 tn0 s0 Gf tnf sf` by
    (drule_all encoder_dynamic_effect_then >> simp[]) >>
  `encoder_dynamic_effect entry sites b dcap G0 tn0 s0 Gf tnf sf` by
    (irule encoder_complex_effect_restrict >> metis_tac[]) >>
  `encoder_dynamic_effect entry sites b dcap G tn s Gf tnf sf` by
    metis_tac[encoder_dynamic_effect_then] >>
  `!z. not_fresh_at prepared z ==> not_fresh_at child_end z` by
    (drule abi_encoder_child_bounds >> simp[not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `~sp.vs_halted /\ ~sf.vs_halted` by
    metis_tac[encoder_complex_member_inv_def] >>
  qexistsl_tac [`Gp`, `tnp`, `sp`, `Gf`, `tnf`, `sf`] >>
  simp[encoder_complex_fold_adapter_def] >>
  metis_tac[]
QED

Theorem encoder_semantic_complex_members_counted_ptr:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  compile_abi_encode_complex_elems (Var dst) (Var src)
    (encoder_complex_infos eis hs ms dyn) so ho (Var ip) sa = (out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v 0 sa G tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!i. i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap /\
    vyper_to_abi env (tys i) (v i) = SOME (avs i) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env (tys i)) (avs i))) /\
  encoder_complex_semantic_children env tys tv v eis ms hs tails dyn caps children
    cost so ho a scap b protected cid cursor D ctx fn PG ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s (SUM (GENLIST cost (LENGTH ms)))
      Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
      active cid cursor so ho ms hs tails tv v (LENGTH ms) sb Gf tnf sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf /\
    (!x. b <= x /\ x < b+(ho+SUM hs+SUM tails) ==> x NOTIN tnf.t_mem) /\
    (active ==> mload cursor sf = n2w (ho+SUM hs+SUM tails))
Proof
  strip_tac >>
  `encoder_complex_fold_adapter ctx fn sites protected
    src dst ip a b scap dcap active cid cursor so ho ms hs tails dyn eis tv v
    sa G tn s 0 (encoder_complex_infos eis hs ms dyn) so ho sa G tn s` by
    simp[encoder_complex_fold_adapter_def, encoder_member_offset_zero,
         encoder_dynamic_effect_refl] >>
  mp_tac (encoder_complex_members_invariant_counted_ptr |>
    Q.INST [`dst` |-> `Var dst_name`, `src` |-> `Var src_name`, `dp` |-> `Var ip`] |>
    Q.GEN `member_inv` |>
    Q.ISPEC `encoder_complex_fold_adapter ctx fn sites protected
      src dst ip a b scap dcap active cid cursor so ho ms hs tails
      (dyn:bool list) (eis:num->abi_enc_info) tv v sa G tn s` |>
    Q.INST [`dst_name` |-> `dst`, `src_name` |-> `src`]) >>
  disch_then (drule_at (Pat `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _`)) >>
  disch_then drule >>
  disch_then (qspecl_then [`0`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt gen_tac >> strip_tac >>
     drule_all encoder_complex_fold_step >> simp[])) >>
  strip_tac >>
  qhdtm_x_assum `encoder_complex_fold_adapter`
    (strip_assume_tac o PURE_REWRITE_RULE [encoder_complex_fold_adapter_def]) >>
  gvs[encoder_complex_infos_length] >>
  `LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms` by
    metis_tac[encoder_complex_layout_def] >>
  drule_all encoder_complex_member_completed >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> gvs[ETA_THM]
QED
