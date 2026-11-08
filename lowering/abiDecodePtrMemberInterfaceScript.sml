(* Iteration contracts: output coverage does not imply initialized capacity. *)
Theory abiDecodePtrMemberInterface
Ancestors
  abiDecodePtrMember abiDecodePtrMemberFrame abiEncoder compileEnv context
  bodyPtrDefs ptrDiscipline contractABI vyperTypeABI emitHelper
  venomExecSemantics venomState venomInst finite_map words arithmetic list
  pred_set exprLoweringProps stateFrame freshWrites

Definition abi_decode_member_code_def:
  abi_decode_member_code dst pos src hi ei off q sa sb <=>
    ?sm sn v out.
      compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD
        (Var src) hi sa = (v,sm) /\
      emit_op ADD [Var dst;Lit (n2w q)] sm = (Var out,sn) /\
      compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sn = ((),sb)
End

Definition abi_decode_member_layout_def:
  abi_decode_member_layout ei off q k z h cap <=>
    q+k <= cap /\ w2n z+off+32 <= h /\
    ((?clamp. ei = DecPrimWord clamp /\ k = 32) \/
     (?n. ei = DecBytestring n /\ k = 32+contractABI$ceil32 n /\
          n+31 < dimword(:256)))
End

Definition abi_decode_member_live_def:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s <=>
    ghost_inv ret cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ fresh_vars_wrt sa s /\
    local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    (!x. pos = Var x ==> not_fresh_at sa x) /\
    (!x. hi = Var x ==> not_fresh_at sa x) /\
    abi_decode_ptr_window G tn s src b h /\
    lookup_var dst s = SOME d /\ ptr_covers G tn dst s cap /\
    eval_operand pos s = SOME z /\ eval_operand hi s = SOME (n2w h) /\
    hi <> Lit 0w /\ op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    w2n b+h < dimword(:256) /\ w2n d+cap < dimword(:256) /\
    (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
    (!name a k. local_region cenv es.scopes s name a k ==>
      a+k <= w2n d \/ w2n d+cap <= a) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n d) cap)
End

Definition abi_decode_member_frame_def:
  abi_decode_member_frame sa G tn s H tf t a k <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(a <= i /\ i < a+k) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem))
End

Theorem abi_decode_member_frame_covers:
  abi_decode_member_frame sa G tn s H tf t a k /\
  not_fresh_at sa x /\ ptr_covers G tn x s n ==>
  ptr_covers H tf x t n
Proof
  simp[abi_decode_member_frame_def, ptr_covers_def] >> metis_tac[]
QED

Theorem abi_decode_member_frame_window:
  abi_decode_member_frame sa G tn s H tf t a k /\
  not_fresh_at sa x /\ abi_decode_ptr_window G tn s x b n /\
  (w2n b+n <= a \/ a+k <= w2n b) ==>
  abi_decode_ptr_window H tf t x b n
Proof
  strip_tac >> irule abi_decode_ptr_window_frame >>
  goal_assum (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  fs[abi_decode_member_frame_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem abi_decode_member_live_resources:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s ==>
  ghost_inv ret cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  abi_decode_ptr_window G tn s src b h /\ ptr_covers G tn dst s cap /\
  lookup_var dst s = SOME d /\ eval_operand pos s = SOME z /\
  eval_operand hi s = SOME (n2w h) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {}
Proof
  simp[abi_decode_member_live_def]
QED

Theorem abi_decode_member_live_compiler:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s ==>
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ fresh_vars_wrt sa s /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)
Proof
  simp[abi_decode_member_live_def]
QED

Theorem abi_decode_member_frame_compose:
  abi_decode_member_frame sa G tn s H tm t a1 k1 /\
  abi_decode_member_frame sb H tm t J tf u a2 k2 /\
  sa.cs_next_var <= sb.cs_next_var /\
  a <= a1 /\ a1+k1 <= a+k /\ a <= a2 /\ a2+k2 <= a+k ==>
  abi_decode_member_frame sa G tn s J tf u a k
Proof
  strip_tac >> fs[abi_decode_member_frame_def] >>
  conj_tac >- suspend "runtime" >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sb x` by (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
    metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `~(a1 <= i /\ i < a1+k1) /\ ~(a2 <= i /\ i < a2+k2)` by decide_tac >>
  metis_tac[]
QED

Resume abi_decode_member_frame_compose[runtime]:
  qpat_x_assum `(u with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = t` mp_tac >>
  qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality]
QED

Finalise abi_decode_member_frame_compose

(* Zero-write phases fit any containing member slice. *)
Theorem abi_decode_member_frame_readonly:
  state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
  t.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  abi_decode_member_frame sa G tn s H tf t a k
Proof
  strip_tac >> simp[abi_decode_member_frame_def] >>
  qpat_x_assum `state_frame t = _` mp_tac >>
  simp[state_frame_def, venom_state_component_equality]
QED

Theorem abi_decode_member_code_bind:
  abi_decode_member_code dst pos src hi ei off q sa sb <=>
  (do v <- compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD (Var src) hi;
      out <- emit_op ADD [Var dst;Lit (n2w q)];
      compile_abi_decode_to_buf out v MLOAD (Var src) hi ei
   od) sa = ((),sb)
Proof
  simp[abi_decode_member_code_def, comp_bind_def] >>
  Cases_on `compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD (Var src) hi sa` >>
  rename1 `compile_getelemptr_abi _ _ _ _ _ _ _ = (v,sm)` >> simp[] >>
  Cases_on `emit_op ADD [Var dst;Lit (n2w q)] sm` >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >> gvs[]
QED

Theorem abi_decode_member_live_separation:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s ==>
  hi <> Lit 0w /\ w2n b+h < dimword(:256) /\ w2n d+cap < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
  (!name a k. local_region cenv es.scopes s name a k ==>
    a+k <= w2n d \/ w2n d+cap <= a) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n d) cap)
Proof
  simp[abi_decode_member_live_def] >> metis_tac[]
QED

Theorem abi_decode_member_frame_bytes:
  abi_decode_member_frame sa G tn s H tf t a k /\
  (b+n <= a \/ a+k <= b) ==>
  mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory
Proof
  strip_tac >> irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt gen_tac >> strip_tac >> fs[abi_decode_member_frame_def] >>
  first_x_assum irule >> decide_tac
QED
