Theory bodyAssignLocalSnapshotMods
Ancestors
  bodyFullTargetDefs bodyPtrBytestringBuiltinsWindowGhost
  exprPtrUnwrapFrames exprSimProps nameLoweringProps stmtLoweringMono
  stmtSimDefs freshWrites exprLowering compileEnv context
  loweringPosts bodyPtrDefs loweringStateRelDefs exprLoweringProps
  valueEncodingProofs venomState finite_map words

(* A genuine nonword snapshot is memory-backed. Its final unwrap therefore
   emits no instructions, so the target landing is already the copy cursor. *)
Theorem local_snapshot_unwrap[local]:
  ~is_word_type (vv_type vv) /\
  compile_snapshot_vv ce T vv sm = (snap,ss) /\
  vv_operand snap = Var x /\ unwrap_value ce snap st = (op,su) ==>
  vv_location snap = SOME LocMemory /\ op = Var x /\ su = st
Proof
  strip_tac >> qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  Cases_on `compile_materialize_vv ce (vv_type vv) vv sm` >>
  simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[vv_location_def, vv_operand_def, mk_ptr_def,
                   unwrap_value_def, compile_ptr_load_def, comp_return_def]
QED

Theorem local_snapshot_frame[local]:
  wb_frame ce mid ee ss u z /\ ghost_kept_at lo ce mid ss G tn u Gz tnz /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
  (!n off len. local_region ce mid.scopes u n off len ==>
     regions_disjoint b (type_memory_size tv) off len) /\
  not_fresh_at ss x /\ lookup_var x u = SOME (n2w b) /\
  ptr_covers G tn x u (type_memory_size tv) /\ val_wf tv v /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) ==>
  lookup_var x z = SOME (n2w b) /\ FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\
  ptr_covers Gz tnz x z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem)
Proof
  strip_tac >> fs[wb_frame_def, ghost_kept_at_def] >>
  `lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP G x /\
   op_taint tnz (Var x) = op_taint tn (Var x)` by simp[] >>
  `ptr_covers Gz tnz x z (type_memory_size tv)` by
    drule_all_then (fn th => fs[th]) copy_ptr_covers_transport >>
  simp[] >> rpt strip_tac >>
  irule robust_val_in_memory_window_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`,`tnz.t_mem`,`type_memory_size tv`,`u.vs_memory`,`z.vs_memory`] >>
  simp[val_footprint_le] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP _ _ = SOME _ /\ _ ==> i IN tn.t_mem`
        irule >> simp[] >> qexistsl_tac [`aid`,`b`,`type_memory_size tv`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!n off len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _`
        (drule_then mp_tac) >> simp[regions_disjoint_def]) >>
  qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` irule >>
  reverse conj_tac >- (qexists `aid` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!n off len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _`
    (drule_then mp_tac) >> simp[regions_disjoint_def]
QED

(* At a known snapshot cut and a selected successful target endpoint, the
   delayed RHS is still the original value even if the target modified a
   live local. Only the private snapshot's allocation is framed. *)
Theorem assign_local_snapshot_ready_mods:
  ~is_word_type (vv_type vv) /\
  compile_snapshot_vv ce T vv sm = (snap,ss) /\ vv_operand snap = Var x /\
  compile_get_target_ptr compile_expr ce t ss = (r,st) /\
  unwrap_value ce snap st = (op,su) /\
  assign_target_post imm H ctx func ce cx mid ss st u ee p ty r Gz z /\
  stmt_state_rel H ctx func ce cx mid u /\ local_ptrs_reserved ce ss /\
  MAP FDOM ee.scopes = MAP FDOM mid.scopes /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ghost_kept_at lo ce mid ss G tn u Gz tnz /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
  lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= u.vs_alloca_next /\
  (!n off len. local_region ce mid.scopes u n off len ==>
     regions_disjoint b (type_memory_size tv) off len) /\
  not_fresh_at ss x /\ lookup_var x u = SOME (n2w b) /\
  ptr_covers G tn x u (type_memory_size tv) /\ val_wf tv v /\
  (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) ==>
  vv_location snap = SOME LocMemory /\ op = Var x /\ su = st /\ not_fresh_at su x /\
  lookup_var x z = SOME (n2w b) /\ FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\
  aid < su.cs_next_id /\ lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= z.vs_alloca_next /\
  (!n off len. local_region ce ee.scopes z n off len ==>
     regions_disjoint b (type_memory_size tv) off len) /\
  ptr_covers Gz tnz x z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem)
Proof
  strip_tac >> drule_all_then strip_assume_tac local_snapshot_unwrap >>
  drule_then strip_assume_tac assign_target_post_frame >>
  drule_all_then strip_assume_tac local_snapshot_frame >>
  `ci_mono ss st` by
    (qspecl_then [`t`,`ce`,`ss`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `not_fresh_at st x` by (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `aid < st.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `b + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==> lookup_var x z = SOME w` by
    fs[wb_frame_def] >>
  simp[] >> rpt strip_tac >>
  drule_all_then assume_tac local_region_kept >>
  qpat_assum `!n off len. local_region ce mid.scopes u n off len ==> regions_disjoint _ _ _ _`
    (drule_then ACCEPT_TAC)
QED
