(*
 * Internal Return Copy Forwarding — the simulation
 *
 * The source runs MCOPY d <- s and later reads d; the target skips the
 * copy and reads s.  On reachable states (ptr_discipline) nothing else
 * touches either buffer after the copy, so source d equals target s
 * there, byte for byte and taint for taint, while the block runs, and
 * across any call it makes.  d itself is never read again, so the
 * forwarded destination buffers of every frame are dead.
 *
 * ircf_R relates block-boundary states: taint agreement outside the
 * dead buffers (with the taint before the block's PHIs: the boundary's
 * ghost taint is the one after them), and the cross fact for the
 * forwards suspended callers have done so far in their blocks.
 *
 * TOP-LEVEL:
 *   ircf_R, ircf_R_ret  — the relations handed to reachable_fn_sim_ctx_sim
 *   ircf_block_sim      — one block from a reachable boundary
 *   ircf_ctx_sim        — the pass as a context simulation
 *)

Theory internalReturnCopyFwdSim
Ancestors
  internalReturnCopyFwdPlan internalReturnCopyFwdDefs internalReturnCopyFwdAlias reachableFnSim
  taintAgree o1LowerDloadShared o1PassContract ptrDiscipline passSharedDefs
  venomExecSemantics venomInst venomWf venomState finite_map pred_set list
  rangeAnalysisProofs stepWriteFootprintBase o1LowerDloadOccurrence occurrenceGeometry
  venomExecProps

(* The transformed block, before NOPs are cleared *)
Definition ircf_tbb_def:
  ircf_tbb fn_meta rma C fn bb =
    SND (ircf_transform_block
           (icf_build_ctx fn_meta C.ctx_functions rma fn) bb)
End

(* inst ids of the ALLOCAs whose buffers are forwarded destinations *)
Definition ircf_dst_ids_def:
  ircf_dst_ids fn_meta rma C =
    {id | ?fn bb k d s sz ai.
            MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
            k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
            ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,sz) /\
            MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
            ai.inst_outputs = [d] /\ id = ai.inst_id}
End

Definition site_bytes_def:
  site_bytes ids (allocas : (num, num # num) fmap) =
    {i | ?id b sz. id IN ids /\ FLOOKUP allocas id = SOME (b,sz) /\
                   b <= i /\ i < b + sz}
End

(* The dead bytes: forwarded destination buffers of this frame and of
   every suspended caller *)
Definition ircf_dead_def:
  ircf_dead ids s stk =
    site_bytes ids s.vs_allocas UNION
    BIGUNION (set (MAP (\f. site_bytes ids f.cf_state.vs_allocas) stk))
End

(* (destination base, source base, size) of each forward of bb before
   index n whose buffers are allocated *)
Definition ircf_gam_def:
  ircf_gam fn_meta rma C fn bb allocas n =
    {x | ?k d s szw dai sai db sb sz1 sz2.
           k < n /\ k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
           ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,s,szw) /\
           MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\
           dai.inst_outputs = [d] /\
           MEM sai (fn_insts fn) /\ sai.inst_opcode = ALLOCA /\
           sai.inst_outputs = [s] /\
           FLOOKUP allocas dai.inst_id = SOME (db,sz1) /\
           FLOOKUP allocas sai.inst_id = SOME (sb,sz2) /\
           x = (db, sb, w2n szw)}
End

(* The forwards done so far in fn's current block at state s *)
Definition ircf_gam_cur_def:
  ircf_gam_cur fn_meta rma C fn s =
    {x | ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
              x IN ircf_gam fn_meta rma C fn bb s.vs_allocas s.vs_inst_idx}
End

(* The forwards each suspended caller did before its INVOKE *)
Definition ircf_gam_stk_def:
  ircf_gam_stk fn_meta rma C stk =
    BIGUNION (set (MAP (\f. ircf_gam_cur fn_meta rma C f.cf_fn f.cf_state)
                       stk))
End

(* Source destination bytes equal target source bytes, taint included *)
Definition ircf_cross_def:
  ircf_cross tn gam s t <=>
    !db sb sz k.
      (db,sb,sz) IN gam /\ k < sz ==>
      (db + k IN tn.t_mem <=> sb + k IN tn.t_mem) /\
      (db + k NOTIN tn.t_mem ==>
       read_byte (db + k) s.vs_memory = read_byte (sb + k) t.vs_memory)
End

Definition ircf_R_def:
  ircf_R D fn_meta rma C stk (PG : (num # num) option list)
         (G : (string, num # num) fmap) tn fn s t <=>
    (?tn0. tn = (if s.vs_prev_bb = NONE then tn0
                 else entry_taint_vars fn s tn0) /\
           taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
             tn0 s t) /\
    ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s t
End

Definition ircf_R_ret_def:
  ircf_R_ret D fn_meta rma C stk (PG : (num # num) option list)
             (G : (string, num # num) fmap) tn fn (v : internal_return) s t <=>
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
    ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s t
End

(* The return certificate couples semantic agreement and reachability at
   the same ghosts; the public return relation remains unchanged. *)
Definition ircf_R_ret_reachable_def:
  ircf_R_ret_reachable vs D fn_meta rma C stk PG G tn fn v s t <=>
    ircf_R_ret D fn_meta rma C stk PG G tn fn v s t /\
    ?ri sr j. frame_reachable vs C stk PG G tn fn ri sr /\
              active_inst fn ri sr /\ step_inst j C ri sr = IntRet v s
End

Theorem ircf_R_ret_reachable_forget:
  ircf_R_ret_reachable vs D fn_meta rma C stk PG G tn fn v s t ==>
  ircf_R_ret D fn_meta rma C stk PG G tn fn v s t
Proof
  simp[ircf_R_ret_reachable_def]
QED

Theorem ircf_R_ret_reachable_resume:
  ircf_R_ret_reachable vs D fn_meta rma C (f::stk) PG G tn fn ret se te /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ircf_R_ret D fn_meta rma C (f::stk) PG G tn fn ret se te /\
  frame_reachable vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> gvs[ircf_R_ret_reachable_def] >>
  irule frame_reachable_ret >> metis_tac[]
QED

(* ===== The transformed context, structurally ===== *)

Theorem FOLDL_block_pass_SND:
  !f bbs c0 acc0.
    SND (FOLDL (\(changed, acc) bb.
      let (bb_changed, new_bb) = f bb in
      (changed \/ bb_changed, acc ++ [new_bb])) (c0, acc0) bbs) =
    acc0 ++ MAP (\bb. SND (f bb)) bbs
Proof
  gen_tac >> Induct_on `bbs` >> fs[] >> rpt gen_tac >>
  Cases_on `f h` >> fs[]
QED

Theorem ircf_transform_block_label[simp]:
  !ctx bb. (SND (ircf_transform_block ctx bb)).bb_label = bb.bb_label
Proof
  rw[ircf_transform_block_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL g (F,bb) l` >>
  `!l acc. (SND (FOLDL g acc l)).bb_label = (SND acc).bb_label`
    suffices_by simp[] >>
  Induct >> simp[] >> rpt gen_tac >>
  `(SND (g acc h)).bb_label = (SND acc).bb_label` suffices_by simp[] >>
  PairCases_on `acc` >> simp[Abbr `g`] >> rw[] >> rpt (CASE_TAC >> simp[])
QED

(* The transformed function: the transformed blocks, NOPs cleared if any
   copy was forwarded *)
Theorem ircf_transform_function_blocks:
  !fn_meta fns rma fn.
    (ircf_transform_function fn_meta fns rma fn).fn_name = fn.fn_name /\
    ?ch. (ircf_transform_function fn_meta fns rma fn).fn_blocks =
         (if ch then MAP clear_nops_block else I)
           (MAP (\bb. SND (ircf_transform_block
                             (icf_build_ctx fn_meta fns rma fn) bb))
                fn.fn_blocks)
Proof
  rpt gen_tac >> simp[ircf_transform_function_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL g (F,[]) fn.fn_blocks` >>
  Cases_on `FOLDL g (F,[]) fn.fn_blocks` >> simp[] >>
  `r = MAP (\bb. SND (ircf_transform_block
                        (icf_build_ctx fn_meta fns rma fn) bb)) fn.fn_blocks`
    by (qspecl_then [`ircf_transform_block (icf_build_ctx fn_meta fns rma fn)`,
                     `fn.fn_blocks`, `F`, `[]`] mp_tac FOLDL_block_pass_SND >>
        simp[Abbr `g`]) >>
  Cases_on `q` >> simp[clear_nops_function_def]
  >- (qexists_tac `T` >> simp[])
  >> qexists_tac `F` >> simp[]
QED

Theorem ircf_transform_function_entry_label:
  !fn_meta fns rma fn.
    fn_entry_label (ircf_transform_function fn_meta fns rma fn) =
    fn_entry_label fn
Proof
  rpt gen_tac >>
  qspecl_then [`fn_meta`, `fns`, `rma`, `fn`] strip_assume_tac
    ircf_transform_function_blocks >>
  gvs[fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> rw[] >> gvs[clear_nops_block_def]
QED

Theorem ircf_transform_ctx_lookup:
  !fn_meta rma C fn.
    ctx_wf C /\ MEM fn C.ctx_functions ==>
    lookup_function fn.fn_name (ircf_transform_ctx fn_meta rma C).ctx_functions =
    SOME (ircf_transform_function fn_meta C.ctx_functions rma fn)
Proof
  rw[ircf_transform_ctx_def] >>
  qmatch_goalsub_abbrev_tac `MAP g _` >>
  qspecl_then [`fn.fn_name`, `C.ctx_functions`, `g`] mp_tac
    lookup_function_map >>
  impl_tac >- simp[Abbr `g`, ircf_transform_function_blocks] >>
  disch_then SUBST1_TAC >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` suffices_by
    simp[Abbr `g`] >>
  gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  qpat_x_assum `MEM _ _` mp_tac >> qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`C.ctx_functions`, `fns`) >>
  Induct >> rw[lookup_function_def, FIND_thm] >> gvs[MEM_MAP] >>
  gvs[lookup_function_def] >> metis_tac[]
QED

Theorem ircf_gam_allocations:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  ircf_no_dst_write_alias fn /\ MEM bb fn.fn_blocks /\
  ircf_size_coherent fn s /\
  (db,sb,sz) IN ircf_gam fn_meta rma C fn bb s.vs_allocas n ==>
  ?k d sr amount dai sai.
    k < n /\ ircf_fwd_ok fn bb k d sr amount /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,amount) /\
    MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\ dai.inst_outputs = [d] /\
    MEM sai (fn_insts fn) /\ sai.inst_opcode = ALLOCA /\ sai.inst_outputs = [sr] /\
    FLOOKUP s.vs_allocas dai.inst_id = SOME (db,sz) /\
    FLOOKUP s.vs_allocas sai.inst_id = SOME (sb,sz)
Proof
  strip_tac >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    simp[ircf_tbb_def, ircf_transform_block_plan] >>
  gvs[ircf_gam_def] >>
  rename1 `ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,szw)` >>
  `ircf_fwd_ok fn bb k d sr szw` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  `sz1 = w2n szw /\ sz2 = w2n szw` by
    (conj_tac >> irule ircf_alloca_of_coherent_size >>
     gvs[wf_ssa_def] >> metis_tac[ircf_fwd_ok_def]) >>
  metis_tac[]
QED

Theorem ircf_gam_cur_write_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  ircf_size_coherent fn s /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (db,sb,sz) IN ircf_gam_cur fn_meta rma C fn s /\ q < sz /\
  MEM (off,len) (source_memory_write_ranges inst s) ==>
  ~(off <= db+q /\ db+q < off+len) /\
  ~(off <= sb+q /\ sb+q < off+len)
Proof
  strip_tac >>
  qpat_x_assum `_ IN ircf_gam_cur _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ircf_gam_cur_def]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  drule_all ircf_gam_allocations >> strip_tac >>
  `db <= db+q /\ db+q < db+sz /\ sb <= sb+q /\ sb+q < sb+sz` by decide_tac >>
  conj_tac >> irule ircf_current_forward_write_disjoint >> metis_tac[]
QED

Theorem ircf_gam_saved_write_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  j < LENGTH stk /\ wf_function (EL j stk).cf_fn /\
  fn_inst_wf (EL j stk).cf_fn /\ wf_ssa (EL j stk).cf_fn /\
  fn_inst_ids_distinct (EL j stk).cf_fn /\ ircf_no_dst_write_alias (EL j stk).cf_fn /\
  ircf_size_coherent (EL j stk).cf_fn (EL j stk).cf_state /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (db,sb,sz) IN ircf_gam_cur fn_meta rma C (EL j stk).cf_fn (EL j stk).cf_state /\
  q < sz /\ MEM (off,len) (source_memory_write_ranges inst s) ==>
  ~(off <= db+q /\ db+q < off+len) /\
  ~(off <= sb+q /\ sb+q < off+len)
Proof
  strip_tac >>
  qpat_x_assum `_ IN ircf_gam_cur _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ircf_gam_cur_def]) >>
  `MEM bb (EL j stk).cf_fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  drule_all ircf_gam_allocations >> strip_tac >>
  `db <= db+q /\ db+q < db+sz /\ sb <= sb+q /\ sb+q < sb+sz` by decide_tac >>
  conj_tac >> irule ircf_saved_forward_write_disjoint >> metis_tac[]
QED

Theorem ircf_gam_write_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (db,sb,sz) IN ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk /\
  q < sz /\ MEM (off,len) (source_memory_write_ranges inst s) ==>
  ~(off <= db+q /\ db+q < off+len) /\
  ~(off <= sb+q /\ sb+q < off+len)
Proof
  strip_tac >>
  `ircf_alias_frames C stk fn inst s G` by
    (drule o1LowerDloadOccurrenceTheory.occ_frame_reachable_projection >> strip_tac >>
     drule_all ircf_alias_frames_reachable >> simp[]) >>
  `MEM fn C.ctx_functions /\ ircf_size_coherent fn s /\
   EVERY (ircf_alias_saved C) stk` by
    fs[ircf_alias_frames_def, ircf_alias_boundary_def] >>
  qpat_x_assum `_ IN _ UNION _` (strip_assume_tac o REWRITE_RULE [IN_UNION])
  >- (irule ircf_gam_cur_write_disjoint >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?j. j < LENGTH stk /\
       (db,sb,sz) IN ircf_gam_cur fn_meta rma C (EL j stk).cf_fn (EL j stk).cf_state` by
    (fs[ircf_gam_stk_def, IN_BIGUNION, MEM_MAP, MEM_EL] >> metis_tac[]) >>
  `ircf_alias_saved C (EL j stk)` by metis_tac[EVERY_EL] >>
  `MEM (EL j stk).cf_fn C.ctx_functions /\
   ircf_size_coherent (EL j stk).cf_fn (EL j stk).cf_state` by
    fs[ircf_alias_saved_def, ircf_alias_boundary_def] >>
  irule ircf_gam_saved_write_disjoint >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ircf_gam_frontier:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ircf_no_dst_write_alias C.ctx_functions /\
  (db,sb,sz) IN ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk /\
  q < sz ==> db+q < s.vs_alloca_next /\ sb+q < s.vs_alloca_next
Proof
  strip_tac >>
  `ircf_alias_frames C stk fn inst s G` by
    (drule o1LowerDloadOccurrenceTheory.occ_frame_reachable_projection >> strip_tac >>
     drule_all ircf_alias_frames_reachable >> simp[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry] >>
  qpat_x_assum `_ IN _ UNION _` (strip_assume_tac o REWRITE_RULE [IN_UNION])
  >- (qpat_x_assum `_ IN ircf_gam_cur _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [ircf_gam_cur_def]) >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `MEM fn C.ctx_functions /\ ircf_size_coherent fn s` by
        fs[ircf_alias_frames_def, ircf_alias_boundary_def] >>
      `wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ircf_no_dst_write_alias fn` by
        metis_tac[EVERY_MEM] >>
      drule_all ircf_gam_allocations >> strip_tac >>
      fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
      `db+sz <= s.vs_alloca_next /\ sb+sz <= s.vs_alloca_next` by
        metis_tac[occurrence_geometry_site_bounds] >> decide_tac) >>
  `?j. j < LENGTH stk /\
       (db,sb,sz) IN ircf_gam_cur fn_meta rma C (EL j stk).cf_fn (EL j stk).cf_state` by
    (fs[ircf_gam_stk_def, IN_BIGUNION, MEM_MAP, MEM_EL] >> metis_tac[]) >>
  `ircf_alias_saved C (EL j stk)` by
    (fs[ircf_alias_frames_def] >> metis_tac[EVERY_EL]) >>
  `MEM (EL j stk).cf_fn C.ctx_functions /\
   ircf_size_coherent (EL j stk).cf_fn (EL j stk).cf_state` by
    fs[ircf_alias_saved_def, ircf_alias_boundary_def] >>
  qpat_x_assum `_ IN ircf_gam_cur _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ircf_gam_cur_def]) >>
  `MEM bb (EL j stk).cf_fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `wf_function (EL j stk).cf_fn /\ fn_inst_wf (EL j stk).cf_fn /\
   wf_ssa (EL j stk).cf_fn /\ ircf_no_dst_write_alias (EL j stk).cf_fn` by
    metis_tac[EVERY_MEM] >>
  drule_all ircf_gam_allocations >> strip_tac >>
  fs[occurrence_annotation_ok_def] >>
  `FLOOKUP B ((EL j U).of_owner,dai.inst_id) = SOME (db,sz) /\
   FLOOKUP B ((EL j U).of_owner,sai.inst_id) = SOME (sb,sz)` by
    metis_tac[occurrence_saved_ok_allocas] >>
  `db+sz <= s.vs_alloca_next /\ sb+sz <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >> decide_tac
QED

Theorem ircf_cross_base_frame:
  ircf_cross tn gam s t /\
  step_inst_base inst s = OK s' /\
  step_inst_base ti t = OK t' /\
  (!op j. MEM op inst.inst_operands /\ j IN op_taint tn op ==> j < 32) /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
     db+k NOTIN new_site_bytes s s' /\
     sb+k NOTIN new_site_bytes s s' /\
     db+k NOTIN range_bytes (source_memory_write_ranges inst s) /\
     sb+k NOTIN range_bytes (source_memory_write_ranges inst s) /\
     sb+k NOTIN range_bytes (source_memory_write_ranges ti t)) ==>
  ircf_cross (step_taint inst s s' tn) gam s' t'
Proof
  strip_tac >> rw[ircf_cross_def] >>
  `db+k NOTIN new_site_bytes s s' /\
   sb+k NOTIN new_site_bytes s s' /\
   db+k NOTIN range_bytes (source_memory_write_ranges inst s) /\
   sb+k NOTIN range_bytes (source_memory_write_ranges inst s) /\
   sb+k NOTIN range_bytes (source_memory_write_ranges ti t)` by metis_tac[] >>
  `db+k IN mem_taint tn inst s s' <=> db+k IN tn.t_mem` by
    (irule mem_taint_frame_source_range >> metis_tac[]) >>
  `sb+k IN mem_taint tn inst s s' <=> sb+k IN tn.t_mem` by
    (irule mem_taint_frame_source_range >> metis_tac[]) >>
  qpat_x_assum `ircf_cross _ _ _ _`
    (mp_tac o REWRITE_RULE [ircf_cross_def]) >>
  disch_then (qspecl_then [`db`, `sb`, `sz`, `k`] mp_tac) >>
  simp[] >> strip_tac >>
  fs[step_taint_def] >>
  `read_byte (db+k) s'.vs_memory = read_byte (db+k) s.vs_memory` by
    (irule step_inst_base_OK_byte_frame >>
     gvs[range_bytes_def] >> metis_tac[]) >>
  `read_byte (sb+k) t'.vs_memory = read_byte (sb+k) t.vs_memory` by
    (irule step_inst_base_OK_byte_frame >>
     gvs[range_bytes_def] >> metis_tac[]) >>
  gvs[]
QED

Theorem ircf_cross_protected_base:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  gam = ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk /\
  ircf_cross tn gam s t /\
  step_inst_base inst s = OK s' /\ step_inst_base ti t = OK t' /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    db+k NOTIN new_site_bytes s s' /\ sb+k NOTIN new_site_bytes s s' /\
    sb+k NOTIN range_bytes (source_memory_write_ranges ti t)) ==>
  ircf_cross (step_taint inst s s' tn) gam s' t'
Proof
  strip_tac >> irule ircf_cross_base_frame >>
  conj_tac
  >- (drule o1LowerDloadOccurrenceTheory.occ_frame_reachable_projection >>
      strip_tac >> metis_tac[frame_reachable_op_taint_bounded]) >>
  simp[IgnAsm `gam = _`] >> qexistsl_tac [`t`, `ti`] >>
  simp[IgnAsm `gam = _`] >> rpt gen_tac >> strip_tac >>
  `db+k NOTIN new_site_bytes s s' /\ sb+k NOTIN new_site_bytes s s' /\
   sb+k NOTIN range_bytes (source_memory_write_ranges ti t)` by metis_tac[] >>
  simp[] >>
  `!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
    ~(off <= db+k /\ db+k < off+len) /\
    ~(off <= sb+k /\ sb+k < off+len)` by
    (rpt strip_tac >> metis_tac[ircf_gam_write_disjoint]) >>
  gvs[range_bytes_def] >> metis_tac[]
QED

Theorem ircf_cross_disciplined_base:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ ptr_discipline lo C vs /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  gam = ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk /\
  ircf_cross tn gam s t /\
  step_inst_base inst s = OK s' /\ step_inst_base ti t = OK t' /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    sb+k NOTIN range_bytes (source_memory_write_ranges ti t)) ==>
  ircf_cross (step_taint inst s s' tn) gam s' t'
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `active_inst fn inst s` by
    (qpat_assum `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[occ_frame_reachable_cases] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
  `inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> DRET` by
    (drule_all o1LowerDloadPtrDisciplineTheory.ptr_discipline_inst_opcode_exclusions >>
     simp[]) >>
  `!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
     db+k NOTIN new_site_bytes s s' /\ sb+k NOTIN new_site_bytes s s' /\
     sb+k NOTIN range_bytes (source_memory_write_ranges ti t)` by
    (rpt gen_tac >> strip_tac >>
     `db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next` by
       metis_tac[ircf_gam_frontier] >>
     metis_tac[step_inst_base_new_site_bytes_frontier]) >>
  drule_all ircf_cross_protected_base >> simp[]
QED

Theorem ircf_block_plan_write_ranges:
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> DRET /\
  taint_ok fn tn (EL i bb.bb_instructions) s /\ taint_agree D X tn s t ==>
  range_bytes (source_memory_write_ranges (EL i bb2.bb_instructions) t) SUBSET
  range_bytes (source_memory_write_ranges (EL i bb.bb_instructions) s)
Proof
  strip_tac >> Cases_on `i IN ircf_fwds bb bb2`
  >- (fs[ircf_block_plan_def] >>
      simp[mk_nop_inst_def, codegenRelTheory.source_memory_write_ranges_def, range_bytes_def]) >>
  Cases_on `mem_write_ops (EL i bb.bb_instructions) = NONE`
  >- (fs[ircf_block_plan_def] >>
      Cases_on `(EL i bb.bb_instructions).inst_opcode = ASSIGN`
      >- simp[codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
      `source_memory_write_ranges
         ((EL i bb.bb_instructions) with inst_operands :=
           MAP (ircf_redirect_op fn bb bb2) (EL i bb.bb_instructions).inst_operands)
         t = []` by (irule codegenRelTheory.source_memory_write_ranges_nonwriter >> simp[]) >>
      simp[range_bytes_def]) >>
  `EL i bb2.bb_instructions = EL i bb.bb_instructions` by
    (drule_all ircf_block_plan_writer >> simp[]) >>
  drule_all taint_agree_write_ranges >> simp[]
QED

Theorem ircf_cross_block_plan_base:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ ptr_discipline lo C vs /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  gam = ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk /\
  ircf_cross tn gam s t /\ taint_agree D X tn s t /\
  step_inst_base inst s = OK s' /\ step_inst_base ti t = OK t' /\
  ircf_block_plan fn bb bb2 /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  ti = EL i bb2.bb_instructions ==>
  ircf_cross (step_taint inst s s' tn) gam s' t'
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `MEM inst (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks, EL_MEM]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `inst.inst_opcode <> DRET` by
    (drule_all o1LowerDloadPtrDisciplineTheory.ptr_discipline_inst_opcode_exclusions >>
     simp[]) >>
  `fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `range_bytes (source_memory_write_ranges ti t) SUBSET
   range_bytes (source_memory_write_ranges inst s)` by
    (gvs[] >> irule ircf_block_plan_write_ranges >> simp[] >> metis_tac[]) >>
  `!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
     sb+k NOTIN range_bytes (source_memory_write_ranges ti t)` by
    (rpt gen_tac >> strip_tac >>
     `sb+k NOTIN range_bytes (source_memory_write_ranges inst s)` by
       (strip_tac >>
        qpat_x_assum `_ IN range_bytes _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [range_bytes_def]) >>
        metis_tac[ircf_gam_write_disjoint]) >>
     metis_tac[SUBSET_DEF]) >>
  drule_all ircf_cross_disciplined_base >> simp[]
QED

Theorem ircf_gam_phi_prefix:
  ircf_gam fn_meta rma C fn bb allocas
    (phi_prefix_length bb.bb_instructions) = {}
Proof
  rw[EXTENSION, ircf_gam_def, NOT_IN_EMPTY] >>
  spose_not_then strip_assume_tac >>
  fs[ircf_fwds_def] >>
  drule phi_prefix_length_el_phi >> simp[]
QED

Theorem ircf_gam_stk_cons[simp]:
  ircf_gam_stk fn_meta rma C (f::stk) =
  ircf_gam_cur fn_meta rma C f.cf_fn f.cf_state UNION
  ircf_gam_stk fn_meta rma C stk
Proof
  simp[ircf_gam_stk_def]
QED

Theorem ircf_dead_cons[simp]:
  ircf_dead ids s (f::stk) =
  site_bytes ids f.cf_state.vs_allocas UNION ircf_dead ids s stk
Proof
  simp[ircf_dead_def] >> SET_TAC[]
QED

Theorem ircf_gam_mono:
  a SUBMAP b /\ n <= m ==>
  ircf_gam fn_meta rma C fn bb a n SUBSET
  ircf_gam fn_meta rma C fn bb b m
Proof
  rw[SUBSET_DEF, ircf_gam_def] >>
  fs[SUBMAP_FLOOKUP_EQN] >>
  qexistsl_tac [`k`, `d`, `s`, `dai`, `sai`, `sz1`, `sz2`] >>
  simp[] >> decide_tac
QED

Theorem ircf_gam_suc:
  ircf_gam fn_meta rma C fn bb a (SUC n) =
  ircf_gam fn_meta rma C fn bb a n UNION
  {x | ?d s szw dai sai db sb sz1 sz2.
    n IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
    ircf_copy_roots fn (EL n bb.bb_instructions) = SOME (d,s,szw) /\
    MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\ dai.inst_outputs = [d] /\
    MEM sai (fn_insts fn) /\ sai.inst_opcode = ALLOCA /\ sai.inst_outputs = [s] /\
    FLOOKUP a dai.inst_id = SOME (db,sz1) /\
    FLOOKUP a sai.inst_id = SOME (sb,sz2) /\ x = (db,sb,w2n szw)}
Proof
  simp[EXTENSION, ircf_gam_def, arithmeticTheory.LT] >> metis_tac[]
QED

Theorem ircf_gam_suc_no_forward:
  n NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) ==>
  ircf_gam fn_meta rma C fn bb a (SUC n) =
  ircf_gam fn_meta rma C fn bb a n
Proof
  strip_tac >>
  `!k. k < SUC n /\ k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) <=>
       k < n /\ k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb)` by
    (gen_tac >> Cases_on `k = n` >> simp[arithmeticTheory.LT]) >>
  simp[EXTENSION, ircf_gam_def] >> metis_tac[]
QED

Theorem site_bytes_mono:
  ids SUBSET ids' /\ a SUBMAP b ==>
  site_bytes ids a SUBSET site_bytes ids' b
Proof
  rw[site_bytes_def, SUBSET_DEF] >>
  fs[SUBMAP_FLOOKUP_EQN] >> metis_tac[SUBSET_DEF]
QED

Theorem ircf_dead_allocas_mono:
  s.vs_allocas SUBMAP s'.vs_allocas ==>
  ircf_dead ids s stk SUBSET ircf_dead ids s' stk
Proof
  strip_tac >>
  `site_bytes ids s.vs_allocas SUBSET site_bytes ids s'.vs_allocas` by
    (irule site_bytes_mono >> simp[]) >>
  simp[ircf_dead_def] >> ASM_SET_TAC[]
QED

Theorem ircf_R_ret_reachable_caller_memory:
  ircf_R_ret_reachable vs D fn_meta rma C (f::stk) PG G tn fn ret se te /\
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\ ~ctx_has_dalloca C /\
  i < f.cf_state.vs_alloca_next /\
  i NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) f.cf_state stk /\
  i NOTIN tn.t_mem ==>
  read_byte i se.vs_memory = read_byte i te.vs_memory
Proof
  strip_tac >> gvs[ircf_R_ret_reachable_def] >>
  drule_all frame_reachable_intret_saved_frontier >> strip_tac >>
  `i NOTIN site_bytes (ircf_dst_ids fn_meta rma C) se.vs_allocas` by
    (simp[site_bytes_def] >> rpt strip_tac >>
     `f.cf_state.vs_alloca_next <= b` by metis_tac[] >>
     decide_tac) >>
  `i NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) se (f::stk)` by
    (fs[ircf_dead_def] >> ASM_SET_TAC[]) >>
  qpat_x_assum `ircf_R_ret _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ircf_R_ret_def] >> strip_tac >>
  `i < se.vs_alloca_next` by decide_tac >>
  drule_all taint_agree_memory >> simp[]
QED

Theorem ircf_R_boundary:
  s.vs_prev_bb <> NONE /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s t ==>
  ircf_R D fn_meta rma C stk PG G (entry_taint_vars fn s tn) fn s t
Proof
  strip_tac >> simp[ircf_R_def] >> conj_tac
  >- (qexists_tac `tn` >> simp[]) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  gvs[ircf_cross_def, entry_taint_vars_def] >> gvs[]
QED

Theorem ircf_R_eval_phis:
  ircf_R D fn_meta rma C stk PG G tn fn s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK s1 ==>
  ?t1. eval_phis t bb.bb_instructions = OK t1 /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s1 stk) tn s1 t1 /\
    ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s1 t1
Proof
  strip_tac >>
  qpat_x_assum `ircf_R _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ircf_R_def]) >>
  `tn = tn0 with t_var := phis_taint s.vs_prev_bb tn0 bb.bb_instructions` by
    (Cases_on `s.vs_prev_bb = NONE`
     >- (gvs[] >> Cases_on `bb.bb_instructions` >>
         gvs[eval_phis_def, eval_one_phi_def, phis_taint_def, AllCaseEqs()]) >>
     gvs[entry_taint_vars_def]) >>
  qpat_x_assum `tn = if _ then _ else _` kall_tac >>
  drule_all taint_agree_eval_phis >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_memory = s.vs_memory` by
    (qpat_x_assum `eval_phis s _ = _`
       (mp_tac o MATCH_MP venomExecProofsTheory.eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `t1.vs_memory = t.vs_memory` by
    (qpat_x_assum `eval_phis t _ = _`
       (mp_tac o MATCH_MP venomExecProofsTheory.eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[ircf_dead_def, ircf_cross_def, entry_taint_vars_def] >> gvs[]
QED

Theorem ircf_gam_cur_phi_prefix:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = phi_prefix_length bb.bb_instructions ==>
  ircf_gam_cur fn_meta rma C fn s = {}
Proof
  strip_tac >> simp[ircf_gam_cur_def, ircf_gam_phi_prefix, EXTENSION]
QED

(* ===== One block, and the pass ===== *)

Theorem ircf_block_sim:
  !D lo vs C fn_meta rma k stk PG G tn fn fn' s t bb.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
      (ircf_R D fn_meta rma C) (ircf_R_ret D fn_meta rma C) (SUC k) /\
    MEM fn C.ctx_functions /\
    lookup_function fn.fn_name (ircf_transform_ctx fn_meta rma C).ctx_functions =
      SOME fn' /\
    ircf_R D fn_meta rma C stk PG G tn fn s t /\
    block_reach vs C stk PG G tn fn s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    terminates (run_block k C bb s) ==>
    ?m bb'.
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      block_step_rel D vs C (ircf_R D fn_meta rma C)
        (ircf_R_ret D fn_meta rma C) stk PG fn
        (run_block k C bb s)
        (run_block m (ircf_transform_ctx fn_meta rma C) bb' t)
Proof
  cheat
QED

Theorem ircf_ctx_sim:
  !D lo vs C fn_meta rma.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D ==>
    ctx_sim D C (ircf_transform_ctx fn_meta rma C) vs vs
Proof
  rpt strip_tac >>
  `ctx_wf C` by gvs[o1_ctx_shape_def] >>
  irule reachable_fn_sim_ctx_sim >>
  rpt conj_tac >|
  [rw[] >> simp[ircf_transform_ctx_lookup,
                ircf_transform_function_entry_label],
   qexistsl_tac [`ircf_R D fn_meta rma C`, `ircf_R_ret D fn_meta rma C`] >>
   conj_tac
   >- rw[ircf_R_def, ircf_cross_def, ircf_gam_stk_def, taint_agree_def,
         ld_shared_agree_refl, word_agree_except_def,
         venom_state_component_equality]
   >> rpt strip_tac >> irule ircf_block_sim >> simp[] >> metis_tac[],
   simp[],
   simp[ircf_transform_ctx_def]]
QED
