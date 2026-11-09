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
