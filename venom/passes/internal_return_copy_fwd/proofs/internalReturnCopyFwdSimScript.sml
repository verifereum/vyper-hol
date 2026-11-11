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
  venomExecProps fnRunFields ptrTaintClean internalReturnCopyFwdAbort
  o1LowerDloadForwardInversion reachableNonhalted

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

Theorem ircf_cross_source_mcopy:
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
       read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) ==>
  ircf_cross
    (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
                       {db+q | q < len /\ sb+q IN tn.t_mem})
    {(db,sb,len)} (mcopy db sb len s) t
Proof
  strip_tac >> rw[ircf_cross_def] >>
  `~(db <= sb+k /\ sb+k < db+len)` by decide_tac >>
  `db <= db+k /\ db+k < db+len` by decide_tac >>
  `!q. q < len ==> sb+k <> db+q` by (rpt strip_tac >> decide_tac) >>
  simp[arithmeticTheory.ADD_COMM] >>
  simp[mcopy_def, GSYM read_memory_def,
       regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
       o1LowerDloadRangeTransportTheory.ld_read_memory_length,
       o1LowerDloadRangeTransportTheory.ld_read_memory_element] >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED

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

Theorem ircf_forward_destination_hidden:
  MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [d] /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (db,z) ==>
  {i | db <= i /\ i < db+z} SUBSET ircf_dead (ircf_dst_ids fn_meta rma C) s stk
Proof
  strip_tac >>
  `ai.inst_id IN ircf_dst_ids fn_meta rma C` by
    (simp[ircf_dst_ids_def] >> metis_tac[]) >>
  rw[SUBSET_DEF, ircf_dead_def, site_bytes_def] >> metis_tac[]
QED

Theorem ircf_dst_ids_owned:
  ctx_inst_ids_distinct C /\ MEM fn C.ctx_functions /\
  MEM ai (fn_insts fn) /\ ai.inst_id IN ircf_dst_ids fn_meta rma C ==>
  ?bb k d sr sz.
    MEM bb fn.fn_blocks /\
    k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
    ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [d]
Proof
  strip_tac >> fs[ircf_dst_ids_def] >>
  `ALL_DISTINCT (FLAT (MAP (\f. MAP (\i. i.inst_id) (fn_insts f))
     C.ctx_functions))` by
    fs[ctx_inst_ids_distinct_def, fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat,
       MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `fn' = fn` by
    (irule (venomWfPropsTheory.all_distinct_flat_map_inj |> INST_TYPE [alpha |-> ``:num``]) >> simp[] >>
     qexists_tac `\f. MAP (\i. i.inst_id) (fn_insts f)` >>
     qexists_tac `C.ctx_functions` >> simp[MEM_MAP] >> metis_tac[]) >>
  gvs[] >>
  `ai' = ai` by
    (irule venomWfPropsTheory.fn_inst_ids_distinct_inj >> simp[] >> qexists_tac `fn` >>
     metis_tac[allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn,
               fn_inst_ids_distinct_def, fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat,
               MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  gvs[] >> metis_tac[]
QED

Theorem ircf_forward_source_not_dst_id:
  ctx_inst_ids_distinct C /\ MEM fn C.ctx_functions /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  MEM bb fn.fn_blocks /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sr] ==>
  ai.inst_id NOTIN ircf_dst_ids fn_meta rma C
Proof
  strip_tac >> strip_tac >>
  drule_all ircf_dst_ids_owned >> strip_tac >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb) /\
   ircf_block_plan fn bb' (ircf_tbb fn_meta rma C fn bb')` by
    simp[wf_ssa_def, ircf_tbb_def, ircf_transform_block_plan] >>
  `ircf_fwd_ok fn bb k d sr sz /\ ircf_fwd_ok fn bb' k' sr sr' sz'` by
    (gvs[] >> metis_tac[ircf_block_plan_fwd_ok]) >>
  Cases_on `(EL k bb.bb_instructions).inst_id =
            (EL k' bb'.bb_instructions).inst_id`
  >- (`EL k bb.bb_instructions = EL k' bb'.bb_instructions` by
        (irule venomWfPropsTheory.fn_inst_ids_distinct_inj >> simp[] >>
         qexists_tac `fn` >> gvs[wf_function_def, ircf_fwd_ok_def] >>
         simp[fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[EL_MEM]) >>
      gvs[ircf_fwd_ok_def]) >>
  `MEM (EL k' bb'.bb_instructions) bb'.bb_instructions /\
   (EL k' bb'.bb_instructions).inst_opcode = MCOPY` by
    (gvs[ircf_fwd_ok_def] >> metis_tac[EL_MEM]) >>
  drule_all ircf_forward_roots_separate >> gvs[]
QED

(* A current allocation whose id is not hidden cannot overlap a hidden
   current allocation or any saved-frame allocation. *)
Theorem ircf_dead_current_site_exclusion:
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  ALL_DISTINCT (a::MAP (\u. u.of_owner) U) /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) /\ aid NOTIN ids /\
  b <= p /\ p < b+z ==>
  p NOTIN ircf_dead ids s stk
Proof
  strip_tac >> strip_tac >>
  `FLOOKUP B (a,aid) = SOME (b,z)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  `0 < z` by decide_tac >>
  qpat_x_assum `_ IN ircf_dead _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ircf_dead_def, site_bytes_def, pred_setTheory.IN_BIGUNION, MEM_MAP])
  >- (`FLOOKUP B (a,id) = SOME (b',sz)` by
        fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
      `aid <> id` by metis_tac[] >>
      `0 < sz` by decide_tac >>
      `b+z <= b' \/ b'+sz <= b` by
        metis_tac[occurrence_geometry_sites_disjoint, pairTheory.PAIR_EQ] >>
      decide_tac) >>
  gvs[] >> rename1 `FLOOKUP f.cf_state.vs_allocas did = SOME (c,w)` >>
  `?j. j < LENGTH stk /\ EL j stk = f` by metis_tac[MEM_EL] >>
  `FLOOKUP B ((EL j U).of_owner,did) = SOME (c,w)` by
    (fs[occurrence_annotation_ok_def] >>
     metis_tac[occurrence_saved_ok_allocas]) >>
  `LENGTH U = LENGTH stk` by fs[occurrence_natural_geometry_def] >>
  `a <> (EL j U).of_owner` by
    (fs[ALL_DISTINCT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  `0 < z /\ 0 < w` by decide_tac >>
  `b+z <= c \/ c+w <= b` by
    metis_tac[occurrence_geometry_sites_disjoint, pairTheory.PAIR_EQ] >>
  decide_tac
QED

Theorem ircf_forward_source_bytes:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  MEM bb fn.fn_blocks /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sr] /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (rb,z) /\ q < z ==>
  rb+q NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) s stk /\
  rb+q < s.vs_alloca_next
Proof
  strip_tac >>
  drule occ_frame_reachable_annotation >> simp[] >> strip_tac >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry] >>
  `ALL_DISTINCT (a::MAP (\u. u.of_owner) U)` by
    metis_tac[occ_frame_reachable_owner_fresh] >>
  `ai.inst_id NOTIN ircf_dst_ids fn_meta rma C` by
    metis_tac[ircf_forward_source_not_dst_id] >>
  `rb <= rb+q /\ rb+q < rb+z` by decide_tac >>
  conj_tac
  >- (drule_all ircf_dead_current_site_exclusion >>
      simp[arithmeticTheory.ADD_COMM]) >>
  `FLOOKUP B (a,ai.inst_id) = SOME (rb,z)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  `rb+z <= s.vs_alloca_next` by metis_tac[occurrence_geometry_site_bounds] >>
  decide_tac
QED

Theorem ircf_forward_source_agreement:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  MEM bb fn.fn_blocks /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sr] /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (rb,z) /\ q < z /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  rb+q NOTIN tn.t_mem ==>
  read_byte (rb+q) s.vs_memory = read_byte (rb+q) t.vs_memory
Proof
  strip_tac >> drule_all ircf_forward_source_bytes >> strip_tac >>
  drule_all taint_agree_memory >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem ircf_forward_copy_sites:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ s.vs_inst_idx = k /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) ==>
  ?dai rai db rb.
    MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\ dai.inst_outputs = [d] /\
    MEM rai (fn_insts fn) /\ rai.inst_opcode = ALLOCA /\ rai.inst_outputs = [sr] /\
    FLOOKUP s.vs_allocas dai.inst_id = SOME (db,w2n sz) /\
    FLOOKUP s.vs_allocas rai.inst_id = SOME (rb,w2n sz) /\
    lookup_var d s = SOME (n2w db) /\ lookup_var sr s = SOME (n2w rb) /\
    db+w2n sz <= s.vs_alloca_next /\ rb+w2n sz <= s.vs_alloca_next /\
    (db+w2n sz <= rb \/ rb+w2n sz <= db) /\
    (!q. q < w2n sz ==> rb+q NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    simp[wf_ssa_def, ircf_tbb_def, ircf_transform_block_plan] >>
  `ircf_fwd_ok fn bb k d sr sz` by metis_tac[ircf_block_plan_fwd_ok] >>
  drule_all ircf_fwd_operand_sites >> strip_tac >>
  drule occ_frame_reachable_annotation >> simp[] >> strip_tac >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry] >>
  `FLOOKUP B (a,dai.inst_id) = SOME (db,w2n sz) /\
   FLOOKUP B (a,rai.inst_id) = SOME (rb,w2n sz)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  `db+w2n sz <= s.vs_alloca_next /\ rb+w2n sz <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >>
  `dai.inst_id <> rai.inst_id` by
    (strip_tac >> `dai = rai` by
       (irule venomWfPropsTheory.fn_inst_ids_distinct_inj >> simp[] >>
        qexists_tac `fn` >> simp[] >>
        gvs[wf_function_def]) >>
     gvs[ircf_fwd_ok_def]) >>
  `db+w2n sz <= rb \/ rb+w2n sz <= db` by
    (Cases_on `w2n sz = 0` >- decide_tac >>
     `0 < w2n sz` by decide_tac >>
     metis_tac[occurrence_geometry_sites_disjoint, pairTheory.PAIR_EQ]) >>
  qexistsl_tac [`dai`, `rai`, `db`, `rb`] >> simp[] >>
  gen_tac >> strip_tac >>
  drule_all ircf_forward_source_bytes >> simp[]
QED

Theorem ircf_saved_dead_read_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\
  j < LENGTH stk /\ MEM (EL j stk).cf_fn C.ctx_functions /\
  p IN site_bytes (ircf_dst_ids fn_meta rma C) (EL j stk).cf_state.vs_allocas /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  ~(off <= p /\ p < off+len)
Proof
  strip_tac >>
  qpat_x_assum `_ IN site_bytes _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [site_bytes_def]) >>
  `MEM (EL j stk) stk` by metis_tac[EL_MEM] >>
  `?ai w. MEM ai (fn_insts (EL j stk).cf_fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w` by
    metis_tac[frameAllocationHistoryTheory.occ_frame_reachable_saved_allocation_syntax] >>
  `?bb k d sr amount.
    MEM bb (EL j stk).cf_fn.fn_blocks /\
    k IN ircf_fwds bb (ircf_tbb fn_meta rma C (EL j stk).cf_fn bb) /\
    ircf_copy_roots (EL j stk).cf_fn (EL k bb.bb_instructions) = SOME (d,sr,amount) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [d]` by
    (irule ircf_dst_ids_owned >> metis_tac[]) >>
  `ircf_block_plan (EL j stk).cf_fn bb
     (ircf_tbb fn_meta rma C (EL j stk).cf_fn bb)` by
    (fs[EVERY_MEM] >> simp[ircf_tbb_def, ircf_transform_block_plan]) >>
  `ircf_fwd_ok (EL j stk).cf_fn bb k d sr amount` by
    (drule_all ircf_block_plan_fwd_ok >> simp[]) >>
  irule ircf_saved_destination_read_disjoint >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ircf_forward_copy_transport:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ s.vs_inst_idx = k /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t ==>
  ?db rb.
    lookup_var d s = SOME (n2w db) /\ lookup_var sr s = SOME (n2w rb) /\
    let tm = tn with t_mem :=
      (tn.t_mem DIFF {i | db <= i /\ i < db+w2n sz}) UNION
      {db+q | q < w2n sz /\ rb+q IN tn.t_mem} in
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tm
      (mcopy db rb (w2n sz) s) t /\
    ircf_cross tm {(db,rb,w2n sz)} (mcopy db rb (w2n sz) s) t
Proof
  strip_tac >> drule_all ircf_forward_copy_sites >> strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `{i | db <= i /\ i < db+w2n sz} SUBSET
    ircf_dead (ircf_dst_ids fn_meta rma C) s stk` by
    (drule_all ircf_forward_destination_hidden >> simp[]) >>
  `!q. q < w2n sz /\ rb+q NOTIN tn.t_mem ==>
    read_byte (rb+q) s.vs_memory = read_byte (rb+q) t.vs_memory` by
    (rpt strip_tac >> drule_all ircf_forward_source_agreement >> simp[]) >>
  qexistsl_tac [`db`, `rb`] >> simp[] >>
  (conj_tac
   >- (drule_all taint_agree_source_mcopy >> simp[arithmeticTheory.ADD_COMM]) >>
   gvs[SRULE [arithmeticTheory.ADD_COMM] ircf_cross_source_mcopy])
QED
Theorem ircf_forward_copy_step_sites:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ s.vs_inst_idx = k /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  access_ok lo G fn (EL k bb.bb_instructions) s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t ==>
  ?s1 dai rai db rb.
    MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\ dai.inst_outputs = [d] /\
    MEM rai (fn_insts fn) /\ rai.inst_opcode = ALLOCA /\ rai.inst_outputs = [sr] /\
    FLOOKUP s.vs_allocas dai.inst_id = SOME (db,w2n sz) /\
    FLOOKUP s.vs_allocas rai.inst_id = SOME (rb,w2n sz) /\
    step_inst_base (EL k bb.bb_instructions) s = OK s1 /\
    step_inst_base (mk_nop_inst (EL k bb.bb_instructions)) t = OK t /\
    lookup_var d s = SOME (n2w db) /\ lookup_var sr s = SOME (n2w rb) /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
      (step_taint (EL k bb.bb_instructions) s s1 tn) s1 t /\
    ircf_cross (step_taint (EL k bb.bb_instructions) s s1 tn)
      {(db,rb,w2n sz)} s1 t
Proof
  strip_tac >> drule_all ircf_forward_copy_sites >> strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    simp[wf_ssa_def, ircf_tbb_def, ircf_transform_block_plan] >>
  `ircf_fwd_ok fn bb k d sr sz` by metis_tac[ircf_block_plan_fwd_ok] >>
  drule_all ircf_fwd_operand_sites_at >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = MCOPY` by fs[ircf_fwd_ok_def] >>
  `(EL k bb.bb_instructions).inst_outputs = []` by
    (`inst_wf (EL k bb.bb_instructions)` by
      (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def] >>
       metis_tac[MEM_FLAT, MEM_MAP, EL_MEM, ircf_fwd_ok_def]) >>
     gvs[inst_wf_def]) >>
  `eval_operand (Var dv) s = SOME (n2w db) /\
   eval_operand (Var rv) s = SOME (n2w rb) /\ eval_operand (Lit sz) s = SOME sz` by
    simp[eval_operand_def] >>
  drule_all step_taint_mcopy >> disch_then (qspec_then `tn` assume_tac) >>
  qexistsl_tac [`mcopy (w2n (n2w db : bytes32)) (w2n (n2w rb : bytes32)) (w2n sz) s`,
                `dai`, `rai`, `db`, `rb`] >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, mk_nop_inst_def] >>
  (Cases_on `w2n sz = 0`
   >- (simp[ircf_cross_def] >>
       irule (SRULE [GSYM arithmeticTheory.NOT_LESS_EQUAL, taint_component_equality]
         (Q.INST [`len` |-> `0`] (SPEC_ALL taint_agree_source_mcopy))) >>
       simp[]) >>
   `w2n (n2w db : bytes32) = db /\ w2n (n2w rb : bytes32) = rb` by
     (drule_all access_ok_mcopy_site_bases >> simp[]) >>
   `{i | db <= i /\ i < db+w2n sz} SUBSET
     ircf_dead (ircf_dst_ids fn_meta rma C) s stk` by
     (drule_all ircf_forward_destination_hidden >> simp[]) >>
   `!q. q < w2n sz /\ rb+q NOTIN tn.t_mem ==>
     read_byte (rb+q) s.vs_memory = read_byte (rb+q) t.vs_memory` by
     (rpt strip_tac >> drule_all ircf_forward_source_agreement >> simp[]) >>
   gvs[] >> conj_tac
   >- (drule_all taint_agree_source_mcopy >> simp[arithmeticTheory.ADD_COMM]) >>
   gvs[SRULE [arithmeticTheory.ADD_COMM] ircf_cross_source_mcopy])
QED


Theorem ircf_forward_copy_step:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ s.vs_inst_idx = k /\
  k IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL k bb.bb_instructions) = SOME (d,sr,sz) /\
  access_ok lo G fn (EL k bb.bb_instructions) s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t ==>
  ?s1 db rb.
    step_inst_base (EL k bb.bb_instructions) s = OK s1 /\
    step_inst_base (mk_nop_inst (EL k bb.bb_instructions)) t = OK t /\
    lookup_var d s = SOME (n2w db) /\ lookup_var sr s = SOME (n2w rb) /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
      (step_taint (EL k bb.bb_instructions) s s1 tn) s1 t /\
    ircf_cross (step_taint (EL k bb.bb_instructions) s s1 tn)
      {(db,rb,w2n sz)} s1 t
Proof
  strip_tac >> drule_all ircf_forward_copy_step_sites >> metis_tac[]
QED

Theorem ircf_current_dead_read_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  MEM fn C.ctx_functions /\ wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\
  EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst /\
  p IN site_bytes (ircf_dst_ids fn_meta rma C) s.vs_allocas /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  ~(off <= p /\ p < off+len)
Proof
  strip_tac >>
  qpat_x_assum `_ IN site_bytes _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [site_bytes_def]) >>
  `?ai w. MEM ai (fn_insts fn) /\ ai.inst_id = id /\
    ai.inst_opcode = ALLOCA /\ ai.inst_operands = [Lit w] /\ sz = w2n w` by
    metis_tac[frameAllocationHistoryTheory.occ_frame_reachable_current_allocation_syntax] >>
  `?pb k d sr amount.
    MEM pb fn.fn_blocks /\
    k IN ircf_fwds pb (ircf_tbb fn_meta rma C fn pb) /\
    ircf_copy_roots fn (EL k pb.bb_instructions) = SOME (d,sr,amount) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [d]` by
    (irule ircf_dst_ids_owned >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb) /\
   ircf_block_plan fn pb (ircf_tbb fn_meta rma C fn pb)` by
    simp[ircf_tbb_def, ircf_transform_block_plan] >>
  irule (ircf_planned_destination_read_disjoint |>
    Q.INST [`tr` |-> `ircf_tbb fn_meta rma C fn`]) >>
  fs[wf_ssa_def] >> metis_tac[]
QED

Theorem ircf_unchanged_dead_read_disjoint:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\
  EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst /\
  p IN ircf_dead (ircf_dst_ids fn_meta rma C) s stk /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  ~(off <= p /\ p < off+len)
Proof
  strip_tac >>
  qpat_x_assum `_ IN ircf_dead _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ircf_dead_def, pred_setTheory.IN_BIGUNION, MEM_MAP])
  >- (irule ircf_current_dead_read_disjoint >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?j. j < LENGTH stk /\ EL j stk = f` by metis_tac[MEM_EL] >>
  irule ircf_saved_dead_read_disjoint >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ircf_redirect_read_cross:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (w2n w,len) (source_memory_read_ranges inst s) /\ len <> 0 /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t ==>
  ?sr sb sz.
    ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v = sr /\
    lookup_var sr s = SOME (n2w sb) /\ len <= sz /\
    (w2n w,sb,sz) IN ircf_gam_cur fn_meta rma C fn s /\
    (!q. q < len ==>
      (w2n w+q IN tn.t_mem <=> sb+q IN tn.t_mem) /\
      (w2n w+q NOTIN tn.t_mem ==>
       read_byte (w2n w+q) s.vs_memory = read_byte (sb+q) t.vs_memory))
Proof
  strip_tac >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  drule_all ircf_redirect_read_sites >> strip_tac >>
  `(w2n w,sb,w2n sz) IN ircf_gam_cur fn_meta rma C fn s` by
    (simp[ircf_gam_cur_def, ircf_gam_def] >> metis_tac[]) >>
  qexistsl_tac [`sr`, `sb`, `w2n sz`] >> simp[] >>
  qx_gen_tac `q` >> strip_tac >>
  `q < w2n sz` by decide_tac >>
  qpat_x_assum `ircf_cross _ _ _ _` mp_tac >>
  simp[ircf_cross_def] >>
  disch_then (qspecl_then [`w2n w`, `sb`, `w2n sz`, `q`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem ircf_redirect_read_observation:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (w2n w,len) (source_memory_read_ranges inst s) /\ len <> 0 /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t ==>
  ?sr sb sz.
    ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v = sr /\
    lookup_var sr s = SOME (n2w sb) /\ len <= sz /\
    (w2n w,sb,sz) IN ircf_gam_cur fn_meta rma C fn s /\
    eval_operand (Var sr) t = SOME (n2w sb) /\
    (!q. q < len ==>
      (w2n w+q IN tn.t_mem <=> sb+q IN tn.t_mem) /\
      (w2n w+q NOTIN tn.t_mem ==>
       read_byte (w2n w+q) s.vs_memory = read_byte (sb+q) t.vs_memory))
Proof
  strip_tac >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  drule_all ircf_redirect_read_sites >> strip_tac >>
  `op_taint tn (Var sr) = {}` by
    (irule frame_reachable_alloca_root_clean >> metis_tac[]) >>
  `eval_operand (Var sr) t = SOME (n2w sb)` by
    (drule_all taint_agree_operand_clean >> simp[eval_operand_def]) >>
  drule_all ircf_redirect_read_cross >> strip_tac >>
  metis_tac[]
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

Theorem ircf_gam_cur_source_roundtrip:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  ircf_no_dst_write_alias fn /\ ircf_size_coherent fn s /\
  ircf_completed_bases fn s /\
  (db,sb,sz) IN ircf_gam_cur fn_meta rma C fn s /\ sz <> 0 ==>
  w2n (n2w sb : bytes32) = sb
Proof
  strip_tac >>
  qpat_x_assum `_ IN ircf_gam_cur _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ircf_gam_cur_def]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  drule_all ircf_gam_allocations >> strip_tac >>
  `sz = w2n amount` by
    (irule ircf_alloca_of_coherent_size >>
     gvs[wf_ssa_def] >> metis_tac[ircf_fwd_ok_def]) >>
  irule ircf_completed_bases_source_roundtrip >>
  gvs[wf_ssa_def] >> metis_tac[]
QED

Theorem ircf_redirect_read_effective_observation:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (w2n w,len) (source_memory_read_ranges inst s) /\ len <> 0 /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ taint_agree D X tn s t ==>
  ?sr r sz.
    ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v = sr /\
    eval_operand (Var sr) t = SOME r /\ len <= sz /\
    (!q. q < len ==>
      (w2n w+q IN tn.t_mem <=> w2n r+q IN tn.t_mem) /\
      (w2n w+q NOTIN tn.t_mem ==>
       read_byte (w2n w+q) s.vs_memory = read_byte (w2n r+q) t.vs_memory))
Proof
  strip_tac >>
  `EVERY ssa_form C.ctx_functions` by
    (fs[EVERY_MEM, wf_ssa_def] >> metis_tac[]) >>
  drule_all ircf_redirect_read_observation >> strip_tac >>
  `ircf_completed_bases fn s` by
    (irule ircf_completed_bases_reachable >> metis_tac[]) >>
  `ircf_size_coherent fn s` by fs[ircf_alias_boundary_def] >>
  `sz <> 0` by decide_tac >>
  `w2n (n2w sb : bytes32) = sb` by
    (irule ircf_gam_cur_source_roundtrip >> metis_tac[]) >>
  qexistsl_tac [`sr`, `n2w sb`, `sz`] >> simp[]
QED

Theorem ircf_redirect_read_address_defined:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ MEM (Var v) inst.inst_operands /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t ==>
  ?r. eval_operand (Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v)) t = SOME r
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ fn_inst_ids_distinct fn` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomWfTheory.wf_function_def] >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    simp[ircf_tbb_def, ircf_transform_block_plan] >>
  `ssa_form fn` by fs[venomWfTheory.wf_ssa_def] >>
  drule_all ircf_redirect_changed_forward >> strip_tac >>
  `s.vs_inst_idx <> k` by metis_tac[] >>
  `k < s.vs_inst_idx` by metis_tac[ircf_fwd_dst_use_later] >>
  `k <= s.vs_inst_idx` by decide_tac >>
  drule_all ircf_fwd_source_root_later >> strip_tac >>
  `op_taint tn (Var sr) = {}` by
    (irule frame_reachable_alloca_root_clean >> metis_tac[]) >>
  drule_all taint_agree_operand_clean >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem ircf_redirect_operand_defined_forward:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ MEM op inst.inst_operands /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t /\
  IS_SOME (eval_operand op s) ==>
  IS_SOME (eval_operand (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) op) t)
Proof
  strip_tac >> Cases_on `op` >> simp[ircf_redirect_op_def, eval_operand_def]
  >- (rename1 `lookup_var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v) t` >>
      Cases_on `ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v = v`
      >- metis_tac[taint_agree_operand_defined, eval_operand_def] >>
      drule_all ircf_redirect_read_address_defined >>
      strip_tac >> gvs[eval_operand_def]) >>
  metis_tac[taint_agree_operand_defined, eval_operand_def]
QED

Theorem ircf_redirect_operands_defined_forward:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t /\
  IS_SOME (eval_operands inst.inst_operands s) ==>
  IS_SOME (eval_operands
    (MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands) t)
Proof
  strip_tac >>
  fs[o1LowerDloadJointInternalEffectsTheory.ld_eval_operands_defined,
     EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> irule ircf_redirect_operand_defined_forward >>
  simp[EVERY_MEM] >>
  goal_assum (drule_at Any) >> fs[] >> metis_tac[]
QED

Theorem ircf_redirect_observation_abort:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t /\
  MEM inst.inst_opcode [MLOAD; SHA3; LOG] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base (inst with inst_operands :=
    MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands) t = Abort a t'
Proof
  strip_tac >>
  `inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  `IS_SOME (eval_operands inst.inst_operands s) ==>
   IS_SOME (eval_operands
     (MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands) t)` by
    (strip_tac >> irule ircf_redirect_operands_defined_forward >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >> simp[]
QED

Theorem ircf_redirect_create_abort:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY ssa_form C.ctx_functions /\ taint_agree D X tn s t /\
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [CREATE; CREATE2] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base (inst with inst_operands :=
    MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands) t = Abort a t'
Proof
  strip_tac >>
  `inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `!pos op. pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = op /\ pos <> 1 ==>
     eval_operand (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) op) t = eval_operand op s` by
    (rpt strip_tac >>
     `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) op = op` by
       (irule ircf_redirect_non_address_operand >> simp[] >>
        conj_tac >- metis_tac[wf_ssa_def] >>
        qexistsl_tac [`s.vs_inst_idx`, `pos`] >>
        gvs[wf_ssa_def, MEM, invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
     `op_taint tn op = {}` by
       (irule taint_ok_observation_operand >> simp[] >>
        metis_tac[EL_MEM, MEM]) >>
     metis_tac[taint_agree_operand_clean]) >>
  `!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) op) t)` by
    (rpt strip_tac >> irule ircf_redirect_operand_defined_forward >> metis_tac[]) >>
  `IS_SOME (eval_operands inst.inst_operands s) ==>
   IS_SOME (eval_operands
     (MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands) t)` by
    (strip_tac >> irule ircf_redirect_operands_defined_forward >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
  qpat_assum `!pos. pos < _ /\ _ ==> _` (qspec_then `0` (assume_tac o SRULE [])) >>
  qpat_x_assum `!pos. pos < _ /\ _ ==> _` (qspec_then `2` (assume_tac o SRULE [])) >>
  gvs[eval_operands_def] >>
  metis_tac[optionTheory.IS_SOME_DEF, optionTheory.option_CASES]
QED

Theorem ircf_redirect_clean_read_slice:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (Var v) inst.inst_operands /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (w2n w,len) (source_memory_read_ranges inst s) /\
  (!q. q < len ==> w2n w+q NOTIN tn.t_mem) /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ taint_agree D X tn s t ==>
  ?r. eval_operand (Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v)) t = SOME r /\
    read_memory (w2n w) len s = read_memory (w2n r) len t
Proof
  strip_tac >> Cases_on `len = 0`
  >- (`EVERY ssa_form C.ctx_functions` by
        (fs[EVERY_MEM, venomWfTheory.wf_ssa_def] >> metis_tac[]) >>
      drule_all ircf_redirect_read_address_defined >> strip_tac >>
      qexists_tac `r` >> simp[read_memory_def]) >>
  drule_all ircf_redirect_read_effective_observation >> strip_tac >>
  qexists_tac `r` >> simp[] >>
  irule o1LowerDloadRangeTransportTheory.read_memory_eq_from_bytes >>
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

Theorem ircf_gam_suc_forward:
  ssa_form fn /\
  n IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn (EL n bb.bb_instructions) = SOME (d,root,szw) /\
  MEM dai (fn_insts fn) /\ dai.inst_opcode = ALLOCA /\ dai.inst_outputs = [d] /\
  MEM sai (fn_insts fn) /\ sai.inst_opcode = ALLOCA /\ sai.inst_outputs = [root] /\
  FLOOKUP a dai.inst_id = SOME (db,dsz) /\
  FLOOKUP a sai.inst_id = SOME (sb,ssz) ==>
  ircf_gam fn_meta rma C fn bb a (SUC n) =
  ircf_gam fn_meta rma C fn bb a n UNION {(db,sb,w2n szw)}
Proof
  strip_tac >> rewrite_tac[ircf_gam_suc] >> AP_TERM_TAC >>
  simp[EXTENSION] >> gen_tac >> eq_tac
  >- (strip_tac >> gvs[] >>
      `dai' = dai /\ sai' = sai` by
        (fs[venomInstTheory.fn_insts_def] >>
         metis_tac[venomWfPropsTheory.ssa_outputs_same_inst, MEM]) >>
      gvs[]) >>
  strip_tac >> gvs[] >> metis_tac[]
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

Theorem ircf_gam_allocas_extension:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_allocas SUBMAP a ==>
  ircf_gam fn_meta rma C fn bb a s.vs_inst_idx =
  ircf_gam fn_meta rma C fn bb s.vs_allocas s.vs_inst_idx
Proof
  strip_tac >> irule SUBSET_ANTISYM >> reverse conj_tac
  >- (irule ircf_gam_mono >> simp[]) >>
  simp[SUBSET_DEF, ircf_gam_def] >> rpt strip_tac >>
  rename1 `ircf_copy_roots fn _ = SOME (d,root,szw)` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    simp[wf_ssa_def, ircf_tbb_def, ircf_transform_block_plan] >>
  `ircf_fwd_ok fn bb k d root szw` by metis_tac[ircf_block_plan_fwd_ok] >>
  `?b z. FLOOKUP s.vs_allocas dai.inst_id = SOME (b,z)` by
    (metis_tac[ircf_fwd_earlier_allocations, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `?b z. FLOOKUP s.vs_allocas sai.inst_id = SOME (b,z)` by
    (metis_tac[ircf_fwd_earlier_allocations, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  fs[SUBMAP_FLOOKUP_EQN] >>
  `FLOOKUP s.vs_allocas dai.inst_id = SOME (db,sz1) /\
   FLOOKUP s.vs_allocas sai.inst_id = SOME (sb,sz2)` by metis_tac[optionTheory.SOME_11] >>
  qexistsl_tac [`k`, `d`, `root`, `dai`, `sai`, `sz1`, `sz2`] >> simp[]
QED

Theorem ircf_gam_cur_control:
  ircf_gam_cur fn_meta rma C fn
    (s with <|vs_current_bb := label; vs_inst_idx := n|>) =
  {x | ?bb. lookup_block label fn.fn_blocks = SOME bb /\
    x IN ircf_gam fn_meta rma C fn bb s.vs_allocas n}
Proof
  simp[ircf_gam_cur_def]
QED

Theorem ircf_gam_cur_suc_no_forward:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) ==>
  ircf_gam_cur fn_meta rma C fn (s with vs_inst_idx := SUC s.vs_inst_idx) =
  ircf_gam_cur fn_meta rma C fn s
Proof
  strip_tac >> simp[ircf_gam_cur_def, ircf_gam_suc_no_forward]
QED

Theorem ircf_gam_cur_ordinary_step:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' ==>
  ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx) =
  ircf_gam_cur fn_meta rma C fn s
Proof
  strip_tac >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `s.vs_allocas SUBMAP s'.vs_allocas` by
    metis_tac[step_inst_noninvoke_allocas_submap] >>
  drule_all ircf_gam_allocas_extension >>
  simp[ircf_gam_cur_def, ircf_gam_suc_no_forward]
QED

Theorem ircf_dead_control[simp]:
  ircf_dead ids (s with <|vs_current_bb := label; vs_inst_idx := n|>) stk =
  ircf_dead ids s stk
Proof
  simp[ircf_dead_def]
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

Theorem ircf_dead_noninvoke_mono:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' ==>
  ircf_dead ids s stk SUBSET ircf_dead ids s' stk
Proof
  strip_tac >> irule ircf_dead_allocas_mono >>
  metis_tac[step_inst_noninvoke_allocas_submap]
QED

Theorem ircf_dead_step_agree:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  taint_agree D (ircf_dead ids s stk) tn' s' t' ==>
  taint_agree D (ircf_dead ids s' stk) tn' s' t'
Proof
  strip_tac >> irule taint_agree_hidden_mono >>
  qexists_tac `ircf_dead ids s stk` >>
  simp[] >> metis_tac[ircf_dead_noninvoke_mono]
QED

Theorem ircf_unchanged_nonassign_step:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE /\
  EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = r /\ terminates r ==>
  (!s'. r = OK s' ==> ?t'. step_inst_base inst t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t') /\
  (!v s'. r = IntRet v s' ==> ?t'. step_inst_base inst t = IntRet v t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s' t') /\
  (!s'. r = Halt s' ==> ?t'. step_inst_base inst t = Halt t' /\
    dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. r = Abort a s' ==> ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `!off len p. MEM (off,len) (source_memory_read_ranges inst s) /\
      off <= p /\ p < off+len ==>
      p NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) s stk` by
    (rpt strip_tac >> drule_all ircf_unchanged_dead_read_disjoint >> simp[]) >>
  drule_all taint_agree_step_base >> strip_tac >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `?t'. step_inst_base inst t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
      (step_taint inst s s' tn) s' t'` by metis_tac[] >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  metis_tac[step_inst_non_invoke]
QED

Theorem ircf_unchanged_nonassign_ok:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE /\
  EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `terminates (OK s')` by simp[passSimulationDefsTheory.terminates_def] >>
  drule_all ircf_unchanged_nonassign_step >> metis_tac[]
QED

Theorem ircf_redirect_mload_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [Var v] /\ inst.inst_outputs = [out] /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `MEM (w2n w,32) (source_memory_read_ranges inst s) /\ inst.inst_opcode <> ASSIGN` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def, eval_operand_def] >>
  `32 <> (0:num)` by simp[] >>
  drule_all ircf_redirect_read_effective_observation >> strip_tac >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `ti.inst_opcode = MLOAD /\ ti.inst_operands = [Var sr] /\ ti.inst_outputs = [out]` by
    (gvs[ircf_block_plan_def, ircf_redirect_op_def] >> metis_tac[]) >>
  `?t'. step_inst_base ti t = OK t' /\
     taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
       (step_taint inst s s' tn) s' t'` by
    (irule taint_agree_translated_mload_step >>
     simp[eval_operand_def] >>
     gvs[]) >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  metis_tac[step_inst_non_invoke]
QED

Theorem ircf_redirect_hash_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [Var v; len] /\ inst.inst_outputs = [out] /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ eval_operand len s = SOME nw /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `MEM (w2n w,w2n nw) (source_memory_read_ranges inst s) /\
    inst.inst_opcode <> ASSIGN /\ MEM (Var v) inst.inst_operands` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def,
         contextCodegenRelTheory.memory_range_of_operands_def, eval_operand_def] >>
  `!q. q < w2n nw ==> w2n w+q NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> irule taint_ok_observation_read >> simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule taint_ok_observation_operand >> simp[] >> metis_tac[]) >>
  drule_all ircf_redirect_clean_read_slice >> strip_tac >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) len = len` by
    (irule ircf_redirect_non_address_operand >>
     simp[] >> conj_tac >- metis_tac[venomWfTheory.wf_ssa_def] >>
     qexistsl_tac [`s.vs_inst_idx`, `1`] >>
     gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
  `ti.inst_opcode = SHA3 /\ ti.inst_operands =
    [Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v); len] /\
    ti.inst_outputs = [out]` by
    (gvs[ircf_block_plan_def, ircf_redirect_op_def] >> metis_tac[]) >>
  `?t'. step_inst_base ti t = OK t' /\
     taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
       (step_taint inst s s' tn) s' t'` by
    (irule taint_agree_translated_hash_step >> simp[eval_operand_def] >>
     metis_tac[taint_agree_operand_clean, MEM]) >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  qexistsl_tac [`C`, `0`, `inst`, `s`] >>
  gvs[step_inst_non_invoke]
QED

Theorem ircf_redirect_create_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = CREATE /\ inst.inst_operands = [value; Var v; len] /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ eval_operand len s = SOME nw /\
  eval_operand value s = SOME vw /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>

  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `MEM (w2n w,w2n nw) (source_memory_read_ranges inst s) /\
    inst.inst_opcode <> ASSIGN /\ MEM (Var v) inst.inst_operands` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def,
         contextCodegenRelTheory.memory_range_of_operands_def, eval_operand_def] >>
  `!q. q < w2n nw ==> w2n w+q NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> irule taint_ok_observation_read >> simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule taint_ok_observation_operand >> simp[] >> metis_tac[]) >>
  drule_all ircf_redirect_clean_read_slice >> strip_tac >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) len = len` by
    (irule ircf_redirect_non_address_operand >> simp[] >>
     conj_tac >- metis_tac[venomWfTheory.wf_ssa_def] >>
     qexistsl_tac [`s.vs_inst_idx`, `2`] >>
     gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) value = value` by
    (irule ircf_redirect_non_address_operand >> simp[] >>
     conj_tac >- metis_tac[venomWfTheory.wf_ssa_def] >>
     qexistsl_tac [`s.vs_inst_idx`, `0`] >>
     gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
  `ti.inst_opcode = CREATE /\ ti.inst_operands =
    [value; Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v); len] /\
    ti.inst_outputs = inst.inst_outputs` by
    (gvs[ircf_block_plan_def, ircf_redirect_op_def] >> metis_tac[]) >>
  `MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by simp[] >>
  drule_all taint_agree_external_clean_shared >> strip_tac >>
  `?t'. step_inst_base ti t = OK t' /\
     taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
       (step_taint inst s s' tn) s' t'` by
    (irule taint_agree_translated_create_step >> simp[out_taint_def, eval_operand_def] >>
     metis_tac[taint_agree_operand_clean, MEM]) >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  qexistsl_tac [`C`, `0`, `inst`, `s`] >> gvs[step_inst_non_invoke]
QED

Theorem ircf_redirect_create2_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; Var v; len; salt] /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ eval_operand len s = SOME nw /\
  eval_operand value s = SOME vw /\ eval_operand salt s = SOME sw /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `MEM (w2n w,w2n nw) (source_memory_read_ranges inst s) /\
    inst.inst_opcode <> ASSIGN /\ MEM (Var v) inst.inst_operands` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def,
         contextCodegenRelTheory.memory_range_of_operands_def, eval_operand_def] >>
  `!q. q < w2n nw ==> w2n w+q NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> irule taint_ok_observation_read >> simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule taint_ok_observation_operand >> simp[] >> metis_tac[]) >>
  drule_all ircf_redirect_clean_read_slice >> strip_tac >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `!pos. pos < LENGTH inst.inst_operands /\ pos <> 1 ==>
    ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) (EL pos inst.inst_operands) =
      EL pos inst.inst_operands` by
    (rpt strip_tac >> irule ircf_redirect_non_address_operand >> simp[] >>
     conj_tac >- metis_tac[venomWfTheory.wf_ssa_def] >>
     qexistsl_tac [`s.vs_inst_idx`, `pos`] >>
     gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
  `ti.inst_opcode = CREATE2 /\ ti.inst_operands =
    [value; Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v); len; salt] /\
    ti.inst_outputs = inst.inst_outputs` by
    (qpat_x_assum `!pos. _` (fn th => map_every mp_tac [Q.SPEC `0` th, Q.SPEC `2` th, Q.SPEC `3` th]) >>
     simp[] >> rpt strip_tac >> gvs[ircf_block_plan_def, ircf_redirect_op_def] >> metis_tac[]) >>
  `MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by simp[] >>
  drule_all taint_agree_external_clean_shared >> strip_tac >>
  `?t'. step_inst_base ti t = OK t' /\
     taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
       (step_taint inst s s' tn) s' t'` by
    (irule taint_agree_translated_create2_step >> simp[out_taint_def, eval_operand_def] >>
     metis_tac[taint_agree_operand_clean, MEM]) >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  qexistsl_tac [`C`, `0`, `inst`, `s`] >> gvs[step_inst_non_invoke]
QED

Theorem ircf_redirect_log_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ MEM fn C.ctx_functions /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst.inst_operands = Lit tc :: REVERSE (Var v :: len :: tops) /\
  LENGTH tops = w2n tc /\ eval_operands tops s = SOME topics /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ eval_operand len s = SOME nw /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s /\ ?P. fn_ptr_ok P fn` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    (Cases_on `tops` >> simp[memLocDefsTheory.mem_read_ops_def, REVERSE_APPEND]) >>
  `MEM (w2n w,w2n nw) (source_memory_read_ranges inst s) /\
    inst.inst_opcode <> ASSIGN /\ MEM (Var v) inst.inst_operands` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def,
         contextCodegenRelTheory.memory_range_of_operands_def, eval_operand_def, MEM_REVERSE,
         REVERSE_APPEND] >>
  `!q. q < w2n nw ==> w2n w+q NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> irule taint_ok_observation_read >> simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule taint_ok_observation_operand >> simp[] >> metis_tac[]) >>
  drule_all ircf_redirect_clean_read_slice >> strip_tac >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb) /\
    MEM inst (fn_insts fn)` by
    (conj_asm1_tac >- metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     conj_tac >- metis_tac[ircf_tbb_def, ircf_transform_block_plan] >>
     simp[venomInstTheory.fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[] >> metis_tac[EL_MEM]) >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) len = len /\
    MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) tops = tops` by
    (irule ircf_redirect_log_scalars >> simp[] >>
     conj_tac >- fs[venomWfTheory.wf_ssa_def] >>
     conj_tac >- (qexistsl_tac [`inst`, `Var v`, `tc`] >> simp[]) >>
     metis_tac[]) >>
  `ti.inst_opcode = LOG /\ ti.inst_outputs = [] /\ ti.inst_operands =
    Lit tc :: REVERSE (Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v) :: len :: tops)` by
    (gvs[ircf_block_plan_def, MAP_REVERSE, ircf_redirect_op_def] >> metis_tac[]) >>
  `eval_operands tops t = SOME topics` by
    (qsuff_tac `eval_operands tops s = eval_operands tops t` >- simp[] >>
     irule taint_agree_operands_clean >> simp[EVERY_MEM] >>
     metis_tac[MEM, MEM_REVERSE]) >>
  `?t'. step_inst_base ti t = OK t' /\
     taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk)
       (step_taint inst s s' tn) s' t'` by
    (irule taint_agree_translated_log_step >> simp[eval_operand_def] >>
     metis_tac[taint_agree_operand_clean, MEM, MEM_REVERSE]) >>
  qexists_tac `t'` >> simp[] >> irule ircf_dead_step_agree >>
  qexistsl_tac [`C`, `0`, `inst`, `s`] >> gvs[step_inst_non_invoke]
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

Theorem ircf_cross_memory_transport:
  ircf_cross tn gam s t /\ s'.vs_memory = s.vs_memory /\
  t'.vs_memory = t.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  ircf_cross tn' gam s' t'
Proof
  simp[ircf_cross_def] >> metis_tac[]
QED

Theorem ircf_R_ret_reachable_restore:
  ircf_R_ret_reachable vs D fn_meta rma C (f::stk) PG G tn fn ret se te /\
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\ ~ctx_has_dalloca C /\
  taint_agree D X0 saved f.cf_state t /\ saved.t_var = f.cf_tvar /\
  f.cf_state.vs_call_ctx.cc_address = se.vs_call_ctx.cc_address /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  ircf_gam_cur fn_meta rma C f.cf_fn
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) =
    ircf_gam_cur fn_meta rma C f.cf_fn f.cf_state ==>
  ?t'. bind_outputs f.cf_inst.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state t te)) = SOME t' /\
    frame_reachable vs C stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) f.cf_state stk)
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    ircf_cross
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      (ircf_gam_cur fn_meta rma C f.cf_fn
         (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) UNION
       ircf_gam_stk fn_meta rma C stk)
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `!i. i NOTIN ircf_dead (ircf_dst_ids fn_meta rma C) f.cf_state stk /\
       i NOTIN tn.t_mem /\ i < f.cf_state.vs_alloca_next ==>
       read_byte i se.vs_memory = read_byte i te.vs_memory` by
    (rpt strip_tac >> drule_all ircf_R_ret_reachable_caller_memory >> simp[]) >>
  drule_all ircf_R_ret_reachable_resume >> strip_tac >>
  `taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) se (f::stk)) tn se te` by
    gvs[ircf_R_ret_def] >>
  drule_all taint_agree_resume_caller >> strip_tac >>
  qexists_tac `t'` >> simp[] >> conj_tac
  >- (irule taint_agree_inst_idx >> gvs[]) >>
  `s'.vs_memory = se.vs_memory /\ t'.vs_memory = te.vs_memory` by
    (imp_res_tac o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def,
         venom_state_component_equality]) >>
  gvs[ircf_R_ret_def] >> irule ircf_cross_memory_transport >>
  goal_assum (drule_at Any) >> simp[]
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

Theorem ircf_redirect_ordinary_ok:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ti <> inst /\ ~is_terminator inst.inst_opcode /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\ MEM fn C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan,
      venomExecPropsTheory.lookup_block_MEM] >>
  `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
    metis_tac[ircf_block_plan_changed_opcode] >>
  `inst.inst_opcode <> ASSIGN /\ inst_wf inst` by
    (fs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `?pos v. pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = Var v /\
    ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v` by
    metis_tac[ircf_block_plan_changed_operand] >>
  `is_mem_addr_position inst.inst_opcode pos` by
    (irule ircf_redirect_changed_position >> metis_tac[]) >>
  fs[MEM, is_terminator_def] >> fs[is_terminator_def]
  >- suspend "mload"
  >- suspend "hash"
  >- suspend "log"
  >- suspend "create"
  >> suspend "create2"
QED

Resume ircf_redirect_ordinary_ok[mload]:
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def] >>
  `?w. lookup_var v s = SOME w` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs(), eval_operand_def]) >>
  irule ircf_redirect_mload_ok >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume ircf_redirect_ordinary_ok[hash]:
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def] >>
  `?w nw. lookup_var v s = SOME w /\ eval_operand h' s = SOME nw` by
    (gvs[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def, eval_operand_def]) >>
  irule ircf_redirect_hash_ok >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume ircf_redirect_ordinary_ok[log]:
  `?tc rest. inst.inst_operands = Lit tc :: rest /\
    LENGTH rest = w2n tc + 2 /\ inst.inst_outputs = []` by
    gvs[inst_wf_def] >>
  `?off len tops. REVERSE rest = off :: len :: tops` by
    (Cases_on `REVERSE rest` >> fs[] >>
     Cases_on `t'` >> fs[] >> metis_tac[LENGTH_REVERSE]) >>
  `inst.inst_operands = Lit tc :: REVERSE (off :: len :: tops) /\
   LENGTH tops = w2n tc` by
    (conj_tac >- metis_tac[REVERSE_REVERSE] >>
     qpat_x_assum `REVERSE rest = _` (mp_tac o AP_TERM ``LENGTH:operand list->num``) >> simp[]) >>
  `?P. fn_ptr_ok P fn` by (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> simp[] >> metis_tac[EL_MEM]) >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) len = len /\
   MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) tops = tops` by
    (irule ircf_redirect_log_scalars >> metis_tac[]) >>
  `ti = inst with inst_operands :=
    MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands` by
    (fs[ircf_block_plan_def] >> gvs[]) >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) off <> off` by
    (strip_tac >>
     `MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands =
        inst.inst_operands` by simp[MAP_REVERSE, ircf_redirect_op_def] >>
     fs[]) >>
  Cases_on `off` >> fs[ircf_redirect_op_def] >>
  rename1 `REVERSE rest = Var cv :: len :: tops` >>
  `?w nw topics. lookup_var cv s = SOME w /\ eval_operand len s = SOME nw /\
     eval_operands tops s = SOME topics` by
    (gvs[step_inst_base_opcode_eqs, REVERSE_REVERSE, AllCaseEqs(), eval_operand_def]) >>
  irule ircf_redirect_log_ok >> simp[] >> metis_tac[]
QED
Resume ircf_redirect_ordinary_ok[create]:
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def] >>
  `?w nw vw. lookup_var v s = SOME w /\ eval_operand h'' s = SOME nw /\
    eval_operand h s = SOME vw` by
    (gvs[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def, eval_operand_def]) >>
  irule ircf_redirect_create_ok >> simp[] >> metis_tac[]
QED
Resume ircf_redirect_ordinary_ok[create2]:
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def] >>
  `?w nw vw sw. lookup_var v s = SOME w /\ eval_operand h'' s = SOME nw /\
    eval_operand h s = SOME vw /\ eval_operand h''' s = SOME sw` by
    (gvs[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def, eval_operand_def]) >>
  irule ircf_redirect_create2_ok >> simp[] >> metis_tac[]
QED
Finalise ircf_redirect_ordinary_ok

Theorem ircf_ordinary_nonassign_abort:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = Abort reason s' ==>
  ?t'. step_inst_base ti t = Abort reason t'
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  Cases_on `ti = inst`
  >- (gvs[] >>
      `terminates (Abort reason s')` by simp[passSimulationDefsTheory.terminates_def] >>
      metis_tac[ircf_unchanged_nonassign_step]) >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
   fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\ EVERY ssa_form C.ctx_functions` by
    (fs[EVERY_MEM, wf_ssa_def] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2]` by
    (`ssa_form fn` by fs[wf_ssa_def] >>
     `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
       metis_tac[ircf_block_plan_changed_opcode] >>
     gvs[MEM, is_terminator_def]) >>
  `ti = inst with inst_operands :=
     MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands` by
    (fs[ircf_block_plan_def] >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [MLOAD; SHA3; LOG]`
  >- (drule_all ircf_redirect_observation_abort >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by fs[MEM] >>
  drule_all ircf_redirect_create_abort >> metis_tac[]
QED

Theorem ircf_ordinary_nonassign_step:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = r /\ terminates r ==>
  (!s'. r = OK s' ==> ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t') /\
  (!v s'. r = IntRet v s' ==> ?t'. step_inst_base ti t = IntRet v t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s' t') /\
  (!s'. r = Halt s' ==> ?t'. step_inst_base ti t = Halt t' /\
    dead_result_rel D (Halt s') (Halt t')) /\
  (!reason s'. r = Abort reason s' ==> ?t'. step_inst_base ti t = Abort reason t')
Proof
  strip_tac >>
  Cases_on `ti = inst`
  >- (qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
      `EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst` by metis_tac[] >>
      drule_all ircf_unchanged_nonassign_step >> simp[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
   fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ircf_redirect_ordinary_ok >> metis_tac[]) >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
    metis_tac[ircf_block_plan_changed_opcode] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[MEM, is_terminator_def, step_inst_base_opcode_eqs, exec_read1_def,
          AllCaseEqs()] >> gvs[is_terminator_def, step_inst_base_opcode_eqs,
          exec_read1_def, exec_create_not_IntRet, AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[MEM, is_terminator_def, step_inst_base_opcode_eqs, exec_read1_def,
          AllCaseEqs()] >> gvs[is_terminator_def, step_inst_base_opcode_eqs,
          exec_read1_def, exec_create_not_Halt, AllCaseEqs()]) >>
  rpt strip_tac >> irule ircf_ordinary_nonassign_abort >> metis_tac[]
QED

Theorem ircf_ordinary_nonassign_next:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
    ircf_gam_stk fn_meta rma C stk) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t' /\
    ircf_cross (step_taint inst s s' tn)
      (ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx)
        UNION ircf_gam_stk fn_meta rma C stk) s' t'
Proof
  strip_tac >>
  `ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t` by
    (fs[ircf_cross_def] >> metis_tac[IN_UNION]) >>
  `terminates (OK s')` by simp[passSimulationDefsTheory.terminates_def] >>
  drule_all ircf_ordinary_nonassign_step >> strip_tac >>
  qpat_x_assum `!u. OK s' = OK u ==> _` (qspec_then `s'` mp_tac) >>
  pure_rewrite_tac[REFL_CLAUSE, IMP_CLAUSES] >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 C inst s = OK s'` by simp[step_inst_non_invoke] >>
  `ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx) =
    ircf_gam_cur fn_meta rma C fn s` by
    (drule_all ircf_gam_cur_ordinary_step >> simp[]) >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan,
      venomExecPropsTheory.lookup_block_MEM] >>
  metis_tac[ircf_cross_block_plan_base]
QED

Theorem ircf_assign_next:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = ASSIGN /\ ptr_discipline lo C vs /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
    ircf_gam_stk fn_meta rma C stk) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t' /\
    ircf_cross (step_taint inst s s' tn)
      (ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx)
        UNION ircf_gam_stk fn_meta rma C stk) s' t'
Proof
  strip_tac >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan,
      venomExecPropsTheory.lookup_block_MEM] >>
  `ti = inst` by metis_tac[ircf_block_plan_assign] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    simp[is_terminator_def] >>
  `step_inst 0 C inst s = OK s'` by simp[step_inst_non_invoke] >>
  drule_all taint_agree_assign >> strip_tac >>
  `taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t'` by
    metis_tac[ircf_dead_step_agree] >>
  `ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx) =
    ircf_gam_cur fn_meta rma C fn s` by
    (drule_all ircf_gam_cur_ordinary_step >> simp[]) >>
  qexists_tac `t'` >> simp[] >> metis_tac[ircf_cross_block_plan_base]
QED

Theorem ircf_forward_copy_next:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ lo <= vs.vs_alloca_next /\
  ctx_inst_ids_distinct C /\ EVERY wf_function C.ctx_functions /\
  EVERY wf_ssa C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ircf_copy_roots fn inst = SOME (d,sr,sz) /\
  ptr_discipline lo C vs /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
    ircf_gam_stk fn_meta rma C stk) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  step_inst_base ti t = OK t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
    (step_taint inst s s' tn) s' t /\
  ircf_cross (step_taint inst s s' tn)
    (ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx)
      UNION ircf_gam_stk fn_meta rma C stk) s' t
Proof
  strip_tac >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan,
      venomExecPropsTheory.lookup_block_MEM] >>
  `ti = mk_nop_inst inst` by (fs[ircf_block_plan_def] >> metis_tac[]) >>
  `ircf_fwd_ok fn bb s.vs_inst_idx d sr sz` by
    metis_tac[ircf_block_plan_fwd_ok] >>
  `inst.inst_opcode = MCOPY` by fs[ircf_fwd_ok_def] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   ~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `step_inst 0 C inst s = OK s'` by simp[step_inst_non_invoke] >>
  `s'.vs_allocas = s.vs_allocas /\ s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas,
      venomInstProofsTheory.step_preserves_control_flow] >>
  gvs[] >>
  drule_all (SRULE [] (Q.INST [`k` |-> `s.vs_inst_idx`]
    (SPEC_ALL ircf_forward_copy_step_sites))) >> strip_tac >>
  `s1 = s'` by gvs[] >>
  `ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx) =
   ircf_gam_cur fn_meta rma C fn s UNION {(db,rb,w2n sz)}` by
    (simp[ircf_gam_cur_def] >> irule ircf_gam_suc_forward >>
     fs[wf_ssa_def] >> metis_tac[]) >>
  `ircf_cross (step_taint (EL s.vs_inst_idx bb.bb_instructions) s s' tn)
     (ircf_gam_cur fn_meta rma C fn s UNION ircf_gam_stk fn_meta rma C stk) s' t` by
    metis_tac[ircf_cross_block_plan_base] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[ircf_dead_def] >>
  simp[ircf_cross_def] >> rpt gen_tac >> strip_tac >>
  fs[ircf_cross_def] >> metis_tac[]
QED

Theorem ircf_noninvoke_next:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ ptr_discipline lo C vs /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  taint_within D C vs /\ dead_wf D /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
    ircf_gam_stk fn_meta rma C stk) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base ti t = OK t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk)
      (step_taint inst s s' tn) s' t' /\
    ircf_cross (step_taint inst s s' tn)
      (ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx)
        UNION ircf_gam_stk fn_meta rma C stk) s' t'
Proof
  strip_tac >> drule frame_reachable_occurrence_lift >> strip_tac >>
  drule occ_frame_reachable_annotation >> strip_tac >>
  `ctx_inst_ids_distinct C /\ EVERY wf_function C.ctx_functions /\
   EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
     metis_tac[]) >>
  `lo <= vs.vs_alloca_next /\ access_ok lo G fn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `ircf_alias_boundary fn s G` by
    (drule_all ircf_alias_frames_reachable >>
     metis_tac[ircf_alias_frames_current]) >>
  Cases_on `s.vs_inst_idx IN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb)`
  >- (`ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
        (fs[EVERY_MEM] >> metis_tac[ircf_transform_block_plan, ircf_tbb_def,
          venomExecPropsTheory.lookup_block_MEM]) >>
      `?d sr sz. ircf_copy_roots fn inst = SOME (d,sr,sz)` by
        metis_tac[ircf_block_plan_def] >>
      drule_all ircf_forward_copy_next >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (drule_all ircf_assign_next >> metis_tac[]) >>
  drule_all ircf_ordinary_nonassign_next >> metis_tac[]
QED

Theorem ircf_jump_boundary:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  ptr_discipline lo C vs /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb) /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s t /\
  step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
  ?t'. step_inst_base ti t = OK t' /\ ~t'.vs_halted /\
    block_reach vs C stk PG (entry_prov fn s' G)
      (entry_taint_vars fn s' tn) fn s' /\
    ircf_R D fn_meta rma C stk PG (entry_prov fn s' G)
      (entry_taint_vars fn s' tn) fn s' t'
Proof
  strip_tac >>
  `ssa_form fn /\ inst.inst_opcode <> INVOKE` by
    gvs[wf_ssa_def, MEM] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb)` by
    (strip_tac >>
     `?d sr sz. ircf_fwd_ok fn bb s.vs_inst_idx d sr sz` by
       metis_tac[ircf_block_plan_fwd_ok, ircf_block_plan_def] >>
     gvs[ircf_fwd_ok_def, MEM]) >>
  `ti = inst` by
    (spose_not_then assume_tac >>
     `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
       metis_tac[ircf_block_plan_changed_opcode] >> gvs[MEM]) >>
  `inst.inst_outputs = []` by
    (`inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
     qpat_x_assum `inst_wf inst` mp_tac >>
     gvs[MEM] >> simp[inst_wf_def] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  drule_all taint_agree_jump >> strip_tac >>
  `step_inst 0 C inst s = OK s' /\ step_inst 0 C inst t = OK t'` by
    simp[step_inst_non_invoke] >>
  `s' = s with <|vs_current_bb := s'.vs_current_bb;
     vs_prev_bb := s'.vs_prev_bb; vs_inst_idx := s'.vs_inst_idx|> /\
   t' = t with <|vs_current_bb := t'.vs_current_bb;
     vs_prev_bb := t'.vs_prev_bb; vs_inst_idx := t'.vs_inst_idx|>` by
    metis_tac[o1LowerDloadPhiEntryTheory.ld_branch_noncontrol] >>
  `s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory /\
   s'.vs_allocas = s.vs_allocas` by
    (qpat_assum `s' = _` (fn th =>
       mp_tac (Q.AP_TERM `\x. x.vs_memory` th) >>
       mp_tac (Q.AP_TERM `\x. x.vs_allocas` th)) >>
     qpat_assum `t' = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_memory`) >> simp[]) >>
  `step_taint inst s s' tn = tn /\ s'.vs_prev_bb <> NONE` by
    metis_tac[step_taint_jump] >>
  `~t'.vs_halted` by
    (drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\x. x.vs_halted`) >> simp[]) >>
  `block_reach vs C stk PG (entry_prov fn s' G)
     (entry_taint_vars fn s' tn) fn s'` by
    metis_tac[frame_reachable_block_reach, is_terminator_def, MEM] >>
  qexists_tac `t'` >> conj_tac >- metis_tac[] >> simp[] >>
  irule ircf_R_boundary >> gvs[ircf_dead_def, ircf_cross_def] >> gvs[]
QED

Theorem ircf_ret_result:
  inst.inst_opcode = RET /\ taint_ok fn tn inst s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
                 ircf_gam_stk fn_meta rma C stk) s t /\
  step_inst_base inst s = IntRet v s' ==>
  ?t'. step_inst_base inst t = IntRet v t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk) tn s' t' /\
    ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s' t'
Proof
  strip_tac >>
  drule_all taint_agree_ret >> strip_tac >>
  `s' = s /\ t' = t` by
    gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  qexists_tac `t'` >> gvs[ircf_cross_def] >> metis_tac[IN_UNION]
QED

Theorem ircf_intret_result:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ptr_discipline lo C vs /\ MEM fn C.ctx_functions /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
                 ircf_gam_stk fn_meta rma C stk) s t /\
  step_inst_base inst s = IntRet v s' ==>
  ?t'. step_inst_base ti t = IntRet v t' /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s' stk) tn s' t' /\
    ircf_cross tn (ircf_gam_stk fn_meta rma C stk) s' t'
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[contextCodegenRelTheory.active_inst_def, fn_insts_def] >>
     irule venomInstTheory.fmp_fn_insts_blocks_intro >>
     metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> DRET /\ inst.inst_opcode <> RETFMP` by
    (fs[ptr_discipline_def, EVERY_MEM] >>
     metis_tac[fn_ptr_ok_def]) >>
  `inst.inst_opcode = RET` by
    metis_tac[opcodeClassTheory.step_inst_base_intret_opcodes] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `ti = inst` by
    (spose_not_then assume_tac >>
     `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
       metis_tac[ircf_block_plan_changed_opcode] >> gvs[]) >>
  gvs[] >> irule ircf_ret_result >> metis_tac[]
QED

Theorem ircf_redirect_return_halt:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ircf_no_dst_write_alias fn /\ ircf_alias_boundary fn s G /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [Var v; len] /\
  ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v /\
  lookup_var v s = SOME w /\ eval_operand len s = SOME nw /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ taint_within D C vs /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = Halt sh ==>
  ?th. step_inst_base ti t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `MEM (w2n w,w2n nw) (source_memory_read_ranges inst s) /\
    inst.inst_opcode <> ASSIGN` by
    simp[contextCodegenRelTheory.source_memory_read_ranges_def,
         contextCodegenRelTheory.memory_range_of_operands_def, eval_operand_def] >>
  `EVERY ssa_form C.ctx_functions` by
    (fs[EVERY_MEM, wf_ssa_def] >> metis_tac[]) >>
  `MEM (Var v) inst.inst_operands` by simp[] >>
  drule_all ircf_redirect_read_address_defined >> strip_tac >>
  `!q. q < w2n nw /\ w2n w + q NOTIN tn.t_mem ==>
    read_byte (w2n w + q) s.vs_memory = read_byte (w2n r + q) t.vs_memory` by
    (Cases_on `w2n nw = 0` >- simp[] >>
     drule_all ircf_redirect_read_effective_observation >>
     strip_tac >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) len = len` by
    (irule ircf_redirect_non_address_operand >>
     simp[] >> conj_tac >- metis_tac[venomWfTheory.wf_ssa_def] >>
     qexistsl_tac [`s.vs_inst_idx`, `1`] >>
     gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def]) >>
  `ti.inst_opcode = RETURN /\ ti.inst_operands =
     [Var (ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v); len]` by
    (gvs[ircf_block_plan_def, ircf_redirect_op_def] >> metis_tac[]) >>
  `op_taint tn len = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> metis_tac[]) >>
  `eval_operand len t = SOME nw` by metis_tac[taint_agree_operand_clean] >>
  irule taint_agree_translated_return_halt >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  simp[eval_operand_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ircf_halt_result:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C fn s) s t /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = Halt sh ==>
  ?th. step_inst_base ti t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `MEM inst.inst_opcode [STOP; RETURN; SINK; SELFDESTRUCT]` by
    metis_tac[opcodeClassTheory.step_inst_base_halt_opcodes, MEM] >>
  `inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> INVOKE` by fs[MEM] >>
  Cases_on `ti = inst`
  >- (qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
      `terminates (Halt sh)` by simp[passSimulationDefsTheory.terminates_def] >>
      metis_tac[ircf_unchanged_nonassign_step]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
    metis_tac[ircf_block_plan_changed_opcode] >>
  `inst.inst_opcode = RETURN` by gvs[MEM] >>
  `?pos v. pos < LENGTH inst.inst_operands /\ EL pos inst.inst_operands = Var v /\
    ircf_redirect fn bb (ircf_tbb fn_meta rma C fn bb) v <> v` by
    metis_tac[ircf_block_plan_changed_operand] >>
  `is_mem_addr_position inst.inst_opcode pos` by
    (irule ircf_redirect_changed_position >> metis_tac[]) >>
  `?len w nw. inst.inst_operands = [Var v;len] /\
    lookup_var v s = SOME w /\ eval_operand len s = SOME nw` by
    (gvs[invokeCopyFwdCommonDefsTheory.is_mem_addr_position_def,
         step_inst_base_opcode_eqs, AllCaseEqs(), eval_operand_def]) >>
  irule ircf_redirect_return_halt >> metis_tac[]
QED

Theorem ircf_terminal_abort:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ o1_ctx_shape C /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  lo <= vs.vs_alloca_next /\ ctx_inst_ids_distinct C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY fn_inst_ids_distinct C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ MEM fn C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\ ircf_alias_boundary fn s G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  ti = EL s.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions /\
  s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb) /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ dead_wf D /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  step_inst_base inst s = Abort reason se ==>
  ?te. step_inst_base ti t = Abort reason te
Proof
  strip_tac >>
  `inst.inst_opcode <> ASSIGN` by (strip_tac >> gvs[is_terminator_def]) >>
  Cases_on `ti = inst`
  >- (qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
      `terminates (Abort reason se)` by simp[passSimulationDefsTheory.terminates_def] >>
      metis_tac[ircf_unchanged_nonassign_step]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn /\ EVERY ssa_form C.ctx_functions` by
    (fs[EVERY_MEM, wf_ssa_def] >> metis_tac[]) >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `MEM bb fn.fn_blocks /\ ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    metis_tac[ircf_tbb_def, ircf_transform_block_plan, venomExecPropsTheory.lookup_block_MEM] >>
  `MEM inst.inst_opcode [MLOAD; SHA3; LOG; CREATE; CREATE2; RETURN; REVERT]` by
    metis_tac[ircf_block_plan_changed_opcode] >>
  `ti = inst with inst_operands :=
    MAP (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb)) inst.inst_operands` by
    (fs[ircf_block_plan_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands /\ IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand (ircf_redirect_op fn bb (ircf_tbb fn_meta rma C fn bb) op) t)` by
    (rpt strip_tac >> irule ircf_redirect_operand_defined_forward >> metis_tac[]) >>
  gvs[MEM, is_terminator_def] >> gvs[is_terminator_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  qpat_x_assum `_ with inst_operands := _ = _` (SUBST1_TAC o SYM) >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem ircf_revert_forward_suffix:
  frame_reachable vs C stk PG G tn fn inst s /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ ptr_discipline lo C vs /\
  vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ in_revert_forward fn s /\
  taint_agree D X tn s t /\ terminates (exec_block fuel C bb s) ==>
  ?reason se. exec_block fuel C bb s = Abort reason se /\
    !fuel' C'. ?te. exec_block fuel' C' (ircf_tbb fn_meta rma C fn bb) t = Abort reason te
Proof
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx` by
    gvs[contextCodegenRelTheory.in_revert_forward_def] >>
  `?reason se. exec_block fuel C bb s = Abort reason se` by
    metis_tac[revert_forward_at_terminates_abort] >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by
    (drule frame_reachable_occurrence_lift >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    (fs[EVERY_MEM] >> metis_tac[ircf_transform_block_plan, ircf_tbb_def,
      venomExecPropsTheory.lookup_block_MEM]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  qexistsl_tac [`reason`, `se`] >> simp[] >>
  fs[contextCodegenRelTheory.revert_forward_at_def]
  >- (drule_all ircf_revert_forward_copy_abort >> simp[]) >>
  `inst.inst_opcode = REVERT` by
    gvs[contextCodegenRelTheory.revert_forward_pair_def] >>
  `s.vs_inst_idx = t.vs_inst_idx /\ s.vs_labels = t.vs_labels /\
   FDOM s.vs_vars = FDOM t.vs_vars` by
    (drule taint_agree_labels >> drule taint_agree_var_domain >>
     drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  `inst = EL s.vs_inst_idx bb.bb_instructions` by fs[get_instruction_def] >>
  metis_tac[SRULE [] (Q.INST [`d` |-> `0`] (SPEC_ALL ircf_assign_prefix_abort_domain))]
QED

Theorem ircf_invoke_arguments:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) ==>
  eval_operands ops s = eval_operands ops t
Proof
  strip_tac >> irule taint_agree_operands_clean >>
  qexistsl_tac [`D`, `X`, `tn`] >> simp[] >>
  gvs[decode_invoke_def, AllCaseEqs()] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule taint_ok_invoke_operand >> metis_tac[MEM]
QED

Theorem ircf_setup_entry:
  frame_reachable vs C stk PG G tn caller inst s /\
  active_inst caller inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  taint_ok caller tn inst s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C caller s UNION
                ircf_gam_stk fn_meta rma C stk) s t ==>
  let f = <| cf_fn := caller; cf_inst := inst; cf_state := s;
             cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>;
      callee' = ircf_transform_function fn_meta C.ctx_functions rma callee
  in ?ct. eval_operands ops t = SOME args /\
    setup_callee callee' args t = SOME ct /\
    ircf_R D fn_meta rma C (f::stk) (MAP (op_prov G) ops) FEMPTY
      (tn with t_var := FEMPTY) callee cs ct /\
    block_reach vs C (f::stk) (MAP (op_prov G) ops) FEMPTY
      (tn with t_var := FEMPTY) callee cs
Proof
  simp[] >> strip_tac >>
  `eval_operands ops s = eval_operands ops t` by
    (irule ircf_invoke_arguments >> metis_tac[]) >>
  drule_all frame_reachable_call_block_reach >> strip_tac >>
  qmatch_goalsub_abbrev_tac `setup_callee callee'` >>
  `callee'.fn_blocks <> [] /\
   (HD callee'.fn_blocks).bb_label = (HD callee.fn_blocks).bb_label` by
    (qspec_then `callee` mp_tac
      (Q.SPECL [`fn_meta`, `C.ctx_functions`, `rma`]
        ircf_transform_function_entry_label) >>
     gvs[Abbr `callee'`, setup_callee_def, fn_entry_label_def,
         entry_block_def, NULL_EQ] >>
     Cases_on `(ircf_transform_function fn_meta C.ctx_functions rma callee).fn_blocks` >>
     gvs[]) >>
  drule_all taint_agree_setup_callee >> strip_tac >>
  qexists_tac `ct` >> gvs[] >>
  simp[ircf_R_def] >>
  conj_tac
  >- (qexists_tac `tn with t_var := FEMPTY` >>
      gvs[setup_callee_def, NULL_EQ, ircf_dead_def, site_bytes_def]) >>
  gvs[setup_callee_def, NULL_EQ, ircf_cross_def] >> gvs[]
QED

Theorem ircf_invoke_restore_gam:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' ==>
  ircf_gam_cur fn_meta rma C fn (s' with vs_inst_idx := SUC s.vs_inst_idx) =
    ircf_gam_cur fn_meta rma C fn s /\
  ircf_dead ids (s' with vs_inst_idx := SUC s.vs_inst_idx) stk =
    ircf_dead ids s stk
Proof
  strip_tac >>
  `s'.vs_allocas = s.vs_allocas /\ s'.vs_current_bb = s.vs_current_bb` by
    (drule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def,
         venom_state_component_equality]) >>
  `s.vs_inst_idx NOTIN ircf_fwds bb (ircf_tbb fn_meta rma C fn bb)` by
    gvs[get_instruction_def, ircf_fwds_def] >>
  drule ircf_gam_suc_no_forward >> strip_tac >>
  simp[ircf_gam_cur_def, ircf_dead_def] >>
  irule ircf_gam_suc_no_forward >> simp[]
QED

Theorem ircf_invoke_return_restore:
  f = <| cf_fn := caller; cf_inst := inst; cf_state := s;
         cf_params := params; cf_prov := prov; cf_tvar := saved.t_var |> /\
  ircf_R_ret_reachable vs D fn_meta rma C (f::stk) PG G tn fn ret se te /\
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\ ~ctx_has_dalloca C /\
  taint_agree D X0 saved s t /\
  setup_callee fn args s = SOME cs /\ run_blocks k C fn cs = IntRet ret se /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' /\
  active_inst caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t'. bind_outputs inst.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state t te)) = SOME t' /\
    frame_reachable vs C stk params
      (DRESTRICT prov (COMPL (set inst.inst_outputs)))
      (tn with t_var := DRESTRICT saved.t_var (COMPL (set inst.inst_outputs)))
      caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
    taint_agree D
      (ircf_dead (ircf_dst_ids fn_meta rma C)
         (s' with vs_inst_idx := SUC s.vs_inst_idx) stk)
      (tn with t_var := DRESTRICT saved.t_var (COMPL (set inst.inst_outputs)))
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC s.vs_inst_idx) /\
    ircf_cross
      (tn with t_var := DRESTRICT saved.t_var (COMPL (set inst.inst_outputs)))
      (ircf_gam_cur fn_meta rma C caller
         (s' with vs_inst_idx := SUC s.vs_inst_idx) UNION
       ircf_gam_stk fn_meta rma C stk)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = se.vs_call_ctx.cc_address` by
    (drule run_blocks_intret_fields >>
     gvs[setup_callee_def, NULL_EQ]) >>
  drule_all ircf_invoke_restore_gam >> strip_tac >>
  gvs[] >>
  drule ircf_R_ret_reachable_restore >> simp[] >>
  metis_tac[]
QED

Theorem ircf_invoke_recursive_result:
  ctx_wf C /\
  fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
    (ircf_R D fn_meta rma C) (ircf_R_ret_reachable vs D fn_meta rma C) (SUC k) /\
  frame_reachable vs C stk PG G tn caller inst s /\
  active_inst caller inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  taint_ok caller tn inst s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C caller s UNION
                ircf_gam_stk fn_meta rma C stk) s t /\
  terminates (step_inst k C inst s) ==>
  let f = <| cf_fn := caller; cf_inst := inst; cf_state := s;
             cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>;
      callee' = ircf_transform_function fn_meta C.ctx_functions rma callee
  in ?ct m. eval_operands ops t = SOME args /\
    setup_callee callee' args t = SOME ct /\
    fn_run_rel D (ircf_R_ret_reachable vs D fn_meta rma C)
      (f::stk) (MAP (op_prov G) ops) callee
      (run_blocks k C callee cs)
      (run_blocks m (ircf_transform_ctx fn_meta rma C) callee' ct)
Proof
  simp[] >> strip_tac >>
  `terminates (run_blocks k C callee cs)` by
    (drule_at (Pat `terminates _`) ld_terminating_invoke_inversion >>
     disch_then (qspecl_then [`s`, `k`, `inst`, `C`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  drule_all ircf_setup_entry >> simp[] >> strip_tac >>
  `MEM callee C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_all ircf_transform_ctx_lookup >>
  disch_then (qspecl_then [`fn_meta`, `rma`] assume_tac) >>
  `k < SUC k` by simp[] >>
  qpat_x_assum `fn_sim_below _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[fn_sim_below_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem ircf_invoke_step_transport:
  ctx_wf C /\ vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\
  ~ctx_has_dalloca C /\
  fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
    (ircf_R D fn_meta rma C) (ircf_R_ret_reachable vs D fn_meta rma C) (SUC k) /\
  frame_reachable vs C stk PG G tn caller inst s /\
  active_inst caller inst s /\ inst.inst_opcode = INVOKE /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  taint_ok caller tn inst s /\
  taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
  ircf_cross tn (ircf_gam_cur fn_meta rma C caller s UNION
                ircf_gam_stk fn_meta rma C stk) s t /\
  terminates (step_inst k C inst s) ==>
  ?m. case step_inst k C inst s of
    OK s' => ?t'. step_inst m (ircf_transform_ctx fn_meta rma C) inst t = OK t' /\
      !inst'. active_inst caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
        ?tn'. frame_reachable vs C stk PG
          (DRESTRICT G (COMPL (set inst.inst_outputs))) tn'
          caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
        taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C)
          (s' with vs_inst_idx := SUC s.vs_inst_idx) stk) tn'
          (s' with vs_inst_idx := SUC s.vs_inst_idx)
          (t' with vs_inst_idx := SUC s.vs_inst_idx) /\
        ircf_cross tn'
          (ircf_gam_cur fn_meta rma C caller
             (s' with vs_inst_idx := SUC s.vs_inst_idx) UNION
           ircf_gam_stk fn_meta rma C stk)
          (s' with vs_inst_idx := SUC s.vs_inst_idx)
          (t' with vs_inst_idx := SUC s.vs_inst_idx)
  | _ => dead_result_rel D (step_inst k C inst s)
           (step_inst m (ircf_transform_ctx fn_meta rma C) inst t)
Proof
  strip_tac >>
  drule_at (Pat `terminates _`) ld_terminating_invoke_inversion >>
  disch_then (qspecl_then [`s`, `k`, `inst`, `C`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all ircf_invoke_recursive_result >> simp[] >> strip_tac >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  drule ctxLookupAgreeHelpersTheory.lookup_function_selected_name >> strip_tac >>
  `lookup_function callee.fn_name
     (ircf_transform_ctx fn_meta rma C).ctx_functions =
     SOME (ircf_transform_function fn_meta C.ctx_functions rma callee)` by
    (irule ircf_transform_ctx_lookup >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  Cases_on `run_blocks m (ircf_transform_ctx fn_meta rma C)
    (ircf_transform_function fn_meta C.ctx_functions rma callee) ct` >>
  gvs[fn_run_rel_def] >>
  qexists_tac `m` >>
  simp[Once step_inst_def] >>
  rename1 `ircf_R_ret_reachable _ _ _ _ _ _ _ _ _ _ ret se te` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state t te))`
  >- (gvs[bind_outputs_def, AllCaseEqs()]) >>
  simp[] >> rpt strip_tac >>
  drule_at (Pat `ircf_R_ret_reachable _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ircf_invoke_return_restore >> simp[] >>
  disch_then (qspecl_then [`t`, `tn`] mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ircf_runner_forward:
  !D lo vs C fn_meta rma k stk PG G tn fn s t bb inst.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
      (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) (SUC k) /\
    MEM fn C.ctx_functions /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
    ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
      ircf_gam_stk fn_meta rma C stk) s t /\
    inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
    terminates (exec_block k C bb s)
    ==> ?m. block_step_rel D vs C (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) stk PG fn
      (exec_block k C bb s)
      (exec_block m (ircf_transform_ctx fn_meta rma C)
        (ircf_tbb fn_meta rma C fn bb) t)
Proof
  rpt gen_tac >> strip_tac >>
  `revert_forward_at bb s.vs_inst_idx` by
    gvs[contextCodegenRelTheory.in_revert_forward_def] >>
  `?j. revert_forward_pair bb s.vs_inst_idx j` by
    (fs[contextCodegenRelTheory.revert_forward_at_def] >>
     gvs[contextCodegenRelTheory.revert_forward_pair_def] >> metis_tac[]) >>
  `?reason se. exec_block k C bb s = Abort reason se` by
    metis_tac[revert_forward_at_terminates_abort] >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    (simp[ircf_tbb_def] >> irule ircf_transform_block_plan >>
     gvs[EVERY_MEM] >> metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  drule_all ircf_revert_forward_copy_abort >>
  disch_then (qspecl_then [`k`, `ircf_transform_ctx fn_meta rma C`] strip_assume_tac) >>
  qexists_tac `k` >>
  simp[block_step_rel_def, fn_run_rel_def, dead_result_rel_def]
QED

Theorem ircf_runner_invoke_nonok:
  !D lo vs C fn_meta rma k stk PG G tn fn s t bb inst.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
      (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) (SUC k) /\
    MEM fn C.ctx_functions /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
    ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
      ircf_gam_stk fn_meta rma C stk) s t /\
    inst.inst_opcode = INVOKE /\ terminates (step_inst k C inst s) /\
    (!u. step_inst k C inst s <> OK u)
    ==> ?m. block_step_rel D vs C (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) stk PG fn
      (exec_block k C bb s)
      (exec_block m (ircf_transform_ctx fn_meta rma C)
        (ircf_tbb fn_meta rma C fn bb) t)
Proof
  rpt gen_tac >> strip_tac >>
  `ctx_wf C /\ EVERY wf_function C.ctx_functions /\
   EVERY fn_inst_wf C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `lo <= vs.vs_alloca_next /\ taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `ircf_block_plan fn bb (ircf_tbb fn_meta rma C fn bb)` by
    (simp[ircf_tbb_def] >> irule ircf_transform_block_plan >>
     gvs[EVERY_MEM] >> metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  `MEM bb fn.fn_blocks /\ fn_inst_ids_distinct fn /\
   ircf_no_dst_write_alias fn` by
    (fs[EVERY_MEM, wf_function_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  `get_instruction (ircf_tbb fn_meta rma C fn bb) t.vs_inst_idx = SOME inst` by
    (fs[get_instruction_def] >>
     `EL t.vs_inst_idx (ircf_tbb fn_meta rma C fn bb).bb_instructions = inst` by
       (metis_tac[ircf_block_plan_invoke]) >>
     fs[ircf_block_plan_def]) >>
  drule_all ircf_invoke_step_transport >> strip_tac >>
  qexists_tac `m` >>
  Cases_on `step_inst k C inst s` >> gvs[] >>
  Cases_on `step_inst m (ircf_transform_ctx fn_meta rma C) inst t` >>
  gvs[dead_result_rel_def] >>
  once_rewrite_tac[exec_block_def] >>
  simp[block_step_rel_def, fn_run_rel_def, dead_result_rel_def]
QED

Theorem ircf_runner_halted_ok:
  !D lo vs C fn_meta rma k stk PG G tn fn s t bb inst u.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_sim_below D vs C (ircf_transform_ctx fn_meta rma C)
      (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) (SUC k) /\
    MEM fn C.ctx_functions /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
    taint_agree D (ircf_dead (ircf_dst_ids fn_meta rma C) s stk) tn s t /\
    ircf_cross tn (ircf_gam_cur fn_meta rma C fn s UNION
      ircf_gam_stk fn_meta rma C stk) s t /\
    terminates (step_inst k C inst s) /\
    (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) /\
    step_inst k C inst s = OK u /\ u.vs_halted ==>
    ?m. block_step_rel D vs C (ircf_R D fn_meta rma C)
      (ircf_R_ret_reachable vs D fn_meta rma C) stk PG fn
      (exec_block k C bb s)
      (exec_block m (ircf_transform_ctx fn_meta rma C)
        (ircf_tbb fn_meta rma C fn bb) t)
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_halted` by metis_tac[frame_reachable_not_halted] >>
  drule venomStepPropsTheory.step_inst_ok_halted >> simp[]
QED

Theorem ircf_block_sim:
  !D lo vs C fn_meta rma k stk PG G tn fn fn' s t bb.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ircf_no_dst_write_alias C.ctx_functions /\
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
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
    ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
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
