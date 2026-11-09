(*
 * The cut invariant MakeSSA's lockstep runs on.  At a cut (l,i) of an
 * input block, past its PHIs, the pairing current_cut_sg relates each
 * output name to the input variable it holds: a variable the rest of the
 * run demands from the cut is held by the name its reaching source token
 * was given, or, when that token is an inserted PHI the cleanup collapsed
 * to a copy of src, by src (the collapsed PHI's output and src then hold
 * the same value).  current_cut_inv says the two states agree through that
 * pairing and that every demanded variable is defined on the input side.
 *
 * The lemmas below are what the lockstep needs: the pairing names one
 * owner, it holds at entry, an ordinary instruction keeps it, and entering
 * a block keeps it through the PHIs and the cleanup's copies.
 *)
Theory makeSsaCurrentCutInv
Ancestors
  makeSsaCurrentCleanupTransparent makeSsaCurrentSourceEntryRuntime
  makeSsaCurrentPhiBatchRuntime venomState
  makeSsaCurrentExecRuntime makeSsaCurrentReturnRuntime
  makeSsaCurrentWfSsa o1FrameLockstep o1PassLift makeSsaCurrentDemand
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation makeSsaCurrentCertificate
  makeSsaCurrentTreePaths makeSsaCurrentTokens makeSsaCurrentCarrierOwner
  makeSsaCurrentCutTransport makeSsaCurrentPrefixSuffixOwner
  makeSsaCurrentLockstepShape
  makeSsaCurrentPrefixMaps makeSsaCurrentPrefixOwner makeSsaCurrentCleanupShape
  makeSsaCurrentLockstepShape makeSsaCurrentPrefixRuntime
  makeSsaCurrentRetainedContext makeSsaCurrentPrefixPayload
  makeSsaCurrentEdgeTransport makeSsaCurrentPrefixEndpoints
  makeSsaCurrentHistoryOwner venomInst venomWf venomExecProps list rich_list
  makeSsaCurrentNonphiDemandEdge makeSsaCurrentSingletonDemandEdge
  makeSsaCurrentPrefixCopyOccurrence makeSsaCurrentExternalExclusion
  makeSsaCurrentScanOrigin makeSsaCurrentEntryProvenance
  makeSsaCurrentCarrierExternal makeSsaCurrentLastOutput makeSsaCurrentRuntime
  makeSsaCurrentDemandRuntime makeSsaRfAllocation simplifyCfgRetpc

(* An inserted PHI for v at h that the cleanup collapsed to a copy of src. *)
Definition current_collapsed_carrier_def:
  current_collapsed_carrier fn A renamed h v src <=>
    ?old new q out.
      lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h renamed = SOME new /\
      (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
            ~MEM v di.inst_outputs) /\
      current_wf_inserted_phi_at A renamed h q v /\
      (EL q new.bb_instructions).inst_outputs = [out] /\
      simplify_current_phi (EL q new.bb_instructions) =
        (EL q new.bb_instructions) with
          <| inst_opcode := ASSIGN; inst_operands := [Var src] |>
End

(* At cut (l,i), output name x' holds the demanded input variable v. *)
Definition current_cut_pair_def:
  current_cut_pair fn A renamed H events l i x' v <=>
    ?ev old pre rs E.
      MEM ev events /\ current_event_label ev = l /\
      lookup_block l fn.fn_blocks = SOME old /\
      A l = current_block_annotations old pre /\
      LENGTH (collect_phis old.bb_instructions) <= i /\
      i <= LENGTH old.bb_instructions /\
      current_source_cut A ev (LENGTH pre + i) rs E /\
      current_demand fn v l i /\
      (current_token_name H (E v) = SOME x' \/
       ?h. E v = CurrentInserted v h /\
           current_collapsed_carrier fn A renamed h v x')
End

Definition current_cut_sg_def:
  current_cut_sg fn A renamed H events l i =
    alist_to_fmap
      (FILTER (\(x',v). current_cut_pair fn A renamed H events l i x' v)
         (MAP (\(t,v,x'). (x',v)) H))
End

Definition current_cut_inv_def:
  current_cut_inv fn A renamed H events l i st st' <=>
    state_rel (current_cut_sg fn A renamed H events l i) st st' /\
    !v. current_demand fn v l i ==> IS_SOME (lookup_var v st)
End

(* An output name holds at most one demanded variable at a cut. *)
Theorem current_cut_pair_unique_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_cut_pair fn A renamed H events l i x' v1 /\
  current_cut_pair fn A renamed H events l i x' v2 ==>
  v1 = v2 /\ MEM (x',v1) (MAP (\(t,v,x). (x,v)) H)
Proof
  suspend "owned_history"
QED

(* At entry nothing is demanded, so the pairing is empty. *)
Theorem current_cut_inv_entry:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_entry_state fn s0 ==>
  current_cut_inv fn A renamed H events eb.bb_label 0 s0 s0 /\
  current_cut_sg fn A renamed H events eb.bb_label 0 = FEMPTY
Proof
  strip_tac >>
  `!v. ~current_demand fn v eb.bb_label 0` by
    (gen_tac >> irule current_wf_entry_undemanded >>
     fs[current_wf_phi_context_def, venomInstTheory.fn_entry_label_def]) >>
  `!x v. ~current_cut_pair fn A renamed H events eb.bb_label 0 x v` by
    simp[current_cut_pair_def] >>
  `current_cut_sg fn A renamed H events eb.bb_label 0 = FEMPTY` by
    (rewrite_tac[current_cut_sg_def] >>
     `FILTER (\(x',v). current_cut_pair fn A renamed H events eb.bb_label 0 x' v)
        (MAP (\(t,v,x'). (x',v)) H) = []` by
       (irule (iffRL listTheory.FILTER_EQ_NIL) >>
        simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD]) >>
     simp[]) >>
  simp[current_cut_inv_def, state_rel_def, vars_rel_def]
QED

(* An instruction past the PHIs pairs with the output's instruction at the
   same place after the inserted PHIs, and a step of the output's
   instruction is matched by the input's, keeping the invariant. *)
Theorem current_cut_inv_ordinary_step:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\
  lookup_block l fn.fn_blocks = SOME old /\
  A l = current_block_annotations old pre /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i < LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\
  current_cut_inv fn A renamed H events l i st st' ==>
  ?bb'.
    lookup_block l fn'.fn_blocks = SOME bb' /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
    inst_pair (current_cut_sg fn A renamed H events l i)
      (EL i old.bb_instructions) (EL (LENGTH pre + i) bb'.bb_instructions) /\
    (!fuel t'.
       (EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode <> INVOKE /\
       step_inst fuel C' (EL (LENGTH pre + i) bb'.bb_instructions) st' =
         OK t' ==>
       ?t. step_inst fuel C (EL i old.bb_instructions) st = OK t /\
           current_cut_inv fn A renamed H events l (SUC i) t t' /\
           out_rename_ok (current_cut_sg fn A renamed H events l i)
             (EL i old.bb_instructions).inst_outputs
             (EL (LENGTH pre + i) bb'.bb_instructions).inst_outputs
             (current_cut_sg fn A renamed H events l (SUC i))) /\
    (!fuel v e'.
       (EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode <> INVOKE /\
       step_inst fuel C' (EL (LENGTH pre + i) bb'.bb_instructions) st' =
         IntRet v e' ==>
       ?e. step_inst fuel C (EL i old.bb_instructions) st = IntRet v e /\
           execution_frame e' = execution_frame e) /\
    (!fuel h'.
       (EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode <> INVOKE /\
       step_inst fuel C' (EL (LENGTH pre + i) bb'.bb_instructions) st' =
         Halt h' ==>
       ?h. step_inst fuel C (EL i old.bb_instructions) st = Halt h /\
           execution_frame h' = execution_frame h) /\
    (!ret e e' t'.
       (EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode = INVOKE /\
       execution_frame e' = execution_frame e /\
       bind_outputs (EL (LENGTH pre + i) bb'.bb_instructions).inst_outputs
         ret.iret_values (adopt_return_fmp ret (merge_callee_state st' e')) =
         SOME t' ==>
       ?t. bind_outputs (EL i old.bb_instructions).inst_outputs
             ret.iret_values (adopt_return_fmp ret (merge_callee_state st e)) =
             SOME t /\
           current_cut_inv fn A renamed H events l (SUC i) t t' /\
           out_rename_ok (current_cut_sg fn A renamed H events l i)
             (EL i old.bb_instructions).inst_outputs
             (EL (LENGTH pre + i) bb'.bb_instructions).inst_outputs
             (current_cut_sg fn A renamed H events l (SUC i)))
Proof
  suspend "ordinary_transport"
QED

(* Entering h from p: the output's retained PHIs are matched by the
   input's PHIs (pairing sgs at the end of the output's PHI prefix), then
   the cleanup's copies up to the input's first ordinary instruction each
   extend the pairing, which ends at the invariant's pairing at h's first
   cut past its PHIs. *)
Theorem current_cut_inv_block_entry_prefix:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME old_p /\
  current_cut_inv fn A renamed H events p (LENGTH old_p.bb_instructions)
    t t' /\
  t.vs_prev_bb = SOME p /\ t.vs_current_bb = h ==>
  ?old_h bb' pre sgs.
    lookup_block h fn.fn_blocks = SOME old_h /\
    lookup_block h fn'.fn_blocks = SOME bb' /\
    A h = current_block_annotations old_h pre /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old_h.bb_instructions /\
    phi_prefix_length bb'.bb_instructions <=
      LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) /\
    phis_rename_ok (SOME p)
      (current_cut_sg fn A renamed H events p (LENGTH old_p.bb_instructions))
      (block_insts fn h) (block_insts fn' h)
      (sgs (phi_prefix_length bb'.bb_instructions)) /\
    sgs (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions)) =
      current_cut_sg fn A renamed H events h
        (LENGTH (collect_phis old_h.bb_instructions)) /\
    (!k. phi_prefix_length bb'.bb_instructions <= k /\
         k < LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) ==>
         ((EL k bb'.bb_instructions).inst_opcode = ASSIGN \/
          (EL k bb'.bb_instructions).inst_opcode = NOP /\
          (EL k bb'.bb_instructions).inst_operands = []) /\
         copy_rename_ok (sgs k) (EL k bb'.bb_instructions) (sgs (SUC k))) /\
    !post'.
      enters_block fn' t' post' ==>
      ?post.
        enters_block fn t post /\
        post.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions) /\
        state_rel (sgs (phi_prefix_length bb'.bb_instructions)) post post' /\
        !v. current_demand fn v h
              (LENGTH (collect_phis old_h.bb_instructions)) ==>
            IS_SOME (lookup_var v post)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `?old_h. lookup_block h fn.fn_blocks = SOME old_h` by
    (fs[venomWfTheory.fn_cfg_edge_def, venomWfTheory.wf_function_def] >>
     `MEM h (venomInst$fn_labels fn)` by
       metis_tac[venomWfTheory.fn_succs_closed_def] >>
     gvs[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  suspend "prefix_structure"
QED

Theorem current_collapsed_carrier_owned_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_collapsed_carrier fn A renamed h v src ==>
  ?t. MEM (t,v,src) H
Proof
  simp[current_collapsed_carrier_def] >> rpt strip_tac >>
  irule current_carrier_copy_owned_name >> metis_tac[]
QED

Theorem current_cut_pair_owned_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_cut_pair fn A renamed H events l i n v ==>
  ?t. MEM (t,v,n) H
Proof
  simp[current_cut_pair_def] >> rpt strip_tac
  >- (gvs[arithmeticTheory.ADD_COMM] >>
      drule_all (SRULE [arithmeticTheory.ADD_COMM] current_carrier_cut_token_owned_name) >> metis_tac[]) >>
  irule current_collapsed_carrier_owned_name >> metis_tac[]
QED

Resume current_cut_pair_unique_owner[owned_history]:
  strip_tac >>
  `?t. MEM (t,v1,x') H` by metis_tac[current_cut_pair_owned_name] >>
  `?u. MEM (u,v2,x') H` by metis_tac[current_cut_pair_owned_name] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `v1 = v2` by metis_tac[current_history_name_unique] >>
  simp[listTheory.MEM_MAP] >> qexists `(t,v1,x')` >> simp[]
QED

Finalise current_cut_pair_unique_owner

Theorem current_cut_functional_alist_lookup[local]:
  !xs. (!k a b. MEM (k,a) xs /\ MEM (k,b) xs ==> a = b) ==>
    (FLOOKUP (alist_to_fmap xs) k = SOME v <=> MEM (k,v) xs)
Proof
  Induct >> simp[alistTheory.alist_to_fmap_def] >>
  gen_tac >> PairCases_on `h` >> strip_tac >>
  `!a b c. MEM (a,b) xs /\ MEM (a,c) xs ==> b = c` by metis_tac[] >>
  fs[alistTheory.ALOOKUP_def] >> Cases_on `h0 = k` >>
  simp_tac (srw_ss()) [] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_cut_sg_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb ==>
  (FLOOKUP (current_cut_sg fn A renamed H events l i) n = SOME v <=>
   current_cut_pair fn A renamed H events l i n v)
Proof
  strip_tac >> rewrite_tac[current_cut_sg_def] >>
  `!k a b.
    MEM (k,a) (FILTER (\(n,v). current_cut_pair fn A renamed H events l i n v)
      (MAP (\(t,v,n). (n,v)) H)) /\
    MEM (k,b) (FILTER (\(n,v). current_cut_pair fn A renamed H events l i n v)
      (MAP (\(t,v,n). (n,v)) H)) ==> a = b` by
    (simp[listTheory.MEM_FILTER] >> rpt strip_tac >>
     metis_tac[current_cut_pair_unique_owner]) >>
  drule current_cut_functional_alist_lookup >> disch_then (rewrite_tac o single) >>
  simp[listTheory.MEM_FILTER] >>
  metis_tac[current_cut_pair_unique_owner]
QED

Theorem current_cut_sg_exit_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\
  current_event_label ev = pred /\
  lookup_block pred fn.fn_blocks = SOME old_p /\
  current_demand fn v pred (LENGTH old_p.bb_instructions) /\
  (current_token_name H (current_event_exit_env ev v) = SOME n \/
   ?d. current_event_exit_env ev v = CurrentInserted v d /\
       current_collapsed_carrier fn A renamed d v n) ==>
  FLOOKUP (current_cut_sg fn A renamed H events pred
    (LENGTH old_p.bb_instructions)) n = SOME v
Proof
  strip_tac >>
  drule_all current_cut_sg_lookup >> disch_then (rewrite_tac o single) >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `lookup_block (current_event_label ev) fn.fn_blocks = SOME old_p` by simp[] >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH (current_event_input_block ev).bb_instructions =
    LENGTH pre + LENGTH old_p.bb_instructions` by
    (qpat_x_assum `current_edge_shape _ (current_event_input_block ev)` mp_tac >>
     simp[makeSsaCurrentFinalBlockTheory.current_edge_shape_def,
       listTheory.LIST_REL_EL_EQN]) >>
  drule current_wf_event_exit_cut >> strip_tac >>
  simp[current_cut_pair_def] >>
  qexistsl [`ev`, `pre`, `current_event_exit_rs ev`,
    `current_event_exit_env ev`] >>
  simp[makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  metis_tac[]
QED

Theorem current_cut_sg_exit_name_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\
  current_event_label ev = pred /\
  lookup_block pred fn.fn_blocks = SOME old_p /\
  current_demand fn v pred (LENGTH old_p.bb_instructions) /\
  current_token_name H (current_event_exit_env ev v) = SOME n ==>
  FLOOKUP (current_cut_sg fn A renamed H events pred
    (LENGTH old_p.bb_instructions)) n = SOME v
Proof
  strip_tac >> irule current_cut_sg_exit_lookup >> metis_tac[]
QED

Theorem current_cut_phi_slots_shape[local]:
  !slots. phi_well_formed (current_phi_slots slots) /\
    phi_pairs (current_phi_slots slots) = slots
Proof
  Induct >> simp[makeSsaCurrentEdgeTraceTheory.current_phi_slots_def,
    venomWfTheory.phi_well_formed_def, venomInstTheory.phi_pairs_def] >>
  gen_tac >> PairCases_on `h` >>
  fs[makeSsaCurrentEdgeTraceTheory.current_phi_slots_def,
    venomWfTheory.phi_well_formed_def, venomInstTheory.phi_pairs_def]
QED

Theorem current_cut_original_phi_edge_resolution:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  ALL_DISTINCT (MAP FST slots) /\ MEM (p,v) slots ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (resolve_phi p (EL k old.bb_instructions).inst_operands)
    (resolve_phi p (EL q new.bb_instructions).inst_operands)
Proof
  strip_tac >>
  drule_all current_wf_original_phi_shape >> strip_tac >>
  `?i. i < LENGTH slots /\ EL i slots = (p,v)` by metis_tac[listTheory.MEM_EL] >>
  drule_all current_wf_original_phi_pair >> strip_tac >>
  `wf_function fn /\ fn_phis_cover_preds fn` by fs[current_wf_phi_context_def] >>
  qpat_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  `old' = old` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `old' = old` SUBST_ALL_TAC >>
  `MEM old fn.fn_blocks /\ MEM (EL k old.bb_instructions) old.bb_instructions /\
   old.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecProofsTheory.lookup_block_label, listTheory.MEM_EL] >>
  `fn_cfg_edge fn p h` by
    (qpat_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[current_wf_phi_context_def] >> strip_tac >> metis_tac[]) >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_original_phi_demand >> metis_tac[]) >>
  `FLOOKUP (current_cut_sg fn A renamed H events p
     (LENGTH pred.bb_instructions)) n = SOME v` by
    (irule current_cut_sg_exit_name_lookup >> metis_tac[]) >>
  `MEM (p,n) pairs` by metis_tac[listTheory.MEM_EL, listTheory.LENGTH_MAP] >>
  qpat_x_assum `slots = phi_pairs _` kall_tac >>
  `resolve_phi p (EL k old.bb_instructions).inst_operands = SOME (Var v)` by
    (irule retpc_phi_pair_selected >>
     simp[current_cut_phi_slots_shape]) >>
  `resolve_phi p (EL q new.bb_instructions).inst_operands = SOME (Var n)` by
    (irule retpc_phi_pair_selected >>
     simp[current_cut_phi_slots_shape]) >>
  simp[op_rename_def]
QED

Theorem current_cut_inserted_phi_edge_resolution:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  fn_cfg_edge fn p h /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (SOME (Var v))
    (resolve_phi p (EL q new.bb_instructions).inst_operands)
Proof
  strip_tac >> drule_all current_wf_inserted_phi_slots >> strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `MEM h (fn_labels fn)` by
    (simp[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecProofsTheory.lookup_block_label]) >>
  `MAP FST pairs = cfg_preds_of (cfg_analyze fn) h` by
    (drule makeSsaDefsTheory.ALOOKUP_current_pred_map >> disch_tac >>
     qpat_x_assum `MAP FST pairs = _` mp_tac >> simp[]) >>
  `ALL_DISTINCT (MAP FST pairs)` by simp[cfg_analyze_preds_distinct] >>
  `MEM p (MAP FST pairs)` by
    metis_tac[makeSsaCurrentAnalysisTheory.current_cfg_edge_preds] >>
  `?n. MEM (p,n) pairs` by
    (fs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `?i. i < LENGTH pairs /\ EL i pairs = (p,n)` by metis_tac[listTheory.MEM_EL] >>
  drule_all current_wf_inserted_phi_pair >> strip_tac >>
  drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_inserted_pred_demand >> metis_tac[]) >>
  `FLOOKUP (current_cut_sg fn A renamed H events p
     (LENGTH pred.bb_instructions)) n = SOME v` by
    (irule current_cut_sg_exit_name_lookup >> metis_tac[]) >>
  `resolve_phi p (EL q new.bb_instructions).inst_operands = SOME (Var n)` by
    (irule retpc_phi_pair_selected >>
     simp[current_cut_phi_slots_shape, cfg_analyze_preds_distinct] >>
     metis_tac[]) >>
  simp[op_rename_def]
QED

Theorem current_cut_pair_precleanup_output_exclusion:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions /\
  current_cut_pair fn A renamed H events l (SUC i) n v /\
  ~MEM v (EL i old.bb_instructions).inst_outputs ==>
  ~MEM n (EL (LENGTH pre + i) new.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `?t. MEM (t,v,n) H` by metis_tac[current_cut_pair_owned_name] >>
  metis_tac[current_transport_precleanup_output_exclusion,
    arithmeticTheory.ADD_COMM]
QED

Theorem current_cut_pair_written_last_slot:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions /\
  current_cut_pair fn A renamed H events l (SUC i) n v /\
  MEM v (EL i old.bb_instructions).inst_outputs ==>
  ?k. k < LENGTH (EL i old.bb_instructions).inst_outputs /\
    EL k (EL i old.bb_instructions).inst_outputs = v /\
    ~MEM v (DROP (SUC k) (EL i old.bb_instructions).inst_outputs) /\
    EL k (EL (LENGTH pre + i) new.bb_instructions).inst_outputs = n
Proof
  strip_tac >>
  `old.bb_label = l` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  qpat_x_assum `current_cut_pair _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_cut_pair_def] >> strip_tac >>
  `old' = old` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `LENGTH pre' = LENGTH pre` by
    (qpat_x_assum `current_block_annotations _ _ = current_block_annotations _ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  `?k. k < LENGTH (EL i old.bb_instructions).inst_outputs /\
    EL k (EL i old.bb_instructions).inst_outputs = v /\
    ~MEM v (DROP (SUC k) (EL i old.bb_instructions).inst_outputs) /\
    E v = CurrentOriginal old.bb_label i k` by
    (irule current_source_cut_last_output >> metis_tac[]) >>
  `current_token_name H (CurrentOriginal old.bb_label i k) =
    SOME (EL k (EL (i + LENGTH pre) new.bb_instructions).inst_outputs)` by
    (irule current_precleanup_original_output_slot >> metis_tac[]) >>
  qexists_tac `k` >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem current_cut_pair_unaffected_predecessor:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i < LENGTH old.bb_instructions /\
  ~MEM v (EL i old.bb_instructions).inst_outputs /\
  current_cut_pair fn A renamed H events l (SUC i) n v ==>
  current_cut_pair fn A renamed H events l i n v
Proof
  strip_tac >>
  qpat_x_assum `current_cut_pair _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_cut_pair_def] >> strip_tac >>
  `old' = old` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `old' = old` SUBST_ALL_TAC >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev` by metis_tac[listTheory.EVERY_MEM] >>
  `LENGTH pre + i <= LENGTH (current_event_input_block ev).bb_instructions` by
    (drule current_transport_source_cut_bound >> decide_tac) >>
  drule_all current_wf_event_source_cut_exists >> strip_tac >>
  `old.bb_label = l` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `E' v = E v` by
    (irule current_transport_source_cut_unaffected >> metis_tac[]) >>
  `current_demand fn v l i` by
    (irule (cj 3 current_demand_rules) >>
     simp[venomInstTheory.inst_defs_def] >> metis_tac[]) >>
  simp[current_cut_pair_def] >>
  qexistsl_tac [`ev`, `pre`, `rs'`, `E'`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem current_cut_last_output_slots:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i < LENGTH old.bb_instructions ==>
  current_last_output_slots (current_cut_sg fn A renamed H events l i)
    (EL i old.bb_instructions).inst_outputs
    (EL (LENGTH pre + i) new.bb_instructions).inst_outputs
    (current_cut_sg fn A renamed H events l (SUC i))
Proof
  strip_tac >> rewrite_tac[current_last_output_slots_def] >>
  conj_tac
  >- (drule_all current_transport_precleanup_output_names >>
      metis_tac[LIST_REL_LENGTH, arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (drule_all current_wf_phi_context_ssa_form >>
      rewrite_tac[venomWfTheory.ssa_form_def] >> strip_tac >>
      `MEM new renamed` by metis_tac[lookup_block_MEM] >>
      `LENGTH pre + i < LENGTH new.bb_instructions` by
        (drule_all current_wf_precleanup_output_alignment >>
         disch_then (mp_tac o Q.AP_TERM `LENGTH`) >>
         `LENGTH (current_original_annotations old.bb_label 0 old.bb_instructions) =
           LENGTH old.bb_instructions` by
           metis_tac[current_original_annotations_owners, LIST_REL_LENGTH] >>
         simp[current_block_annotations_def, current_inserted_annotations_def]) >>
      `MEM (EL (LENGTH pre + i) new.bb_instructions)
        (fn_insts (fn with fn_blocks := renamed))` by
        (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
         qexists_tac `new` >> simp[] >>
         metis_tac[EL_MEM, arithmeticTheory.ADD_COMM]) >>
      `?xs ys. fn_insts (fn with fn_blocks := renamed) =
        xs ++ EL (LENGTH pre + i) new.bb_instructions :: ys` by
        metis_tac[MEM_SPLIT] >>
      gvs[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  rpt strip_tac >>
  `current_cut_pair fn A renamed H events l (SUC i) n v` by
    metis_tac[current_cut_sg_lookup] >>
  Cases_on `MEM v (EL i old.bb_instructions).inst_outputs`
  >- (disj1_tac >> drule_all current_cut_pair_written_last_slot >> metis_tac[]) >>
  disj2_tac >> simp[] >> conj_tac
  >- (drule_all current_cut_pair_precleanup_output_exclusion >>
      simp[arithmeticTheory.ADD_COMM]) >>
  drule_all current_cut_pair_unaffected_predecessor >>
  metis_tac[current_cut_sg_lookup]
QED

Theorem current_cut_rename_operands_rel[local]:
  !ops. (!v. MEM (Var v) ops ==> FLOOKUP sg (latest_current_name rs v) = SOME v) ==>
    LIST_REL (op_rename sg) ops (rename_current_operands rs ops)
Proof
  Induct >> simp[makeSsaDefsTheory.rename_current_operands_def] >>
  Cases_on `h` >> simp[makeSsaDefsTheory.rename_current_operands_def,
    op_rename_def] >> metis_tac[]
QED

Theorem current_cut_ordinary_operand_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\ current_event_label ev = l /\
  lookup_block l fn.fn_blocks = SOME old /\
  A l = current_block_annotations old pre /\
  current_source_cut A ev (LENGTH pre + i) rs E /\
  i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL i old.bb_instructions).inst_operands ==>
  FLOOKUP (current_cut_sg fn A renamed H events l i)
    (latest_current_name rs v) = SOME v
Proof
  strip_tac >>
  `current_demand fn v l i /\ MEM v (FLAT (MAP block_ir_vars fn.fn_blocks))` by
    metis_tac[current_wf_ordinary_demand] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `current_token_name H (E v) = SOME (latest_current_name rs v)` by
    metis_tac[current_wf_precleanup_cut_name] >>
  drule_all current_cut_sg_lookup >> disch_then (rewrite_tac o single) >>
  simp[current_cut_pair_def] >>
  qexistsl_tac [`ev`, `pre`, `rs`, `E`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  metis_tac[current_wf_nonphi_after_collect, arithmeticTheory.ADD_COMM]
QED

Theorem current_cut_ordinary_operands_rel:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\ current_event_label ev = l /\
  lookup_block l fn.fn_blocks = SOME old /\
  A l = current_block_annotations old pre /\
  current_source_cut A ev (LENGTH pre + i) rs E /\
  i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode <> PHI ==>
  LIST_REL (op_rename (current_cut_sg fn A renamed H events l i))
    (EL i old.bb_instructions).inst_operands
    (rename_current_operands rs (EL i old.bb_instructions).inst_operands)
Proof
  strip_tac >> irule current_cut_rename_operands_rel >>
  metis_tac[current_cut_ordinary_operand_lookup]
QED

Theorem current_cut_pair_cleanup_output_exclusion:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions /\
  LENGTH pre + i < LENGTH new.bb_instructions /\
  (EL (LENGTH pre + i) new.bb_instructions).inst_opcode <> PHI /\
  current_cut_pair fn A renamed H events l (SUC i) n v /\
  ~MEM v (EL i old.bb_instructions).inst_outputs ==>
  ~MEM n (EL (LENGTH pre + i)
    (simplify_current_phi_block new).bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM new renamed` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  drule_all current_transport_cleanup_ordinary_outputs >>
  disch_then (rewrite_tac o single) >>
  metis_tac[current_cut_pair_precleanup_output_exclusion]
QED

Theorem current_cut_sg_owned_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  FLOOKUP (current_cut_sg fn A renamed H events l i) z = SOME x ==>
  ?t. MEM (t,x,z) H
Proof
  strip_tac >> drule_all current_cut_sg_lookup >> strip_tac >>
  irule current_cut_pair_owned_name >> metis_tac[]
QED

Theorem current_cut_cleaned_suffix_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k <= phi_prefix_length new.bb_instructions ==>
  (!z x. current_prefix_back
    (TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions))
    (current_cut_sg fn A renamed H events l i) z x ==> ?t. MEM (t,x,z) H) /\
  current_prefix_functional (current_prefix_back
    (TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions))
    (current_cut_sg fn A renamed H events l i))
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  irule current_prefix_cleaned_suffix_owner >> metis_tac[current_cut_sg_owned_name]
QED

Theorem current_cut_actual_suffix_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ A h = current_block_annotations old pre /\
  lookup_block h (simplify_current_phis_if enabled renamed) = SOME bb /\
  phi_prefix_length bb.bb_instructions <= k /\
  k <= LENGTH pre + LENGTH (collect_phis old.bb_instructions) ==>
  (!z x. current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - k)
      (DROP k bb.bb_instructions))
    (current_cut_sg fn A renamed H events h (LENGTH (collect_phis old.bb_instructions)))
    z x ==> ?t. MEM (t,x,z) H) /\
  current_prefix_functional (current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - k)
      (DROP k bb.bb_instructions))
    (current_cut_sg fn A renamed H events h (LENGTH (collect_phis old.bb_instructions))))
Proof
  strip_tac >>
  `phi_prefix_length new.bb_instructions =
    LENGTH pre + LENGTH (collect_phis old.bb_instructions)` by
    metis_tac[current_prefix_actual_endpoint] >>
  fs[current_cleanup_if_lookup] >> Cases_on `enabled` >> gvs[]
  >- (qpat_assum `phi_prefix_length bb'.bb_instructions = _`
        (fn th => rewrite_tac[GSYM th]) >>
      irule current_cut_cleaned_suffix_owner >> metis_tac[]) >>
  `k = LENGTH pre + LENGTH (collect_phis old.bb_instructions)` by decide_tac >>
  gvs[current_prefix_back_def] >>
  conj_tac >- metis_tac[current_cut_sg_owned_name] >>
  simp[current_prefix_functional_def, current_prefix_back_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem current_cut_original_phi_cleanup_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  ALL_DISTINCT (MAP FST slots) /\ MEM (p,v) slots /\
  (EL k old.bb_instructions).inst_outputs = [x] /\
  (EL q new.bb_instructions).inst_outputs = [y] /\
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) x old.bb_instructions)
    (phi_eff (SOME p) y (simplify_current_phi_block new).bb_instructions)
Proof
  strip_tac >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  `phi_eff (SOME p) x old.bb_instructions =
    resolve_phi p (EL k old.bb_instructions).inst_operands` by
    metis_tac[current_retained_original_at_effect] >>
  `phi_eff (SOME p) y (simplify_current_phi_block new).bb_instructions =
    resolve_phi p (EL q new.bb_instructions).inst_operands` by
    metis_tac[current_retained_context_effect] >>
  simp[] >> irule current_cut_original_phi_edge_resolution >> metis_tac[]
QED

Theorem current_cut_original_phi_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  ALL_DISTINCT (MAP FST slots) /\ MEM (p,v) slots /\
  (EL k old.bb_instructions).inst_outputs = [x] /\
  (EL q new.bb_instructions).inst_outputs = [y] ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) x old.bb_instructions)
    (phi_eff (SOME p) y new.bb_instructions)
Proof
  strip_tac >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  `phi_eff (SOME p) x old.bb_instructions =
    resolve_phi p (EL k old.bb_instructions).inst_operands` by
    metis_tac[current_retained_original_at_effect] >>
  `phi_eff (SOME p) y new.bb_instructions =
    resolve_phi p (EL q new.bb_instructions).inst_operands` by
    metis_tac[current_retained_context_effect] >>
  simp[] >> irule current_cut_original_phi_edge_resolution >> metis_tac[]
QED

Theorem current_cut_inserted_phi_cleanup_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  (EL q new.bb_instructions).inst_outputs = [y] /\
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) v old.bb_instructions)
    (phi_eff (SOME p) y (simplify_current_phi_block new).bb_instructions)
Proof
  strip_tac >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[]) >>
  `phi_eff (SOME p) v old.bb_instructions = SOME (Var v)` by
    (irule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
     fs[listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `phi_eff (SOME p) y (simplify_current_phi_block new).bb_instructions =
    resolve_phi p (EL q new.bb_instructions).inst_operands` by
    metis_tac[current_retained_context_effect] >>
  simp[] >> irule current_cut_inserted_phi_edge_resolution >> metis_tac[]
QED

Theorem current_cut_inserted_phi_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  (EL q new.bb_instructions).inst_outputs = [y] ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) v old.bb_instructions)
    (phi_eff (SOME p) y new.bb_instructions)
Proof
  strip_tac >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[]) >>
  `phi_eff (SOME p) v old.bb_instructions = SOME (Var v)` by
    (irule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
     fs[listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `phi_eff (SOME p) y new.bb_instructions =
    resolve_phi p (EL q new.bb_instructions).inst_operands` by
    metis_tac[current_retained_context_effect] >>
  simp[] >> irule current_cut_inserted_phi_edge_resolution >> metis_tac[]
QED

Resume current_cut_inv_ordinary_step[ordinary_transport]:
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `?eb. entry_block fn = SOME eb` by
    (drule venomExecPropsTheory.lookup_block_MEM >>
     Cases_on `fn.fn_blocks` >> simp[venomInstTheory.entry_block_def]) >>
  `?new. lookup_block l renamed = SOME new` by
    (drule current_wf_precleanup_labels >> strip_tac >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) renamed)` by
       fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
     `MEM l (MAP (\bb. bb.bb_label) renamed)` by
       metis_tac[venomExecPropsTheory.lookup_block_MEM,
         venomExecProofsTheory.lookup_block_label, listTheory.MEM_MAP] >>
     fs[listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  `MEM new renamed /\ new.bb_label = l` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecProofsTheory.lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `lookup_block (current_event_label ev) fn.fn_blocks = SOME old` by simp[] >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH pre = LENGTH pre'` by
    (`LENGTH (current_block_annotations old pre) =
      LENGTH (current_block_annotations old pre')` by metis_tac[] >>
     qpat_x_assum `LENGTH (current_block_annotations _ _) = _` mp_tac >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  `bb_well_formed old` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomWfTheory.wf_function_def] >>
  `(EL i old.bb_instructions).inst_opcode <> PHI` by
    (fs[venomWfTheory.bb_well_formed_def] >>
     metis_tac[current_phi_index_before_prefix, arithmeticTheory.NOT_LESS]) >>
  drule_all current_wf_edge_shape_ordinary_index >> strip_tac >>
  `?rs E. current_source_cut A ev (LENGTH pre + i) rs E` by
    metis_tac[current_wf_event_source_cut_exists, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `LENGTH pre + i < LENGTH (current_event_input_block ev).bb_instructions` by simp[] >>
  drule_all current_wf_event_source_cut_step >> strip_tac >>
  `LIST_REL (op_rename (current_cut_sg fn A renamed H events l i))
     (EL i old.bb_instructions).inst_operands
     (rename_current_operands rs (EL i old.bb_instructions).inst_operands)` by
    (irule current_cut_ordinary_operands_rel >> metis_tac[]) >>
  drule makeSsaCurrentRenameTraceTheory.current_inst_trace_projection >> strip_tac >>
  drule rename_current_inst_signature >> strip_tac >>
  drule makeSsaCurrentRenameTraceTheory.current_inst_trace_operands >> strip_tac >>
  `inst_pair (current_cut_sg fn A renamed H events l i)
     (EL i old.bb_instructions)
     (EL (LENGTH pre + i) (current_event_renamed_block ev).bb_instructions)` by
    (gvs[inst_pair_def, arithmeticTheory.ADD_COMM]) >>
  suspend "ordinary_cleanup"
QED

Resume current_cut_inv_ordinary_step[ordinary_cleanup]:
  `LENGTH (current_event_renamed_block ev).bb_instructions =
     LENGTH pre + LENGTH old.bb_instructions` by
    (`LENGTH (current_event_renamed_block ev).bb_instructions =
       LENGTH (current_event_input_block ev).bb_instructions` by
       (qpat_x_assum `current_event_trace A H ev` mp_tac >>
        PairCases_on `ev` >>
        simp[makeSsaCurrentTreeTraceTheory.current_event_trace_def,
          makeSsaCurrentFinalBlockTheory.current_event_renamed_block_def,
          current_event_input_block_def] >>
        metis_tac[current_local_trace_lengths]) >>
     fs[makeSsaCurrentFinalBlockTheory.current_edge_shape_def,
        listTheory.LIST_REL_EL_EQN]) >>
  `EL (LENGTH pre + i) new.bb_instructions =
   EL (LENGTH pre + i) (current_event_renamed_block ev).bb_instructions` by
    (fs[makeSsaCurrentFinalBlockTheory.current_edge_shape_def,
        listTheory.LIST_REL_EL_EQN, inst_pair_def] >> metis_tac[]) >>
  suspend "ordinary_final_lookup"
QED

Resume current_cut_inv_ordinary_step[ordinary_final_lookup]:
  `LENGTH new.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
   (EL (LENGTH pre + i) new.bb_instructions).inst_opcode <> PHI` by
    (fs[makeSsaCurrentFinalBlockTheory.current_edge_shape_def,
        listTheory.LIST_REL_EL_EQN, inst_pair_def] >> metis_tac[]) >>
  drule_all current_wf_phi_context_cleanup_split >> strip_tac >>
  qpat_x_assum `new.bb_instructions = _` (fn th => assume_tac th) >>
  rename1 `new.bb_instructions = bp ++ bt` >>
  `LENGTH bp <= LENGTH pre + i` by
    (Cases_on `LENGTH pre + i < LENGTH bp` >> simp[] >>
     `MEM (EL (LENGTH pre + i) bp) bp` by metis_tac[listTheory.EL_MEM] >>
     fs[listTheory.EL_APPEND_EQN, listTheory.EVERY_MEM]) >>
  `bt <> [] /\ (HD bt).inst_opcode <> PHI` by
    (Cases_on `bt` >> fs[listTheory.EVERY_DEF] >> gvs[]) >>
  `LENGTH pre + i - LENGTH bp < LENGTH bt` by fs[] >>
  `?bb'. lookup_block l
     (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed) = SOME bb' /\
     LENGTH bb'.bb_instructions = LENGTH new.bb_instructions /\
     current_inst_no_id (EL (LENGTH bp + (LENGTH pre + i - LENGTH bp)) bb'.bb_instructions) =
     current_inst_no_id (EL (LENGTH pre + i - LENGTH bp) bt)` by
    (irule makeSsaCurrentCleanupShapeTheory.current_cleanup_if_ordinary_index >>
     metis_tac[]) >>
  `current_inst_no_id (EL (LENGTH pre + i) bb'.bb_instructions) =
   current_inst_no_id (EL (LENGTH pre + i) new.bb_instructions)` by
    (gvs[listTheory.EL_APPEND_EQN, arithmeticTheory.ADD_COMM]) >>
  `phi_prefix_length new.bb_instructions = LENGTH bp` by
    (simp[phi_prefix_length_prepend] >>
     Cases_on `bt` >> fs[venomExecSemanticsTheory.phi_prefix_length_def]) >>
  qpat_assum `lookup_block l renamed = SOME new`
    (mp_then Any mp_tac simplify_current_phis_if_lookup_shape) >>
  disch_then (qspec_then `blocks_have_leading_phi fn.fn_blocks` mp_tac) >>
  strip_tac >>
  `inst_pair (current_cut_sg fn A renamed H events l i)
     (EL i old.bb_instructions) (EL (LENGTH pre + i) bb'.bb_instructions)` by
    (gvs[inst_pair_def,
       makeSsaCurrentCleanupShapeTheory.current_inst_no_id_def,
       venomInstTheory.instruction_component_equality,
       arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  qexists_tac `bb'` >>
  simp[] >>
  suspend "ordinary_runtime"
QED

Resume current_cut_inv_ordinary_step[ordinary_runtime]:
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[venomWfTheory.fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `current_last_output_slots (current_cut_sg fn A renamed H events l i)
    (EL i old.bb_instructions).inst_outputs
    (EL (LENGTH pre + i) new.bb_instructions).inst_outputs
    (current_cut_sg fn A renamed H events l (SUC i))` by
    (irule current_cut_last_output_slots >> metis_tac[]) >>
  `current_last_output_slots (current_cut_sg fn A renamed H events l i)
    (EL i old.bb_instructions).inst_outputs
    (EL (LENGTH pre + i) bb'.bb_instructions).inst_outputs
    (current_cut_sg fn A renamed H events l (SUC i))` by
    (gvs[makeSsaCurrentCleanupShapeTheory.current_inst_no_id_def,
      venomInstTheory.instruction_component_equality]) >>
  drule current_last_output_slots_out_rename >> strip_tac >>
  gvs[current_cut_inv_def, arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (rpt strip_tac >>
      `(EL i old.bb_instructions).inst_opcode <> INVOKE` by fs[inst_pair_def] >>
      drule_all current_exec_step_noninvoke_ok_pair >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >>
      metis_tac[current_demand_step_defined]) >>
  conj_tac
  >- (rpt strip_tac >>
      `(EL i old.bb_instructions).inst_opcode <> INVOKE` by fs[inst_pair_def] >>
      drule_all current_exec_step_noninvoke_intret_pair >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexists_tac `t` >> fs[stateFrameTheory.execution_frame_def,
        venomStateTheory.venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >>
      `(EL i old.bb_instructions).inst_opcode <> INVOKE` by fs[inst_pair_def] >>
      drule_all current_exec_step_noninvoke_halt_pair >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexists_tac `t` >> fs[stateFrameTheory.execution_frame_def,
        venomStateTheory.venom_state_component_equality]) >>
  rpt strip_tac >>
  `execution_frame e' = execution_frame e` by
    fs[stateFrameTheory.execution_frame_def,
      venomStateTheory.venom_state_component_equality] >>
  drule_all current_return_bind_last_slots >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  metis_tac[current_demand_return_defined]
QED

Finalise current_cut_inv_ordinary_step

Resume current_cut_inv_block_entry_prefix[prefix_structure]:
  `?eb. entry_block fn = SOME eb` by
    (drule venomExecPropsTheory.lookup_block_MEM >>
     Cases_on `fn.fn_blocks` >> simp[venomInstTheory.entry_block_def]) >>
  `?new. lookup_block h renamed = SOME new` by
    (drule current_wf_precleanup_labels >> strip_tac >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) renamed)` by
       fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
     `MEM h (MAP (\bb. bb.bb_label) renamed)` by
       metis_tac[venomExecPropsTheory.lookup_block_MEM,
         venomExecProofsTheory.lookup_block_label, listTheory.MEM_MAP] >>
     fs[listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  `MEM new renamed /\ new.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecProofsTheory.lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `lookup_block (current_event_label ev) fn.fn_blocks = SOME old_h` by simp[] >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `A h = current_block_annotations old_h pre` by metis_tac[] >>
  `phi_prefix_length new.bb_instructions =
    LENGTH pre + LENGTH (collect_phis old_h.bb_instructions)` by
    (irule current_prefix_actual_endpoint >> metis_tac[]) >>
  `LENGTH new.bb_instructions = LENGTH pre + LENGTH old_h.bb_instructions` by
    (drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
     `LENGTH pre = LENGTH pre'` by
       (qpat_x_assum `A h = current_block_annotations old_h pre` mp_tac >>
        simp[current_block_annotations_def, current_inserted_annotations_def] >>
        disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     metis_tac[listTheory.LENGTH_MAP, listTheory.LENGTH_APPEND]) >>
  qpat_assum `lookup_block h renamed = SOME new`
    (mp_then Any mp_tac simplify_current_phis_if_lookup_shape) >>
  disch_then (qspec_then `blocks_have_leading_phi fn.fn_blocks` mp_tac) >>
  strip_tac >>
  qexistsl_tac [`old_h`, `b'`, `pre`] >>
  simp[] >>
  suspend "prefix_maps"
QED

Resume current_cut_inv_block_entry_prefix[prefix_maps]:
  qexists_tac `\k. current_prefix_map
    (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) - k)
      (DROP k b'.bb_instructions))
    (current_cut_sg fn A renamed H events h
      (LENGTH (collect_phis old_h.bb_instructions)))` >>
  simp[current_prefix_map_nil] >>
  `!k. phi_prefix_length b'.bb_instructions <= k /\
       k <= LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) ==>
       current_prefix_functional (current_prefix_back
         (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) - k)
           (DROP k b'.bb_instructions))
         (current_cut_sg fn A renamed H events h
           (LENGTH (collect_phis old_h.bb_instructions))))` by
    (rpt strip_tac >> irule (cj 2 current_cut_actual_suffix_owner) >> metis_tac[]) >>
  conj_asm1_tac >- suspend "prefix_phi_relation" >>
  conj_tac >- suspend "prefix_copy_chain" >>
  suspend "prefix_enter_runtime"
QED

Resume current_cut_inv_block_entry_prefix[prefix_copy_chain]:
  `!k. phi_prefix_length b'.bb_instructions <= k /\
       k < LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) ==>
       current_copy_payload (EL k b'.bb_instructions)` by
    (rpt strip_tac >> irule current_prefix_actual_payload >> metis_tac[]) >>
  `LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) <=
    LENGTH b'.bb_instructions` by
    (qspec_then `new.bb_instructions` mp_tac
      venomExecProofsTheory.phi_prefix_length_le >> simp[]) >>
  `!k. phi_prefix_length b'.bb_instructions <= k /\
       k < LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) ==>
       copy_rename_ok
         (current_prefix_map
           (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) - k)
             (DROP k b'.bb_instructions))
           (current_cut_sg fn A renamed H events h
             (LENGTH (collect_phis old_h.bb_instructions))))
         (EL k b'.bb_instructions)
         (current_prefix_map
           (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) - SUC k)
             (DROP (SUC k) b'.bb_instructions))
           (current_cut_sg fn A renamed H events h
             (LENGTH (collect_phis old_h.bb_instructions))))` by
    (rpt strip_tac >> irule (cj 2 current_prefix_map_chain) >>
     conj_tac >- simp[] >> reverse conj_tac >- simp[] >>
     qexists_tac `phi_prefix_length b'.bb_instructions` >>
     gvs[current_copy_payload_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `!k. _ ==> current_copy_payload _` drule_all >>
      simp[current_copy_payload_def] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Resume current_cut_inv_block_entry_prefix[prefix_enter_runtime]:
  `state_rel (current_cut_sg fn A renamed H events p
     (LENGTH old_p.bb_instructions)) t t' /\
   (!v. current_demand fn v p (LENGTH old_p.bb_instructions) ==>
     IS_SOME (lookup_var v t))` by fs[current_cut_inv_def] >>
  `?raw. eval_phis t old_h.bb_instructions = OK raw` by
    (irule current_source_phi_entry_success >> metis_tac[]) >>
  rpt strip_tac >>
  fs[contextCodegenRelTheory.enters_block_def] >>
  `t'.vs_current_bb = h /\ t'.vs_prev_bb = SOME p` by fs[state_rel_def] >>
  `bb = b'` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  simp[GSYM current_prefix_collect_length] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `IS_SOME (lookup_var v raw)` by
        (irule current_source_phi_post_defined >> metis_tac[]) >>
      fs[lookup_var_def]) >>
  qmatch_goalsub_abbrev_tac `state_rel sg` >>
  `state_rel sg raw s_phi` by
    (fs[block_insts_def, Abbr `sg`, GSYM current_prefix_collect_length] >>
     gvs[] >> drule_all current_phi_batch_state_rel >> simp[]) >>
  fs[state_rel_def]
QED


Theorem current_cut_sg_unaffected_edge_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  lookup_block h fn.fn_blocks = SOME dest /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  ~current_actual_inserted fn v h /\ current_phi_cut_clear fn v h /\
  current_demand fn v h (LENGTH (collect_phis dest.bb_instructions)) /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs) /\
  (current_token_name H (current_event_entry_env hev v) = SOME n \/
   ?d. current_event_entry_env hev v = CurrentInserted v d /\
       current_collapsed_carrier fn A renamed d v n) ==>
  FLOOKUP (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)) n = SOME v
Proof
  strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_demand_edge_no_phi_defs >>
     simp[] >> qexistsl_tac [`dest`, `h`] >>
     fs[makeSsaCurrentLastSiteTheory.current_phi_cut_clear_def]) >>
  `current_event_exit_env pev v = current_event_entry_env hev v` by
    (irule current_edge_unaffected_env >> metis_tac[]) >>
  irule current_cut_sg_exit_lookup >> metis_tac[]
QED

Theorem current_cut_prefix_back_demand:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_prefix_back xs (current_cut_sg fn A renamed H events h i) z x ==>
  current_demand fn x h i
Proof
  strip_tac >> drule current_prefix_back_range >> strip_tac >>
  drule_all current_cut_sg_lookup >> strip_tac >>
  fs[current_cut_pair_def]
QED

Definition current_cut_semantic_endpoint_def:
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x <=>
    (?k q slots v.
      current_wf_original_phi_at fn A renamed h k q slots /\
      ALL_DISTINCT (MAP FST slots) /\ MEM (p,v) slots /\
      (EL k old.bb_instructions).inst_outputs = [x] /\
      (EL q new.bb_instructions).inst_outputs = [z] /\
      simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions) \/
    (?q. current_wf_inserted_phi_at A renamed h q x /\
      (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
        ~MEM x di.inst_outputs) /\
      (EL q new.bb_instructions).inst_outputs = [z] /\
      simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions) \/
    (?u. EVERY (\j. ~MEM z j.inst_outputs)
        (collect_phis (simplify_current_phi_block new).bb_instructions) /\
      phi_eff (SOME p) x old.bb_instructions = SOME (Var u) /\
      FLOOKUP (current_cut_sg fn A renamed H events p
        (LENGTH pred.bb_instructions)) z = SOME u)
End

Theorem current_cut_semantic_endpoint_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) x old.bb_instructions)
    (phi_eff (SOME p) z (simplify_current_phi_block new).bb_instructions)
Proof
  pure_rewrite_tac[current_cut_semantic_endpoint_def] >> strip_tac
  >- (irule current_cut_original_phi_cleanup_effect >> metis_tac[])
  >- (irule current_cut_inserted_phi_cleanup_effect >> metis_tac[]) >>
  drule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
  disch_then (qspec_then `SOME p` assume_tac) >> simp[op_rename_def]
QED

Theorem current_cut_phi_eff_clear:
  lookup_block h fn.fn_blocks = SOME old /\ current_phi_cut_clear fn x h ==>
  phi_eff prev x old.bb_instructions = SOME (Var x)
Proof
  strip_tac >>
  `!xs n. n < LENGTH (collect_phis xs) ==>
    EL n (collect_phis xs) = EL n xs` by
    (Induct >> simp[livenessDefsTheory.collect_phis_def] >>
     gen_tac >> Cases_on `h'.inst_opcode = PHI` >> simp[] >>
     Cases_on `n` >> simp[]) >>
  irule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
  simp[listTheory.EVERY_EL] >> rpt strip_tac >>
  `EL n (collect_phis old.bb_instructions) = EL n old.bb_instructions` by metis_tac[] >>
  fs[makeSsaCurrentLastSiteTheory.current_phi_cut_clear_def,
    venomInstTheory.inst_defs_def] >> metis_tac[]
QED

Theorem current_cut_original_slots_cover[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  fn_cfg_edge fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  current_wf_original_phi_at fn A renamed h j r slots ==>
  ALL_DISTINCT (MAP FST slots) /\ ?u. MEM (p,u) slots
Proof
  strip_tac >>
  qpat_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = current_phi_slots _` kall_tac) >>
  gvs[] >>
  `MEM old fn.fn_blocks /\ MEM (EL j old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, MEM_EL] >>
  qpat_x_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
  fs[fn_phis_cover_preds_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[lookup_block_label]
QED

Theorem current_cut_retained_original_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  current_wf_original_phi_at fn A renamed h j r slots /\
  MEM z (EL r new.bb_instructions).inst_outputs /\ MEM (t,x,z) H ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\
   ir_supply_inst_ok s /\ fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `j < LENGTH old.bb_instructions /\
   (EL j old.bb_instructions).inst_opcode = PHI` by
    (gvs[current_wf_original_phi_at_def]) >>
  `inst_wf (EL j old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `?v. (EL j old.bb_instructions).inst_outputs = [v]` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  drule_all current_wf_original_phi_output_length >> strip_tac >>
  `(EL r new.bb_instructions).inst_outputs = [z]` by
    (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `0 < LENGTH (EL j old.bb_instructions).inst_outputs` by simp[] >>
  drule_all current_wf_original_phi_output >> strip_tac >> gvs[] >>
  rename1 `current_token_name H (CurrentOriginal h j 0) = SOME z` >>
  `MEM (CurrentOriginal h j 0,v,z) H` by
    (irule current_history_owned_name_member >> simp[] >> metis_tac[]) >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `v = x` by metis_tac[current_history_name_unique] >> gvs[] >>
  drule_all current_cut_original_slots_cover >> strip_tac >>
  `simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions` by
    metis_tac[current_wf_original_phi_retained] >>
  simp[current_cut_semantic_endpoint_def] >> disj1_tac >>
  qexistsl_tac [`j`, `r`, `slots`, `u`] >> simp[]
QED

Theorem current_cut_prefix_retained_original_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  current_wf_original_phi_at fn A renamed h j r slots /\
  MEM z (EL r new.bb_instructions).inst_outputs /\
  A h = current_block_annotations old pre /\
  lookup_block h (simplify_current_phis_if enabled renamed) = SOME bb /\
  phi_prefix_length bb.bb_instructions <= k /\
  k <= LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
  current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - k)
      (DROP k bb.bb_instructions))
    (current_cut_sg fn A renamed H events h (LENGTH (collect_phis old.bb_instructions)))
    z x ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >>
  drule_all (cj 1 current_cut_actual_suffix_owner) >>
  strip_tac >>
  irule current_cut_retained_original_endpoint >> metis_tac[]
QED

Theorem current_cut_clear_edge_env:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  ~current_actual_inserted fn v h /\ current_phi_cut_clear fn v h /\
  lookup_block h fn.fn_blocks = SOME old /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) ==>
  current_event_exit_env pev v = current_event_entry_env hev v
Proof
  strip_tac >>
  Cases_on `?pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))`
  >- (irule current_phi_operand_demand_edge_env >> metis_tac[]) >>
  irule current_nonphi_demand_edge_env >> metis_tac[]
QED

Theorem current_cut_reaching_external_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  ~current_actual_inserted fn x h /\ current_phi_cut_clear fn x h /\
  current_demand fn x h (LENGTH (collect_phis old.bb_instructions)) /\
  (current_token_name H (current_event_entry_env hev x) = SOME z \/
   ?d. current_event_entry_env hev x = CurrentInserted x d /\
     current_collapsed_carrier fn A renamed d x z) /\
  EVERY (\j. ~MEM z j.inst_outputs)
    (collect_phis (simplify_current_phi_block new).bb_instructions) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `current_demand fn x p (LENGTH pred.bb_instructions)` by
    (irule current_demand_edge_no_phi_defs >>
     fs[makeSsaCurrentLastSiteTheory.current_phi_cut_clear_def] >>
     qexistsl [`old`, `h`] >> metis_tac[]) >>
  `current_event_exit_env pev x = current_event_entry_env hev x` by
    (irule current_cut_clear_edge_env >> metis_tac[]) >>
  `FLOOKUP (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)) z = SOME x` by
    (irule current_cut_sg_exit_lookup >> metis_tac[]) >>
  `phi_eff (SOME p) x old.bb_instructions = SOME (Var x)` by
    metis_tac[current_cut_phi_eff_clear] >>
  simp[current_cut_semantic_endpoint_def] >>
  disj2_tac >> disj2_tac >> qexists `x` >> simp[]
QED

Theorem current_cut_nonself_slot_values[local]:
  !pairs out. current_phi_values
    (remove_current_phi_self out (current_phi_slots pairs)) =
    SOME (MAP SND (FILTER (\a. SND a <> out) pairs))
Proof
  Induct >> simp[makeSsaCurrentEdgeTraceTheory.current_phi_slots_def,
    makeSsaDefsTheory.remove_current_phi_self_def,
    makeSsaDefsTheory.current_phi_values_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[makeSsaCurrentEdgeTraceTheory.current_phi_slots_def,
    makeSsaDefsTheory.remove_current_phi_self_def,
    makeSsaDefsTheory.current_phi_values_def] >>
  Cases_on `h1 = out` >>
  fs[makeSsaCurrentEdgeTraceTheory.current_phi_slots_def,
    makeSsaDefsTheory.current_phi_values_def]
QED

Theorem current_cut_collapsed_slot_cases[local]:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots pairs /\
  simplify_current_phi inst =
    inst with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
  MEM (p,n) pairs ==> n = out \/ n = src
Proof
  strip_tac >>
  gvs[makeSsaDefsTheory.simplify_current_phi_def,
    makeSsaDefsTheory.keep_current_phi_vars_def, AllCaseEqs()] >>
  gvs[makeSsaDefsTheory.simplify_current_phi_raw_def,
    makeSsaDefsTheory.current_phi_output_def,
    current_cut_nonself_slot_values, AllCaseEqs()] >>
  gvs[venomInstTheory.instruction_component_equality] >>
  Cases_on `n = out` >> simp[] >>
  `MEM n (MAP SND (FILTER (\a. SND a <> out) pairs))` by
    (simp[listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
     qexists_tac `(p,n)` >> simp[]) >>
  gvs[listTheory.EVERY_MEM]
QED

Theorem current_cut_collapsed_inserted_edge_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var src]|> ==>
  FLOOKUP (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)) src = SOME v
Proof
  strip_tac >> drule_all current_wf_inserted_phi_slots >> strip_tac >>
  drule_all current_wf_inserted_phi_output >> strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `MEM h (fn_labels fn)` by
    (simp[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecProofsTheory.lookup_block_label]) >>
  `MAP FST pairs = cfg_preds_of (cfg_analyze fn) h` by
    (drule makeSsaDefsTheory.ALOOKUP_current_pred_map >> disch_tac >>
     qpat_x_assum `MAP FST pairs = _` mp_tac >> simp[]) >>
  `MEM p (MAP FST pairs)` by
    metis_tac[makeSsaCurrentAnalysisTheory.current_cfg_edge_preds] >>
  `?n. MEM (p,n) pairs` by
    (fs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `?i. i < LENGTH pairs /\ EL i pairs = (p,n)` by metis_tac[listTheory.MEM_EL] >>
  drule_all current_wf_inserted_phi_pair >> strip_tac >>
  drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_inserted_pred_demand >> metis_tac[]) >>
  `(EL q new.bb_instructions).inst_opcode = PHI` by
    fs[current_wf_inserted_phi_at_def] >>
  `n = out \/ n = src` by
    (irule current_cut_collapsed_slot_cases >> metis_tac[]) >>
  reverse (Cases_on `n = src`)
  >- (`current_wf_precleanup_certificate s fn renamed s' A H events /\
       fn_inst_wf fn /\ fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
       all_reachable fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
       ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
        fs[current_wf_phi_context_def] >>
      `lookup_block (current_event_label ev) fn.fn_blocks = SOME pred` by simp[] >>
      `current_demand fn v (current_event_label ev) (LENGTH pred.bb_instructions)` by simp[] >>
      drule_all current_wf_precleanup_exit_nondefault >> disch_tac >>
      drule_all current_wf_precleanup_names >> strip_tac >>
      `current_event_exit_env ev v = CurrentInserted v h` by
        (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
      `current_collapsed_carrier fn A renamed h v src` by
        (simp[current_collapsed_carrier_def] >> metis_tac[]) >>
      irule current_cut_sg_exit_lookup >> metis_tac[]) >>
  irule current_cut_sg_exit_name_lookup >> metis_tac[]
QED

Theorem current_cut_actual_copy_source_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  A h = current_block_annotations old pre /\ bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
  (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL k bb.bb_instructions).inst_outputs = [d] /\
  (EL k bb.bb_instructions).inst_operands = [Var z] /\
  current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - SUC k)
      (DROP (SUC k) bb.bb_instructions))
    (current_cut_sg fn A renamed H events h
      (LENGTH (collect_phis old.bb_instructions))) d x ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >>
  `phi_prefix_length new.bb_instructions =
    LENGTH pre + LENGTH (collect_phis old.bb_instructions)` by
    (irule current_prefix_actual_endpoint >> metis_tac[]) >>
  `phi_prefix_length bb.bb_instructions <= SUC k` by decide_tac >>
  `?t. MEM (t,x,d) H` by
    (qpat_assum `phi_prefix_length new.bb_instructions = _`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
     irule (cj 1 current_cut_cleaned_suffix_owner) >>
     goal_assum (drule_at (Pat `current_prefix_back _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `k < phi_prefix_length new.bb_instructions` by simp[] >>
  drule_all current_prefix_cleaned_copy_source_cases >> strip_tac >>
  drule_all current_wf_inserted_phi_output >> strip_tac >>
  `out = d` by fs[] >> gvs[] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\
   ir_supply_inst_ok s` by fs[current_wf_phi_context_def] >>
  `MEM (CurrentInserted v h,v,d) H` by
    (irule current_history_owned_name_member >>
     simp[current_wf_token_owner_def] >> metis_tac[]) >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `v = x` by metis_tac[current_history_name_unique] >> gvs[]
  >- (`!oi. MEM oi old.bb_instructions /\ oi.inst_opcode = PHI ==>
         ~MEM v oi.inst_outputs` by
        (metis_tac[current_wf_external_collapsed_phi_clear]) >>
      `!ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs` by
        (metis_tac[current_wf_external_output_disjoint]) >>
      `FLOOKUP (current_cut_sg fn A renamed H events p
         (LENGTH pred.bb_instructions)) z = SOME v` by
        (irule current_cut_collapsed_inserted_edge_lookup >> metis_tac[]) >>
      `phi_eff (SOME p) v old.bb_instructions = SOME (Var v)` by
        (irule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
         simp[listTheory.EVERY_MEM] >>
         metis_tac[livenessProofsTheory.collect_phis_mem]) >>
      simp[current_cut_semantic_endpoint_def] >> disj2_tac >> disj2_tac >>
      simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
      `MEM z (FLAT (MAP (\i. i.inst_outputs)
        (simplify_current_phi_block new).bb_instructions))` by
        (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
         metis_tac[livenessProofsTheory.collect_phis_mem]) >>
      drule current_wf_cleanup_block_output_member >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `?w td ts. MEM (td,w,d) H /\ MEM (ts,w,z) H` by
    (irule current_prefix_cleaned_copy_owner >> simp[] >> metis_tac[]) >>
  `w = v` by metis_tac[current_history_name_unique] >> gvs[] >>
  irule current_cut_retained_original_endpoint >> metis_tac[]
QED

Theorem current_cut_phi_lookup_origin:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  A h = current_block_annotations old pre /\
  FLOOKUP (current_cut_sg fn A renamed H events h
    (LENGTH (collect_phis old.bb_instructions))) z = SOME x ==>
  current_demand fn x h (LENGTH (collect_phis old.bb_instructions)) /\
  ?ev rs E.
    MEM ev events /\ current_event_label ev = h /\
    current_source_cut A ev
      (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
    (current_token_name H (E x) = SOME z \/
     ?d. E x = CurrentInserted x d /\
         current_collapsed_carrier fn A renamed d x z) /\
    (E x = current_event_entry_env ev x \/
     ((?inst. MEM inst pre /\ MEM x inst.inst_outputs) /\
      E x = CurrentInserted x h) \/
     ?j r. j < LENGTH (collect_phis old.bb_instructions) /\
       r < LENGTH (EL j old.bb_instructions).inst_outputs /\
       EL r (EL j old.bb_instructions).inst_outputs = x /\
       E x = CurrentOriginal h j r)
Proof
  rpt strip_tac >>
  `current_cut_pair fn A renamed H events h
    (LENGTH (collect_phis old.bb_instructions)) z x` by
    metis_tac[current_cut_sg_lookup] >>
  fs[current_cut_pair_def] >>
  `old' = old` by metis_tac[optionTheory.SOME_11] >>
  gvs[] >>
  `LENGTH (current_block_annotations old pre') =
   LENGTH (current_block_annotations old pre)` by metis_tac[] >>
  `LENGTH pre' = LENGTH pre` by
    fs[current_block_annotations_def, current_inserted_annotations_def] >>
  `current_event_label ev = old.bb_label` by
    metis_tac[lookup_block_label] >>
  `current_original_scan x old.bb_label 0
     (TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions)
     (if (?inst. MEM inst pre /\ MEM x inst.inst_outputs)
      then CurrentInserted x old.bb_label else current_event_entry_env ev x) = E x` by
    metis_tac[current_wf_source_cut_original_scan] >>
  qspecl_then [`TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions`,
                `0`,
                `if (?inst. MEM inst pre /\ MEM x inst.inst_outputs)
                 then CurrentInserted x old.bb_label else current_event_entry_env ev x`]
    mp_tac (Q.INST [`v` |-> `x`, `l` |-> `old.bb_label`]
      current_original_scan_origin) >>
  simp[LENGTH_TAKE, EL_TAKE] >>
  (strip_tac
   >- (Cases_on `?inst. MEM inst pre /\ MEM x inst.inst_outputs` >>
       gvs[] >> metis_tac[]) >>
   gvs[EL_TAKE] >> metis_tac[])
QED

Theorem current_cut_phi_prefix_index[local]:
  !xs j. j < LENGTH (collect_phis xs) ==>
    j < LENGTH xs /\ (EL j xs).inst_opcode = PHI
Proof
  Induct >> simp[livenessDefsTheory.collect_phis_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `j` >> simp[]
QED

Theorem current_cut_local_original_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  A h = current_block_annotations old pre /\
  j < LENGTH (collect_phis old.bb_instructions) /\
  r < LENGTH (EL j old.bb_instructions).inst_outputs /\
  EL r (EL j old.bb_instructions).inst_outputs = x /\
  E x = CurrentOriginal h j r /\
  (current_token_name H (E x) = SOME z \/
   ?d. E x = CurrentInserted x d /\
       current_collapsed_carrier fn A renamed d x z) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >>
  `current_token_name H (CurrentOriginal h j r) = SOME z` by gvs[] >>
  drule current_cut_phi_prefix_index >> strip_tac >>
  drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
  rename1 `A h = current_block_annotations old pre'` >>
  `LENGTH new.bb_instructions = LENGTH pre' + LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `(EL (LENGTH pre' + j) new.bb_instructions).inst_opcode = PHI` by
    (qpat_x_assum `MAP instruction_inst_opcode _ = _`
      (mp_tac o Q.AP_TERM `\xs. EL (LENGTH pre' + j) xs`) >>
     simp[EL_MAP, EL_APPEND_EQN]) >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf (EL j old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `phi_well_formed (EL j old.bb_instructions).inst_operands` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `current_wf_original_phi_at fn A renamed h j (LENGTH pre' + j)
    (phi_pairs (EL j old.bb_instructions).inst_operands)` by
    (simp[current_wf_original_phi_at_def] >> qexists_tac `pre'` >>
     simp[makeSsaCurrentNonDegCleanupTheory.current_nondeg_slots_decode] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_all current_wf_original_phi_output >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  `MEM (CurrentOriginal h j r,x,z) H` by
    (irule current_history_owned_name_member >> gvs[] >> metis_tac[]) >>
  gvs[] >> irule current_cut_retained_original_endpoint >> metis_tac[]
QED

Theorem current_cut_output_token_inserted[local]:
  !xs j t. current_output_token x l i j xs t = CurrentInserted v h <=>
    ~MEM x xs /\ t = CurrentInserted v h
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h' = x` >> simp[]
QED

Theorem current_cut_original_scan_inserted[local]:
  !insts i t. current_original_scan x l i insts t = CurrentInserted v h <=>
    EVERY (\inst. ~MEM x inst.inst_outputs) insts /\ t = CurrentInserted v h
Proof
  Induct >> simp[current_original_scan_def,
    current_cut_output_token_inserted] >> metis_tac[]
QED

Theorem current_cut_inserted_scan_phi_clear[local]:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  A h = current_block_annotations old pre /\ current_event_label ev = h /\
  current_source_cut A ev
    (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  E x = CurrentInserted x h ==>
  !di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
    ~MEM x di.inst_outputs
Proof
  strip_tac >>
  `h = old.bb_label` by metis_tac[lookup_block_label] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  `current_event_label ev = old.bb_label /\
   A old.bb_label = current_block_annotations old pre` by metis_tac[] >>
  drule_all current_wf_source_cut_original_scan >>
  disch_then (qspec_then `x` assume_tac) >>
  `EVERY (\inst. ~MEM x inst.inst_outputs)
    (TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions)` by
    metis_tac[current_cut_original_scan_inserted] >>
  `bb_well_formed old` by metis_tac[wf_function_def, lookup_block_MEM, EVERY_MEM] >>
  rpt strip_tac >>
  `?j. j < LENGTH old.bb_instructions /\ EL j old.bb_instructions = di` by
    metis_tac[MEM_EL] >>
  `j < LENGTH (collect_phis old.bb_instructions)` by
    (irule makeSsaCurrentDemandTheory.current_phi_index_before_prefix >>
     fs[bb_well_formed_def] >> metis_tac[]) >>
  qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  disch_then (qspec_then `j` mp_tac) >> simp[LENGTH_TAKE, EL_TAKE]
QED

Theorem current_cut_inserted_occurrence[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  A h = current_block_annotations old pre /\
  MEM inst pre /\ MEM x inst.inst_outputs ==>
  ?q. current_wf_inserted_phi_at A renamed h q x
Proof
  strip_tac >>
  `?q. q < LENGTH pre /\ EL q pre = inst` by metis_tac[MEM_EL] >>
  drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
  `LENGTH pre' = LENGTH pre` by
    (fs[current_block_annotations_def, current_inserted_annotations_def] >>
     metis_tac[LENGTH_MAP, LENGTH_APPEND, arithmeticTheory.EQ_ADD_RCANCEL]) >>
  `?id w. EL q pre' = build_phi_inst_supply id w
    (case ALOOKUP (current_pred_map fn) old.bb_label of SOME ps => ps | NONE => [])` by
    (fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `MAP (\v. (CurrentInserted v old.bb_label,v)) inst.inst_outputs =
    [(CurrentInserted w old.bb_label,w)]` by
    (`current_block_annotations old pre = current_block_annotations old pre'` by
       metis_tac[] >>
     qpat_x_assum `current_block_annotations _ _ = _`
       (mp_tac o Q.AP_TERM `\xs. EL q xs`) >>
     simp[current_block_annotations_def, current_inserted_annotations_def,
       EL_APPEND_EQN, EL_MAP, makeSsaDefsTheory.build_phi_inst_supply_def]) >>
  `w = x` by
    (qpat_x_assum `MAP _ _ = _` (mp_tac o Q.AP_TERM `MAP SND`) >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >> gvs[]) >>
  `LENGTH new.bb_instructions = LENGTH pre' + LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `(EL q new.bb_instructions).inst_opcode = PHI` by
    (qpat_x_assum `MAP instruction_inst_opcode _ = _`
      (mp_tac o Q.AP_TERM `\xs. EL q xs`) >>
     simp[EL_MAP, EL_APPEND_EQN, makeSsaDefsTheory.build_phi_inst_supply_def]) >>
  qexists_tac `q` >> simp[current_wf_inserted_phi_at_def] >>
  simp[current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, EL_MAP, makeSsaDefsTheory.build_phi_inst_supply_def] >>
  metis_tac[lookup_block_label]
QED

Theorem current_cut_moved_phi_index[local]:
  !xs phis ord. MEM inst (collect_phis xs) /\
  (simplify_current_phi inst).inst_opcode <> PHI /\
  makeSsaDefs$simplify_current_phi_prefix_parts xs = (phis,ord) ==>
  ?k. k < phi_prefix_length xs - LENGTH phis /\
    k < LENGTH ord /\ EL k ord = simplify_current_phi inst
Proof
  Induct >> simp[livenessDefsTheory.collect_phis_def,
    makeSsaDefsTheory.simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `makeSsaDefs$simplify_current_phi_prefix_parts xs` >>
  simp[] >> Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  fs[venomExecSemanticsTheory.phi_prefix_length_def]
  >- (qexists_tac `k` >> simp[])
  >- (drule simplify_current_phi_prefix_partition >> strip_tac >>
      qexists_tac `0` >> simp[] >> decide_tac)
  >> qexists_tac `SUC k` >>
  simp[] >> decide_tac
QED

Theorem current_cut_moved_phi_nonwrite[local]:
  MEM inst (collect_phis xs) /\
  (simplify_current_phi inst).inst_opcode <> PHI /\
  EVERY (\i. ~MEM z i.inst_outputs)
    (TAKE (phi_prefix_length xs - phi_prefix_length (simplify_current_phi_prefix xs))
      (DROP (phi_prefix_length (simplify_current_phi_prefix xs))
        (simplify_current_phi_prefix xs))) ==>
  ~MEM z (simplify_current_phi inst).inst_outputs
Proof
  strip_tac >>
  Cases_on `makeSsaDefs$simplify_current_phi_prefix_parts xs` >>
  rename1 `makeSsaDefs$simplify_current_phi_prefix_parts xs = (phis,ord)` >>
  drule_all current_cut_moved_phi_index >> strip_tac >>
  `phi_prefix_length (simplify_current_phi_prefix xs) = LENGTH phis` by
    (simp[makeSsaDefsTheory.simplify_current_phi_prefix_def,
      reassign_current_inst_ids_phi_prefix] >>
     metis_tac[simplify_current_phi_parts_prefix]) >>
  `LENGTH phis + k < LENGTH (phis ++ ord)` by simp[] >>
  drule makeSsaCurrentCleanupBoundaryTheory.current_reassign_content >>
  disch_then (qspec_then `MAP (\i. i.inst_id) xs` strip_assume_tac) >>
  qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[LENGTH_TAKE, LENGTH_DROP,
    makeSsaDefsTheory.simplify_current_phi_prefix_def,
    makeSsaCurrentCleanupBoundaryTheory.current_reassign_length,
    EL_TAKE, EL_DROP, EL_APPEND_EQN] >>
  gvs[LENGTH_TAKE_EQ, LENGTH_DROP,
    makeSsaCurrentCleanupBoundaryTheory.current_reassign_length,
    EL_APPEND_EQN, arithmeticTheory.ADD_COMM, arithmeticTheory.MIN_DEF]
QED

Theorem current_cut_inserted_name_endpoint[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ A h = current_block_annotations old pre /\
  current_wf_inserted_phi_at A renamed h q x /\
  current_token_name H (CurrentInserted x h) = SOME z /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM x di.inst_outputs) /\
  EVERY (\inst. ~MEM z inst.inst_outputs)
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length (simplify_current_phi_block new).bb_instructions)
      (DROP (phi_prefix_length (simplify_current_phi_block new).bb_instructions)
        (simplify_current_phi_block new).bb_instructions)) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >> drule_all current_wf_inserted_phi_output >> strip_tac >>
  `out = z` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `out = z` SUBST_ALL_TAC >>
  Cases_on `simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions`
  >- (simp[current_cut_semantic_endpoint_def] >> metis_tac[]) >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  `MEM (EL q new.bb_instructions) (collect_phis new.bb_instructions)` by
    (irule makeSsaCurrentDemandTheory.current_phi_in_prefix >>
     metis_tac[current_wf_phi_context_prefix_order]) >>
  `phi_prefix_length new.bb_instructions = LENGTH pre + LENGTH (collect_phis old.bb_instructions)` by
    (irule current_prefix_actual_endpoint >> metis_tac[]) >>
  `~MEM z (simplify_current_phi (EL q new.bb_instructions)).inst_outputs` suffices_by
    (drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >>
     gvs[] >> fs[]) >>
  irule current_cut_moved_phi_nonwrite >> conj_tac
  >- (drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >> gvs[] >> fs[]) >>
  qexists_tac `new.bb_instructions` >>
  Cases_on `new.bb_instructions` >>
  fs[livenessDefsTheory.collect_phis_def] >>
  rename1 `new.bb_instructions = hd::tl` >>
  Cases_on `hd.inst_opcode = PHI` >>
  fs[livenessDefsTheory.collect_phis_def,
    makeSsaDefsTheory.simplify_current_phi_block_def]
QED

Theorem current_cut_local_carrier_endpoint[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  current_collapsed_carrier fn A renamed h x z ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac >> drule_all current_collapsed_carrier_owned_name >> strip_tac >>
  qpat_x_assum `current_collapsed_carrier _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_collapsed_carrier_def] >> strip_tac >>
  `old' = old /\ new' = new` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  qpat_assum `simplify_current_phi _ = _` (mk_asm "collapse") >>
  drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >>
  gvs[venomInstTheory.instruction_component_equality] >>
  asm "collapse" assume_tac >>
  rename1 `MEM (t,x,z) H`
  >- (`!ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs` by
        metis_tac[current_wf_external_output_disjoint] >>
      `FLOOKUP (current_cut_sg fn A renamed H events p
         (LENGTH pred.bb_instructions)) z = SOME x` by
        (irule current_cut_collapsed_inserted_edge_lookup >> metis_tac[]) >>
      `phi_eff (SOME p) x old.bb_instructions = SOME (Var x)` by
        (irule makeSsaCurrentPrefixEffectTheory.current_prefix_phi_eff_absent >>
         simp[EVERY_MEM] >> metis_tac[livenessProofsTheory.collect_phis_mem]) >>
      simp[current_cut_semantic_endpoint_def] >> disj2_tac >> disj2_tac >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM z (FLAT (MAP (\i. i.inst_outputs)
        (simplify_current_phi_block new).bb_instructions))` by
        (simp[MEM_FLAT, MEM_MAP] >> metis_tac[livenessProofsTheory.collect_phis_mem]) >>
      drule current_wf_cleanup_block_output_member >>
      simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  irule current_cut_retained_original_endpoint >> metis_tac[]
QED

Theorem current_cut_local_inserted_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\
  A h = current_block_annotations old pre /\
  (?inst. MEM inst pre /\ MEM x inst.inst_outputs) /\
  MEM ev events /\ current_event_label ev = h /\
  current_source_cut A ev
    (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  current_demand fn x h (LENGTH (collect_phis old.bb_instructions)) /\
  E x = CurrentInserted x h /\
  (current_token_name H (E x) = SOME z \/
   ?d. E x = CurrentInserted x d /\
       current_collapsed_carrier fn A renamed d x z) /\
  EVERY (\inst. ~MEM z inst.inst_outputs)
    (TAKE
      (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length (simplify_current_phi_block new).bb_instructions)
      (DROP (phi_prefix_length (simplify_current_phi_block new).bb_instructions)
        (simplify_current_phi_block new).bb_instructions)) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  strip_tac
  >- (`wf_function fn` by fs[current_wf_phi_context_def] >>
      `!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
        ~MEM x di.inst_outputs` by
        metis_tac[current_cut_inserted_scan_phi_clear] >>
      `?q. current_wf_inserted_phi_at A renamed h q x` by
        (irule current_cut_inserted_occurrence >> metis_tac[]) >>
      irule current_cut_inserted_name_endpoint >> metis_tac[]) >>
  `d = h` by metis_tac[current_token_11] >>
  irule current_cut_local_carrier_endpoint >> metis_tac[]
QED

Theorem current_cut_output_token_external[local]:
  !xs j t. current_token_label u <> SOME l ==>
    (current_output_token v l i j xs t = u <=> t = u /\ ~MEM v xs)
Proof
  Induct >> simp[current_output_token_def] >> rpt strip_tac >>
  Cases_on `h = v` >> simp[] >>
  metis_tac[current_token_label_def]
QED

Theorem current_cut_original_scan_external[local]:
  !insts i t. current_token_label u <> SOME l ==>
    (current_original_scan v l i insts t = u <=>
     t = u /\ EVERY (\inst. ~MEM v inst.inst_outputs) insts)
Proof
  Induct >> simp[current_original_scan_def] >>
  metis_tac[current_cut_output_token_external]
QED

Theorem current_cut_output_at_label[local]:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  current_wf_output_at A H ev k t ==>
  current_token_label t = SOME (current_event_label ev)
Proof
  strip_tac >>
  `?v. MEM (t,v) (FLAT (A (current_event_label ev)))` by
    (fs[current_wf_output_at_def] >>
     metis_tac[MEM_FLAT, EL_MEM, pairTheory.PAIR]) >>
  drule_all current_wf_precleanup_annotation_lookup >> strip_tac >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `MEM t (MAP FST (FLAT (current_block_annotations old pre)))` by
    (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  metis_tac[current_block_annotations_label, lookup_block_label]
QED

Theorem current_cut_entry_token_external[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\
  current_event_entry_env ev x <> CurrentDefault x ==>
  current_token_label (current_event_entry_env ev x) <>
    SOME (current_event_label ev) /\
  ?d. current_token_label (current_event_entry_env ev x) = SOME d /\
    d <> current_event_label ev /\
    fn_dominates fn d (current_event_label ev)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev` by fs[EVERY_MEM] >>
  drule_all current_wf_precleanup_structural >> strip_tac >>
  `!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
    j < LENGTH (EL k (A (current_event_label dev))) ==>
    current_wf_output_at A H dev k
      (FST (EL j (EL k (A (current_event_label dev)))))` by
    metis_tac[current_wf_precleanup_output_sites] >>
  drule_all current_wf_nondefault_entry_output >> strip_tac >>
  drule_all current_cut_output_at_label >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem current_cut_inherited_phi_clear[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  lookup_block h fn.fn_blocks = SOME old /\
  A h = current_block_annotations old pre /\ current_event_label ev = h /\
  current_source_cut A ev
    (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  E x = current_event_entry_env ev x /\ current_token_label (E x) <> SOME h ==>
  ~current_actual_inserted fn x h /\ current_phi_cut_clear fn x h
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn` by fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  `LENGTH pre' = LENGTH pre` by
    (fs[current_block_annotations_def, current_inserted_annotations_def] >>
     metis_tac[LENGTH_MAP, LENGTH_APPEND, arithmeticTheory.EQ_ADD_RCANCEL]) >>
  `current_original_scan x h 0
    (TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions)
    (if (?inst. MEM inst pre' /\ MEM x inst.inst_outputs)
     then CurrentInserted x h else current_event_entry_env ev x) = E x` by
    metis_tac[current_wf_source_cut_original_scan,
      makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  `~current_actual_inserted fn x h /\
   EVERY (\inst. ~MEM x inst.inst_outputs)
     (TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions)` by
    (drule_all current_cut_original_scan_external >>
     Cases_on `?inst. MEM inst pre' /\ MEM x inst.inst_outputs` >>
     simp[] >> metis_tac[current_token_label_def]) >>
  simp[makeSsaCurrentLastSiteTheory.current_phi_cut_clear_def] >>
  rpt strip_tac >>
  qpat_x_assum `EVERY (\inst. ~MEM x inst.inst_outputs) _`
    (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  disch_then (qspec_then `k` mp_tac) >>
  fs[inst_defs_def] >>
  simp[LENGTH_TAKE, EL_TAKE, inst_defs_def,
    makeSsaCurrentDemandDominanceTheory.current_collect_phis_length]
QED

Theorem current_cut_phi_demand_nondefault[local]:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  MEM ev events /\ current_event_label ev = h /\
  lookup_block h fn.fn_blocks = SOME old /\
  A h = current_block_annotations old pre /\
  current_source_cut A ev
    (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  current_demand fn x h (LENGTH (collect_phis old.bb_instructions)) ==>
  E x <> CurrentDefault x
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  `LENGTH pre' = LENGTH pre` by
    (fs[current_block_annotations_def, current_inserted_annotations_def] >>
     metis_tac[LENGTH_MAP, LENGTH_APPEND, arithmeticTheory.EQ_ADD_RCANCEL]) >>
  drule_all current_wf_precleanup_structural >> strip_tac >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  `current_source_cut A ev
    (LENGTH pre' + LENGTH (collect_phis old.bb_instructions)) rs E` by simp[] >>
  fs[current_wf_phi_context_def] >>
  metis_tac[current_wf_demanded_source_cut_nondefault, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem current_cut_inherited_nonwrite[local]:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  MEM ev events /\ current_event_label ev = h /\
  current_event_entry_env ev x <> CurrentDefault x /\
  (current_token_name H (current_event_entry_env ev x) = SOME z \/
   ?d. current_event_entry_env ev x = CurrentInserted x d /\
     current_collapsed_carrier fn A renamed d x z) ==>
  !ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev` by fs[EVERY_MEM] >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (drule_all current_wf_phi_context_entry_named_output >> strip_tac >>
      `MEM bb renamed /\ MEM (EL k bb.bb_instructions) bb.bb_instructions /\
       new.bb_label = h` by metis_tac[lookup_block_MEM, lookup_block_label, EL_MEM] >>
      metis_tac[current_wf_external_output_disjoint]) >>
  `d <> h /\ fn_dominates fn d h` by
    (drule_all current_cut_entry_token_external >>
     simp[current_token_label_def]) >>
  fs[current_collapsed_carrier_def] >>
  `q < LENGTH new'.bb_instructions /\
   (EL q new'.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> gvs[]) >>
  metis_tac[makeSsaCurrentCarrierExternalTheory.current_wf_inherited_collapsed_source_external]
QED

Theorem current_cut_inherited_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  fn_cfg_edge fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ lookup_block p fn.fn_blocks = SOME pred /\
  A h = current_block_annotations old pre /\ MEM ev events /\
  current_event_label ev = h /\
  current_source_cut A ev
    (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  current_demand fn x h (LENGTH (collect_phis old.bb_instructions)) /\
  E x = current_event_entry_env ev x /\
  (current_token_name H (E x) = SOME z \/
   ?d. E x = CurrentInserted x d /\ current_collapsed_carrier fn A renamed d x z) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `E x <> CurrentDefault x` by metis_tac[current_cut_phi_demand_nondefault] >>
  `current_token_label (E x) <> SOME h` by
    metis_tac[current_cut_entry_token_external] >>
  `~current_actual_inserted fn x h /\ current_phi_cut_clear fn x h` by
    metis_tac[current_cut_inherited_phi_clear] >>
  `!ni. MEM ni new.bb_instructions ==> ~MEM z ni.inst_outputs` by
    metis_tac[current_cut_inherited_nonwrite] >>
  `EVERY (\j. ~MEM z j.inst_outputs)
    (collect_phis (simplify_current_phi_block new).bb_instructions)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM z (FLAT (MAP (\inst. inst.inst_outputs)
       (simplify_current_phi_block new).bb_instructions))` by
       (simp[MEM_FLAT, MEM_MAP] >>
        metis_tac[livenessProofsTheory.collect_phis_mem]) >>
     drule current_wf_cleanup_block_output_member >>
     simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `MAP (\bb. bb.bb_label) renamed = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[current_wf_precleanup_labels] >>
  `?pb. MEM pb renamed /\ pb.bb_label = p` by
    (`MEM p (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
       (simp[MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
     metis_tac[MEM_MAP]) >>
  drule_all current_wf_precleanup_coverage >> strip_tac >>
  metis_tac[current_cut_reaching_external_endpoint]
QED

Theorem current_cut_terminal_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ A h = current_block_annotations old pre /\
  FLOOKUP (current_cut_sg fn A renamed H events h
    (LENGTH (collect_phis old.bb_instructions))) z = SOME x /\
  EVERY (\inst. ~MEM z inst.inst_outputs)
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length (simplify_current_phi_block new).bb_instructions)
      (DROP (phi_prefix_length (simplify_current_phi_block new).bb_instructions)
        (simplify_current_phi_block new).bb_instructions)) ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  rpt strip_tac >>
  drule_all current_cut_phi_lookup_origin >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `ev` (qx_choose_then `rs` (qx_choose_then `E` assume_tac)))) >>
  qpat_x_assum `MEM ev events /\ _` (strip_assume_tac) >>
  metis_tac[current_cut_inherited_endpoint,
    current_cut_local_inserted_endpoint, current_cut_local_original_endpoint]
QED

Theorem current_cut_prefix_semantic_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ A h = current_block_annotations old pre /\
  bb = simplify_current_phi_block new /\
  current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length bb.bb_instructions)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions))
    (current_cut_sg fn A renamed H events h
      (LENGTH (collect_phis old.bb_instructions))) z x ==>
  current_cut_semantic_endpoint fn A renamed H events p h old new pred z x
Proof
  rpt strip_tac >>
  drule current_prefix_back_endpoint_cases >> strip_tac
  >- (irule current_cut_terminal_endpoint >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `TAKE (n - q) (DROP q is) = before ++ inst::after` >>
  `LENGTH before < n - q /\ LENGTH before < LENGTH (DROP q is)` by
    (qpat_x_assum `TAKE _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
     rw[] >> decide_tac) >>
  `EL (q + LENGTH before) is = inst` by
    (`EL (LENGTH before) (TAKE (n-q) (DROP q is)) = inst` by
       (simp[EL_APPEND_EQN] >> metis_tac[EL_LENGTH_APPEND]) >>
     gvs[EL_TAKE, EL_DROP]) >>
  `after = TAKE (n - SUC (q + LENGTH before))
    (DROP (SUC (q + LENGTH before)) is)` by
    (qpat_x_assum `TAKE _ _ = _` (mp_tac o Q.AP_TERM `DROP (SUC (LENGTH before))`) >>
     simp[DROP_TAKE, DROP_DROP_T, DROP_APPEND, DROP_LENGTH_TOO_LONG,
       arithmeticTheory.ADD_CLAUSES] >>
     `n - q - SUC (LENGTH before) = n - SUC (q + LENGTH before)` by decide_tac >>
     `SUC (LENGTH before) + q = SUC (q + LENGTH before)` by decide_tac >>
     `SUC (LENGTH before) - (LENGTH before + 1) = 0` by decide_tac >>
     simp[]) >>
  irule current_cut_actual_copy_source_endpoint >>
  simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`dst`, `q + LENGTH before`, `pre`] >>
  simp[] >>
  gvs[Abbr `n`, Abbr `q`, Abbr `is`] >> decide_tac
QED

Theorem current_cut_prefix_phi_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  lookup_block p fn.fn_blocks = SOME pred /\ A h = current_block_annotations old pre /\
  bb = simplify_current_phi_block new /\
  current_prefix_back
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length bb.bb_instructions)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions))
    (current_cut_sg fn A renamed H events h
      (LENGTH (collect_phis old.bb_instructions))) z x ==>
  OPTREL (op_rename (current_cut_sg fn A renamed H events p
    (LENGTH pred.bb_instructions)))
    (phi_eff (SOME p) x old.bb_instructions)
    (phi_eff (SOME p) z bb.bb_instructions)
Proof
  rpt strip_tac >>
  `current_cut_semantic_endpoint fn A renamed H events p h old new pred z x` by
    (irule current_cut_prefix_semantic_endpoint >> metis_tac[]) >>
  gvs[] >> irule current_cut_semantic_endpoint_effect >> metis_tac[]
QED

Resume current_cut_inv_block_entry_prefix[prefix_phi_relation]:
  irule current_prefix_map_phis >>
  reverse conj_tac >- (first_x_assum irule >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  `b' = if blocks_have_leading_phi fn.fn_blocks
    then simplify_current_phi_block new else new` by
    (gvs[current_cleanup_if_lookup]) >>
  `block_insts fn h = old_h.bb_instructions /\
   block_insts (fn with fn_blocks :=
     simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed) h =
     b'.bb_instructions` by simp[block_insts_def] >>
  simp[] >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- (irule current_cut_prefix_phi_effect >> metis_tac[]) >>
  gvs[current_prefix_back_def] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==> simplify_current_phi inst = inst)
    b'.bb_instructions` by (irule current_phi_free_context_fixed >> metis_tac[]) >>
  `phi_eff (SOME p) z (simplify_current_phi_block b').bb_instructions =
   phi_eff (SOME p) z b'.bb_instructions` by
    (irule current_fixed_phi_cleanup_effect >> simp[]) >>
  `phi_prefix_length (simplify_current_phi_block b').bb_instructions =
   LENGTH pre + LENGTH (collect_phis old_h.bb_instructions)` by
    (simp[current_fixed_phi_cleanup_prefix]) >>
  `OPTREL (op_rename (current_cut_sg fn A renamed H events p
      (LENGTH old_p.bb_instructions)))
    (phi_eff (SOME p) x old_h.bb_instructions)
    (phi_eff (SOME p) z (simplify_current_phi_block b').bb_instructions)` suffices_by metis_tac[] >>
  irule current_cut_prefix_phi_effect >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`t.vs_current_bb`, `b'`, `pre`] >>
  simp[current_prefix_back_def]
QED

Finalise current_cut_inv_block_entry_prefix
