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
  makeSsaCurrentWfSsa o1FrameLockstep o1PassLift makeSsaCurrentDemand
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation makeSsaCurrentCertificate
  makeSsaCurrentTreePaths makeSsaCurrentTokens makeSsaCurrentCarrierOwner
  makeSsaCurrentCutTransport

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
  cheat
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
  cheat
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
  `v1 = v2` by metis_tac[current_carrier_history_name_owner] >>
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
  `old.bb_label = l` by metis_tac[makeSsaHelperTheory.lookup_block_label] >>
  `E' v = E v` by
    (irule current_transport_source_cut_unaffected >> metis_tac[]) >>
  `current_demand fn v l i` by
    (irule (cj 3 current_demand_rules) >>
     simp[venomInstTheory.inst_defs_def] >> metis_tac[]) >>
  simp[current_cut_pair_def] >>
  qexistsl_tac [`ev`, `pre`, `rs'`, `E'`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
