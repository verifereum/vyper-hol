(* One actual member-setup step, shared semantic and pointer endpoints.
   This is ML proof code, not a new HOL contract or a decoder API.

   C3.4.2.2 finite validation input (all conjuncts are explicit local inputs):
     abi_decode_member_setup (Var output) pos MLOAD (Var source) hi
       dyn ao vo st = (ops,en)
     abi_malformed_entry H ctx func cenv cx es st sites dstid live
       (Var source) hi pos (Var output) B L xs p d outsz s
     p+ao+(if dyn then 32 else 0) <= L, vo+childsz <= outsz
     en.cs_next_var <= ceiling.cs_next_var, fresh_vars_wrt ceiling s
     fn_has_code st en func, ~ctx_has_dalloca ctx, ~s.vs_halted
     s.vs_current_bb = st.cs_current_bb
     s.vs_inst_idx = LENGTH st.cs_current_insts
     abi_decode_ptr_window G tn s source (n2w B) L
     ptr_covers G tn output s outsz
     op_prov G pos = NONE, op_taint tn pos = {}, allocas_from lo s
     s.vs_accounts = incoming.vs_accounts
     s.vs_transient = incoming.vs_transient
     s.vs_call_ctx = incoming.vs_call_ctx
     s.vs_immutables = incoming.vs_immutables
     !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (incoming,Gi,ti) [] (OK s,G,tn)

   Checked output disjunction (witnesses precede D/explicit in both arms):
   - ?u G' tn'. four observations at u equal those at incoming, and
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (incoming,Gi,ti) [] (Abort Revert_abort u,G',tn')
   - ?u G' tn' out. SND ops = Var out,
       u.vs_inst_idx = LENGTH en.cs_current_insts,
       abi_malformed_entry H ctx func cenv cx es en sites dstid live
         (Var source) hi (FST ops) (SND ops) B L xs
         (p + if dyn then abi_head_word (DROP (p+ao) xs) else ao)
         (d+vo) childsz u,
       abi_malformed_resource_post ctx func cenv cx es
         st.cs_next_var sites dstid s u,
       fresh_vars_wrt ceiling u,
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (incoming,Gi,ti) [] (OK u,G',tn'),
       op_prov G' (FST ops) = NONE, op_taint tn' (FST ops) = {},
       ptr_covers G' tn' out u childsz,
       state_frame (u with vs_inst_idx := s.vs_inst_idx) = state_frame s,
       !x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x),
       tn'.t_mem = tn.t_mem, tn'.t_stor = tn.t_stor,
       tn'.t_trans = tn.t_trans, tn'.t_imm = tn.t_imm,
       abi_decode_ptr_window G' tn' u source (n2w B) L,
       allocas_from lo u.

   Residual obligations for the recursive join (NOT proved here): obtain
   this setup compilation/code from abi_decoder_member_cons_trace/code;
   derive the intermediate input invariant, actual offsets/capacity bounds
   and incoming path from the executed prefix; apply the child rejection
   induction hypothesis or successful-child continuation at this SAME u,G',tn';
   fold subsequent members and prove the final malformed-parent contradiction.
   No child validity, decoded value, child inhabitation or recursive width
   premise is assumed. No whole-parent success theorem is invoked.
   The temporary local validation script is deliberately not published.
   Validation evidence: C3.4.2.2 dossier, one-step build recorded there. *)
structure abiDecodeJointRejectMemberSetupLib =
struct
open HolKernel boolLib bossLib
open abiMalformedMemberSetupTheory abiMalformedRecursiveInterfaceTheory
     abiDecodePtrMemberJointTheory abiDecodePtrMemberFrameTheory
     abiDecoderMemberSetupTheory abiDecoderReentryTheory
     loweringStateRelDefsTheory bodyPtrDefsTheory exprLoweringPropsTheory
     compileEnvTheory venomStateTheory wordsTheory listTheory
     stateFrameTheory fragGasOriginPtrTheory

val inputs =
  `stmt_state_rel H ctx func cenv cx es s /\
   abi_malformed_allocated_window live B L xs s /\
   abi_malformed_destination func cenv es.scopes dstid d outsz s /\
   live <> dstid /\ B+L < dimword(:256) /\ d+outsz < dimword(:256) /\
   eval_operand pos s = SOME (n2w p) /\
   lookup_var output s = SOME (n2w d)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def, eval_operand_def] >>
  `not_fresh_at st source /\ not_fresh_at st output /\
   (!x. pos = Var x ==> not_fresh_at st x)` by
    (Cases_on `pos` >>
     fs[abi_malformed_entry_def, EVERY_DEF, abi_decoder_operand_live_def,
        abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all abi_malformed_allocated_bounds >>
  disch_then (assume_tac o cj 1) >>
  `B < dimword(:256) /\ p+ao < dimword(:256)` by
    (Cases_on `dyn` >> fs[] >> decide_tac) >>
  `p+ao = w2n ((n2w p:bytes32)+n2w ao)` by
    simp[word_add_n2w, w2n_n2w] >>
  `dyn ==> p+ao+32 <= L /\ w2n (n2w B:bytes32)+L < dimword(:256) /\
    w2n (n2w B:bytes32)+L <= s.vs_alloca_next` by
    (strip_tac >> fs[w2n_n2w]) >>
  `w2n (n2w d:bytes32)+outsz < dimword(:256)` by simp[w2n_n2w];

val split =
  drule_all abi_malformed_member_setup_observed >> strip_tac;

(* Incoming uniform path, if any, is kept separate and composed afterwards. *)
val abort =
  drule_all abi_decode_member_setup_abort_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) [] (Abort Revert_abort (t with vs_inst_idx := j),G',tn')` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  qexistsl_tac [`t with vs_inst_idx := j`, `G'`, `tn'`] >>
  simp[] >>
  qpat_x_assum `(_ with <|vs_vars := _; vs_inst_idx := _;
    vs_halted := _; vs_returndata := _|>) = s` mp_tac >>
  simp[venom_state_component_equality];

val success =
  drule_all (abi_decode_member_setup_success_joint |> SPEC_ALL |>
    Q.INST [`k` |-> `childsz`, `cap` |-> `outsz`, `p` |-> `p+ao`]) >>
  disch_then (qspec_then `PG` strip_assume_tac);

val source_window =
  `abi_decode_ptr_window G' tn' t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]);

val prepend_success =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) []
    (OK (t with vs_inst_idx := LENGTH en.cs_current_insts),G',tn')` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL];

val normalized_success =
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `G'`, `tn'`, `out`] >>
  simp[abi_malformed_entry_inst_idx, abi_malformed_resource_post_inst_idx,
    ghostPcTransportPtrTheory.ptr_covers_inst_idx, fresh_vars_wrt_def,
    ptrDisciplineTheory.allocas_from_def, lookup_var_def,
    abi_decode_ptr_window_def] >>
  fs[state_frame_def, venom_state_component_equality,
    fresh_vars_wrt_def, lookup_var_def, ptrDisciplineTheory.allocas_from_def,
    abi_decode_ptr_window_def] >> metis_tac[];

val one_step =
  strip_tac >> inputs >> split
  >- (disj1_tac >> abort) >>
  disj2_tac >> success >> source_window >> prepend_success >> normalized_success;
end
