(* Finite member-cons proof procedures, not a HOL decoder contract.

   VALIDATION BOUNDARY (C3.4.2.3)
   cons_case and nil_case were executed by the temporary closed assertions
   cons_routing_local / nil_local in abiDecodeJointRejectMembersProbeTheory.
   Their statement/proof and passing build are persisted in the dossier;
   no probe theorem/API is published. This does NOT prove the member fold.

   Local inputs, in addition to MemberSetupLib's documented setup inputs:
   - actual compile_abi_decode_complex_elems on
       abi_decoder_member_infos sf ce (ty::tys), from st to final;
   - final.cs_next_var <= ceiling.cs_next_var and fn_has_code st final func;
   - abi_decoder_coherent ce env sf ty tv, LENGTH xs = L;
   - p+ao+abi_member_head_size (vyper_to_abi_type env ty) <= L;
   - dyn = dec_info_needs_offset (type_to_abi_dec_info sf ce ty).
   compile_cons derives actual ops,en,child_end, phase equations, cs_extends,
   code splits and intermediate variable bounds. It rewrites ONLY the setup
   equation to dyn: broad simplification can erase dyn and alter callbacks.

   Let cp = p + (if dyn then abi_head_word (DROP (p+ao) xs) else ao).
   Two explicit adapters are local assumptions, each guarded by ALL THREE
   actual setup/child/tail compiler equations (not guessed compiler states):
   CHILD: at the SAME u,G1,tn1 from setup, with SND ops = Var out,
     child abi_malformed_entry at en, cp,d+vo,childsz; freshness, output
     coverage, source window, clean FST ops and allocas_from lo:
     choose v,G2,tn2 before all masks, preserve four world fields, and give
     either a uniform abort path or a uniform OK path PLUS validity and
     admissibility of the selected child bytes AND parent abi_malformed_entry
     at child_end, parent resource_post (from u), freshness, full parent
     output coverage, source window and allocas_from lo at v.
   TAIL: from those parent reentry facts at v,G2,tn2 choose w,G3,tn3,
     preserve four world fields and give uniform abort OR uniform OK with
     tuple validity, list admissibility at ao+member_head_size and parent
     resource_post (from v).
   cons_case checks setup abort, child abort, tail abort, and all-success
   semantic cons reflection, at common runtime/ghost endpoints. It composes
   resource_post only on success. Abort branches promise exactly observations
   and the uniform abort path, not an unproved success resource invariant.
   nil_case checks empty semantic validity/admissibility, resource identity
   and the zero-step OK path from stmt_state_rel and ~s.vs_halted.

   EXACT SUCCESS IH (quotation from abiValidAllocatedJointScript.sml C,
   also abiDecodeJointSuccessCasesLib.C; documentation, not a new predicate):
   `\ty tv.
    !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
    abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
      st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
    !G tn PG lo.
    ~ctx_has_dalloca ctx /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s u /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G',tn')) /\
    ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' u source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==> val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next`

   EXACT REJECTION IH: universal closure of the immutable reject declaration
   (recorded in E0024, TO_extcall_case-L0002-20261116T080330251967Z_m0018_t003),
   at the coherent child parameters; it is NOT the CHILD adapter above:
   `abi_decoder_coherent ce env sf ty tv /\
    compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    (?av. has_type (vyper_to_abi_type env ty) av) /\
    assignable_type env ty /\ type_memory_size tv < dimword(:256) /\
    abi_size_bound sf ty < dimword(:256) /\
    abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => p+32 <= L | _ => T) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
      else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
    ~ctx_has_dalloca ctx /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G',tn'))`

   RESIDUAL LEDGER -- all below are unproved here, not extra TASK premises:
   1. Derive initial parent entry/coverage, clean pos and incoming path from
      the exact root/guard. No parent validity is assumed by this fragment.
   2. Derive childsz = type_memory_bytes ce ty, coherent head/tail layouts,
      vo+childsz <= outsz and both head bounds from the parent layout,
      including zero-size fields. Source bound is actual L, not max width.
   3. At setup success derive alloca_history func u and lo<=u.vs_alloca_next;
      setup's allocas_from alone does not supply these IH prerequisites.
      Transport hi provenance/taint and child PC/not-halted conditions;
      setup currently supplies clean FST ops but not all exact C/IH inputs.
   4. Instantiate exact rejection IH only after deriving child assignability,
      ABI inhabitant, memory/ABI size bounds, source readability (primitive),
      distinct IDs and child scratch-site entry. Parent inhabitation does
      not license inventing an unexecuted child inhabitant (zero arrays).
   5. In the other branch, derive a value v and abi_valid_allocated_entry for
      exact C: validity/admissibility of selected bytes must be related to
      DROP cp xs and abi_to_vyper env ty ... = SOME v with p<=L/static bound.
      Neither exact C nor reject IH directly yields the adapter disjunction;
      the complete case split and all its applicability premises are owed.
   6. From the exact SAME child success endpoint derive parent reentry,
      restore parent operands/live ghosts, expand child coverage to full
      parent coverage, preserve protected input/window, and weaken child
      resource_post next/sites to the parent next/sites. Scratch-site subset,
      operand liveness and disjoint current/prefix footprints are obligations;
      they are NOT consequences of semantic validity alone.
   7. Derive the tail adapter from the genuine recursive member invariant,
      with ao+embedded_static_size and vo+type_memory_bytes, including layout
      alignment to semantic ao+member_head_size. Current proof consumes its
      output; it does not construct the recursive continuation or its IH.
   8. At the root fold close malformedness against reflected success. Dynamic
      array traversal and the public pair remain outside this finite test.
   No whole-parent success supplier, width premise or separately existential
   semantic execution endpoint is used to hide these adapters. *)
structure abiDecodeJointRejectMembersLib =
struct
open HolKernel boolLib bossLib
open abiMalformedMembersTheory abiMalformedMemberReflectionTheory
     abiMalformedRecursiveInterfaceTheory fragGasOriginPtrTheory
     stateFrameTheory venomStateTheory listTheory

val compile_cons =
  drule abiDecoderMemberConsTheory.abi_decoder_member_cons_trace >> strip_tac >>
  rename1 `abi_decode_member_setup _ _ _ _ _ _ _ _ st = (ops,en)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ _ en = ((),child_end)` >>
  `abi_decode_source_opcode MLOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderMemberConsTheory.abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code st en func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `en.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  `abi_decode_member_setup (Var output) pos MLOAD (Var source) hi dyn ao vo st = (ops,en)` by
    (qpat_assum `dyn = _` (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC);

val compile_continuations =
  ntac 2
    (qpat_x_assum `!ops en child_end. _`
      (qspecl_then [`ops`, `en`, `child_end`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then assume_tac);

(* Keep the actual one_step proof in the validation, not an assumed
   disjunction or an independently chosen semantic/pointer endpoint. *)
val setup_split =
  `T ==>
   (?u G' tn'.
     u.vs_accounts = incoming.vs_accounts /\ u.vs_transient = incoming.vs_transient /\
     u.vs_call_ctx = incoming.vs_call_ctx /\ u.vs_immutables = incoming.vs_immutables /\
     !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (incoming,Gi,ti) [] (Abort Revert_abort u,G',tn')) \/
   (?u G' tn' out.
     SND ops = Var out /\ u.vs_inst_idx = LENGTH en.cs_current_insts /\
     abi_malformed_entry H ctx func cenv cx es en sites dstid live
       (Var source) hi (FST ops) (SND ops) B L xs
       (p + if dyn then abi_head_word (DROP (p+ao) xs) else ao)
       (d+vo) childsz u /\
     abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s u /\
     fresh_vars_wrt ceiling u /\
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (incoming,Gi,ti) [] (OK u,G',tn')) /\
     op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
     ptr_covers G' tn' out u childsz /\
     state_frame (u with vs_inst_idx := s.vs_inst_idx) = state_frame s /\
     (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
     tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
     tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
     abi_decode_ptr_window G' tn' u source (n2w B) L /\ allocas_from lo u)` by
    abiDecodeJointRejectMemberSetupLib.one_step >>
  pop_assum (strip_assume_tac o SIMP_RULE bool_ss []);

val setup_observations =
  `u.vs_accounts = incoming.vs_accounts /\ u.vs_transient = incoming.vs_transient /\
   u.vs_call_ctx = incoming.vs_call_ctx /\ u.vs_immutables = incoming.vs_immutables` by
    (fs[state_frame_def, venom_state_component_equality]);

(* The two path premises always have the SAME intermediate runtime and
   ghost state. No semantic frag_outcome is used as a pointer path. *)
val child_abort_path =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) [] (Abort Revert_abort v,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL];

val child_ok_path =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) [] (OK v,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL];

val tail_abort_path =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) [] (Abort Revert_abort w,G3,tn3)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL];

val tail_ok_path =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (incoming,Gi,ti) [] (OK w,G3,tn3)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL];

val reflect_head =
  drule abi_malformed_member_reflection >>
  disch_then (qspecl_then [`xs`, `p`] mp_tac) >>
  disch_then (qspecl_then
    [`p + if dyn then abi_head_word (DROP (p+ao) xs) else ao`, `ao`, `L`] mp_tac) >>
  simp[] >> strip_tac;

val reflect_cons =
  drule_at (Pat `vyper_decode_valid_enc_tuple _ _ _`) abi_malformed_members_reflect_cons >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> strip_tac;

(* Cons routing consumes explicit child/tail adapters, NOT the recursive IHs.
   compile_cons chooses the actual intermediate compiler states first. *)
val cons_case =
  strip_tac >> compile_cons >> compile_continuations >> setup_split
  >- metis_tac[] >>
  setup_observations >>
  qpat_x_assum `!u G1 tn1 out. _` (qspecl_then [`u`, `G'`, `tn'`, `out`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))
  >- (child_abort_path >> metis_tac[]) >>
  child_ok_path >>
  qpat_x_assum `!v G2 tn2. _` (qspecl_then [`v`, `G2`, `tn2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `w` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)))
  >- (tail_abort_path >> metis_tac[]) >>
  tail_ok_path >> reflect_head >> reflect_cons >>
  disj2_tac >> qexistsl_tac [`w`, `G3`, `tn3`] >> simp[] >>
  irule abi_malformed_resource_trans >> qexists_tac `v` >> simp[] >>
  irule abi_malformed_resource_trans >> qexists_tac `u` >> simp[];

val nil_case =
  simp[Once vyperABITheory.vyper_decode_valid_enc_def,
    abiValidMembersTheory.abi_decode_members_def,
    abiVyperAdmissibleTheory.abi_vyper_admissible_list_nil] >>
  conj_tac >- metis_tac[abi_malformed_resource_refl] >>
  rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[];
end
