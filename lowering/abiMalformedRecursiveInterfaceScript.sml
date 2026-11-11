(* Allocation-backed resources for arbitrary-input recursive decoding.
   Execution/reflection is a conclusion of the later induction, not an
   assumption in these resource predicates. *)
Theory abiMalformedRecursiveInterface
Ancestors
  abiMalformedSiteFrame abiMalformedPruneState abiMalformedPrefix
  abiDecoderReentry abiDecoderVarExtend abiDecoderContract fragExec
  venomExecSemantics exprLoweringProps compileEnv
  venomState venomMemDefs valueEncoding valueEncodingDefs finite_map pred_set words list arithmetic

Definition abi_malformed_destination_def:
  abi_malformed_destination func cenv scopes aid d n s <=>
    ?inst q b sz.
      MEM inst (fn_insts func) /\ inst.inst_id = aid /\
      inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
      not_local_ptr cenv scopes q /\
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      b <= d /\ d + n <= b + sz
End

(* Source is a protected incoming allocation, not a canonical encoding. *)
Definition abi_malformed_allocated_window_def:
  abi_malformed_allocated_window live B L xs s <=>
    (?cap. FLOOKUP s.vs_allocas live = SOME (B,cap) /\ L <= cap) /\
    B + L < dimword (:256) /\ mem_bytes_at B L s.vs_memory = xs
End

Definition abi_malformed_resource_post_def:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t <=>
    stmt_state_rel ctx func cenv cx es t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid B cap L. aid NOTIN sites /\ aid <> dstid /\
       FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ L <= cap ==>
       mem_bytes_at B L t.vs_memory = mem_bytes_at B L s.vs_memory) /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w)
End

Theorem abi_malformed_destination_subrange:
  abi_malformed_destination func cenv scopes aid d n s /\
  d <= child /\ child + k <= d + n ==>
  abi_malformed_destination func cenv scopes aid child k s
Proof
  rw[abi_malformed_destination_def] >>
  qexistsl_tac [`inst`, `q`, `b`, `sz`] >> simp[] >> decide_tac
QED

Theorem abi_malformed_resource_window:
  abi_malformed_allocated_window live B L xs s /\
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  live NOTIN sites /\ live <> dstid ==>
  abi_malformed_allocated_window live B L xs t
Proof
  rw[abi_malformed_allocated_window_def, abi_malformed_resource_post_def] >>
  metis_tac[]
QED

Theorem abi_malformed_resource_ancestor:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  aid NOTIN sites /\ aid <> dstid /\
  FLOOKUP s.vs_allocas aid = SOME (A,32) ==>
  mload A t = mload A s
Proof
  strip_tac >>
  `mem_bytes_at A 32 t.vs_memory = mem_bytes_at A 32 s.vs_memory` by
    (fs[abi_malformed_resource_post_def] >> first_x_assum irule >>
     qexistsl_tac [`aid`, `32`] >> simp[]) >>
  gvs[mem_bytes_at_def, mload_def]
QED

Theorem abi_malformed_resource_refl:
  stmt_state_rel ctx func cenv cx es s ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s s
Proof
  simp[abi_malformed_resource_post_def]
QED

Theorem abi_malformed_resource_weaken:
  abi_malformed_resource_post ctx func cenv cx es child_next child_sites dstid s t /\
  next <= child_next /\ child_sites SUBSET sites ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
Proof
  rw[abi_malformed_resource_post_def]
  >- (first_x_assum irule >> qexistsl_tac [`aid`, `cap`] >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]
QED

Theorem abi_malformed_resource_trans:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  abi_malformed_resource_post ctx func cenv cx es next sites dstid t u ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s u
Proof
  rw[abi_malformed_resource_post_def]
  >- (qpat_assum `!aid B cap L. _ ==> mem_bytes_at B L t.vs_memory = _`
        (qspecl_then [`aid`, `B`, `cap`, `L`] mp_tac) >>
      simp[] >> strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (B,cap)` by metis_tac[] >>
      qpat_x_assum `!aid B cap L. _ ==> mem_bytes_at B L u.vs_memory = _`
        (qspecl_then [`aid`, `B`, `cap`, `L`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem abi_malformed_resource_destination:
  abi_malformed_destination func cenv es.scopes aid d n s /\
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t ==>
  abi_malformed_destination func cenv es.scopes aid d n t
Proof
  rw[abi_malformed_destination_def, abi_malformed_resource_post_def] >>
  qexistsl_tac [`inst`, `q`, `b`, `sz`] >> simp[]
QED

(* Pruning is only a proof-state transformation. In particular this lemma
   makes no assertion that the runtime executes a pruning operation. *)
Theorem abi_malformed_resource_prune:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  local_ptrs_reserved cenv st /\ next <= st.cs_next_var ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid
    (abi_decoder_prune_vars st.cs_next_var s)
    (abi_decoder_prune_vars st.cs_next_var t)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     (abi_decoder_prune_vars st.cs_next_var t)` by
    (irule abi_malformed_prune_state >>
     fs[abi_malformed_resource_post_def]) >>
  simp[abi_malformed_resource_post_def, abi_decoder_prune_vars_def] >>
  fs[abi_malformed_resource_post_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qexistsl_tac [`aid`, `cap`] >> simp[]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  fs[GSYM abi_decoder_prune_vars_def, abi_decoder_prune_eval] >>
  metis_tac[]
QED

(* Input pruning changes no resources and preserves every live operand. *)
Theorem abi_malformed_resource_input_unprune:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid
    (abi_decoder_prune_vars next s) t ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
Proof
  simp[abi_malformed_resource_post_def, abi_decoder_prune_vars_def] >>
  strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qexistsl_tac [`aid`, `cap`] >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  simp[GSYM abi_decoder_prune_vars_def, abi_decoder_prune_eval]
QED

(* Compiler ids select actual ALLOCA instructions, never address intervals. *)
Definition abi_malformed_scratch_sites_def:
  abi_malformed_scratch_sites st en func =
    {aid | st.cs_next_id <= aid /\ aid < en.cs_next_id /\
      ?inst. MEM inst (fn_insts func) /\ inst.inst_id = aid /\
             inst.inst_opcode = ALLOCA}
End

Theorem abi_malformed_scratch_sites_older:
  aid < st.cs_next_id ==>
  aid NOTIN abi_malformed_scratch_sites st en func
Proof
  simp[abi_malformed_scratch_sites_def]
QED

Theorem abi_malformed_scratch_sites_nested:
  st.cs_next_id <= child.cs_next_id /\
  child_end.cs_next_id <= en.cs_next_id ==>
  abi_malformed_scratch_sites child child_end func SUBSET
    abi_malformed_scratch_sites st en func
Proof
  rw[abi_malformed_scratch_sites_def, SUBSET_DEF] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

(* The child's execution may be justified on a pruned proof state and
   transported by the existing execution-extension simulation. Resource
   restoration itself needs agreement on reserved local/immutable pointers. *)
Theorem abi_malformed_resource_restore:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  abi_decoder_vars_extend extras t u /\ local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t) ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s u
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >> strip_tac >>
  `u = t with vs_vars := u.vs_vars` by
    (drule abi_decoder_vars_extend_restore >>
     disch_then (mp_tac o AP_TERM ``\v:venom_state. v with vs_vars := u.vs_vars``) >>
     simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_x_assum `u = _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >>
     reverse conj_tac >- fs[abi_malformed_resource_post_def] >>
     qexists_tac `st` >> fs[lookup_var_def]) >>
  fs[abi_malformed_resource_post_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qexistsl_tac [`aid`, `cap`] >> simp[]) >>
  rpt strip_tac >> irule abi_decoder_vars_extend_eval >> qexistsl_tac [`extras`, `t`] >>
  simp[] >> metis_tac[]
QED

Definition abi_malformed_entry_def:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
      base_op hi src dst B L xs p d n s <=>
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
    abi_malformed_allocated_window live B L xs s /\
    live NOTIN sites /\ live <> dstid /\ dstid NOTIN sites /\
    abi_malformed_destination func cenv es.scopes dstid d n s /\
    hi <> Lit 0w /\ p < dimword (:256) /\ d + n < dimword (:256) /\
    eval_operand base_op s = SOME (n2w B) /\
    eval_operand hi s = SOME (n2w L) /\
    eval_operand src s = SOME (n2w p) /\
    eval_operand dst s = SOME (n2w d) /\
    EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst]
End

Definition abi_malformed_reflected_post_def:
  abi_malformed_reflected_post env ty bytes ctx func cenv cx es
      next sites dstid s t <=>
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes) /\
    abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
End

(* Child navigation supplies the new pointer operands, not a decoded value.
   A dynamic pointer may be outside L; the child's real guard must reject it. *)
Theorem abi_malformed_child_entry:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n s /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
  child_sites SUBSET sites /\ local_ptrs_reserved cenv child /\
  d <= cd /\ cd + cn <= d + n /\
  child_pos < dimword (:256) /\ cd + cn < dimword (:256) /\
  eval_operand child_src t = SOME (n2w child_pos) /\
  eval_operand child_dst t = SOME (n2w cd) /\
  EVERY (abi_decoder_operand_live child.cs_next_var)
    [base_op;hi;child_src;child_dst] ==>
  abi_malformed_entry ctx func cenv cx es child child_sites dstid live
    base_op hi child_src child_dst B L xs child_pos cd cn t
Proof
  strip_tac >>
  `abi_malformed_allocated_window live B L xs s /\
   live NOTIN sites /\ live <> dstid /\
   abi_malformed_destination func cenv es.scopes dstid d n s` by
    fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_resource_window >> strip_tac >>
  drule_all abi_malformed_resource_destination >> strip_tac >>
  drule_all abi_malformed_destination_subrange >> strip_tac >>
  fs[abi_malformed_entry_def, abi_malformed_resource_post_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem abi_malformed_reflected_child_return:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  abi_malformed_reflected_post env ty bytes ctx func cenv cx es
    child_next child_sites dstid t u /\
  next <= child_next /\ child_sites SUBSET sites ==>
  abi_malformed_reflected_post env ty bytes ctx func cenv cx es
    next sites dstid s u
Proof
  simp_tac bool_ss [abi_malformed_reflected_post_def] >> strip_tac >> simp[] >>
  drule_all abi_malformed_resource_weaken >> strip_tac >>
  drule_all abi_malformed_resource_trans >> simp[]
QED

(* The hypothesis is the universally state-quantified execution specification
   of a child. The actual abort alternative is retained, without inventing an
   operational prune transition or assuming acceptance of future input. *)
Theorem abi_malformed_child_execution_return:
  frag_exec ctx child en P
    (abi_malformed_reflected_post env ty bytes ctx func cenv cx es
      child.cs_next_var child_sites dstid t)
    (\r. ?v. r = Abort Revert_abort v) /\
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
  next <= child.cs_next_var /\ child_sites SUBSET sites ==>
  frag_exec ctx child en P
    (abi_malformed_reflected_post env ty bytes ctx func cenv cx es
      next sites dstid s)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac >> drule_all abi_malformed_reflected_child_return >> simp[]
QED

Theorem abi_malformed_entry_prune:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n s ==>
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule abi_malformed_prune_state >> fs[abi_malformed_entry_def]) >>
  fs[abi_malformed_entry_def] >>
  simp[abi_malformed_entry_def, abi_decoder_prune_eval] >>
  fs[abi_malformed_allocated_window_def, abi_malformed_destination_def,
     abi_decoder_prune_vars_def] >> metis_tac[]
QED

(* Premise map for the caller and recursive use sites:
   - stmt_state_rel and local_ptrs_reserved are caller resources; the proved
     index and contained-copy state boundaries retain them during execution.
   - allocated_window comes from the incoming buffer ALLOCA witness and the
     capped returndata bytes. L is the payload bound, not the full returndata.
   - destination comes from the fresh result ALLOCA; recursive destinations
     are subranges of that same allocation. Its nonlocal output is justified
     by compiler freshness and local pointer reservation, not by value typing.
   - live/dstid predate decoder scratch: scratch_sites_older discharges their
     exclusion. scratch_sites_nested handles a compiled child's actual sites.
   - the four operand equations come from decode-bound setup / checked member
     navigation; operand liveness is reservation or generated-operand liveness.
   - source and destination nonwrap follow from their allocated bounds. The
     source position alone is a word; it need not be within L. Readability for
     a primitive is a separate checked-parent/root-head premise.
   - coherent metadata, actual code containment, compiler-limit freshness and
     cursor premises stay separate; frag_exec supplies its cursor contract.
   - resource_post and reflected_post are conclusions required of the later
     constructor induction, NEVER premises silently appended to the caller.
     child_execution_return is conditional only on the explicit child
     specification; it asserts no complete decoder execution theorem.
   - prune/restore are simulation transports. restore explicitly requires
     reserved-lookup agreement; an arbitrary map extension is insufficient.
   No whole-input decoded-value typing or source acceptance occurs in entry.
*)
