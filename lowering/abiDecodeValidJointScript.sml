(* Discharge the coherent-entry induction with the actual-run suppliers. *)
Theory abiDecodeValidJoint
Ancestors
  abiDecodeValidCoherentCases abiValidAllocatedPrimitiveJoint
  abiValidAllocatedBytesJoint abiDecodeValidMemberTraversal
  abiDecodeValidBulk abiDecodeValidFiniteArray abiMalformedEntryProps

Theorem abi_valid_allocated_joint:
abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
  st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
abi_decode_ptr_window G tn s source (n2w B) L /\
ptr_covers G tn output s (type_memory_bytes ce ty) /\
op_prov G pos = NONE /\ op_prov G hi = NONE /\
op_taint tn pos = {} /\ op_taint tn hi = {} /\
allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s
==>
?u G' tn'.
  abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
    d (type_memory_bytes ce ty) s u /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,G',tn')) /\
  ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
  abi_decode_ptr_window G' tn' u source (n2w B) L /\
  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
     val_in_memory tv v d mem) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
     FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm /\
  (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
       ~abi_malformed_site_range
          (abi_malformed_scratch_sites st en func) s u a 1 ==>
       (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
  alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule abi_valid_allocated_joint_from_cases >>
  BETA_TAC >> rpt conj_tac >> rpt (first_assum ACCEPT_TAC)
  >- MATCH_ACCEPT_TAC (GEN_ALL (BETA_RULE abi_valid_allocated_joint_tuple))
  >- MATCH_ACCEPT_TAC (GEN_ALL (BETA_RULE abi_valid_allocated_joint_struct))
  >- (POP_ASSUM_LIST (K all_tac) >>
      rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
        (qpat_assum `abi_valid_allocated_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o PURE_REWRITE_RULE
              [abiValidAllocatedContractTheory.abi_valid_allocated_entry_def]) >>
         drule_then ACCEPT_TAC abi_malformed_entry_allocas_below_fmp) >>
      drule_all abi_valid_allocated_primitive_joint_observations >>
      disch_then (qspec_then `PG` ACCEPT_TAC))
  >- (POP_ASSUM_LIST (K all_tac) >>
      rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_valid_allocated_joint_bulk >> simp[] >>
      qexistsl_tac [`H0`, `abi_sz`, `ei`, `env`, `hi`, `live`,
                    `mem_sz`, `p`, `pos`, `sf`, `xs`] >> simp[])
  >- MATCH_ACCEPT_TAC (BETA_RULE abi_valid_allocated_finite_array_joint)
  >- MATCH_ACCEPT_TAC (GEN_ALL (BETA_RULE abi_valid_allocated_joint_fixed_array))
  >- (POP_ASSUM_LIST (K all_tac) >>
      rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
        (qpat_assum `abi_valid_allocated_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o PURE_REWRITE_RULE
              [abiValidAllocatedContractTheory.abi_valid_allocated_entry_def]) >>
         drule_then ACCEPT_TAC abi_malformed_entry_allocas_below_fmp) >>
      drule_all abi_valid_allocated_bytes_joint_observations >>
      disch_then (qspec_then `PG` ACCEPT_TAC))
  >- (qexistsl_tac [`H0`,`env`,`hi`,`live`,`p`,`pos`,`sf`,`xs`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
QED
