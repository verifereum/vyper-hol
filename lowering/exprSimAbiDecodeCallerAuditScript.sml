(* Proof-interface probes for the callers of the owned recursive contract. *)
Theory exprSimAbiDecodeCallerAudit
Ancestors
  exprSimAbiDecodeOwnedRows exprSimAbiDecodeSiteAllocation
  exprSimAbiDecodeSiteOwnership exprSimAbiDecodeOwnedContext
  actualDecoderSites abiBuiltinDecodeSetup
  finite_map pred_set words arithmetic

(* The builtin's output site lies strictly before the recursive interval.
   This covers both initial execution and a second visit reusing the site. *)
Theorem abi_decode_builtin_setup_ownership:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  abi_builtin_allocation_frame st.cs_next_var
    (abi_builtin_decode_output_site st min_size max_size) outsz s t /\
  alloca_inv s /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
      SOME(d,outsz)) ==>
  abi_decode_owned (abi_decode_sites ready.cs_next_id last)
    ({a | t.vs_alloca_next <= a} UNION
     {a | ?id b sz. id IN abi_decode_sites ready.cs_next_id last /\
       FLOOKUP t.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}) d outsz t
Proof
  strip_tac >> irule abi_decode_setup_output_owned >>
  metis_tac[abi_decode_setup_output_excluded]
QED

(* DynArray scratch allocation does not cost destination ownership or the
   explicit numeric source/site premise. The latter also covers zero sizes. *)
Theorem abi_decode_owned_scratch_allocate:
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit w] /\ inst.inst_outputs = [v] /\
  inst.inst_id IN sites /\ abi_decode_owned sites scratch d n s /\
  B+cnt <= s.vs_alloca_next /\
  (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint B cnt [(b,sz)]) ==>
  ?t b. exec_alloca inst s w = OK t /\ decode_site_resources ctx func t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,w2n w) /\
    abi_decode_alloc_progress sites s t /\ abi_decode_owned sites scratch d n t /\
    (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
      abi_footprint_disjoint B cnt [(b,sz)])
Proof
  strip_tac >> drule_all decode_site_allocation_progress >> strip_tac >>
  qexistsl_tac [`t`,`b`] >> simp[] >> conj_tac
  >- metis_tac[abi_decode_owned_transport] >>
  match_mp_tac abi_decode_alloc_progress_source_separation >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* Runtime-array iterations and static member offsets use the same bounded
   slice rule; in particular neither an empty element nor zero count requires
   a positive destination size. *)
Theorem abi_decode_owned_iteration_slice:
  abi_decode_owned sites scratch d n s /\
  abi_decode_alloc_progress sites s t /\ off+len <= n ==>
  abi_decode_owned sites scratch (d+off) len t
Proof
  metis_tac[abi_decode_owned_transport, abi_decode_owned_slice]
QED
