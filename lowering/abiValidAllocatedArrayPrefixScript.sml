(* Typed initialized prefixes and cumulative allocation-backed loop effects. *)
Theory abiValidAllocatedArrayPrefix
Ancestors
  abiValidAllocatedContract abiMalformedRecursiveInterface abiMalformedSiteFrame
  exprSimAggregateEncoding valueEncodingProps valueEncoding venomState venomMemDefs
  exprLoweringProps exprSimDefs compileEnv words list arithmetic finite_map

Definition abi_valid_allocated_array_prefix_def:
  abi_valid_allocated_array_prefix tv vs j d (s:venom_state) <=>
    j <= LENGTH vs /\ mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
    !k. k < j ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) s.vs_memory
End

Theorem abi_valid_allocated_array_prefix_zero:
  abi_valid_allocated_array_prefix tv vs 0 d s <=>
  mem_word_at d s.vs_memory = n2w (LENGTH vs)
Proof
  simp[abi_valid_allocated_array_prefix_def]
QED

Theorem abi_valid_allocated_array_prefix_step:
  abi_valid_allocated_array_prefix tv vs j d s /\ j < LENGTH vs /\
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) t.vs_memory) /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory ==>
  abi_valid_allocated_array_prefix tv vs (SUC j) d t
Proof
  rw[abi_valid_allocated_array_prefix_def] >>
  Cases_on `k = j` >> gvs[]
QED

Theorem abi_valid_allocated_array_prefix_complete:
  abi_valid_allocated_array_prefix tv vs (LENGTH vs) d s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp[abi_valid_allocated_array_prefix_def, val_in_memory_dynarray] >>
  strip_tac >> irule elems_in_memory_intro >> simp[]
QED

Definition abi_valid_allocated_effect_def:
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n s t <=>
    abi_malformed_resource_post ctx func cenv cx es next sites dstid s t /\
    abi_valid_allocated_frame sites d n s t /\
    (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b)
End

Theorem abi_valid_allocated_effect_trans:
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n s t /\
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n t u ==>
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n s u
Proof
  simp_tac bool_ss [abi_valid_allocated_effect_def] >> strip_tac >>
  `alloca_inv t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_alloca_next <= u.vs_alloca_next` by
    fs[abi_malformed_resource_post_def, stmt_state_rel_def] >>
  conj_tac >- metis_tac[abi_malformed_resource_trans] >>
  conj_tac >- (irule abi_valid_allocated_frame_trans >> qexists_tac `t` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!id b sz. FLOOKUP u.vs_allocas id = _ ==> _` drule >>
  strip_tac >- metis_tac[] >> disj2_tac >> decide_tac
QED
