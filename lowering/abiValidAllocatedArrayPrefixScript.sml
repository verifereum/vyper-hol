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

(* Writes at or beyond the next element preserve the initialized prefix. *)
Theorem abi_valid_allocated_array_prefix_frame:
  abi_valid_allocated_array_prefix tv vs j d s /\
  EVERY (val_wf tv) vs /\
  abi_valid_allocated_frame sites cd cn s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ aid NOTIN sites /\
  B <= d /\ d+32+j*type_memory_size tv <= B+cap /\
  d+32+j*type_memory_size tv <= cd ==>
  abi_valid_allocated_array_prefix tv vs j d t
Proof
  strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (irule abi_valid_allocated_frame_owned_slice >>
     qpat_assum `abi_valid_allocated_frame _ _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP s.vs_allocas aid = _` (irule_at Any) >> simp[]) >>
  simp_tac bool_ss [abi_valid_allocated_array_prefix_def] >>
  conj_tac >- fs[abi_valid_allocated_array_prefix_def] >>
  conj_tac >- fs[abi_valid_allocated_array_prefix_def,
                 abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  rpt strip_tac >>
  `SUC k * type_memory_size tv <= j * type_memory_size tv` by
    (irule LESS_MONO_MULT2 >> decide_tac) >>
  `d+32+k*type_memory_size tv+type_memory_size tv <=
     d+32+j*type_memory_size tv` by
    (qpat_x_assum `SUC k * _ <= _` mp_tac >>
     simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
  irule val_in_memory_mem_agree >>
  conj_tac >- (fs[EVERY_EL] >> first_x_assum irule >>
               fs[abi_valid_allocated_array_prefix_def]) >>
  qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  reverse conj_tac >- fs[abi_valid_allocated_array_prefix_def] >>
  sym_tac >> irule abi_valid_allocated_frame_owned_slice >>
  qpat_assum `abi_valid_allocated_frame _ _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP s.vs_allocas aid = _` (irule_at Any) >> simp[]
QED

Theorem abi_valid_allocated_effect_refl:
  stmt_state_rel ctx func cenv cx es s ==>
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n s s
Proof
  simp[abi_valid_allocated_effect_def, abi_malformed_resource_refl,
       abi_valid_allocated_frame_refl]
QED

(* Code layout is a consumer premise, not part of the memory invariant. *)
Definition abi_valid_allocated_array_inv_def:
  abi_valid_allocated_array_inv ctx func cenv cx es start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz
      ip slot inst q hdr tv vs origin j u <=>
    abi_malformed_entry ctx func cenv cx es start sites dstid live
      base_op hi src dst B L xs p d outsz u /\
    abi_valid_allocated_array_prefix tv vs j d u /\
    eval_operand ip u = SOME (n2w slot) /\ mload slot u = n2w j /\
    slot < dimword (:256) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32) /\
    inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
    fresh_vars_wrt limit_st u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
      sites dstid d outsz origin u
End

Theorem abi_valid_allocated_array_inv_complete:
  abi_valid_allocated_array_inv ctx func cenv cx es start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin (LENGTH vs) u ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d u.vs_memory
Proof
  rw[abi_valid_allocated_array_inv_def] >>
  irule abi_valid_allocated_array_prefix_complete >> simp[]
QED

Theorem abi_valid_allocated_array_prefix_empty:
  mem_word_at d s.vs_memory = 0w ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV [])) d s.vs_memory
Proof
  strip_tac >> irule abi_valid_allocated_array_prefix_complete >>
  simp[abi_valid_allocated_array_prefix_zero]
QED
