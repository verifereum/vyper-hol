Theory concretizePtrFrameOrigins
Ancestors concretizePtrRuntimeOrigins concretizePtrAllocationOrigins pointerClosure
  ptrDiscipline pointerConfinedDefs venomInst finite_map pred_set list words

Definition ptr_frame_site_roots_def:
  ptr_frame_site_roots fn A PG site =
    {v | ?i. MEM i (fn_insts fn) /\ MEM v i.inst_outputs /\
      ((i.inst_opcode = ALLOCA /\ FLOOKUP A i.inst_id = SOME site) \/
       (i.inst_opcode = PARAM /\ ?idx. i.inst_operands = [Lit idx] /\
         w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME site))}
End

Theorem ptr_frame_site_roots_finite:
  FINITE (ptr_frame_site_roots fn A PG site)
Proof
  irule SUBSET_FINITE_I >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, ptr_frame_site_roots_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem ptr_frame_site_step:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  (!aid p. FLOOKUP s'.vs_allocas aid = SOME p ==> FLOOKUP A aid = SOME p) ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site))
    (step_prov PG G inst s') site
Proof
  strip_tac >> irule ptr_site_step >> simp[] >>
  reverse conj_tac
  >- (qexists `fn` >> simp[] >>
      metis_tac[pointer_derived_vars_closed, ptr_frame_site_roots_finite])
  >> rpt strip_tac >>
  irule (pointer_derived_vars_roots |> REWRITE_RULE [SUBSET_DEF]) >>
  simp[ptr_frame_site_roots_finite] >>
  simp[ptr_frame_site_roots_def] >> qexists `inst` >> simp[] >>
  gvs[out_prov_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_frame_site_phis:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  EVERY (\i. MEM i (fn_insts fn)) insts ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site))
    (phis_prov prev G insts) site
Proof
  strip_tac >> irule ptr_site_phis >> simp[] >> qexists `fn` >> simp[] >>
  metis_tac[pointer_derived_vars_closed, ptr_frame_site_roots_finite]
QED

Theorem ptr_frame_site_entry:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site))
    (entry_prov fn s G) site
Proof
  strip_tac >> irule ptr_site_entry >> simp[] >>
  metis_tac[pointer_derived_vars_closed, ptr_frame_site_roots_finite]
QED

(* A later envelope containing the post-allocation table also contains the
   pre-allocation table. This is only a single-frame segment boundary. *)
Theorem ptr_frame_alloca_envelope_back:
  exec_alloca inst s n = OK s' /\
  (!aid p. FLOOKUP s'.vs_allocas aid = SOME p ==> FLOOKUP A aid = SOME p) ==>
  !aid p. FLOOKUP s.vs_allocas aid = SOME p ==> FLOOKUP A aid = SOME p
Proof
  metis_tac[exec_alloca_lookup_preserved]
QED
