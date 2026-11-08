(* Endpoint backing for the hypothetical Empty local, not a full entry witness. *)
Theory immutableDeployLocalBackingProbe
Ancestors
  immutableDeployLocalCodeProbe compileEnv venomState valueEncoding

Theorem local_backed_zero_at_frontier:
  !func p ss b.
    (!aid lo sz. FLOOKUP ss.vs_allocas aid = SOME (lo,sz) ==> lo + sz <= b) ==>
    local_backed func p ss b 0
Proof
  rpt strip_tac >> rewrite_tac[local_backed_def] >> disj2_tac >>
  rpt strip_tac >> simp[compileEnvTheory.regions_disjoint_def] >>
  metis_tac[]
QED

Definition local_probe_backing_state_def:
  local_probe_backing_state (s:venom_state) = s with
    <|vs_vars := FEMPTY |+ ("%0",0w) |+ ("%1",128w);
      vs_allocas := FEMPTY |+ (1,(96,32)); vs_alloca_next := 128|>
End

Theorem local_probe_endpoint_backing:
  !s.
    lookup_var "%1" (local_probe_backing_state s) = SOME (n2w 128) /\
    (local_probe_backing_state s).vs_allocas = FEMPTY |+ (1,(96,32)) /\
    128 <= (local_probe_backing_state s).vs_alloca_next /\
    local_backed local_probe_fn "%1" (local_probe_backing_state s) 128 0
Proof
  gen_tac >> simp[local_probe_backing_state_def, lookup_var_def,
                  finite_mapTheory.FLOOKUP_UPDATE] >>
  irule local_backed_zero_at_frontier >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[]
QED

Theorem local_probe_empty_value_layout:
  !b mem. type_memory_size (StructTV []) = 0 /\
    val_wf (StructTV []) (StructV []) /\
    val_in_memory (StructTV []) (StructV []) b mem
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem local_probe_empty_local_ptrs:
  !s entry.
    entry.type = StructTV [] /\ entry.value = StructV [] ==>
    local_ptrs_rel local_probe_fn local_probe_empty_ce
      [FEMPTY |+ ("x",entry)] (local_probe_backing_state s)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >>
      simp[vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE,
           AllCaseEqs()] >> strip_tac >> gvs[] >>
      gvs[local_probe_empty_local_metadata] >>
      qexists `128w` >>
      simp[local_probe_endpoint_backing, local_probe_empty_value_layout,
           wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
      simp[local_probe_backing_state_def]) >>
  rpt gen_tac >>
  simp[local_region_def, vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem local_probe_recorded_size_not_zero:
  !s. FLOOKUP (local_probe_backing_state s).vs_allocas 1 = SOME (96,32) /\
      FLOOKUP (local_probe_backing_state s).vs_allocas 1 <> SOME (128,0)
Proof
  simp[local_probe_backing_state_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
