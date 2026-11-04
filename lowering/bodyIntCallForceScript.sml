(* Clean runtime forcing: code-aware allocation and copy composition. *)
Theory bodyIntCallForce
Ancestors
  bodyIntCallArgList bodyIntCallForceFrame loweringSlice exprLoweringProps
  exprSim exprSimOperands context compileEnv venomExecSemantics venomInst
  words finite_map list localPtrsProps venomState

(* Preserve the full statement relation across allocation, including replay.
   This supplements the destination-window contract, rather than rebuilding
   its individual invariant clauses at every aggregate-copy consumer. *)
Theorem compile_alloc_buffer_stmt_step:
  !ctx func cenv cx es s n sm buf sb s'.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    step_inst_base
      (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sm.cs_next_var)]) s = OK s' ==>
    stmt_state_rel ctx func cenv cx es s'
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_member >> strip_tac >>
  `~not_fresh_at sm (STRING #"%" (toString sm.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sm.cs_next_var))` by
    metis_tac[fresh_not_local_ptr] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def] >> strip_tac >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  simp[mk_inst_def] >> metis_tac[mk_inst_def]
QED

(* Runtime copies cannot affect immutables: their image is in the data
   section. Only live-local byte agreement is needed for the memory part. *)
Theorem runtime_stmt_memory_frame:
  !ctx func cenv cx es s mem.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      mem_bytes_at b sz mem = mem_bytes_at b sz s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_memory := mem)
Proof
  rpt strip_tac >> irule stmt_state_rel_allocas_frame >>
  conj_tac >- simp[immutable_alloca_sep_def] >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes (s with vs_memory := mem)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def, lookup_var_def] >>
     conj_tac
     >- (rpt strip_tac >> sym_tac >> first_x_assum irule >>
         goal_assum drule) >>
     rpt strip_tac >> gvs[]) >>
  irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`es`, `s`] >>
  fs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_stmt_memory_window:
  !ctx func cenv cx es s mem b n.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
      regions_disjoint b n lo sz) /\
    (!off len. off+len <= b \/ b+n <= off ==>
      mem_bytes_at off len mem = mem_bytes_at off len s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_memory := mem)
Proof
  rpt strip_tac >> irule runtime_stmt_memory_frame >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_x_assum `!name lo sz. local_region _ _ _ name lo sz ==> _` drule >>
  simp[compileEnvTheory.regions_disjoint_def]
QED
