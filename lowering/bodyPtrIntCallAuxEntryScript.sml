Theory bodyPtrIntCallAuxEntry
Ancestors
  bodyPtrDefs bodyPtrIntCallGhostTaint fragExecPtr intCallCallee
  ptrDiscipline venomInst emitHelperProps finite_map

(* PARAM reads only its own provenance position. Scalar positions may be
   erased for an auxiliary run; memory and return-buffer positions must not. *)
Theorem intcall_param_step_prov:
  w2n idx < LENGTH PG ==>
  step_prov PG G (mk_inst id PARAM [Lit idx] [p]) s =
    set_prov G [p] (EL (w2n idx) PG)
Proof
  simp[step_prov_def, out_prov_def, mk_inst_def]
QED

Theorem intcall_scalar_param_erased:
  step_prov [NONE] FEMPTY (mk_inst id PARAM [Lit 0w] [p]) s = FEMPTY
Proof
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       finite_mapTheory.DRESTRICT_FEMPTY]
QED

Theorem intcall_memory_param_retained:
  step_prov [SOME site] FEMPTY (mk_inst id PARAM [Lit 0w] [p]) s =
    FEMPTY |+ (p,site)
Proof
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def]
QED

(* Entry audit (not an assumed contract).
   moduleLowering.materialize_internal_params, lines 402--420, allocates a
   fresh local for a stack parameter, then MSTOREs the scalar into it. Its
   local pointer's provenance is supplied by step_prov_alloca, independently
   of the scalar PARAM site. mstore_word_clean supplies clean written bytes
   from clean scalar taint. A memory parameter instead becomes the local
   PtrVar directly and therefore needs the retained site. The optional
   return buffer occupies position 0 and must also retain its site.

   The actual body IH consumer is stmt_frag_ptr (bodyPtrDefs:289--300).
   ghost_inv observes local pointers and return-buffer pointers, not the
   scalar PARAM itself. Its storage and return-PC clauses do not observe PG.
   Thus there is no scalar-site obstruction in these entry definitions.
   However compile_internal_prologue_entry (intCallCallee:2376--2418)
   supplies only stmt_state_rel and a semantic run prefix. It supplies no
   ghost_inv or counted pointer-safe prologue for EITHER provenance list.
   The exact missing consumer premise is ghost_inv d cenv_body cxf
   (vs with scopes := [env]) G_body tn_body s_body, with G_body/tn_body
   obtained by the actual prologue ghost execution, together with its
   counted safe path from setup_callee. This must be proved, not inferred
   from the S1 state relation. The equations above are representative PARAM
   tests, not a proof of that whole entry contract.

   Two body-IH applications can have different path lengths and run fuel.
   gas_path_ptr_exec:223--238 yields non-error run/ghost/safety witnesses for
   each exit; aligning them requires successful-run fuel monotonicity and
   ghost_fuel_mono_up, not determinism of an arbitrary low-fuel execution.
   intcall_ghost_run_taint_prov_independent applies only AFTER selecting a
   common fuel. No safety invariance under erasing provenance is asserted.
*)

Theorem intcall_singleton_ghost_inv:
  lookup_var p s = SOME w /\ op_taint tn (Var p) = {} /\
  FLOOKUP G p = SOME (b,n) /\ b <= w2n w /\ w2n w + sz <= b+n /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem) /\
  return_buf_ptr d
    (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var p) sz)) G tn s /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
         op_taint tn (Var x) = {}) /\ stor_taint_ok cx tn s ==>
  ghost_inv d (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var p) sz))
    cx (vs with scopes := [FEMPTY |+ (name,entry)]) G tn s
Proof
  rpt strip_tac >>
  simp[ghost_inv_def, vyperStateTheory.lookup_scopes_def,
       FLOOKUP_UPDATE, ptr_covers_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_stack_singleton_ghost_inv:
  cenv.ce_return_pc = NONE /\ p <> q /\ b < dimword (:256) /\ 32 <= n /\
  lookup_var p s = SOME (n2w b) /\ op_taint tn (Var p) = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value b mem) /\
  stor_taint_ok cx tn s ==>
  ghost_inv NONE (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var p) 32))
    cx (vs with scopes := [FEMPTY |+ (name,entry)])
    (FEMPTY |+ (p,(b,n))) tn s /\
  ghost_inv NONE (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var p) 32))
    cx (vs with scopes := [FEMPTY |+ (name,entry)])
    (FEMPTY |+ (p,(b,n)) |+ (q,site)) tn s
Proof
  strip_tac >> conj_tac >> irule intcall_singleton_ghost_inv >>
  simp[return_buf_ptr_def, FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  metis_tac[]
QED

Theorem intcall_memory_singleton_ghost_inv:
  cenv.ce_return_pc = NONE /\
  lookup_var p s = SOME w /\ op_taint tn (Var p) = {} /\
  b <= w2n w /\ w2n w + sz <= b+n /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem) /\
  stor_taint_ok cx tn s ==>
  ghost_inv NONE (cenv with ce_vars := FEMPTY |+ (name,PtrVar (Var p) sz))
    cx (vs with scopes := [FEMPTY |+ (name,entry)])
    (FEMPTY |+ (p,(b,n))) tn s
Proof
  strip_tac >> irule intcall_singleton_ghost_inv >>
  simp[return_buf_ptr_def, FLOOKUP_UPDATE] >> metis_tac[]
QED
