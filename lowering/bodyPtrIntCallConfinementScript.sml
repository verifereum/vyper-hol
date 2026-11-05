(* Set-level boundaries only; no whole-run confinement is assumed here. *)
Theory bodyPtrIntCallConfinement
Ancestors bodyPtrDefs decoderGhostFramePtr ptrSafeRun ptrDiscipline
  venomExecSemantics
  finite_map pred_set list

Definition intcall_site_outside_def:
  intcall_site_outside P (b:num,n:num) <=>
    DISJOINT P {i | b <= i /\ i < b + n}
End

Definition intcall_prov_outside_def:
  intcall_prov_outside P PG G <=>
    (!site. MEM (SOME site) PG ==> intcall_site_outside P site) /\
    (!x site. FLOOKUP G x = SOME site ==> intcall_site_outside P site)
End

Definition intcall_mem_frame_def:
  intcall_mem_frame P (tn0:taint) (tn:taint) <=>
    tn.t_mem INTER P SUBSET tn0.t_mem
End

Definition intcall_protected_def:
  intcall_protected cenv (es:evaluation_state) sa (s0:venom_state) =
    {i | (?aid off sz.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz) \/
    (?n b sz. local_region cenv es.scopes s0 n b sz /\
      b <= i /\ i < b + sz /\
      (!k. dynarray_len_at cenv n k ==> i < b + k \/ b + k + 32 <= i))}
End

Theorem intcall_mem_frame_refl:
  intcall_mem_frame P tn tn
Proof
  simp[intcall_mem_frame_def, INTER_SUBSET]
QED

Theorem intcall_mem_frame_trans:
  intcall_mem_frame P tn0 tn1 /\ intcall_mem_frame P tn1 tn2 ==>
  intcall_mem_frame P tn0 tn2
Proof
  simp[intcall_mem_frame_def] >> SET_TAC[]
QED

Theorem intcall_ghost_kept_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn <=>
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  intcall_mem_frame (intcall_protected cenv es sa s0) tn0 tn
Proof
  simp[ghost_kept_def, intcall_mem_frame_def, intcall_protected_def,
       SUBSET_DEF, IN_INTER, GSPECIFICATION] >> metis_tac[]
QED

Theorem intcall_mem_frame_step:
  new_site_bytes s t SUBSET COMPL P /\
  written_taint tn inst s SUBSET COMPL P ==>
  intcall_mem_frame P tn (step_taint inst s t tn)
Proof
  strip_tac >> drule_all step_taint_memory_bound >>
  simp[intcall_mem_frame_def, SUBSET_DEF, IN_INTER, IN_UNION,
       IN_COMPL] >> metis_tac[]
QED

Theorem intcall_prov_outside_invoke:
  intcall_prov_outside P PG G ==>
  intcall_prov_outside P (MAP (op_prov G) ops) FEMPTY
Proof
  simp[intcall_prov_outside_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `SOME site = op_prov G op` >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem intcall_mem_frame_invoke:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  intcall_mem_frame P tn0
    (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs)) ==>
  intcall_mem_frame P tn0 (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  disch_then (fn th => rewrite_tac[th]) >>
  gvs[intcall_mem_frame_def]
QED

Theorem intcall_mem_frame_reset:
  intcall_mem_frame P tn0 (tn with t_var := FEMPTY) <=>
  intcall_mem_frame P tn0 tn
Proof
  simp[intcall_mem_frame_def]
QED

(* Entry reset keeps the frontier but discards allocation ids. *)
Theorem intcall_setup_allocator:
  setup_callee fn args s = SOME cs ==>
  cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
  cs.vs_fmp = s.vs_fmp /\ cs.vs_memory = s.vs_memory
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[]
QED

(* Ordinary merge restores the caller's allocator, not the callee frontier. *)
Theorem intcall_merge_allocator:
  (merge_callee_state s cs).vs_allocas = s.vs_allocas /\
  (merge_callee_state s cs).vs_alloca_next = s.vs_alloca_next
Proof
  simp[merge_callee_state_def]
QED

(* C1.2.2 allocator/provenance premise ledger.
   - setup_callee resets allocation ids, not vs_alloca_next or memory (checked
     above). ALLOCA reuses existing ids, otherwise allocates at the frontier
     (venomExecSemantics.exec_alloca_def). Thus required invariant: every
     existing allocation site avoids P, and every byte at/above the current
     frontier avoids P. Instruction-id freshness alone is insufficient.
   - merge_callee_state restores the caller allocator (checked above).
     A nested call can allocate in its own fresh map and return with a
     larger private frontier; caller continuation reuses the old frontier.
     This does not break confinement if both frontiers are above P, but
     global frontier monotonicity through merge is the wrong invariant.
   - ptr judgments assume ~ctx_has_dalloca. This excludes DALLOCA in every
     context function; generic code with DALLOCA would additionally need
     separation of FMP allocations and overflow control. new_site_bytes also
     includes any FMP increase, not just new ALLOCA map entries.
   - PARAM takes the entire EL idx PG site. ADD/SUB/ASSIGN take first_prov;
     PHIs take op_prov of a selected input. These definitions support
     site closure by finite-map/list reasoning, without narrowing a site
     to the used value footprint. INVOKE restores only restricted caller G.
     pointerConfinedDefs is structural pointer-use discipline, not this
     dynamic protected-byte invariant.
   - Actual staging (compile_stage_intcall_args_def) allocates fresh buffers
     for F flags; T flags simply unwrap. unwrap_value returns the operand
     unchanged for StackValue, or MLOADs a LocatedValue of word type. A
     non-word LocatedValue in LocMemory unwraps to its original pointer.
     Therefore the T branch can carry an old complete site unless the
     pass-via-stack/typing invariant rules that case out. This call-site
     exclusion and zero provenance for stack scalar values remain MISSING
     as checked theorem interfaces (not claimed false).
   - S1 stage_mem_arg_frag supplies ordinary values and memory equality,
     not ghost-site separation. S1 compile_internal_prologue_entry supplies
     no PG/G or protected-byte bound. Missing: pointer-counted staging,
     P below caller frontier, whole-site separation of return buffer and
     all inherited operand sites. local_region_below_frontier is local in
     intCallFrame; a reusable boundary or direct derivation is still needed.
   - A prospective whole-run theorem should preserve conjunction of
     intcall_prov_outside P PG G, site exclusion of vs_allocas, frontier
     lower bound above P, and intcall_mem_frame P tn0 tn. It must be mutual
     over ghost_step/block/blocks with their lexicographic fuel/block-tail
     measure, matching ptr_safe_step/block/blocks. Entry PHIs preserve site
     exclusion; nested calls use the same fixed protected set, not the
     callee's own ghost_kept protected set. Missing: written_taint bound
     from access_ok under site exclusion, including fixed-region accesses
     and in_revert_forward exceptions; allocator/FMP increase bound;
     recursive nested-call closure. No whole-run claim follows just from
     the checked conditional INVOKE boundary.
*)

(* C1.2.3 proposed preparation contracts (DESIGN ONLY; no exported claims).

   SOURCE PREFIXES. Name the three antecedents at Eq lines 21--83 HB, HD,
   HA, respectively (including their universal binders), and name their
   conjunctions of successful equations PB, PD, PA. Exact elimination
   signatures, with the displayed variables universally quantified, are:
     HA /\ PA ==> body_results_ptr_ok cx es
     HD /\ PD ==> body_exprs_ptr_ok cxd needed_dflts
     HB /\ PB ==> body_stmts_ptr_ok cxf body'
   These are direct specializations, not strengthened IHs. PA must be
   extracted before argument evaluation, PD after successful results and
   scope reset, PB only after defaults/read_results/binding/push_function.
   Successful source-prefix equations supply every extra premise here;
   no Venom or ghost premise is involved. Proposed helpers should factor
   the source decomposition once rather than copy all tuple projections.

   DEFAULTS. There is NO default-expression phase in compile_call IntCall
   (exprLowering 2627--2667), or in compile_internal_function
   (moduleLowering 658--734). The latter captures/materializes params,
   reserves stack return storage, locks, and compiles the body. The
   supported_function_header_contract (supportedDecls 120 onward) requires
   NULL defaults. Thus the proposed signature to discharge this phase is:
     supported_declaration_header tops
       (FunctionDecl vis mut nr rr name args defaults ret body) ==>
     defaults = [] /\
     DROP (LENGTH defaults - (LENGTH args - LENGTH es)) defaults = []
   Supplier: supported_function_header_contract and list simplification.
   Remaining proof obligation: recover that header for the actual runtime
   lookup from body_inv/supported_program, using selectedBodyCode and
   returnMetadataPtr lookup interfaces. Do NOT invent counted default
   instructions in caller or callee. HD still belongs in source-prefix
   elimination; after header recovery body_exprs_ptr_ok cxd [] is trivial.

   ARGUMENTS. Proposed counted-list interface (schema with A defined
   below; all variables universally quantified):
     body_results_ptr_ok cx es /\
     compile_multi_vvs compile_expr cenv es sa = (vvs,sb) /\ A ==>
     gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
       (eval_expr_results cx es) (ee,s0,G0,tn0)
       (\res ee' G tn t. ?results. res = INL results /\
          LIST_REL (\e tv. T) es results /\
          stmt_state_rel ctx func cenv cx ee' t /\
          ghost_inv d cenv cx ee' G tn t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_kept cenv ee sa G0 tn0 s0 G tn /\
          !i. i < LENGTH es ==>
            ptr_vv_ok cx (expr_type (EL i es)) (EL i results)
                      (EL i vvs) ee' G tn t)
       (\res ee' gt r. expr_exit res r)
   Here LIST_REL above specifies equal lengths only; the final implementation
   MUST additionally carry the ordinary multi-vv post (per-element vv_post
   transported across later evaluations), and ptr_buf_ok for each memory
   operand, exactly as expr_vv_sim_ptr does. This is an unresolved interface
   detail, not permission to assume persistence. A is exactly the common
   code/ids/reservation/runtime/no-dalloca/old-return-variable/initial-PC,
   state-rel and ghost premises of expr_vv_sim_ptr, plus body_inv and
   per-expression typing/supported preconditions, with gas_admissible for
   eval_expr_results. Suppliers: argument IH, body_ptr predicates and
   expr_vv_sim_ptr; composition gas_outcome_ptr_bind and ghost_kept
   transport. MISSING: proved counted list composition and transported
   multi-vv post. S1 simulation cannot supply a pointer path.

   STAGING. The proposed final-state payload is the following exact HOL
   formula, to be conjoined with ordinary internal_args_rel and counted
   pointer-safe execution of compile_stage_intcall_args:
     eval_operands ops t = SOME words /\
     EVERY (\op. op_taint tn op = {}) ops /\
     intcall_prov_outside P (MAP (op_prov G) ops) FEMPTY /\
     intcall_mem_frame P tn0 tn
   P = intcall_protected cenv ee sa s0 is fixed at expression entry, NOT
   recomputed at a callee state. ops includes buf_prefix exactly when
   returns_count = 0 and return_buf is SOME. Ordinary supplier:
   stage_mem_arg_frag / internal_args_rel. MISSING pointer suppliers:
   fresh-buffer typed-copy counted path, whole-site exclusion after copies,
   clean stack operands (including proof that the T flag cannot forward an
   older aggregate pointer), and framing through unwrap_value.
   Additional INVOKE-entry allocator requirements, stated exactly, are:
     (!id b n. FLOOKUP t.vs_allocas id = SOME (b,n) ==>
                 intcall_site_outside P (b,n)) /\
     (!a. t.vs_alloca_next <= a ==> a NOTIN P)
   MISSING suppliers at call site; the old-map reset alone supplies neither.
   Return buffer also needs ptr_covers and clean pointer operand taint;
   its contents need not be clean. compile_call allocates it BEFORE staging
   and after argument evaluation, for 32*returns_count or return_buf_size.

   ABNORMAL/GAS. Counted arguments must retain the gas_outcome_ptr abnormal
   post above, not only a successful argument-list theorem. Source failures
   before PA require source lookup/typechecking impossibility or the
   gas-exempt branch, not an unavailable argument IH. Subsequent source
   failures similarly cannot justify PB. Existing gasIntCallArgs/Body
   provide ordinary gas-exempt facts only; pointer outcomes still require
   the appropriate empty/prefix outcome combinators. These remain proof
   obligations. No whole-run confinement is claimed by any proposed
   payload, and no target hypothesis may be added to supply missing facts.
*)
