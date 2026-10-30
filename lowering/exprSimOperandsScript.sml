(*
 * Operand composition for memory-backed operands (#636, Infrastructure)
 *
 * Two operands lowered in turn: the first one's fragment ends in its
 * expr_post, from which the second one's fragment runs to its own.  The
 * first one's value must still hold when both are done.  For a word type it
 * is the operand itself, a literal or a variable handed out before the
 * second fragment, which keeps those.  For any other type it sits in memory,
 * and the second fragment's expr_post keeps the memory of the allocations
 * made before it, but its own and those holding a live local.  So the first
 * value is kept where it sits in one of the first operand's own allocations
 * and that allocation holds no live local (expr_val_in_alloca): its bytes
 * survive the second fragment, and val_in_memory with them, as val_in_memory
 * reads only the value's val_footprint bytes (exprSim's
 * expr_val_rel_footprint_agree).
 *
 * A first operand that points into a live local's region (expr_val_at's
 * other case) is not covered here.  The second fragment's expr_post keeps
 * that region's bytes (locals_kept) but a DynArray local's length word,
 * which x.pop() writes and expr_val_at lets only a DynArray value cover.
 *
 * TOP-LEVEL:
 *   expr_val_in_alloca      — a memory value sits in one of the
 *                             expression's own allocations, which holds no
 *                             live local
 *   expr_val_in_alloca_at   — it gives expr_val_at
 *   expr_val_in_alloca_intro — from the ALLOCA instruction behind the
 *                             allocation, whose output is no live local's
 *                             pointer
 *   expr_post_operand_kept  — KEY LEMMA: the first operand's value, related
 *                             and placed, through the second's expr_post
 *   expr_post_operand_kept_at — the same with expr_val_at, as expr_post has
 *                             it
 *
 * Helpers: fresh_not_local_ptr, alloca_clear_of_locals,
 *   expr_post_operand_word
 *)

Theory exprSimOperands
Ancestors
  finite_map
  exprSim exprSimOps localPtrsProps compileEnv exprLoweringProps
  valueEncodingProofs venomState venomInst

(* ===== Values in an expression's own allocations ===== *)

(* The value v of an expression of type t, lowered from compile state sa
   to sb, sits in s, when t is not a word type, in an allocation of one of
   the expression's own ALLOCAs that holds no live local at es: expr_val_at's
   first case, with the allocation clear of the locals' regions.  This is
   the case a later operand's expr_post keeps. *)
Definition expr_val_in_alloca_def:
  expr_val_in_alloca cenv cx t sa sb es v op s <=>
    !tv. evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t ==>
      val_wf tv v /\
      ?w aid b sz.
        eval_operand op s = SOME w /\
        FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
        sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
        !n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                   b + sz <= lb \/ lb + lsz <= b
End

Theorem expr_val_in_alloca_at:
  !cenv cx t sa sb es v op s.
    expr_val_in_alloca cenv cx t sa sb es v op s ==>
    expr_val_at cenv cx t sa sb es v op s
Proof
  rewrite_tac[expr_val_in_alloca_def, expr_val_at_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `tv` mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> simp[] >> metis_tac[]
QED

(* Helper: a variable fresh at st is no live local's pointer. *)
Theorem fresh_not_local_ptr:
  !cenv st scopes q.
    local_ptrs_reserved cenv st /\ ~not_fresh_at st q ==>
    not_local_ptr cenv scopes q
Proof
  rw[not_local_ptr_def, local_ptrs_reserved_def] >> strip_tac >>
  metis_tac[]
QED

(* Helper: the allocation of an ALLOCA of func whose output is no live
   local's pointer lies clear of every live local's region. *)
Theorem alloca_clear_of_locals:
  !func cenv cx es s inst q b sz n lb lsz.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b, sz) /\
    local_region cenv es.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b
Proof
  rpt strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def]
QED

(* expr_val_in_alloca from the ALLOCA behind the value's allocation: an
   instruction of func with an id the expression handed out, whose output
   is no live local's pointer (by fresh_not_local_ptr, one fresh at the
   expression's start). *)
Theorem expr_val_in_alloca_intro:
  !func cenv cx t sa sb es v op s.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t ==>
       val_wf tv v /\
       ?w inst q b sz.
         eval_operand op s = SOME w /\
         MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
         not_local_ptr cenv es.scopes q /\
         FLOOKUP s.vs_allocas inst.inst_id = SOME (b, sz) /\
         sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
         b <= w2n w /\ w2n w + val_footprint tv v <= b + sz) ==>
    expr_val_in_alloca cenv cx t sa sb es v op s
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_val_in_alloca_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tv. _` (qspec_then `tv` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w`, `inst.inst_id`, `b`, `sz`] >> simp[] >>
  rpt strip_tac >> drule_all alloca_clear_of_locals >> simp[]
QED

(* ===== Composition ===== *)

(* Helper: the first operand, a literal or a variable handed out before
   the second fragment, holds the same word at the second's end. *)
Theorem expr_post_operand_word:
  !func cenv cx e1 e2 es es1 es' sa s1 s2 s0 t u v1 v2 x y.
    expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
    ?w. eval_operand x t = SOME w /\ eval_operand x u = SOME w
Proof
  rpt strip_tac >>
  `?w. eval_operand x t = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  qexists_tac `w` >> simp[] >>
  irule eval_operand_frame >> simp[] >>
  qexistsl_tac [`s1`, `t`] >> fs[expr_post_def]
QED

(* KEY LEMMA: operand composition.  The first operand's value, sitting in
   one of its own allocations clear of the live locals, survives the second
   operand's fragment: still related by expr_val_rel, and still in that
   allocation, an id below the second's end counter, clear of the locals at
   the source state after the second operand.  The latter lets a third
   operand's expr_post keep it again. *)
Theorem expr_post_operand_kept_stable:
  !func cenv cx e1 e2 es es1 es' sa s1 s2 s0 t u v1 v2 x y.
    expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t /\
    expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
    local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
    s1.cs_next_id <= s2.cs_next_id ==>
    expr_val_rel cx (expr_type e1) v1 x u /\
    expr_val_in_alloca cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  rpt gen_tac >> strip_tac >>
  `?wx. eval_operand x t = SOME wx` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME wx` by metis_tac[] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e1)`
  >- simp[expr_val_rel_def, expr_val_in_alloca_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  qpat_x_assum `expr_post _ _ _ e1 _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `expr_post _ _ _ e2 _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  Cases_on `is_word_type (expr_type e1)`
  >- (simp[expr_val_in_alloca_def] >> fs[expr_val_rel_def] >> gvs[]) >>
  qpat_x_assum `expr_val_in_alloca _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_in_alloca_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  `eval_operand x u = SOME w` by gvs[] >>
  (* the second fragment keeps the allocation, and its bytes *)
  `FLOOKUP u.vs_allocas aid = SOME (b, sz)` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (first_x_assum irule >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> simp[]) >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  conj_tac
  >- (irule expr_val_rel_footprint_agree >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`t`, `tv`, `w`] >> simp[]) >>
  (* still clear of the locals, which the second fragment kept *)
  rewrite_tac[expr_val_in_alloca_def] >> qx_gen_tac `tv2` >> strip_tac >>
  `tv2 = tv` by fs[] >> pop_assum SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w`, `aid`, `b`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!n lb lsz. local_region _ es1.scopes t _ _ _ ==> _` irule >>
  qexists_tac `n` >>
  irule local_region_frame >>
  conj_tac >- (qexists_tac `func` >>
    gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`s1`, `es'.scopes`, `u`] >> simp[]
QED

Theorem expr_post_operand_kept:
  !func cenv cx e1 e2 es es1 es' sa s1 s2 s0 t u v1 v2 x y.
    expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t /\
    expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
    s1.cs_next_id <= s2.cs_next_id ==>
    expr_val_rel cx (expr_type e1) v1 x u /\
    expr_val_in_alloca cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_post_operand_word >> strip_tac >>
  `!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w` by
    (rpt strip_tac >> gvs[]) >>
  drule_all expr_post_operand_kept_stable >> simp[]
QED

(* expr_post_operand_kept with expr_val_at, the placement expr_post asks
   for. *)
Theorem expr_post_operand_kept_at:
  !func cenv cx e1 e2 es es1 es' sa s1 s2 s0 t u v1 v2 x y.
    expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
    expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t /\
    expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
    s1.cs_next_id <= s2.cs_next_id ==>
    expr_val_rel cx (expr_type e1) v1 x u /\
    expr_val_at cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_post_operand_kept >> strip_tac >>
  simp[expr_val_in_alloca_at]
QED

(* A non-dynamic-array value in a local stays outside its mutable length
   word. This is the local-region counterpart of allocation preservation. *)
Theorem expr_post_operand_local_kept:
  expr_val_rel cx ty v op s /\
  ~is_word_type ty /\ ~dynarray_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
  local_region cenv es.scopes s n b sz /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (dynarray_local cenv n /\ ~dynarray_type ty ==> b + 32 <= w2n w) /\
  expr_post func cenv cx e es sa sb s es' v' op' s' ==>
  expr_val_rel cx ty v op s'
Proof
  strip_tac >> irule expr_val_rel_footprint_agree >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`s`, `tv`, `w`] >> simp[] >>
  sym_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `locals_kept _ _ _ _`
    (mp_tac o REWRITE_RULE [locals_kept_def]) >>
  disch_then irule >> qexistsl_tac [`b`, `n`, `sz`] >> simp[]
QED
