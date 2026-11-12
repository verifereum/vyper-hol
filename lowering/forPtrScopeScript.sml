(* Scope boundaries for the For callback. No memory-taint frame is
   inferred from stmt_frag_ptr: robust values come from ghost_inv. *)
Theory forPtrScope
Ancestors bodyPtrDefs forPtrElement stmtSimProps stmtSimForArrayLoop compileEnv vyperState loweringPosts stmtFragPtr finite_map stmtSimForArrayFrame vyperEvalPreservesScopes

(* Only the type and value of a scope entry are relevant to the ghost. *)
Theorem ghost_inv_lookup_transport:
  ghost_inv d cenv cx es G tn s /\
  cenv'.ce_return_buf = cenv.ce_return_buf /\
  cenv'.ce_return_pc = cenv.ce_return_pc /\
  (!name entry p sz.
    lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv'.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ?old. lookup_scopes name es.scopes = SOME old /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
      old.type = entry.type /\ old.value = entry.value) ==>
  ghost_inv d cenv' cx es' G tn s
Proof
  strip_tac >> fs[ghost_inv_def] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
      first_x_assum drule_all >> gvs[])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def])
QED

Theorem ghost_inv_empty_scope:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx (es with scopes := FEMPTY :: es.scopes) G tn s
Proof
  strip_tac >> irule ghost_inv_lookup_transport >>
  qexistsl_tac [`cenv`, `es`] >> simp[lookup_scopes_def] >> metis_tac[]
QED

Theorem cenv_top_ext_outer_lookup:
  cenv_top_ext cenv bc (sc :: rest) /\
  lookup_scopes name rest = SOME entry ==>
  FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name
Proof
  simp[cenv_top_ext_def] >> strip_tac >>
  spose_not_then assume_tac >> first_x_assum drule >> simp[]
QED

Theorem ghost_inv_push_top_ext:
  ghost_inv d cenv cx es G tn s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) ==>
  ghost_inv d bc cx (es with scopes := FEMPTY :: es.scopes) G tn s
Proof
  strip_tac >> irule ghost_inv_lookup_transport >>
  qexistsl_tac [`cenv`, `es`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[lookup_scopes_def] >>
      drule_all cenv_top_ext_outer_lookup >> strip_tac >> metis_tac[])
  >- metis_tac[cenv_top_ext_return_buf]
  >> metis_tac[cenv_top_ext_return_pc]
QED

Theorem ghost_inv_pop_top_ext:
  ghost_inv d bc cx es G tn s /\
  cenv_top_ext cenv bc es.scopes /\ es.scopes = sc :: rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) ==>
  ghost_inv d cenv cx (es with scopes := rest) G tn s
Proof
  strip_tac >> irule ghost_inv_lookup_transport >>
  qexistsl_tac [`bc`, `es`] >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP sc name = NONE` by
        (Cases_on `FLOOKUP sc name` >> gvs[] >>
         fs[FLOOKUP_DEF] >>
         qpat_x_assum `!name. _ ==> _` drule >> simp[]) >>
      gvs[] >> drule_all cenv_top_ext_outer_lookup >> strip_tac >>
      simp[lookup_scopes_def] >> metis_tac[])
  >- metis_tac[cenv_top_ext_return_buf]
  >> metis_tac[cenv_top_ext_return_pc]
QED

(* Establish or replace the loop binding after its element store. The old
   invariant here is for the other live locals at the copy's endpoint. *)
Theorem ghost_inv_set_top_entry:
  ghost_inv d cenv cx es G tn s /\ es.scopes = sc :: rest /\
  (!p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w mem. lookup_var p s = SOME w /\
      mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d cenv cx
    (es with scopes := (sc |+ (name,entry)) :: rest) G tn s
Proof
  simp[ghost_inv_def] >> strip_tac >> simp[] >>
  rpt strip_tac >> Cases_on `name' = name` >>
  gvs[lookup_scopes_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Scope projection is provided by the semantic iterator-unmodified facts;
   recover bytes from the callback invariant, not a nonexistent taint frame. *)
Theorem ghost_inv_projected_local_ptr:
  ghost_inv d cenv cx es G tn s /\
  MAP (\sc. FLOOKUP sc name) es.scopes =
    MAP (\sc. FLOOKUP sc name) before.scopes /\
  lookup_scopes name before.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  ptr_covers G tn p s sz /\
  !w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> drule scope_projection_lookup >> strip_tac >>
  irule ghost_inv_local_ptr >> metis_tac[]
QED

Theorem ghost_inv_body_scope_projection:
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,ee) /\
  cenv_top_ext bc c3 ee.scopes /\
  ghost_inv d c3 cx ee G tn s /\ ee.scopes = sc :: rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) ==>
  ghost_inv d cenv cx (ee with scopes := rest) G tn s
Proof
  strip_tac >> drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `cenv_top_ext cenv c3 ee.scopes` by
    (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `ei.scopes`] >>
     gvs[preserves_scopes_dom_def]) >>
  irule ghost_inv_pop_top_ext >> metis_tac[]
QED

(* The old-variable frame is exactly the one stmt_frag_ptr returns. *)
Theorem old_variable_ghost_frame_compose:
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G1 x = FLOOKUP G0 x /\
    op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
  (!x. not_fresh_at sb x ==>
    FLOOKUP G2 x = FLOOKUP G1 x /\
    op_taint tn2 (Var x) = op_taint tn1 (Var x)) ==>
  !x. not_fresh_at sa x ==>
    FLOOKUP G2 x = FLOOKUP G0 x /\
    op_taint tn2 (Var x) = op_taint tn0 (Var x)
Proof
  metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
QED
