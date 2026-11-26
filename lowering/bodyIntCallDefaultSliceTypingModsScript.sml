Theory bodyIntCallDefaultSliceTypingMods
Ancestors
  vyperTypeSystem vyperTypeContract finite_map externalBodyWidths
  exprSimHypsDefs constSubstCorrect

Theorem default_slice_subscript_exact[local]:
  subscript_base_type_exact (defaults_env ed) e ==>
  subscript_base_type_exact ed e
Proof
  strip_tac >> irule subscript_base_type_exact_transfer >>
  qexists_tac `defaults_env ed` >> simp[defaults_env_def]
QED

(* A successful derivation in the cleared environment cannot read a local
   entry. Restore the maps simultaneously for typing and place lookup. *)
Theorem default_slice_restore_typing[local]:
  (!env e. well_typed_expr env e ==>
    !ed. env = defaults_env ed ==> well_typed_expr ed e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
    !ed. env = defaults_env ed ==> type_place_expr ed e = SOME vt) /\
  (!env tgt vt. type_place_target env tgt = SOME vt ==>
    !ed. env = defaults_env ed ==> type_place_target ed tgt = SOME vt) /\
  (!env es. well_typed_exprs env es ==>
    !ed. env = defaults_env ed ==> well_typed_exprs ed es) /\
  (!env opt. well_typed_opt env opt ==>
    !ed. env = defaults_env ed ==> well_typed_opt ed opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
    !ed. env = defaults_env ed ==> well_typed_named_exprs ed kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[well_typed_expr_def, defaults_env_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[GSYM defaults_env_def, default_slice_subscript_exact]
QED

Theorem intcall_default_slice_typing_mods:
  well_typed_exprs (defaults_env ed) ds /\
  EVERY (runtime_constant_expr mods) ds /\
  (!src id vt. FLOOKUP ed.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype ed.type_defs vt) ==>
  well_typed_exprs ed ds /\
  (!e. MEM e ds ==> byte_widths_expr e)
Proof
  strip_tac >> conj_tac
  >- metis_tac[default_slice_restore_typing] >>
  rpt strip_tac >>
  `well_typed_expr (defaults_env ed) e` by
    (irule frame_well_typed_exprs_member >> qexists_tac `ds` >> simp[]) >>
  irule well_typed_expr_byte_widths >>
  qexists_tac `defaults_env ed` >> fs[defaults_env_def] >>
  first_assum ACCEPT_TAC
QED
