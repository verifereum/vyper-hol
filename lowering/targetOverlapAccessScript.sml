(*
 * What the target-side overlap rejection (target_subscript_overlap) gives a
 * target subscript bt[idx] that passes it: when bt passes through a
 * dynamic-array element, idx writes no variable bt reads and makes no
 * risky call.  bt's root is such a variable: a local always, a storage
 * variable when no constant shares its name.  With the run-time frames
 * (vyperLocalAccessFrame, vyperStorageAccessFrame), evaluating idx leaves
 * the root's scope entry, or its storage region, as it was.
 *
 * TOP-LEVEL:
 *   target_subscript_overlap_unwritten — the rejection's access consequence
 *   target_root_local_nonconstant_read, target_root_state_nonconstant_read
 *     — bt reads its root
 *   find_var_decl_not_constant_decl — a storage variable is not a constant
 *     when top-level names are distinct
 *)

Theory targetOverlapAccess
Ancestors
  allocLimits stmtLowering targetPlaceSim targetPlaceSimCasesBase
  vyperSubscriptOverlap
  vyperTypeContract vyperState vyperLocalAccessFrame vyperStorageAccessFrame

Theorem nonconstant_reads_append:
  !mods xs ys.
    nonconstant_reads mods (xs ++ ys) =
    nonconstant_reads mods xs ++ nonconstant_reads mods ys
Proof
  recInduct nonconstant_reads_ind >> rw[nonconstant_reads_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem any_written_MEM:
  !vs accs. any_written vs accs <=> ?v. MEM v vs /\ MEM (WriteAcc v) accs
Proof
  Induct >> rw[any_written_def] >> metis_tac[]
QED

Theorem target_subscript_overlap_unwritten:
  !cenv bt idx v.
    ~target_subscript_overlap cenv bt idx /\
    target_through_dynarray cenv bt /\
    MEM v (nonconstant_reads cenv.ce_modules
             (expr_accesses cenv.ce_modules (target_to_expr bt))) ==>
    ~MEM (WriteAcc v) (expr_accesses cenv.ce_modules idx) /\
    ~MEM RiskyAcc (expr_accesses cenv.ce_modules idx)
Proof
  rpt gen_tac >> simp[target_subscript_overlap_def, any_written_MEM] >>
  Cases_on `nonconstant_reads cenv.ce_modules
              (expr_accesses cenv.ce_modules (target_to_expr bt))` >>
  simp[] >> metis_tac[]
QED

Theorem target_root_local_nonconstant_read:
  !mods bt id.
    target_root bt = NameTarget id ==>
    MEM (LocalRef id)
      (nonconstant_reads mods (expr_accesses mods (target_to_expr bt)))
Proof
  rpt strip_tac >> simp[expr_accesses_def, nonconstant_reads_append] >>
  disj1_tac >> pop_assum mp_tac >> qid_spec_tac `bt` >>
  ho_match_mp_tac base_assignment_target_induct >>
  rw[target_root_def, target_to_expr_def, accesses_expr_def,
     nonconstant_reads_append, nonconstant_reads_def]
QED

Theorem target_root_state_nonconstant_read:
  !mods bt src id.
    target_root bt = TopLevelNameTarget (src,id) /\
    (!tls. ALOOKUP mods src = SOME tls ==> ~constant_decl id tls) ==>
    MEM (StateRef (src,id))
      (nonconstant_reads mods (expr_accesses mods (target_to_expr bt)))
Proof
  rpt strip_tac >> simp[expr_accesses_def, nonconstant_reads_append] >>
  disj1_tac >> pop_assum mp_tac >> pop_assum mp_tac >> qid_spec_tac `bt` >>
  ho_match_mp_tac base_assignment_target_induct >>
  rw[target_root_def, target_to_expr_def, accesses_expr_def,
     nonconstant_reads_append, nonconstant_reads_def] >>
  Cases_on `ALOOKUP mods src` >> gvs[]
QED

Theorem find_var_decl_vtype_key[local]:
  !id tls src.
    find_var_decl_by_name id tls <> NONE ==>
    MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))
Proof
  Induct_on `tls` >> simp[find_var_decl_by_name_def] >>
  Cases >> rw[find_var_decl_by_name_def, toplevel_vtype_keys_toplevel_def] >>
  Cases_on `find_var_decl_by_name id tls` >> gvs[]
QED

Theorem constant_decl_vtype_key[local]:
  !id tls src.
    constant_decl id tls ==>
    MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))
Proof
  Induct_on `tls` >> simp[constant_decl_def] >>
  Cases >> rw[constant_decl_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[constant_decl_def] >>
  rename1 `VariableDecl _ m _ _ _` >> Cases_on `m` >> gvs[constant_decl_def]
QED

Theorem find_var_decl_not_constant_decl:
  !src tls id.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls)) /\
    find_var_decl_by_name id tls <> NONE ==>
    ~constant_decl id tls
Proof
  Induct_on `tls` >- simp[constant_decl_def] >>
  Cases >>
  simp[find_var_decl_by_name_def, toplevel_vtype_keys_toplevel_def,
       listTheory.ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> TRY (rename1 `VariableDecl _ m _ _ _` >> Cases_on `m`) >>
  rw[constant_decl_def] >>
  metis_tac[find_var_decl_vtype_key, constant_decl_vtype_key]
QED
