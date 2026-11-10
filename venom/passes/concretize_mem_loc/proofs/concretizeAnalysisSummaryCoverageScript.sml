Theory concretizeAnalysisSummaryCoverage
Ancestors
  concretizeMemLocDefs list pair

(* Deduplication preserves keys, not triples with inconsistent metadata. *)
Theorem unique_mems_used_key_mem:
  !xs. MEM a (MAP FST (unique_mems_used xs)) <=> MEM a (MAP FST xs)
Proof
  recInduct unique_mems_used_ind >> simp[unique_mems_used_def] >>
  rpt strip_tac >> simp[MEM_MAP, MEM_FILTER] >>
  Cases_on `a = a'` >> gvs[] >>
  simp[pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem unique_mems_used_key_coverage:
  MEM (a,p,sz) xs ==> ?p' sz'. MEM (a,p',sz') (unique_mems_used xs)
Proof
  strip_tac >>
  `MEM a (MAP FST xs)` by (simp[MEM_MAP] >> metis_tac[FST]) >>
  `MEM a (MAP FST (unique_mems_used xs))` by
    simp[unique_mems_used_key_mem] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem context_layout_own_key_coverage:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items ==>
  ?p sz'. MEM (a,p,sz')
    (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> simp[apply_context_concretize_layout_def] >>
  irule unique_mems_used_key_coverage >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem context_layout_import_key_coverage:
  MEM (a,p,sz) (imported_mems_used ctx fn) ==>
  ?p' sz'. MEM (a,p',sz')
    (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> simp[apply_context_concretize_layout_def] >>
  irule unique_mems_used_key_coverage >> simp[] >> metis_tac[]
QED

Theorem invoke_import_key_coverage:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label name :: ops /\
  MEM (a,p,sz) (callee_mems_used ctx name) ==>
  ?p' sz'. MEM (a,p',sz') (imported_mems_used ctx fn)
Proof
  strip_tac >> simp[imported_mems_used_def] >>
  irule unique_mems_used_key_coverage >>
  qexistsl_tac [`p`,`sz`] >> simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `callee_mems_used ctx name` >> simp[] >>
  qexists_tac `inst` >> simp[]
QED
