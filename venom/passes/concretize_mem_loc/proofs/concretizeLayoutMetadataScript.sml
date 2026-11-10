Theory concretizeLayoutMetadata
Ancestors concretizeAnalysisSummaryCoverage concretizeAnalysisMetadata
  concretizeMemLocDefs list pair finite_map

Theorem layout_find_filter:
  (!x. P x ==> Q x) ==>
  !xs. FIND P (FILTER Q xs) = FIND P xs
Proof
  strip_tac >> Induct >> simp[FIND_thm] >> rpt gen_tac
  >> Cases_on `Q h` >> simp[FIND_thm]
  >> Cases_on `P h` >> gvs[]
QED

Theorem unique_mems_used_find:
  !xs a. FIND (\(b,p,s). b = a) (unique_mems_used xs) =
         FIND (\(b,p,s). b = a) xs
Proof
  recInduct unique_mems_used_ind
  >> simp[unique_mems_used_def, FIND_thm]
  >> rpt strip_tac >> Cases_on `a = a'` >> simp[]
  >> irule layout_find_filter >> simp[FORALL_PROD] >> metis_tac[]
QED

Theorem unique_mems_used_exact_mem:
  MEM (a,p,s) xs /\
  (!q t. MEM (a,q,t) xs ==> q = p /\ t = s) ==>
  MEM (a,p,s) (unique_mems_used xs)
Proof
  strip_tac >> drule unique_mems_used_key_coverage >> strip_tac
  >> `EVERY (\(b,q,t). b = a ==> q = p /\ t = s) xs`
       by (simp[EVERY_MEM, FORALL_PROD] >> metis_tac[])
  >> drule unique_mems_used_every
  >> simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem layout_own_find:
  !items a sz positions imported.
  ALL_DISTINCT (MAP FST items) /\ MEM (a,sz) items ==>
  FIND (\(b,p,s). b = a)
    (MAP (\(b,s). (b,THE (FLOOKUP positions b),s)) items ++ imported) =
  SOME (a,THE (FLOOKUP positions a),sz)
Proof
  Induct >> simp[FORALL_PROD, FIND_thm]
  >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `a = _` SUBST_ALL_TAC
      >> qpat_x_assum `sz = _` SUBST_ALL_TAC >> simp[NoAsms])
  >> `p_1 <> a` by metis_tac[MEM_MAP, FST]
  >> simp[Once boolTheory.COND_RAND]
  >> first_x_assum irule >> simp[]
QED

Theorem context_layout_own_find:
  static_alloca_items fn = SOME items /\ ALL_DISTINCT (MAP FST items) /\
  MEM (a,sz) items ==>
  FIND (\(b,p,s). b = a) (apply_context_concretize_layout ctx layout fn).fn_mems_used =
  SOME (a,THE (FLOOKUP layout.cl_positions a),sz)
Proof
  strip_tac >> simp[apply_context_concretize_layout_def, unique_mems_used_find]
  >> irule layout_own_find >> simp[]
QED
