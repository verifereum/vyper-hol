(* Future-address cones for dynamic occurrence freshness. *)
Theory dftOccurrenceFreshness
Ancestors
  dftOccurrenceMachine venomInst arithmetic list pred_set

Definition dft_suffix_cone_def:
  dft_suffix_cone (p:(num # num) list) v bb i x <=>
    ?w id tail. x = p ++ [(w,id)] ++ tail /\
      (v < w \/ (w = v /\ MEM id (MAP (\inst. inst.inst_id) (DROP i bb.bb_instructions))))
End

Definition dft_entry_cone_def:
  dft_entry_cone (p:(num # num) list) v x <=>
    ?w id tail. x = p ++ [(w,id)] ++ tail /\ v <= w
End

Theorem dft_suffix_cone_entry:
  dft_suffix_cone p v bb i x ==> dft_entry_cone p v x
Proof
  simp[dft_suffix_cone_def, dft_entry_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[]
QED

Theorem dft_entry_cone_next:
  dft_entry_cone p (SUC v) x ==> dft_suffix_cone p v bb i x
Proof
  simp[dft_suffix_cone_def, dft_entry_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[]
QED

Theorem dft_suffix_cone_shrink:
  dft_suffix_cone p v bb (SUC i) x ==> dft_suffix_cone p v bb i x
Proof
  simp[dft_suffix_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[] >>
  gvs[MEM_MAP, MEM_DROP] >>
  qexists_tac `EL (m + SUC i) bb.bb_instructions` >> simp[] >>
  qexists_tac `SUC m` >> simp[ADD_CLAUSES, ADD_COMM]
QED

Theorem dft_suffix_cone_current:
  get_instruction bb i = SOME inst ==>
  dft_suffix_cone p v bb i (p ++ [(v,inst.inst_id)])
Proof
  simp[get_instruction_def, dft_suffix_cone_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[MEM_MAP, MEM_DROP] >> qexists_tac `EL i bb.bb_instructions` >>
  simp[] >> qexists_tac `0` >> simp[]
QED

Theorem dft_suffix_cone_retire:
  ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
  get_instruction bb i = SOME inst ==>
  ~dft_suffix_cone p v bb (SUC i) (p ++ [(v,inst.inst_id)] ++ tail)
Proof
  simp[dft_suffix_cone_def] >> rpt strip_tac >>
  gvs[get_instruction_def, AllCaseEqs(), MEM_MAP, MEM_DROP] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `EL i (MAP (\inst. inst.inst_id) bb.bb_instructions) =
   EL (m + SUC i) (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  `i = m + SUC i` by metis_tac[EL_ALL_DISTINCT_EL_EQ, LENGTH_MAP] >>
  decide_tac
QED

Theorem dft_entry_cone_descendant:
  get_instruction bb i = SOME inst /\
  dft_entry_cone (p ++ [(v,inst.inst_id)]) 0 x ==>
  dft_suffix_cone p v bb i x
Proof
  strip_tac >>
  `dft_suffix_cone p v bb i (p ++ [(v,inst.inst_id)])` by
    (irule dft_suffix_cone_current >> simp[]) >>
  gvs[dft_entry_cone_def, dft_suffix_cone_def] >>
  qexistsl_tac [`v`, `inst.inst_id`, `[(w,id)] ++ tail`] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]
QED

Theorem dft_entry_cone_not_root:
  ~dft_entry_cone (p ++ [(v,id)]) n (p ++ [(v,id)])
Proof
  simp[dft_entry_cone_def]
QED

Theorem dft_suffix_cone_ancestor_exclusion:
  ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
  get_instruction bb i = SOME inst /\
  dft_entry_cone (p ++ [(v,inst.inst_id)]) 0 x ==>
  ~dft_suffix_cone p v bb (SUC i) x
Proof
  strip_tac >> gvs[dft_entry_cone_def] >>
  drule_all dft_suffix_cone_retire >>
  disch_then (qspecl_then [`v`, `[(w,id)] ++ tail`, `p`] mp_tac) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]
QED
