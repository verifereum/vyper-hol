(* Active pointers into an older erased allocation have a translation.
   Mere origin soundness of the entries already present does not imply this. *)
Theory readonlyInvokeCopyFwdMapCoverage
Ancestors
  ptrDiscipline finite_map list pred_set

Definition ricf_mapped_support_def:
  ricf_mapped_support (a:num) (B:(num # num) |-> (num # num)) E PG G sites <=>
    !id b z. id IN E /\ FST id <> a /\ FLOOKUP B id = SOME (b,z) /\
      0 < z /\
      (MEM (SOME (b,z)) PG \/ ?v. FLOOKUP G v = SOME (b,z)) ==>
      (b,z) IN FDOM sites
End

Theorem ricf_mapped_support_empty[simp]:
  ricf_mapped_support a B {} PG G sites
Proof simp[ricf_mapped_support_def]
QED

Theorem ricf_mapped_support_provenance_empty[simp]:
  ricf_mapped_support a B E [] FEMPTY sites
Proof simp[ricf_mapped_support_def]
QED

Theorem ricf_mapped_support_map_extend:
  ricf_mapped_support a B E PG G sites /\ FDOM sites SUBSET FDOM next_sites ==>
  ricf_mapped_support a B E PG G next_sites
Proof rw[ricf_mapped_support_def] >> metis_tac[SUBSET_DEF]
QED

Theorem ricf_mapped_support_provenance_restrict:
  ricf_mapped_support a B E PG G sites ==>
  ricf_mapped_support a B E PG (DRESTRICT G keep) sites
Proof rw[ricf_mapped_support_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ricf_mapped_support_activate:
  ricf_mapped_support a B E PG G sites ==>
  ricf_mapped_support a B (E UNION {(a,k)}) PG G sites
Proof
  simp[ricf_mapped_support_def] >> rpt strip_tac >>
  `id IN E` by (Cases_on `id` >> gvs[]) >> metis_tac[]
QED

Theorem ricf_mapped_support_restrict:
  ricf_mapped_support a B E PG G sites /\ E' SUBSET E /\
  (!id. id IN E' /\ FST id <> a ==> FLOOKUP B' id = FLOOKUP B id) ==>
  ricf_mapped_support a B' E' PG G sites
Proof rw[ricf_mapped_support_def] >> metis_tac[SUBSET_DEF]
QED

Theorem ricf_mapped_support_provenance_origin:
  ricf_mapped_support a B E PG G sites /\
  (!key. MEM (SOME key) PG' ==> MEM (SOME key) PG \/ ?v. FLOOKUP G v = SOME key) /\
  (!v key. FLOOKUP G' v = SOME key ==>
    MEM (SOME key) PG \/ ?u. FLOOKUP G u = SOME key) ==>
  ricf_mapped_support a B E PG' G' sites
Proof rw[ricf_mapped_support_def] >> metis_tac[]
QED

Theorem ricf_mapped_support_call:
  ricf_mapped_support a B E PG G sites /\
  FDOM sites SUBSET FDOM callee_sites /\
  (!id b z. id IN E /\ FLOOKUP B id = SOME (b,z) /\ 0 < z /\
    FST id = a /\ MEM (SOME (b,z)) argsPG ==> (b,z) IN FDOM callee_sites) /\
  (!key. MEM (SOME key) argsPG ==> ?v. FLOOKUP G v = SOME key) ==>
  ricf_mapped_support child B E argsPG FEMPTY callee_sites
Proof
  rw[ricf_mapped_support_def] >> Cases_on `FST id = a` >>
  metis_tac[SUBSET_DEF]
QED
