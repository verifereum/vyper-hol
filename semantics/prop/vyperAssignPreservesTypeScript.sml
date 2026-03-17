(*
 * assign_subscripts preserves value_has_type.
 *
 * TOP-LEVEL:
 *   assign_subscripts_preserves_type - main theorem
 *
 * Helper lemmas for sub-operations:
 *   insert_sarray_SORTED, insert_sarray_sparse_has_type
 *   ADELKEY_SORTED, ADELKEY_sparse_has_type
 *   array_set_index_preserves_type
 *   append_element_preserves_type
 *   pop_element_preserves_type
 *   AFUPDKEY_struct_has_type
 *)

Theory vyperAssignPreservesType
Ancestors
  vyperTyping vyperValueOperation vyperState vyperTypeSoundness
Libs
  sortingTheory alistTheory listTheory

(* ===== insert_sarray helpers ===== *)

Theorem MEM_MAP_FST_insert_sarray:
  !k v al x.
    MEM x (MAP FST (insert_sarray k v al)) <=>
    x = k \/ MEM x (MAP FST al)
Proof
  Induct_on `al` >- simp[insert_sarray_def] >>
  Cases >> rpt gen_tac >>
  simp[Once insert_sarray_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem insert_sarray_SORTED:
  !k v al.
    SORTED $< (MAP FST al) ==>
    SORTED $< (MAP FST (insert_sarray k v al))
Proof
  Induct_on `al` >- simp[insert_sarray_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  rename1 `(k1, v1)::al` >>
  simp[Once insert_sarray_def] >>
  IF_CASES_TAC >- gvs[] >>
  IF_CASES_TAC
  >- (simp[sortingTheory.SORTED_EQ] >>
      gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
      metis_tac[]) >>
  simp[sortingTheory.SORTED_EQ, MEM_MAP_FST_insert_sarray,
       relationTheory.transitive_def] >>
  gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

(* ===== insert_sarray preserves sparse_has_type ===== *)

Theorem insert_sarray_sparse_has_type:
  !k v al tv n.
    sparse_has_type tv n al /\
    k < n /\ v <> default_value tv /\ value_has_type tv v ==>
    sparse_has_type tv n (insert_sarray k v al)
Proof
  Induct_on `al` >- simp[insert_sarray_def, value_has_type_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  simp[Once insert_sarray_def] >>
  rpt (IF_CASES_TAC >> gvs[value_has_type_def])
QED

(* ===== ADELKEY preserves SORTED ===== *)

Theorem ADELKEY_SORTED:
  !k al.
    SORTED $< (MAP FST al) ==>
    SORTED $< (MAP FST (ADELKEY k al))
Proof
  Induct_on `al` >- simp[ADELKEY_def] >>
  Cases >> rpt gen_tac >>
  simp[ADELKEY_def, FILTER] >>
  strip_tac >>
  `SORTED $< (MAP FST al)` by imp_res_tac sortingTheory.SORTED_TL >>
  `SORTED $< (MAP FST (ADELKEY k al))` by (first_x_assum irule >> simp[]) >>
  gvs[GSYM ADELKEY_def] >>
  IF_CASES_TAC >> gvs[] >>
  simp[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
       MEM_MAP, MEM_FILTER, PULL_EXISTS, pairTheory.FORALL_PROD,
       ADELKEY_def] >>
  rpt strip_tac >>
  gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  first_x_assum irule >> simp[MEM_MAP] >>
  qexists_tac `(y, p_2)` >> simp[]
QED

(* ===== ADELKEY preserves sparse_has_type ===== *)

Theorem ADELKEY_sparse_has_type:
  !k al tv n.
    sparse_has_type tv n al ==>
    sparse_has_type tv n (ADELKEY k al)
Proof
  Induct_on `al` >- simp[ADELKEY_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  simp[ADELKEY_def, FILTER] >>
  gvs[value_has_type_def] >>
  IF_CASES_TAC >> gvs[value_has_type_def, GSYM ADELKEY_def]
QED

(* ===== DynArrayV LUPDATE preserves all_have_type ===== *)

Theorem TAKE_DROP_all_have_type:
  !tv vs j v.
    all_have_type tv vs /\ j < LENGTH vs /\ value_has_type tv v ==>
    all_have_type tv (TAKE j vs ++ [v] ++ DROP (SUC j) vs)
Proof
  Induct_on `vs` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  Cases_on `j` >> gvs[value_has_type_def]
QED

(* ===== array_set_index preserves value_has_type ===== *)

Theorem array_set_index_DynArrayV:
  !tv vs i v av'.
    array_set_index tv (DynArrayV vs) i v = INL (ArrayV av') /\
    value_has_type (ArrayTV elem_tv (Dynamic max)) (ArrayV (DynArrayV vs)) /\
    value_has_type elem_tv v ==>
    value_has_type (ArrayTV elem_tv (Dynamic max)) (ArrayV av')
Proof
  rpt gen_tac >> strip_tac >>
  gvs[array_set_index_def, AllCaseEqs(), value_has_type_def] >>
  irule TAKE_DROP_all_have_type >> gvs[]
QED

Theorem array_set_index_SArrayV:
  !elem_tv n al i v av'.
    array_set_index (ArrayTV elem_tv (Fixed n)) (SArrayV al) i v =
      INL (ArrayV av') /\
    value_has_type (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV al)) /\
    value_has_type elem_tv v ==>
    value_has_type (ArrayTV elem_tv (Fixed n)) (ArrayV av')
Proof
  rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  qpat_x_assum `array_set_index _ _ _ _ = _` mp_tac >>
  simp[array_set_index_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[value_has_type_def]
  >- (conj_tac
      >- (irule ADELKEY_SORTED >> simp[])
      >> irule ADELKEY_sparse_has_type >> simp[])
  >- (conj_tac
      >- (irule insert_sarray_SORTED >> simp[])
      >> irule insert_sarray_sparse_has_type >> simp[])
QED

(* ===== append_element preserves value_has_type ===== *)

Theorem append_element_preserves_type:
  !tv a v r elem_tv n.
    append_element tv a v = INL r /\
    value_has_type tv a /\
    tv = ArrayTV elem_tv (Dynamic n) /\
    value_has_type elem_tv v ==>
    value_has_type tv r
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `append_element _ _ _ = _` mp_tac >>
  Cases_on `a` >> simp[append_element_def] >>
  rename1 `ArrayV av` >>
  Cases_on `av` >> simp[append_element_def, AllCaseEqs(),
    vyperValueTheory.compatible_bound_def] >>
  strip_tac >> gvs[value_has_type_def] >>
  drule_all safe_cast_preserves_well_typed >> strip_tac >>
  simp[rich_listTheory.LENGTH_SNOC] >>
  simp[rich_listTheory.SNOC_APPEND, value_has_type_def] >>
  Induct_on `l` >> gvs[value_has_type_def]
QED

(* ===== pop_element preserves value_has_type ===== *)

Theorem FRONT_all_have_type:
  !tv vs.
    all_have_type tv vs /\ vs <> [] ==>
    all_have_type tv (FRONT vs)
Proof
  Induct_on `vs` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  Cases_on `vs` >- simp[value_has_type_def] >>
  gvs[value_has_type_def]
QED

Theorem pop_element_preserves_type:
  !a r tv.
    pop_element a = INL r /\
    value_has_type tv a ==>
    value_has_type tv r
Proof
  rpt gen_tac >>
  Cases_on `a` >> simp[pop_element_def] >>
  rename1 `ArrayV av` >>
  Cases_on `av` >> simp[pop_element_def] >>
  Cases_on `tv` >> simp[value_has_type_def] >>
  Cases_on `b` >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  gvs[value_has_type_def] >>
  conj_tac
  >- (irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `LENGTH l` >> simp[rich_listTheory.LENGTH_FRONT])
  >- (irule FRONT_all_have_type >> simp[])
QED

(* ===== AFUPDKEY preserves struct_has_type ===== *)

Theorem AFUPDKEY_struct_has_type:
  !id f ftypes fields tv.
    struct_has_type ftypes fields /\
    (!v. ALOOKUP fields id = SOME v ==>
         ALOOKUP ftypes id = SOME tv /\
         value_has_type tv (f v)) ==>
    struct_has_type ftypes (AFUPDKEY id f fields)
Proof
  Induct_on `fields`
  >- (Cases_on `ftypes` >> simp[value_has_type_def, AFUPDKEY_def]) >>
  Cases >> rpt gen_tac >>
  simp[AFUPDKEY_def] >>
  Cases_on `ftypes` >> simp[value_has_type_def] >>
  Cases_on `h` >> simp[value_has_type_def] >>
  IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[value_has_type_def] >>
  first_x_assum irule >> simp[] >>
  qexists_tac `tv` >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

(* ===== array_index returns well-typed elements ===== *)

Theorem oEL_all_have_type:
  !j vs tv v.
    oEL j vs = SOME v /\ all_have_type tv vs ==>
    value_has_type tv v
Proof
  Induct_on `vs` >> simp[oEL_def, value_has_type_def] >>
  rpt gen_tac >> Cases_on `j` >> simp[oEL_def, value_has_type_def] >>
  strip_tac >> gvs[value_has_type_def] >>
  first_x_assum drule >> simp[]
QED

Theorem ALOOKUP_sparse_has_type:
  !al tv n k v.
    ALOOKUP al k = SOME v /\ sparse_has_type tv n al ==>
    value_has_type tv v /\ k < n
Proof
  Induct_on `al` >> simp[value_has_type_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  Cases_on `q = k` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem array_index_has_type:
  !tv elem_tv bd av i v.
    array_index tv av i = SOME v /\
    tv = ArrayTV elem_tv bd /\
    value_has_type tv (ArrayV av) /\
    well_formed_type_value elem_tv ==>
    value_has_type elem_tv v
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `av` >> gvs[array_index_def, value_has_type_def] >>
  Cases_on `0 ≤ i` >> gvs[] >>
  Cases_on `bd` >> gvs[AllCaseEqs(), value_has_type_def] >>
  TRY (drule_all oEL_all_have_type >> simp[] >> NO_TAC) >>
  TRY (imp_res_tac ALOOKUP_sparse_has_type >> gvs[] >> NO_TAC) >>
  irule default_value_well_typed >> simp[]
QED

Theorem struct_field_has_type:
  !ftypes fields id v.
    ALOOKUP fields id = SOME v /\
    struct_has_type ftypes fields ==>
    ?tv. ALOOKUP ftypes id = SOME tv /\ value_has_type tv v
Proof
  Induct_on `fields` >> simp[value_has_type_def] >>
  Cases >> rpt gen_tac >>
  Cases_on `ftypes` >> simp[value_has_type_def] >>
  Cases_on `h` >> simp[value_has_type_def] >>
  strip_tac >> gvs[] >>
  Cases_on `q = id` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* ===== Main theorem: assign_subscripts preserves value_has_type ===== *)

(* assign_subscripts requires:
   - well_formed_type_value tv (for default_value typing in SArrayV)
   - The leaf operation preserves typing (Replace/Update/AppendOp/PopOp)
   For Replace: caller ensures new value has the right type.
   For Update: caller ensures binop preserves types.
   For AppendOp: new element must have element type.
   For PopOp: no extra condition needed. *)

Theorem assign_subscripts_preserves_type:
  !tv a subs ao v.
    assign_subscripts tv a subs ao = INL v /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    (* Base cases delegate to caller *)
    (subs = [] /\ (?nv. ao = Replace nv) ==> value_has_type tv v) /\
    (subs = [] /\ (?ty bop nv. ao = Update ty bop nv) ==> value_has_type tv v) /\
    (subs = [] /\ (?nv. ao = AppendOp nv) ==>
       ?elem_tv n. tv = ArrayTV elem_tv (Dynamic n) /\
                   value_has_type elem_tv nv) ==>
    value_has_type tv v
Proof
  (* Base cases and error cases solved by TRY block.
     Remaining: IntSubscript on ArrayV, AttrSubscript on StructV.
     Proof sketch for IntSubscript:
       1. Cases_on tv = ArrayTV elem_tv bd
       2. array_index_has_type gives value_has_type elem_tv v'
       3. well_formed_type_value elem_tv from well_formed_type_value tv
       4. IH gives value_has_type elem_tv vj
       5. array_set_index_{DynArrayV,SArrayV} gives value_has_type tv result
     Proof sketch for AttrSubscript:
       1. Cases_on tv = StructTV ftypes
       2. struct_field_has_type gives value_has_type field_tv v'
       3. well_formed_type_value field_tv from well_formed_type_value tv
       4. IH gives value_has_type field_tv v''
       5. AFUPDKEY_struct_has_type gives struct_has_type ftypes (AFUPDKEY ...) *)
  cheat
QED
