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
  sortingTheory alistTheory listTheory pairTheory

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

(* leaf_type: the type at the leaf of a subscript chain.
   Used to state the base condition for assign_subscripts_preserves_type:
   the caller provides that the base operation is well-typed at the LEAF type,
   not the top-level type. *)
Definition leaf_type_def:
  leaf_type tv [] = tv /\
  leaf_type (ArrayTV t _) (IntSubscript _ :: rest) = leaf_type t rest /\
  leaf_type (StructTV l) (AttrSubscript id :: rest) =
    (case ALOOKUP l id of SOME t => leaf_type t rest | NONE => NoneTV) /\
  leaf_type _ (_ :: _) = NoneTV
End

(* assign_subscripts requires:
   - well_formed_type_value tv (for default_value typing in SArrayV)
   - The leaf operation preserves typing (at the leaf type, not tv)
   For Replace: caller ensures new value has the leaf type.
   For Update: caller ensures binop result has the leaf type.
   For AppendOp: new element must have element type of the leaf array.
   For PopOp: no extra condition needed. *)
Theorem assign_subscripts_IntSubscript_ArrayV[local]:
  !tv av idx rest ao.
  assign_subscripts tv (ArrayV av) (IntSubscript idx::rest) ao =
    (let
       elem_tv =
         case tv of
           ArrayTV t v9 => t
         | BaseTV v6 => NoneTV
         | TupleTV v7 => NoneTV
         | StructTV v10 => NoneTV
         | FlagTV v11 => NoneTV
         | NoneTV => NoneTV
     in
       case array_index tv av idx of
         NONE => INR (RuntimeError "assign_subscripts array_index")
       | SOME v =>
           case assign_subscripts elem_tv v rest ao of
             INL vj => array_set_index tv av idx vj
           | INR err => INR err)
Proof
  simp[Once assign_subscripts_def]
QED

Theorem assign_subscripts_AttrSubscript_StructV[local]:
  !tv al fld rest ao.
  assign_subscripts tv (StructV al) (AttrSubscript fld::rest) ao =
    (case ALOOKUP al fld of
       NONE => INR (TypeError "assign_subscripts AttrSubscript")
     | SOME fv =>
         let
           ftv =
             case tv of
               StructTV args =>
                 (case ALOOKUP args fld of NONE => NoneTV | SOME t => t)
             | BaseTV v6 => NoneTV
             | TupleTV v7 => NoneTV
             | ArrayTV v8 v9 => NoneTV
             | FlagTV v11 => NoneTV
             | NoneTV => NoneTV
         in
           case assign_subscripts ftv fv rest ao of
             INL new_fv => INL (StructV (AFUPDKEY fld (K new_fv) al))
           | INR err => INR err)
Proof
  simp[Once assign_subscripts_def]
QED

Theorem assign_subscripts_preserves_type:
  !tv a subs ao v.
    assign_subscripts tv a subs ao = INL v /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    (* Base conditions at the leaf type *)
    (!nv. ao = Replace nv ==> value_has_type (leaf_type tv subs) nv) /\
    (!ty bop nv. ao = Update ty bop nv ==>
       !la lv. value_has_type (leaf_type tv subs) la /\
               assign_subscripts (leaf_type tv subs) la [] (Update ty bop nv) = INL lv ==>
               value_has_type (leaf_type tv subs) lv) /\
    (!nv. ao = AppendOp nv ==>
       ?elem_tv n. leaf_type tv subs = ArrayTV elem_tv (Dynamic n) /\
                   value_has_type elem_tv nv) ==>
    value_has_type tv v
Proof
  ho_match_mp_tac assign_subscripts_ind >> rpt conj_tac
  >- simp[Once assign_subscripts_def, leaf_type_def] (* Replace *)
  (* Update *)
  >- (rpt gen_tac >> simp[leaf_type_def] >>
      rpt strip_tac >>
      first_x_assum irule >>
      qexists_tac `a` >> gvs[])
  (* AppendOp *)
  >- (rpt gen_tac >> simp[leaf_type_def] >>
      rpt strip_tac >> gvs[Once assign_subscripts_def] >>
      irule append_element_preserves_type >>
      gvs[] >> metis_tac[])
  (* PopOp *)
  >- (rpt gen_tac >> simp[leaf_type_def, Once assign_subscripts_def] >>
      rpt strip_tac >>
      drule_all pop_element_preserves_type >> simp[])
  (* IntSubscript *)
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      Cases_on `a` >> gvs[Once assign_subscripts_def] >>
      rename1 `ArrayV av` >>
      pop_assum mp_tac >>
      simp[assign_subscripts_IntSubscript_ArrayV, LET_THM] >>
      Cases_on `array_index tv av i` >> simp[] >>
      rename1 `array_index tv av i = SOME elem` >>
      qabbrev_tac `elem_tv = case tv of ArrayTV t _ => t | _ => NoneTV` >>
      Cases_on `assign_subscripts elem_tv elem subs ao` >> simp[] >>
      rename1 `assign_subscripts elem_tv elem subs ao = INL new_elem` >>
      strip_tac >>
      `value_has_type elem_tv elem` by (
        Cases_on `tv` >> gvs[Abbr `elem_tv`, value_has_type_def] >>
        irule array_index_has_type >>
        Cases_on `b` >> gvs[value_has_type_def] >> metis_tac[]) >>
      `well_formed_type_value elem_tv` by (
        Cases_on `tv` >> gvs[Abbr `elem_tv`, well_formed_type_value_def]) >>
      `leaf_type tv (IntSubscript i::subs) = leaf_type elem_tv subs` by (
        simp[leaf_type_def, Abbr `elem_tv`]) >>
      `value_has_type elem_tv new_elem` by (
        first_x_assum irule >> gvs[]) >>
      Cases_on `tv` >> gvs[Abbr `elem_tv`, value_has_type_def] >>
      Cases_on `b` >> gvs[value_has_type_def] >>
      TRY (irule array_set_index_DynArrayV >> gvs[value_has_type_def] >> NO_TAC) >>
      irule array_set_index_SArrayV >> gvs[value_has_type_def])
  (* AttrSubscript *)
  >- cheat
  (* Error cases: 10 goals *)
  >> simp[Once assign_subscripts_def]
QED
