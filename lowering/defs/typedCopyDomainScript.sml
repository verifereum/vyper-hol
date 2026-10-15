(* Total rank and computable recursion domain for layout-aware copy.
   The rank computation deletes metadata only internally; compiler recursive
   calls retain the original environment. Missing metadata denotes no fields.
   TOP-LEVEL: type_rank, acyclic_struct_metadata.
   The domain test is a strict ranking of EVERY stored field list, not fuel. *)
Theory typedCopyDomain
Ancestors
  compileEnv vyperAST finite_map pred_set list arithmetic relation combin pair prim_rec

Definition type_rank_def:
  type_rank (sf : (string, (string # type # num) list) fmap) (BaseT _) = 1n /\
  type_rank sf (ArrayT elem _) = 1 + type_rank sf elem /\
  type_rank sf (TupleT tys) = 1 + SUM (MAP (type_rank sf) tys) /\
  type_rank sf (StructT nsid) =
    (let name = nsid_to_string nsid in
     1 + SUM (MAP (type_rank (sf \\ name) o FST o SND)
                  (get_struct_fields sf name))) /\
  type_rank sf (FlagT _) = 1 /\
  type_rank sf NoneT = 1
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(sf, ty).
    (CARD (FDOM sf), type_size ty))` >>
  rw[FDOM_DOMSUB, CARD_DELETE, get_struct_fields_def] >>
  gvs[AllCaseEqs(), TO_FLOOKUP] >>
  Cases_on `CARD (FDOM sf)` >> gvs[FLOOKUP_DEF]
End

Definition acyclic_struct_metadata_def:
  acyclic_struct_metadata sf =
    FEVERY (λ(name, fields).
      SUM (MAP (type_rank sf o FST o SND) fields) <
      type_rank sf (StructT (NONE, name))) sf
End

Definition rank_metadata_agrees_def:
  rank_metadata_agrees sf sub bound <=>
    !name. type_rank sf (StructT (NONE,name)) <= bound ==>
           FLOOKUP sub name = FLOOKUP sf name
End

Theorem rank_metadata_agrees_mono:
  rank_metadata_agrees sf sub big /\ small <= big ==>
  rank_metadata_agrees sf sub small
Proof
  rw[rank_metadata_agrees_def] >> first_x_assum irule >> decide_tac
QED

Theorem rank_metadata_agrees_delete:
  rank_metadata_agrees sf sub big /\ small <= big /\
  small < type_rank sf (StructT (NONE,name)) ==>
  rank_metadata_agrees sf (sub \\ name) small
Proof
  rw[rank_metadata_agrees_def, DOMSUB_FLOOKUP_THM] >>
  rename1 `type_rank sf (StructT (NONE,key)) <= small` >>
  `key <> name` by (strip_tac >> gvs[] >> decide_tac) >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Theorem rank_metadata_agrees_fields:
  rank_metadata_agrees sf sub (type_rank sf (StructT (NONE,name))) ==>
  get_struct_fields sub name = get_struct_fields sf name
Proof
  simp[rank_metadata_agrees_def] >> strip_tac >>
  first_x_assum (qspec_then `name` mp_tac) >>
  simp[get_struct_fields_def]
QED

Theorem type_rank_nsid:
  type_rank sf (StructT nsid) =
  type_rank sf (StructT (NONE,nsid_to_string nsid))
Proof
  simp[type_rank_def, nsid_to_string_def]
QED

Theorem type_rank_positive:
  !sf ty. 0 < type_rank sf ty
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[Once type_rank_def]
QED

Theorem member_rank_le_sum:
  MEM ty tys ==> type_rank sf ty <= SUM (MAP (type_rank sf) tys)
Proof
  Induct_on `tys` >> simp[] >> rpt strip_tac >> gvs[] >>
  res_tac >> decide_tac
QED

Theorem member_rank_lt_tuple:
  MEM ty tys ==> type_rank sf ty < type_rank sf (TupleT tys)
Proof
  simp[type_rank_def] >> strip_tac >>
  drule member_rank_le_sum >> disch_then (qspec_then `sf` mp_tac) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> decide_tac
QED

Theorem acyclic_struct_fields_rank:
  acyclic_struct_metadata sf ==>
  SUM (MAP (type_rank sf o FST o SND) (get_struct_fields sf name)) <
  type_rank sf (StructT (NONE, name))
Proof
  simp[acyclic_struct_metadata_def, FEVERY_DEF, get_struct_fields_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP sf name` >> simp[] >>
  gvs[FLOOKUP_DEF, type_rank_def, get_struct_fields_def] >>
  first_x_assum drule >> simp[]
QED

Theorem member_rank_lt_struct:
  acyclic_struct_metadata sf /\
  MEM (fname, ty, bytes) (get_struct_fields sf name) ==>
  type_rank sf ty < type_rank sf (StructT (NONE, name))
Proof
  rpt strip_tac >> drule acyclic_struct_fields_rank >>
  disch_then (qspec_then `name` assume_tac) >>
  `MEM ty (MAP (FST o SND) (get_struct_fields sf name))` by
    (simp[MEM_MAP] >> qexists_tac `(fname,ty,bytes)` >> simp[]) >>
  drule member_rank_le_sum >> disch_then (qspec_then `sf` mp_tac) >>
  simp[MAP_MAP_o, o_DEF] >> fs[o_DEF] >> decide_tac
QED

(* Deleting a parent affects no smaller reachable type on an acyclic map.
   This is stronger than a one-edge invariance fact: any map agreeing on
   names whose ranks are small enough gives exactly the same computation. *)
Theorem type_rank_metadata_invariant:
  !sf ty sub.
    acyclic_struct_metadata sf /\
    rank_metadata_agrees sf sub (type_rank sf ty) ==>
    type_rank sub ty = type_rank sf ty
Proof
  gen_tac >> measureInduct_on `type_rank sf ty` >>
  rpt strip_tac >> Cases_on `ty`
  >- simp[type_rank_def]
  >- (rename1 `TupleT tys` >> simp[type_rank_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >>
      drule member_rank_lt_tuple >> disch_then (qspec_then `sf` assume_tac) >>
      simp[] >> irule rank_metadata_agrees_mono >>
      qexists_tac `type_rank sf (TupleT tys)` >> simp[])
  >- (rename1 `ArrayT elem bd` >> simp[type_rank_def] >>
      first_x_assum irule >> simp[type_rank_def] >>
      irule rank_metadata_agrees_mono >>
      qexists_tac `type_rank sf (ArrayT elem bd)` >> simp[type_rank_def])
  >- (rename1 `StructT nsid` >>
      `get_struct_fields sub (nsid_to_string nsid) =
       get_struct_fields sf (nsid_to_string nsid)` by
        (irule rank_metadata_agrees_fields >>
         qpat_x_assum `rank_metadata_agrees _ _ _` mp_tac >>
         ONCE_REWRITE_TAC [type_rank_nsid] >> simp[nsid_to_string_def]) >>
      simp[type_rank_def] >> AP_TERM_TAC >>
      irule MAP_CONG >> simp[] >> rpt strip_tac >>
      PairCases_on `x` >> simp[] >>
      drule_all member_rank_lt_struct >> strip_tac >>
      `type_rank sf x1 < type_rank sf (StructT nsid)` by
        (ONCE_REWRITE_TAC [type_rank_nsid] >> simp[]) >>
      `!m. rank_metadata_agrees sf m (type_rank sf (StructT nsid)) ==>
           type_rank (m \\ nsid_to_string nsid) x1 = type_rank sf x1` by
        (rpt strip_tac >> first_x_assum irule >> simp[] >>
         irule rank_metadata_agrees_delete >> simp[] >>
         qexists_tac `type_rank sf (StructT nsid)` >> simp[] >> decide_tac) >>
      `rank_metadata_agrees sf sf (type_rank sf (StructT nsid))` by
        simp[rank_metadata_agrees_def] >>
      metis_tac[])
  >- simp[type_rank_def]
  >- simp[type_rank_def]
QED

Theorem type_rank_struct_equation:
  acyclic_struct_metadata sf ==>
  type_rank sf (StructT nsid) =
  1 + SUM (MAP (type_rank sf o FST o SND)
                (get_struct_fields sf (nsid_to_string nsid)))
Proof
  strip_tac >> simp[type_rank_def] >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> PairCases_on `x` >> simp[] >>
  irule type_rank_metadata_invariant >> simp[] >>
  drule_all member_rank_lt_struct >> strip_tac >>
  irule rank_metadata_agrees_delete >> simp[] >>
  qexists_tac `type_rank sf x1` >> simp[rank_metadata_agrees_def]
QED

Theorem acyclic_struct_metadata_empty[simp]:
  acyclic_struct_metadata FEMPTY
Proof
  simp[acyclic_struct_metadata_def, FEVERY_DEF]
QED

Theorem type_rank_missing_struct:
  FLOOKUP sf (nsid_to_string nsid) = NONE ==>
  type_rank sf (StructT nsid) = 1
Proof
  simp[type_rank_def, get_struct_fields_def]
QED

(* The exact invalid map from the unrestricted-equation counterexample. *)
Definition audit_cycle_type_def:
  audit_cycle_type = StructT (NONE,"AuditCycle")
End
Definition audit_cycle_fields_def:
  audit_cycle_fields =
    [("self",audit_cycle_type,0); ("word",BaseT (UintT 256),0)]
End
Definition audit_cycle_metadata_def:
  audit_cycle_metadata = FEMPTY |+ ("AuditCycle",audit_cycle_fields)
End

(* Kernel-proved finite-map computation rules, never parity rewrites. *)
Theorem restrict_complement_singleton:
  DRESTRICT sf (COMPL {name}) = sf \\ name
Proof
  rw[fmap_eq_flookup, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >> rw[]
QED

Theorem metadata_FEVERY_update[compute]:
  FEVERY P (sf |+ (name, fields)) =
  (P (name, fields) /\ FEVERY P (sf \\ name))
Proof
  simp[FEVERY_FUPDATE, restrict_complement_singleton]
QED

val () = computeLib.add_persistent_funs ["finite_map.FEVERY_FEMPTY"];

Theorem audit_cycle_metadata_not_acyclic:
  ~acyclic_struct_metadata audit_cycle_metadata
Proof
  EVAL_TAC
QED

Theorem type_rank_tuple_bytes_probe:
  type_rank FEMPTY (TupleT [BaseT (BytesT (Dynamic 64));
                          ArrayT (TupleT [BaseT BoolT]) (Fixed 7)]) = 5
Proof
  EVAL_TAC
QED

(* Soundness of the computable test: every actual recursive type edge is
   contained in a well-founded relation, including arbitrary nested tuples
   and arrays. No field-size or array-capacity bound is involved. *)
Definition type_copy_child_def:
  type_copy_child sf child (ArrayT elem _) = (child = elem) /\
  type_copy_child sf child (TupleT tys) = MEM child tys /\
  type_copy_child sf child (StructT nsid) =
    MEM child (MAP (FST o SND)
      (get_struct_fields sf (nsid_to_string nsid))) /\
  type_copy_child sf child (BaseT _) = F /\
  type_copy_child sf child (FlagT _) = F /\
  type_copy_child sf child NoneT = F
End

Theorem type_copy_child_rank:
  acyclic_struct_metadata sf /\ type_copy_child sf child parent ==>
  type_rank sf child < type_rank sf parent
Proof
  strip_tac >> Cases_on `parent` >> gvs[type_copy_child_def]
  >- (drule member_rank_lt_tuple >> simp[])
  >- simp[type_rank_def]
  >> fs[MEM_MAP] >>
  rename1 `MEM triple (get_struct_fields sf (nsid_to_string nsid))` >>
  PairCases_on `triple` >> gvs[] >>
  drule_all member_rank_lt_struct >>
  ONCE_REWRITE_TAC [type_rank_nsid] >> simp[nsid_to_string_def]
QED

Theorem type_copy_child_well_founded:
  acyclic_struct_metadata sf ==> WF (type_copy_child sf)
Proof
  strip_tac >> irule WF_SUBSET >> qexists_tac `measure (type_rank sf)` >>
  simp[WF_measure, measure_def, inv_image_def] >>
  rpt strip_tac >> drule_all type_copy_child_rank >> simp[]
QED

Theorem acyclic_nested_struct_probe:
  acyclic_struct_metadata
    (FEMPTY |+ ("Inner",[("x",BaseT BoolT,32)])
            |+ ("Outer",[("i",ArrayT (StructT (NONE,"Inner")) (Dynamic 3),224)]))
Proof
  EVAL_TAC
QED
