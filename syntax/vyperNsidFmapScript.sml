(* The logical key is (source-id option, name).  The CV encoding is a pair:
   the main module's string trie and a numeric sptree of string tries. *)
Theory vyperNsidFmap
Ancestors
  cv cv_type cv_std cv_string_fmap cv_rep vyperNsidSizeBounds finite_map pred_set option pair alist
Libs
  cv_repLib cv_transLib

Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

Definition nsid_scope_def:
  nsid_scope (m:(num option # string) |-> 'a) src =
    FUN_FMAP (λname. THE (FLOOKUP m (src,name)))
             {name | (src,name) ∈ FDOM m}
End

Definition nsid_sources_def:
  nsid_sources (m:(num option # string) |-> 'a) =
    {n | ∃name. (SOME n,name) ∈ FDOM m}
End

Definition nsid_modules_def:
  nsid_modules (m:(num option # string) |-> 'a) =
    FUN_FMAP (λn. nsid_scope m (SOME n)) (nsid_sources m)
End

Theorem finite_nsid_scope[simp]:
  FINITE {name | (src,name) ∈ FDOM m}
Proof
  irule pred_setTheory.SUBSET_FINITE_I
  \\ qexists_tac ‘IMAGE SND (FDOM m)’ \\ simp[SUBSET_DEF]
  \\ rw[] \\ qexists_tac ‘(src,x)’ \\ simp[]
QED

Theorem finite_nsid_sources[simp]:
  FINITE (nsid_sources m)
Proof
  simp[nsid_sources_def]
  \\ irule pred_setTheory.SUBSET_FINITE_I
  \\ qexists_tac ‘IMAGE (λ(src,name). THE src) (FDOM m)’ \\ simp[SUBSET_DEF]
  \\ rw[] \\ qexists_tac ‘(SOME x,name)’ \\ simp[]
QED

Theorem nsid_scope_lookup[simp]:
  FLOOKUP (nsid_scope m src) name = FLOOKUP m (src,name)
Proof
  simp[nsid_scope_def,finite_mapTheory.FLOOKUP_FUN_FMAP]
  \\ Cases_on ‘FLOOKUP m (src,name)’
  \\ fs[finite_mapTheory.TO_FLOOKUP]
QED

Theorem nsid_modules_lookup[simp]:
  FLOOKUP (nsid_modules m) n =
    if n ∈ nsid_sources m then SOME (nsid_scope m (SOME n)) else NONE
Proof
  simp[nsid_modules_def,finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

Theorem nsid_scope_domain[simp]:
  FDOM (nsid_scope m src) = {name | (src,name) ∈ FDOM m}
Proof
  simp[nsid_scope_def]
QED

Theorem nsid_modules_domain[simp]:
  FDOM (nsid_modules m) = nsid_sources m
Proof
  simp[nsid_modules_def]
QED

Theorem nsid_modules_apply:
  n ∈ nsid_sources m ⇒ nsid_modules m ' n = nsid_scope m (SOME n)
Proof
  simp[nsid_modules_def,finite_mapTheory.FUN_FMAP_DEF]
QED

Theorem nsid_sources_scope_nonempty:
  n ∈ nsid_sources m ⇔ nsid_scope m (SOME n) ≠ FEMPTY
Proof
  simp[nsid_sources_def,nsid_scope_def,
       GSYM finite_mapTheory.FDOM_EQ_EMPTY,
       finite_mapTheory.FDOM_FMAP,EXTENSION]
QED

Definition from_nsid_fmap_def:
  from_nsid_fmap (f:'a -> cv) (m:(num option # string) |-> 'a) =
    from_pair (from_string_fmap f) (from_fmap (from_string_fmap f))
      (nsid_scope m NONE, nsid_modules m)
End

Definition nsid_reassemble_def:
  nsid_reassemble (global:string |-> 'a, modules:num |-> (string |-> 'a)) =
    FUN_FMAP
      (λ(src,name).
        case src of
        | NONE => THE (FLOOKUP global name)
        | SOME n => THE (FLOOKUP (THE (FLOOKUP modules n)) name))
      (IMAGE (λname. (NONE,name)) (FDOM global) ∪
       BIGUNION (IMAGE
         (λn. IMAGE (λname. (SOME n,name)) (FDOM (modules ' n)))
         (FDOM modules)))
End

Theorem nsid_reassemble_finite[simp]:
  FINITE
    (IMAGE (λname. (NONE,name)) (FDOM global) ∪
     BIGUNION (IMAGE
       (λn. IMAGE (λname. (SOME n,name)) (FDOM (modules ' n)))
       (FDOM modules)))
Proof
  simp[] \\ rw[] \\ irule pred_setTheory.IMAGE_FINITE \\ simp[]
QED

Theorem nsid_reassemble_scopes:
  nsid_reassemble (nsid_scope m NONE,nsid_modules m) = m
Proof
  rewrite_tac[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM]
  \\ gen_tac
  \\ rewrite_tac[nsid_reassemble_def]
  \\ dep_rewrite.DEP_REWRITE_TAC [finite_mapTheory.FLOOKUP_FUN_FMAP]
  \\ simp[nsid_reassemble_finite]
  \\ Cases_on ‘x’ \\ Cases_on ‘q’
  \\ simp[nsid_scope_domain,nsid_modules_domain,
          nsid_modules_lookup,nsid_scope_lookup,
          pred_setTheory.IN_BIGUNION,pred_setTheory.IN_IMAGE]
  \\ rw[nsid_modules_apply,nsid_scope_domain]
  \\ fs[nsid_modules_apply,nsid_scope_domain,
        finite_mapTheory.TO_FLOOKUP]
  \\ qmatch_goalsub_abbrev_tac ‘FLOOKUP m key’
  \\ Cases_on ‘FLOOKUP m key’
  \\ fs[Abbr‘key’,finite_mapTheory.TO_FLOOKUP,
        nsid_sources_def,nsid_modules_apply,nsid_scope_domain,
        pred_setTheory.IN_IMAGE]
  \\ qpat_x_assum ‘∀s. _’
       (qspec_then
         ‘IMAGE (λname. (SOME x,name)) (FDOM (nsid_modules m ' x))’
         mp_tac)
  \\ simp[nsid_modules_apply,nsid_scope_domain,
          nsid_sources_def,finite_mapTheory.TO_FLOOKUP]
  \\ ‘x ∈ nsid_sources m’ by
       (simp[nsid_sources_def] \\ qexists_tac ‘r’
        \\ fs[finite_mapTheory.TO_FLOOKUP])
  \\ simp[nsid_modules_apply,nsid_scope_domain,
          finite_mapTheory.TO_FLOOKUP]
  \\ qexists_tac ‘x’
  \\ conj_tac >-
       simp[nsid_modules_apply,nsid_scope_domain,
            finite_mapTheory.TO_FLOOKUP,EXTENSION]
  \\ qexists_tac ‘r’
  \\ fs[finite_mapTheory.TO_FLOOKUP]
QED

Definition to_nsid_fmap_def:
  to_nsid_fmap (t:cv -> 'a) cv =
    nsid_reassemble
      (to_string_fmap t (cv_fst cv),
       to_fmap (to_string_fmap t) (cv_snd cv))
End

Theorem from_to_nsid_fmap[cv_from_to]:
  from_to (f:'a -> cv) t ⇒
  from_to (from_nsid_fmap f) (to_nsid_fmap t)
Proof
  strip_tac
  \\ ‘from_to (from_string_fmap f) (to_string_fmap t)’ by
       metis_tac[cv_string_fmapTheory.from_to_string_fmap]
  \\ ‘from_to (from_fmap (from_string_fmap f))
              (to_fmap (to_string_fmap t))’ by
       metis_tac[cv_stdTheory.from_to_fmap]
  \\ gvs[from_to_def,from_nsid_fmap_def,to_nsid_fmap_def,
         from_pair_def,cv_fst_def,cv_snd_def,nsid_reassemble_scopes]
QED

(* Projection identities make all finite-map operation proofs extensional. *)
Theorem nsid_scope_update:
  nsid_scope (m |+ ((src,name),v)) tgt =
    if src = tgt then nsid_scope m tgt |+ (name,v) else nsid_scope m tgt
Proof
  rw[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
     finite_mapTheory.FLOOKUP_UPDATE,nsid_scope_lookup]
QED

Theorem nsid_scope_delete:
  nsid_scope (m \\ (src,name)) tgt =
    if src = tgt then nsid_scope m tgt \\ name else nsid_scope m tgt
Proof
  rw[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
     finite_mapTheory.DOMSUB_FLOOKUP_THM,nsid_scope_lookup]
QED

Theorem nsid_scope_union:
  nsid_scope (m1 ⊌ m2) src = nsid_scope m1 src ⊌ nsid_scope m2 src
Proof
  rw[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
     finite_mapTheory.FLOOKUP_FUNION,nsid_scope_lookup]
QED

Theorem nsid_sources_update:
  nsid_sources (m |+ ((src,name),v)) =
    case src of NONE => nsid_sources m | SOME n => n INSERT nsid_sources m
Proof
  Cases_on ‘src’ \\ simp[nsid_sources_def,EXTENSION]
  \\ metis_tac[]
QED

Theorem nsid_sources_delete:
  nsid_sources (m \\ (SOME n,name)) =
    if nsid_scope m (SOME n) \\ name = FEMPTY then
      nsid_sources m DELETE n else nsid_sources m
Proof
  simp[EXTENSION,nsid_sources_scope_nonempty,nsid_scope_delete]
  \\ rw[nsid_sources_scope_nonempty]
  \\ Cases_on ‘nsid_scope m (SOME n) = FEMPTY’ \\ fs[]
QED

Theorem nsid_sources_union:
  nsid_sources (m1 ⊌ m2) = nsid_sources m1 ∪ nsid_sources m2
Proof
  simp[nsid_sources_def,EXTENSION] \\ metis_tac[]
QED

Theorem nsid_modules_update:
  nsid_modules (m |+ ((SOME n,name),v)) =
    nsid_modules m |+
      (n,nsid_scope m (SOME n) |+ (name,v))
Proof
  simp[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
       nsid_sources_update,nsid_modules_lookup,nsid_scope_update,
       finite_mapTheory.FLOOKUP_UPDATE]
  \\ rw[nsid_modules_lookup,nsid_scope_update,
        finite_mapTheory.FLOOKUP_UPDATE] \\ fs[]
QED

Theorem nsid_modules_delete:
  nsid_modules (m \\ (SOME n,name)) =
    let inner = nsid_scope m (SOME n) \\ name in
    if inner = FEMPTY then nsid_modules m \\ n
    else nsid_modules m |+ (n,inner)
Proof
  CONV_TAC (REWR_CONV finite_mapTheory.FLOOKUP_EXT)
  \\ rewrite_tac[FUN_EQ_THM]
  \\ gen_tac
  \\ Cases_on ‘nsid_scope m (SOME n) \\ name = FEMPTY’
  \\ Cases_on ‘x = n’
  \\ simp[nsid_modules_lookup,nsid_sources_delete,nsid_scope_delete,
          finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.DOMSUB_FLOOKUP_THM,LET_THM]
  \\ fs[nsid_sources_scope_nonempty]
  \\ Cases_on ‘nsid_scope m (SOME n) = FEMPTY’ \\ fs[]
QED

Definition nsid_modules_merge_def:
  nsid_modules_merge a b =
    FUN_FMAP (λn. (case FLOOKUP a n of
                    NONE => FEMPTY | SOME inner => inner) ⊌
                  (case FLOOKUP b n of
                    NONE => FEMPTY | SOME inner => inner))
             (FDOM a ∪ FDOM b)
End

Theorem nsid_modules_union:
  nsid_modules (m1 ⊌ m2) =
    nsid_modules_merge (nsid_modules m1) (nsid_modules m2)
Proof
  simp[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
       nsid_modules_merge_def,nsid_sources_union,nsid_modules_lookup,
       nsid_scope_union,finite_mapTheory.FLOOKUP_FUN_FMAP]
  \\ rw[nsid_modules_lookup,nsid_scope_union]
  \\ fs[nsid_sources_scope_nonempty]
QED

Definition cv_nsid_lookup_def:
  cv_nsid_lookup src name env =
    cv_if (cv_ispair src)
      (cv_st_get (cv_snd (cv_lookup (cv_snd src) (cv_snd env))) name)
      (cv_st_get (cv_fst env) name)
End

Definition cv_nsid_insert_def:
  cv_nsid_insert src name value env =
    cv_if (cv_ispair src)
      (Pair (cv_fst env)
        (cv_insert (cv_snd src)
          (cv_st_set
            (cv_snd (cv_lookup (cv_snd src) (cv_snd env)))
            name value)
          (cv_snd env)))
      (Pair (cv_st_set (cv_fst env) name value) (cv_snd env))
End

Definition cv_nsid_delete_def:
  cv_nsid_delete src name env =
    cv_if (cv_ispair src)
      (let n = cv_snd src in
       let inner = cv_st_del (cv_snd (cv_lookup n (cv_snd env))) name in
       Pair (cv_fst env)
         (cv_if (cv_ispair inner)
           (cv_insert n inner (cv_snd env))
           (cv_delete n (cv_snd env))))
      (Pair (cv_st_del (cv_fst env) name) (cv_snd env))
End

Theorem nsid_empty_rep[cv_rep]:
  from_nsid_fmap f FEMPTY = Pair (Num 0) (Num 0)
Proof
  simp[from_nsid_fmap_def,nsid_scope_def,nsid_modules_def,
       nsid_sources_def,from_pair_def,cv_rep_string_FEMPTY,cv_rep_FEMPTY]
QED

Theorem cv_nsid_get_missing:
  cv_st_get (Num 0) (from_list from_char name) = Num 0
Proof
  ‘cv_st_get (Num 0) (from_list from_char name) =
   from_option (λn:num. Num n)
     (FLOOKUP (FEMPTY:string |-> num) name)’ by
    simp[cv_rep_string_FLOOKUP,cv_rep_string_FEMPTY]
  \\ simp[from_option_def]
QED

Theorem nsid_lookup_rep[cv_rep]:
  from_option f (FLOOKUP m (src,name)) =
    cv_nsid_lookup (from_option Num src)
      (from_list from_char name) (from_nsid_fmap f m)
Proof
  Cases_on ‘src’
  \\ simp[cv_nsid_lookup_def,from_option_def,cv_if_def,cv_ispair_def,
          from_nsid_fmap_def,from_pair_def,
          GSYM cv_rep_string_FLOOKUP,nsid_scope_lookup,
          GSYM cv_rep_FLOOKUP,nsid_modules_lookup,
          cv_nsid_get_missing]
  \\ Cases_on ‘x ∈ nsid_sources m’
  \\ simp[from_option_def,cv_snd_def,cv_nsid_get_missing,
          GSYM cv_rep_string_FLOOKUP,nsid_scope_lookup]
  \\ fs[nsid_sources_def,finite_mapTheory.TO_FLOOKUP,from_option_def]
QED

Theorem nsid_modules_update_none:
  nsid_modules (m |+ ((NONE,name),v)) = nsid_modules m
Proof
  simp[nsid_modules_def,nsid_sources_update,nsid_scope_update]
QED

Theorem nsid_update_rep[cv_rep]:
  from_nsid_fmap f (m |+ ((src,name),v)) =
    cv_nsid_insert (from_option Num src)
      (from_list from_char name) (f v) (from_nsid_fmap f m)
Proof
  Cases_on ‘src’
  \\ simp[cv_nsid_insert_def,from_option_def,cv_if_def,cv_ispair_def,
          from_nsid_fmap_def,from_pair_def,nsid_scope_update,
          nsid_modules_update_none,nsid_modules_update,
          cv_rep_string_FUPDATE,cv_rep_FUPDATE,
          GSYM cv_rep_FLOOKUP,nsid_modules_lookup]
  \\ Cases_on ‘x ∈ nsid_sources m’
  \\ simp[from_option_def,cv_snd_def,cv_rep_string_FEMPTY]
  \\ fs[nsid_sources_scope_nonempty,cv_rep_string_FEMPTY]
QED


Theorem cv_nsid_string_empty:
  cv_ispair (from_string_fmap f m) =
    if m = FEMPTY then Num 0 else Num 1
Proof
  Cases_on ‘m = FEMPTY’ >-
    simp[cv_rep_string_FEMPTY,cv_ispair_def]
  \\ ‘∃name. name ∈ FDOM m’ by
       (CCONTR_TAC \\ fs[finite_mapTheory.FDOM_F_FEMPTY1])
  \\ Cases_on ‘FLOOKUP m name’ \\ fs[finite_mapTheory.TO_FLOOKUP]
  \\ qmatch_asmsub_rename_tac ‘FLOOKUP m name = SOME value’
  \\ ‘st_sets Nothing (fmap_to_alist m) ≠ Nothing’ by
       (strip_tac
        \\ ‘st_get (st_sets Nothing (fmap_to_alist m)) name = SOME value’ by
             simp[cv_string_fmapTheory.st_get_st_sets,
                  alistTheory.ALOOKUP_EQ_FLOOKUP]
        \\ gvs[cv_string_fmapTheory.st_get_Nothing])
  \\ Cases_on ‘st_sets Nothing (fmap_to_alist m)’
  \\ gvs[from_string_fmap_def,
         cv_string_fmapTheory.from_cv_string_fmap_str_trie_def,
         cv_ispair_def]
QED

Theorem cv_nsid_missing_inner:
  cv_st_del (Num 0) (from_list from_char name) = Num 0
Proof
  ‘cv_st_del (Num 0) (from_list from_char name) =
    from_string_fmap (λn:num. Num n)
      ((FEMPTY:string |-> num) \\ name)’ by
    simp[cv_rep_string_DOMSUB,cv_rep_string_FEMPTY]
  \\ simp[cv_rep_string_FEMPTY]
QED

Theorem nsid_modules_delete_none:
  nsid_modules (m \\ (NONE,name)) = nsid_modules m
Proof
  simp[nsid_modules_def,nsid_sources_def,nsid_scope_delete,EXTENSION]
QED

Theorem nsid_delete_rep[cv_rep]:
  from_nsid_fmap f (m \\ (src,name)) =
    cv_nsid_delete (from_option Num src)
      (from_list from_char name) (from_nsid_fmap f m)
Proof
  Cases_on ‘src’
  \\ simp[cv_nsid_delete_def,from_option_def,cv_if_def,cv_ispair_def,
          from_nsid_fmap_def,from_pair_def,nsid_scope_delete,
          nsid_modules_delete_none,nsid_modules_delete,
          cv_rep_string_DOMSUB,cv_rep_DOMSUB,cv_rep_FUPDATE,
          GSYM cv_rep_FLOOKUP,nsid_modules_lookup,LET_THM]
  \\ Cases_on ‘x ∈ nsid_sources m’
  \\ simp[from_option_def,cv_snd_def,cv_rep_string_FEMPTY,
          cv_nsid_missing_inner,GSYM cv_rep_string_DOMSUB,
          cv_nsid_string_empty]
  \\ Cases_on ‘nsid_scope m (SOME x) \\ name = FEMPTY’
  \\ simp[cv_nsid_string_empty,cv_rep_string_FEMPTY]
  \\ gvs[nsid_sources_scope_nonempty,cv_rep_string_FEMPTY,
         cv_rep_DOMSUB,cv_rep_FUPDATE]
QED

(* Generic-key forms are needed when an interpreter carries an nsid as a
   variable instead of exposing its source/name components syntactically. *)
Theorem nsid_lookup_key_rep[cv_rep]:
  from_option f (FLOOKUP m (key:num option # string)) =
    cv_nsid_lookup
      (cv_fst (from_pair (from_option Num) (from_list from_char) key))
      (cv_snd (from_pair (from_option Num) (from_list from_char) key))
      (from_nsid_fmap f m)
Proof
  Cases_on ‘key’ \\ simp[nsid_lookup_rep,from_pair_def]
QED

Theorem nsid_update_key_rep[cv_rep]:
  from_nsid_fmap f (m |+ ((key:num option # string),v)) =
    cv_nsid_insert
      (cv_fst (from_pair (from_option Num) (from_list from_char) key))
      (cv_snd (from_pair (from_option Num) (from_list from_char) key))
      (f v) (from_nsid_fmap f m)
Proof
  Cases_on ‘key’ \\ simp[nsid_update_rep,from_pair_def]
QED

Theorem nsid_delete_key_rep[cv_rep]:
  from_nsid_fmap f (m \\ (key:num option # string)) =
    cv_nsid_delete
      (cv_fst (from_pair (from_option Num) (from_list from_char) key))
      (cv_snd (from_pair (from_option Num) (from_list from_char) key))
      (from_nsid_fmap f m)
Proof
  Cases_on ‘key’ \\ simp[nsid_delete_rep,from_pair_def]
QED

(* The outer map cannot be merged with cv_union: on a collision its values
   must themselves be merged as string maps.  Traversal visits each distinct
   numeric source once, including when the same name occurs at other sources. *)
Definition cv_nsid_merge_modules_def:
  cv_nsid_merge_modules (Num _) acc = acc ∧
  cv_nsid_merge_modules (Pair entry rest) acc =
    cv_nsid_merge_modules rest
      (cv_insert (cv_fst entry)
        (cv_st_union (cv_snd entry)
          (cv_snd (cv_lookup (cv_fst entry) acc))) acc)
End

(* cv_eval's code-equation registry requires a single equation, rather than
   the constructor equations used for the structural termination proof. *)
Theorem cv_nsid_merge_modules_eq:
  cv_nsid_merge_modules entries acc =
    cv_if (cv_ispair entries)
      (cv_nsid_merge_modules (cv_snd entries)
        (cv_insert (cv_fst (cv_fst entries))
          (cv_st_union (cv_snd (cv_fst entries))
            (cv_snd (cv_lookup (cv_fst (cv_fst entries)) acc))) acc))
      acc
Proof
  Cases_on ‘entries’
  \\ simp[cv_nsid_merge_modules_def,cv_if_def,cv_ispair_def]
QED

val () = DefnBase.register_defn
  {tag = "user", thmname = "cv_nsid_merge_modules_eq"};

Definition nsid_merge_entries_def:
  nsid_merge_entries [] acc = acc ∧
  nsid_merge_entries ((n,inner)::rest) acc =
    nsid_merge_entries rest
      (acc |+ (n,inner ⊌
        (case FLOOKUP acc n of NONE => FEMPTY | SOME old => old)))
End

Theorem nsid_merge_entries_rep:
  ∀entries acc.
    from_fmap (from_string_fmap f) (nsid_merge_entries entries acc) =
    cv_nsid_merge_modules
      (from_list (from_pair (λn. Num n) (from_string_fmap f)) entries)
      (from_fmap (from_string_fmap f) acc)
Proof
  Induct_on ‘entries’ \\ rpt gen_tac
  \\ simp[nsid_merge_entries_def,cv_nsid_merge_modules_def,
          from_list_def]
  \\ Cases_on ‘h’
  \\ simp[nsid_merge_entries_def,from_pair_def,cv_rep_FUPDATE,
          GSYM cv_rep_FLOOKUP,
          from_option_def,cv_rep_string_FUNION,cv_rep_string_FEMPTY]
  \\ Cases_on ‘FLOOKUP acc q’
  \\ simp[from_option_def,cv_rep_string_FEMPTY,
          cv_rep_FUPDATE,cv_rep_string_FUNION]
QED

Theorem nsid_merge_entries_correct:
  ∀entries acc.
    ALL_DISTINCT (MAP FST entries) ⇒
    nsid_merge_entries entries acc =
      nsid_modules_merge (alist_to_fmap entries) acc
Proof
  Induct_on ‘entries’
  >- (gen_tac
      \\ simp[nsid_merge_entries_def,nsid_modules_merge_def,
              finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
              finite_mapTheory.FLOOKUP_FUN_FMAP]
      \\ gen_tac \\ Cases_on ‘FLOOKUP acc x’
      \\ fs[finite_mapTheory.TO_FLOOKUP])
  \\ gen_tac \\ Cases_on ‘h’
  \\ simp[nsid_merge_entries_def,nsid_modules_merge_def]
  \\ simp[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
          finite_mapTheory.FLOOKUP_FUN_FMAP]
  \\ rw[finite_mapTheory.FLOOKUP_SIMP]
  \\ Cases_on ‘x = q’
  \\ gvs[alistTheory.ALOOKUP_NONE]
  \\ ‘ALOOKUP entries q = NONE’ by
       simp[alistTheory.ALOOKUP_NONE]
  \\ simp[]
QED

Theorem nsid_modules_toAList:
  alist_to_fmap (sptree$toAList (sptree$fromAList (fmap_to_alist m))) = m
Proof
  simp[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM,
       sptreeTheory.ALOOKUP_toAList,sptreeTheory.lookup_fromAList,
       finite_mapTheory.TO_FLOOKUP]
QED

Theorem cv_nsid_modules_toAList:
  cv_toAList (from_fmap f m) =
    from_list (from_pair (λn. Num n) f)
      (sptree$toAList (sptree$fromAList (fmap_to_alist m)))
Proof
  simp[from_fmap_def,GSYM cv_stdTheory.cv_toAList_thm]
  \\ ‘(λn. Num n) = Num’ by simp[FUN_EQ_THM]
  \\ simp[]
QED

Theorem nsid_union_rep[cv_rep]:
  from_nsid_fmap f (m1 ⊌ m2) =
    Pair (cv_st_union (cv_fst (from_nsid_fmap f m1))
                      (cv_fst (from_nsid_fmap f m2)))
         (cv_nsid_merge_modules
            (cv_toAList (cv_snd (from_nsid_fmap f m1)))
            (cv_snd (from_nsid_fmap f m2)))
Proof
  simp[from_nsid_fmap_def,from_pair_def,nsid_scope_union,
       nsid_modules_union,cv_rep_string_FUNION]
  \\ simp[cv_nsid_modules_toAList,GSYM nsid_merge_entries_rep]
  \\ simp[nsid_merge_entries_correct,
          sptreeTheory.ALL_DISTINCT_MAP_FST_toAList,
          nsid_modules_toAList]
QED


(* Cross-namespace aliasing, nested union, and removal of the last entry in
   a source are all observable on the same tiny example. *)
Definition nsid_cv_smoke_def:
  nsid_cv_smoke =
    let base =
      (FEMPTY:(num option # string) |-> num)
        |+ ((NONE,"x"),1)
        |+ ((SOME 1,"x"),2) in
    let mixed =
      (FEMPTY |+ ((NONE,"x"),3) |+ ((SOME 1,"y"),4)) ⊌ base in
    FLOOKUP base (NONE,"x") = SOME 1 ∧
    FLOOKUP base (SOME 1,"x") = SOME 2 ∧
    FLOOKUP (base \\ (SOME 1,"x")) (NONE,"x") = SOME 1 ∧
    FLOOKUP (base \\ (NONE,"x")) (SOME 1,"x") = SOME 2 ∧
    FLOOKUP mixed (NONE,"x") = SOME 3 ∧
    FLOOKUP mixed (SOME 1,"x") = SOME 2 ∧
    FLOOKUP mixed (SOME 1,"y") = SOME 4 ∧
    FLOOKUP (mixed \\ (SOME 1,"x")) (SOME 1,"y") = SOME 4
End

val () = cv_auto_trans nsid_cv_smoke_def;

Theorem nsid_cv_smoke_evaluates:
  nsid_cv_smoke
Proof
  CONV_TAC cv_eval
QED

(* An opaque nsid exercises the same rules as literal source/name pairs. *)
Definition nsid_cv_key_projection_def:
  nsid_cv_key_projection (key:num option # string) =
    let env = ((FEMPTY:(num option # string) |-> num)
                 |+ ((NONE,"x"),7)) |+ (key,9) in
    (FLOOKUP (env \\ key) (NONE,"x"), FLOOKUP env key)
End

val () = cv_auto_trans nsid_cv_key_projection_def;

Theorem nsid_cv_key_projection_evaluates:
  nsid_cv_key_projection (SOME 1,"x") = (SOME 7,SOME 9) ∧
  nsid_cv_key_projection (NONE,"x") = (NONE,SOME 9)
Proof
  CONV_TAC cv_eval
QED

Definition cv_nsid_trie_count_def:
  cv_nsid_trie_count (Num n) = (0:num) ∧
  cv_nsid_trie_count (Pair tag (Num n)) =
    (if cv$c2b (cv_lt (Num 1) tag) then 0 else 1) ∧
  cv_nsid_trie_count (Pair tag (Pair char (Num n))) =
    (if cv$c2b (cv_lt (Num 1) tag) then 0 else 1) ∧
  cv_nsid_trie_count (Pair tag (Pair char (Pair child next))) =
    (if cv$c2b (cv_lt (Num 1) tag) then
       cv_nsid_trie_count child + cv_nsid_trie_count next
     else 1)
End


Theorem cv_nsid_trie_count_eq:
  cv_nsid_trie_count t =
    if cv$c2b (cv_ispair t) then
      if cv$c2b (cv_lt (Num 1) (cv_fst t)) then
        cv_nsid_trie_count (cv_fst (cv_snd (cv_snd t))) +
        cv_nsid_trie_count (cv_snd (cv_snd (cv_snd t)))
      else 1
    else 0
Proof
  Cases_on ‘t’
  \\ simp[cv_nsid_trie_count_def,cv_ispair_def,
          cv_fst_def,cv_snd_def]
  \\ Cases_on ‘g'’
  \\ simp[cv_nsid_trie_count_def,cv_fst_def,cv_snd_def]
  \\ qmatch_goalsub_rename_tac ‘cv_nsid_trie_count (Pair tag (Pair char rest))’
  \\ Cases_on ‘rest’
  \\ simp[cv_nsid_trie_count_def,cv_fst_def,cv_snd_def]
QED

Theorem cv_nsid_trie_del_nil_count:
  ∀t. cv_st_get_nil t ≠ Num 0 ⇒
      cv_nsid_trie_count (cv_st_del_nil t) < cv_nsid_trie_count t
Proof
  completeInduct_on ‘cv_size t’
  \\ Cases_on ‘t’
  \\ simp[Once cv_string_fmapTheory.cv_st_get_nil_def,
          Once cv_string_fmapTheory.cv_st_del_nil_def,
          cv_size_def,cv_nsid_trie_count_def]
  \\ Cases_on ‘g’
  \\ gvs[cv_repTheory.cv_termination_simp,cv_nsid_trie_count_def]
  \\ Cases_on ‘g'’
  \\ gvs[cv_repTheory.cv_termination_simp,cv_nsid_trie_count_def,cv_size_def]
  \\ Cases_on ‘1 < m’
  \\ gvs[cv_nsid_trie_count_def,c2b_def]
  \\ TRY (simp[Once cv_string_fmapTheory.cv_st_get_nil_def,
               cv_ispair_def] \\ NO_TAC)
  \\ Cases_on ‘g''’
  \\ gvs[cv_size_def,cv_fst_def,cv_snd_def,cv_nsid_trie_count_def]
  \\ TRY (simp[Once cv_string_fmapTheory.cv_st_get_nil_def,
               cv_ispair_def] \\ NO_TAC)
  \\ TRY (simp[Once cv_nsid_trie_count_eq,
               cv_lt_def,c2b_def,cv_ispair_def] \\ NO_TAC)
  \\ rpt strip_tac
  \\ qmatch_asmsub_rename_tac ‘cv_st_get_nil rest’
  \\ last_x_assum (qspec_then ‘cv_size rest’ mp_tac)
  \\ simp[cv_size_def]
  \\ disch_then (qspec_then ‘rest’ mp_tac)
  \\ simp[]
  \\ strip_tac
  \\ decide_tac
QED

Theorem cv_nsid_trie_count_terminal:
  ¬cv$c2b (cv_lt (Num 1) tag) ⇒
    cv_nsid_trie_count (Pair tag content) = 1
Proof
  simp[Once cv_nsid_trie_count_eq,cv_ispair_def,cv_fst_def]
QED

Theorem cv_nsid_trie_count_branch:
  cv$c2b (cv_lt (Num 1) tag) ⇒
    cv_nsid_trie_count (Pair tag (Pair char tail)) =
    cv_nsid_trie_count (cv_fst tail) +
    cv_nsid_trie_count (cv_snd tail)
Proof
  simp[Once cv_nsid_trie_count_eq,cv_ispair_def,cv_fst_def,
       cv_snd_def]
QED

Theorem cv_nsid_trie_count_mk_Branch:
  ∀c child rest.
    cv_nsid_trie_count (cv_mk_Branch c child rest) =
    cv_nsid_trie_count child + cv_nsid_trie_count rest
Proof
  Cases_on ‘child’
  \\ simp[Once cv_string_fmapTheory.cv_mk_Branch_def,
          cv_nsid_trie_count_def,cv_ispair_def]
  \\ Cases_on ‘g’
  \\ simp[cv_nsid_trie_count_def,cv_ispair_def,cv_lt_def,
          cv_fst_def,cv_snd_def,c2b_def]
  \\ Cases_on ‘g'’
  \\ simp[cv_nsid_trie_count_def,cv_fst_def,cv_snd_def]
  \\ Cases_on ‘1 < m’
  \\ gvs[cv_nsid_trie_count_def,cv_ispair_def,c2b_def,
         cv_fst_def,cv_snd_def]
  \\ simp[cv_nsid_trie_count_terminal,
          cv_nsid_trie_count_branch,cv_lt_def,c2b_def,
          cv_fst_def,cv_snd_def]
QED

Theorem cv_nsid_st_get_nil_num[simp]:
  cv_st_get_nil (Num n) = Num 0
Proof
  simp[Once cv_string_fmapTheory.cv_st_get_nil_def,cv_ispair_def]
QED

Theorem cv_nsid_st_get_cons_num[simp]:
  cv_st_get_cons (Num n) x xs = Num 0
Proof
  simp[Once cv_string_fmapTheory.cv_st_get_def,cv_ispair_def]
QED

Theorem cv_nsid_st_get_num[simp]:
  cv_st_get (Num n) name = Num 0
Proof
  Cases_on ‘name’
  \\ simp[Once cv_string_fmapTheory.cv_st_get_def,cv_ispair_def]
QED

Theorem cv_nsid_st_get_by_name[simp]:
  (cv_st_get t (Num n) = cv_st_get_nil t) ∧
  (cv_st_get t (Pair x xs) = cv_st_get_cons t x xs)
Proof
  simp[Once cv_string_fmapTheory.cv_st_get_def,
       cv_ispair_def,cv_fst_def,cv_snd_def]
  \\ simp[Once cv_string_fmapTheory.cv_st_get_def,
          cv_ispair_def,cv_fst_def,cv_snd_def]
QED

Theorem cv_nsid_trie_del_cons_count:
  ∀t x xs. cv_st_get_cons t x xs ≠ Num 0 ⇒
           cv_nsid_trie_count (cv_st_del_cons t x xs) <
           cv_nsid_trie_count t
Proof
  completeInduct_on ‘cv_size t’
  \\ Cases_on ‘t’
  \\ simp[Once cv_string_fmapTheory.cv_st_get_def,
          Once cv_string_fmapTheory.cv_st_del_cons_def,
          cv_nsid_trie_count_def,cv_size_def]
  \\ Cases_on ‘g’
  \\ gvs[cv_repTheory.cv_termination_simp,cv_nsid_trie_count_def]
  \\ Cases_on ‘g'’
  \\ gvs[cv_repTheory.cv_termination_simp,
         cv_nsid_trie_count_def,cv_size_def]
  \\ Cases_on ‘1 < m’
  \\ gvs[cv_nsid_trie_count_def,c2b_def]
  \\ Cases_on ‘g''’
  \\ gvs[cv_nsid_trie_count_def,cv_size_def,
         cv_fst_def,cv_snd_def]
  \\ rpt strip_tac
  \\ Cases_on ‘∃k. cv_lt x g = Num (SUC k)’ \\ gvs[]
  \\ Cases_on ‘∃k. cv_lt g x = Num (SUC k)’
  \\ gvs[cv_nsid_trie_count_def,cv_nsid_trie_count_mk_Branch]
  \\ Cases_on ‘xs’
  \\ gvs[cv_nsid_st_get_by_name,
         cv_ispair_def,cv_fst_def,cv_snd_def,
         cv_nsid_trie_del_nil_count]
QED

Theorem cv_nsid_trie_delete_count:
  ∀t name. cv_st_get t name ≠ Num 0 ⇒
    cv_nsid_trie_count (cv_st_del t name) <
    cv_nsid_trie_count t
Proof
  Cases_on ‘name’
  \\ simp[cv_string_fmapTheory.cv_st_del_def,
          cv_nsid_st_get_by_name,cv_ispair_def,
          cv_fst_def,cv_snd_def,
          cv_nsid_trie_del_nil_count,
          cv_nsid_trie_del_cons_count]
QED

Definition cv_nsid_count_def:
  cv_nsid_count env =
    cv_nsid_trie_count (cv_fst env) +
    cv_nsid_tree_count cv_nsid_trie_count (cv_snd env)
End

Theorem cv_nsid_ispair_bool[simp]:
  cv$c2b (cv_ispair v) ⇔ cv_ispair v = Num 1
Proof
  Cases_on ‘v’
  \\ simp[cv_ispair_def,c2b_def]
QED

Theorem cv_nsid_delete_count:
  ∀src name env.
    cv_ispair (cv_nsid_lookup src name env) = Num 1 ⇒
    cv_nsid_count (cv_nsid_delete src name env) <
    cv_nsid_count env
Proof
  Cases_on ‘env’ \\ Cases_on ‘src’
  \\ simp[cv_nsid_lookup_def,cv_nsid_delete_def,cv_nsid_count_def,
          cv_if_def,cv_ispair_def,cv_fst_def,cv_snd_def,
          LET_THM,cv_nsid_st_get_num,cv_nsid_trie_delete_count]
  \\ TRY (simp[Once cv_lookup_def,cv_nsid_st_get_num] \\ NO_TAC)
  \\ rpt strip_tac
  \\ TRY (irule cv_nsid_trie_delete_count
          \\ Cases_on ‘cv_st_get g name’
          \\ gvs[cv_ispair_def] \\ NO_TAC)
  \\ qmatch_asmsub_rename_tac
       ‘cv_st_get (cv_snd (cv_lookup key tree)) name’
  \\ qspecl_then [‘key’,‘tree’] strip_assume_tac
       cv_nsid_lookup_numeric_shape
  \\ gvs[cv_nsid_st_get_num]
  \\ ‘cv_nsid_trie_count (cv_st_del old name) <
      cv_nsid_trie_count old’ by (
       irule cv_nsid_trie_delete_count
       \\ Cases_on ‘cv_st_get old name’
       \\ gvs[cv_ispair_def])
  \\ Cases_on ‘cv_st_del old name’
  \\ gvs[cv_ispair_def,cv_nsid_tree_count_delete,
         cv_nsid_tree_count_insert_less]
QED
