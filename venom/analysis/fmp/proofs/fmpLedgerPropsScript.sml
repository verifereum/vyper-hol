(* Concrete, conditional allocation-ledger boundary.  The frontier is an
 * explicit natural address, not the interpreter's hidden vs_fmp field. *)
Theory fmpLedgerProps
Ancestors
  fmpReclaimProps venomState words rich_list list arithmetic finite_map

Datatype:
  fmp_region = <| fr_mark : string; fr_site : num;
                  fr_lo : num; fr_hi : num |>
End

Definition fmp_region_contains_def:
  fmp_region_contains r a <=> r.fr_lo <= a /\ a < r.fr_hi
End

Definition fmp_ledger_ok_def:
  fmp_ledger_ok insts env s top [] = T /\
  fmp_ledger_ok insts env s top (r::rs) =
    (r.fr_hi = top /\ r.fr_lo <= r.fr_hi /\ top < dimword (:256) /\
     lookup_var r.fr_mark s = SOME (n2w r.fr_lo) /\
     fmp_dalloca_query insts env r.fr_mark = SOME r.fr_site /\
     fmp_ledger_ok insts env s r.fr_lo rs)
End

Theorem fmp_ledger_empty[simp]:
  fmp_ledger_ok insts env s top []
Proof simp[fmp_ledger_ok_def]
QED

Theorem fmp_ledger_frame:
  !rs s s' top.
    fmp_ledger_ok insts env s top rs /\
    (!r. MEM r rs ==> lookup_var r.fr_mark s' = lookup_var r.fr_mark s) ==>
    fmp_ledger_ok insts env s' top rs
Proof
  Induct >> simp[fmp_ledger_ok_def] >> metis_tac[]
QED

Theorem fmp_ledger_update_fresh:
  fmp_ledger_ok insts env s top rs /\ ~MEM v (MAP (\r. r.fr_mark) rs) ==>
  fmp_ledger_ok insts env (update_var v value s) top rs
Proof
  strip_tac >> irule fmp_ledger_frame >> qexists `s` >> simp[] >>
  gvs[MEM_MAP, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem fmp_ledger_push:
  fmp_ledger_ok insts env s lo rs /\ lo <= hi /\ hi < dimword (:256) /\
  fmp_dalloca_query insts env mark = SOME site /\
  ~MEM mark (MAP (\r. r.fr_mark) rs) ==>
  fmp_ledger_ok insts env (update_var mark (n2w lo) s) hi
    (<| fr_mark := mark; fr_site := site; fr_lo := lo; fr_hi := hi |> :: rs)
Proof
  strip_tac >>
  `fmp_ledger_ok insts env (update_var mark (n2w lo) s) lo rs` by
    (irule fmp_ledger_update_fresh >> simp[]) >>
  gvs[fmp_ledger_ok_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem fmp_ledger_bounds:
  !rs top. fmp_ledger_ok insts env s top rs ==>
    EVERY (\r. r.fr_lo <= r.fr_hi /\ r.fr_hi <= top /\
               r.fr_hi < dimword (:256)) rs
Proof
  Induct >> simp[fmp_ledger_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[EVERY_MEM] >> rpt strip_tac >>
  res_tac >> decide_tac
QED

Theorem fmp_ledger_split:
  !ps top ks. fmp_ledger_ok insts env s top (ps ++ ks) /\ ps <> [] ==>
    fmp_ledger_ok insts env s (LAST ps).fr_lo ks /\
    (LAST ps).fr_lo <= top /\
    EVERY (\r. (LAST ps).fr_lo <= r.fr_lo /\ r.fr_hi <= top) ps
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `ps = []`
  >- gvs[fmp_ledger_ok_def] >>
  strip_tac >>
  fs[Once fmp_ledger_ok_def] >>
  first_x_assum (qspecl_then [`h.fr_lo`, `ks`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `ps` >> gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem fmp_ledger_retained_disjoint:
  fmp_ledger_ok insts env s top (ps ++ ks) /\ ps <> [] /\
  MEM r ks /\ (LAST ps).fr_lo <= a /\ a < top ==>
  ~fmp_region_contains r a
Proof
  strip_tac >> drule_all fmp_ledger_split >> strip_tac >>
  drule fmp_ledger_bounds >> simp[EVERY_MEM, fmp_region_contains_def] >>
  metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS]
QED

Theorem fmp_ledger_mark:
  !rs top r. fmp_ledger_ok insts env s top rs /\ MEM r rs ==>
    lookup_var r.fr_mark s = SOME (n2w r.fr_lo) /\
    fmp_dalloca_query insts env r.fr_mark = SOME r.fr_site
Proof
  Induct >> simp[fmp_ledger_ok_def] >> metis_tac[]
QED

(* Zero-sized allocations are valid; nonwrapping is still required. *)
Theorem fmp_ledger_zero_push:
  fmp_ledger_ok insts env s lo rs /\ lo < dimword (:256) /\
  fmp_dalloca_query insts env mark = SOME site /\
  ~MEM mark (MAP (\r. r.fr_mark) rs) ==>
  fmp_ledger_ok insts env (update_var mark (n2w lo) s) lo
    (<| fr_mark := mark; fr_site := site; fr_lo := lo; fr_hi := lo |> :: rs)
Proof
  strip_tac >> irule fmp_ledger_push >> simp[]
QED

Theorem fmp_region_zero_empty:
  r.fr_lo = r.fr_hi ==> ~fmp_region_contains r a
Proof simp[fmp_region_contains_def]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpLedgerProps");
