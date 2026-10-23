(* Checked static-layout allocator proof interface. *)

Theory staticLayoutAllocatorProofs
Ancestors
  concretizeMemLocDefs staticLayoutDefs list finite_map

(* Ordering is a separate interface from the canonical liveset map. *)
Theorem ml_complete_order_priority_witness:
  ml_complete_order [Allocation 2; Allocation 1; Allocation 2]
    [Allocation 1; Allocation 2; Allocation 3]
    (FEMPTY |+ (Allocation 1,[]) |+ (Allocation 2,[]) |+ (Allocation 3,[])) =
  [Allocation 2; Allocation 1; Allocation 3]
Proof
  EVAL_TAC
QED

Theorem ml_complete_order_distinct:
  !raw localkeys ls. ALL_DISTINCT (ml_complete_order raw localkeys ls)
Proof
  simp[ml_complete_order_def]
QED

Theorem ml_complete_order_mem:
  !raw localkeys ls a.
    MEM a (ml_complete_order raw localkeys ls) <=>
    MEM a localkeys /\ IS_SOME (FLOOKUP ls a)
Proof
  simp[ml_complete_order_def, MEM_FILTER] >> metis_tac[]
QED

Theorem alloc_liveset_items_ordered_lookup:
  !raw fn ls a live.
    MEM (a,live) (alloc_liveset_items_ordered raw fn ls) ==>
    FLOOKUP ls a = SOME live
Proof
  rw[alloc_liveset_items_ordered_def, MEM_MAP, ml_complete_order_mem] >>
  qmatch_asmsub_abbrev_tac `IS_SOME entry` >>
  Cases_on `entry` >> gvs[]
QED

Theorem alloc_liveset_items_ordered_coverage:
  !raw fn ls a live.
    MEM a (MAP (\inst. Allocation inst.inst_id)
      (FILTER (\inst. is_alloca_op inst.inst_opcode) (fn_insts fn))) /\
    FLOOKUP ls a = SOME live ==>
    MEM (a,live) (alloc_liveset_items_ordered raw fn ls)
Proof
  rpt strip_tac >>
  simp[alloc_liveset_items_ordered_def, MEM_MAP, ml_complete_order_mem] >>
  qpat_x_assum `MEM a (MAP _ _)` mp_tac >> simp[MEM_MAP]
QED

Definition reserved_positions_sorted_def:
  reserved_positions_sorted [] = T /\
  reserved_positions_sorted (((pos : num),size)::rs) =
    (EVERY (\((pos' : num),size'). pos <= pos') rs /\
     reserved_positions_sorted rs)
End

Theorem reserved_intervals_disjoint_sym[local]:
  !r1 r2.
    reserved_intervals_disjoint r1 r2 <=>
    reserved_intervals_disjoint r2 r1
Proof
  PairCases >> PairCases >>
  simp[reserved_intervals_disjoint_def] >> metis_tac[]
QED

Theorem MEM_insert_reserved_by_pos[local]:
  !r x rs.
    MEM x (insert_reserved_by_pos r rs) <=> x = r \/ MEM x rs
Proof
  gen_tac >> gen_tac >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def]
  >> gen_tac >> PairCases_on `h` >> PairCases_on `r` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> metis_tac[]
QED

Theorem MEM_sort_reserved_by_pos:
  !x rs.
    MEM x (sort_reserved_by_pos rs) <=> MEM x rs
Proof
  gen_tac >> Induct_on `rs` >>
  simp[sort_reserved_by_pos_def, MEM_insert_reserved_by_pos]
QED

Theorem EVERY_insert_reserved_by_pos[local]:
  !P r rs.
    EVERY P (insert_reserved_by_pos r rs) <=> P r /\ EVERY P rs
Proof
  rpt gen_tac >>
  simp[EVERY_MEM, MEM_insert_reserved_by_pos] >> metis_tac[]
QED

Theorem insert_reserved_by_pos_wf[local]:
  !r rs.
    reserved_interval_wf r /\
    EVERY (reserved_intervals_disjoint r) rs /\
    reserved_intervals_wf rs ==>
    reserved_intervals_wf (insert_reserved_by_pos r rs)
Proof
  gen_tac >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def, reserved_intervals_wf_def]
  >> gen_tac >> PairCases_on `h` >> PairCases_on `r` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> strip_tac
  >- gvs[reserved_intervals_wf_def]
  >> gvs[reserved_intervals_wf_def, EVERY_insert_reserved_by_pos,
         reserved_intervals_disjoint_sym]
QED

Theorem sort_reserved_by_pos_wf:
  !rs.
    reserved_intervals_wf rs ==>
    reserved_intervals_wf (sort_reserved_by_pos rs)
Proof
  Induct >> simp[sort_reserved_by_pos_def, reserved_intervals_wf_def] >>
  gen_tac >> strip_tac >> irule insert_reserved_by_pos_wf >>
  gvs[EVERY_MEM, MEM_sort_reserved_by_pos]
QED

Theorem insert_reserved_by_pos_sorted[local]:
  !r rs.
    reserved_positions_sorted rs ==>
    reserved_positions_sorted (insert_reserved_by_pos r rs)
Proof
  gen_tac >> PairCases_on `r` >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def, reserved_positions_sorted_def]
  >> gen_tac >> PairCases_on `h` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> strip_tac
  >- (gvs[reserved_positions_sorted_def, EVERY_MEM] >>
      gen_tac >> PairCases_on `e` >> gvs[] >> strip_tac >>
      `h0 <= e0` by
        (qpat_x_assum `!x. MEM x rs ==> _`
           (qspec_then `(e0,e1)` mp_tac) >> simp[]) >>
      decide_tac)
  >> gvs[reserved_positions_sorted_def, EVERY_MEM,
         MEM_insert_reserved_by_pos] >>
     gen_tac >> PairCases_on `e` >> gvs[] >> strip_tac >> gvs[] >>
     qpat_x_assum `!x. MEM x rs ==> _`
       (qspec_then `(e0,e1)` mp_tac) >> simp[]
QED

Theorem sort_reserved_by_pos_sorted:
  !rs. reserved_positions_sorted (sort_reserved_by_pos rs)
Proof
  Induct >> simp[sort_reserved_by_pos_def, reserved_positions_sorted_def,
                 insert_reserved_by_pos_sorted]
QED

Theorem EVERY_sort_reserved_by_pos:
  !P rs.
    EVERY P (sort_reserved_by_pos rs) <=> EVERY P rs
Proof
  simp[EVERY_MEM, MEM_sort_reserved_by_pos]
QED
Theorem intervals_after_disjoint[local]:
  !base pos sz rs.
    EVERY (\((rpos : num),rsz). base <= rpos) rs /\
    pos + sz <= base ==>
    EVERY (reserved_intervals_disjoint (pos,sz)) rs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
  qpat_x_assum `!x. MEM x rs ==> _`
    (qspec_then `(e0,e1)` mp_tac) >>
  simp[reserved_intervals_disjoint_def] >> decide_tac
QED

Theorem checked_first_fit_scan_SOME[local]:
  !rs sz start pos.
    reserved_positions_sorted rs /\
    EVERY reserved_interval_wf rs /\
    checked_first_fit_scan rs sz start = SOME pos ==>
    start <= pos /\
    pos + sz < dimword (:256) /\
    EVERY (reserved_intervals_disjoint (pos,sz)) rs
Proof
  Induct_on `rs`
  >- simp[checked_first_fit_scan_def]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  Cases_on `start + sz >= dimword (:256)`
  >- gvs[checked_first_fit_scan_def]
  >> Cases_on `h0 + h1 <= start`
  >- (gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
          checked_first_fit_scan_def] >>
      first_x_assum (qspecl_then [`sz`,`start`,`pos`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[reserved_intervals_disjoint_def] >> decide_tac)
  >> Cases_on `start + sz <= h0`
  >- (gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
          checked_first_fit_scan_def] >>
      conj_tac
      >- (simp[reserved_intervals_disjoint_def] >> decide_tac)
      >> irule intervals_after_disjoint >> qexists `h0` >> simp[])
  >> gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
         checked_first_fit_scan_def] >>
     first_x_assum (qspecl_then [`sz`,`h0 + h1`,`pos`] mp_tac) >>
     simp[] >> strip_tac >>
     simp[reserved_intervals_disjoint_def] >> decide_tac
QED

Theorem checked_first_fit_SOME:
  !occupied sz pos.
    checked_first_fit occupied sz = SOME pos ==>
    pos + sz < dimword (:256) /\
    EVERY (reserved_intervals_disjoint (pos,sz)) occupied /\
    (0 < sz ==> reserved_interval_wf (pos,sz))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_first_fit_def] >>
  `0 <= pos /\ pos + sz < dimword (:256) /\
   EVERY (reserved_intervals_disjoint (pos,sz))
     (sort_reserved_by_pos occupied)` by
    (irule checked_first_fit_scan_SOME >>
     simp[sort_reserved_by_pos_sorted, EVERY_sort_reserved_by_pos]) >>
  gvs[EVERY_sort_reserved_by_pos, reserved_intervals_wf_def,
      reserved_interval_wf_def]
QED

Theorem collect_static_allocas_MEM:
  !insts items item.
    collect_static_allocas insts = SOME items ==>
    (MEM item items <=>
     ?inst. MEM inst insts /\ exact_static_alloca inst = SOME item)
Proof
  Induct_on `insts`
  >- simp[collect_static_allocas_def]
  >> gen_tac >> rpt gen_tac >>
  Cases_on `collect_static_allocas insts` >>
  gvs[collect_static_allocas_def] >>
  Cases_on `h.inst_opcode = ALLOCA` >> gvs[]
  >- (Cases_on `exact_static_alloca h` >> gvs[] >>
      Cases_on `MEM (FST x') (MAP FST x)` >> gvs[] >>
      strip_tac >> gvs[] >> eq_tac
      >- (strip_tac >> Cases_on `item = x'`
          >- (qexists `h` >> gvs[])
          >> gvs[] >> qexists `inst` >> simp[])
      >> strip_tac >> gvs[] >> disj2_tac >>
         qexists `inst` >> simp[])
  >> `exact_static_alloca h = NONE` by
       simp[exact_static_alloca_def, exact_static_alloca_size_def] >>
     strip_tac >> gvs[] >> eq_tac >> strip_tac
  >- (qexists `inst` >> simp[])
  >> gvs[] >> qexists `inst` >> simp[]
QED

Theorem collect_static_allocas_ALL_DISTINCT:
  !insts items.
    collect_static_allocas insts = SOME items ==>
    ALL_DISTINCT (MAP FST items)
Proof
  Induct_on `insts`
  >- simp[collect_static_allocas_def]
  >> gen_tac >> gen_tac >>
  Cases_on `collect_static_allocas insts` >>
  gvs[collect_static_allocas_def] >>
  Cases_on `h.inst_opcode = ALLOCA` >> gvs[] >>
  Cases_on `exact_static_alloca h` >> gvs[] >>
  Cases_on `MEM (FST x') (MAP FST x)` >> gvs[] >>
  strip_tac >> gvs[]
QED

Theorem exact_static_alloca_opcode[local]:
  exact_static_alloca inst = SOME item ==>
  inst.inst_opcode = ALLOCA
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[exact_static_alloca_def, exact_static_alloca_size_def]
QED

Theorem collect_static_allocas_ALLOCA_exact:
  !insts items inst.
    collect_static_allocas insts = SOME items /\
    MEM inst insts /\ inst.inst_opcode = ALLOCA ==>
    ?size.
      inst.inst_operands = [Lit size] /\
      exact_static_alloca inst =
        SOME (Allocation inst.inst_id,w2n size)
Proof
  Induct
  >- simp[collect_static_allocas_def]
  >> rpt gen_tac
  >> Cases_on `collect_static_allocas insts`
  >> gvs[collect_static_allocas_def]
  >> Cases_on `h.inst_opcode = ALLOCA` >> gvs[]
  >- (Cases_on `exact_static_alloca h` >> gvs[]
      >> Cases_on `MEM (FST x') (MAP FST x)` >> gvs[]
      >> strip_tac
      >- gvs[exact_static_alloca_def, exact_static_alloca_size_def,
             AllCaseEqs()]
      >> first_x_assum irule >> simp[])
  >> strip_tac
  >- gvs[]
  >> first_x_assum irule >> simp[]
QED

Theorem static_alloca_items_ALLOCA_exact:
  static_alloca_items fn = SOME items /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
  ?size.
    inst.inst_operands = [Lit size] /\
    exact_static_alloca inst =
      SOME (Allocation inst.inst_id,w2n size)
Proof
  simp[static_alloca_items_def]
  >> metis_tac[collect_static_allocas_ALLOCA_exact]
QED

Theorem static_alloca_items_MEM:
  static_alloca_items fn = SOME items ==>
  (MEM item items <=>
   ?inst. MEM inst (fn_insts fn) /\
          inst.inst_opcode = ALLOCA /\
          exact_static_alloca inst = SOME item)
Proof
  simp[static_alloca_items_def] >> strip_tac >>
  drule collect_static_allocas_MEM >>
  disch_then (qspec_then `item` assume_tac) >>
  eq_tac >> strip_tac
  >- (gvs[] >> qexists `inst` >> simp[] >>
      irule exact_static_alloca_opcode >> simp[])
  >> gvs[] >> qexists `inst` >> simp[]
QED

Theorem static_alloca_items_ALL_DISTINCT:
  static_alloca_items fn = SOME items ==>
  ALL_DISTINCT (MAP FST items)
Proof
  simp[static_alloca_items_def] >> strip_tac >>
  drule collect_static_allocas_ALL_DISTINCT >> simp[]
QED

Theorem ALL_DISTINCT_MAP_FST_size_unique[local]:
  !items alloc sz1 sz2.
    ALL_DISTINCT (MAP FST items) /\
    MEM (alloc,sz1) items /\ MEM (alloc,sz2) items ==>
    sz1 = sz2
Proof
  Induct
  >- simp[]
  >> gen_tac >> PairCases_on `h`
  >> simp[]
  >> rpt gen_tac >> strip_tac >> gvs[MEM_MAP]
  >> first_x_assum irule
  >> qexists `alloc` >> simp[]
QED

Theorem static_alloca_items_exact_key_size_unique:
  static_alloca_items fn = SOME items /\
  MEM inst1 (fn_insts fn) /\
  exact_static_alloca inst1 = SOME (alloc,sz1) /\
  MEM inst2 (fn_insts fn) /\
  exact_static_alloca inst2 = SOME (alloc,sz2) ==>
  sz1 = sz2
Proof
  strip_tac
  >> `ALL_DISTINCT (MAP FST items)` by
       metis_tac[static_alloca_items_ALL_DISTINCT]
  >> `MEM (alloc,sz1) items` by
       (drule static_alloca_items_MEM
        >> disch_then (qspec_then `(alloc,sz1)` (fn th => rewrite_tac[th]))
        >> qexists `inst1` >> simp[]
        >> irule exact_static_alloca_opcode >> simp[])
  >> `MEM (alloc,sz2) items` by
       (drule static_alloca_items_MEM
        >> disch_then (qspec_then `(alloc,sz2)` (fn th => rewrite_tac[th]))
        >> qexists `inst2` >> simp[]
        >> irule exact_static_alloca_opcode >> simp[])
  >> metis_tac[ALL_DISTINCT_MAP_FST_size_unique]
QED

Theorem merge_forced_positions_extends:
  !items forced positions merged.
    merge_forced_positions items forced positions = SOME merged ==>
    !alloc pos.
      FLOOKUP positions alloc = SOME pos ==>
      FLOOKUP merged alloc = SOME pos
Proof
  Induct_on `items`
  >- simp[merge_forced_positions_def]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `FLOOKUP forced (allocation_id h0)` >>
  gvs[merge_forced_positions_def]
  >- metis_tac[]
  >> Cases_on `FLOOKUP positions h0` >> gvs[]
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!forced positions merged. _`
        (qspecl_then [`forced`,`positions |+ (h0,x)`,`merged`] mp_tac) >>
      simp[] >> disch_then irule >>
      Cases_on `alloc = h0` >> gvs[FLOOKUP_UPDATE])
  >> Cases_on `x' = x` >> gvs[] >> metis_tac[]
QED

Theorem merge_forced_positions_forced:
  !items forced positions merged.
    merge_forced_positions items forced positions = SOME merged ==>
    !alloc pos.
      MEM alloc (MAP FST items) /\
      FLOOKUP forced (allocation_id alloc) = SOME pos ==>
      FLOOKUP merged alloc = SOME pos
Proof
  Induct_on `items`
  >- simp[merge_forced_positions_def]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `FLOOKUP forced (allocation_id h0)` >>
  gvs[merge_forced_positions_def]
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `alloc = h0` >> gvs[] >>
      first_x_assum drule >> simp[])
  >> Cases_on `FLOOKUP positions h0` >> gvs[]
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `alloc = h0` >> gvs[]
      >- (drule merge_forced_positions_extends >>
          disch_then (qspecl_then [`alloc`,`pos`] mp_tac) >>
          simp[FLOOKUP_UPDATE])
      >> first_x_assum drule >> simp[])
  >> Cases_on `x' = x` >> gvs[] >> strip_tac >>
     rpt gen_tac >> strip_tac >> Cases_on `alloc = h0` >> gvs[]
  >- (drule merge_forced_positions_extends >> simp[])
  >> first_x_assum drule >> simp[]
QED

Theorem merge_forced_positions_forced_aid:
  merge_forced_positions items forced positions = SOME merged ==>
  !aid pos.
    FLOOKUP forced aid = SOME pos /\
    MEM (Allocation aid) (MAP FST items) ==>
    FLOOKUP merged (Allocation aid) = SOME pos
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule merge_forced_positions_forced >> simp[allocation_id_def]
QED

(* Occupied intervals may overlap when their allocations have disjoint
   lifetimes. A dead allocation filled afterwards must avoid their union. *)
Theorem checked_first_fit_overlapping_regressions:
  checked_first_fit [(0,32); (0,32)] 32 = SOME 32 /\
  checked_first_fit [(32,32); (0,96); (16,16)] 32 = SOME 96 /\
  checked_first_fit [(64,32); (0,32); (0,32)] 32 = SOME 32
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem checked_first_fit_invalid_regressions:
  checked_first_fit [(0,0)] 32 = NONE /\
  checked_first_fit [(dimword (:256) - 16,32)] 32 = NONE /\
  checked_first_fit [] (dimword (:256)) = NONE
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem complete_dead_alloca_overlapping_regression:
  complete_alloc_positions_aux
    [<| inst_id := 3; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := ["dead"] |>]
    (FEMPTY |+ (Allocation 1,0) |+ (Allocation 2,0)) [(0,32); (0,32)] =
  SOME (FEMPTY |+ (Allocation 1,0) |+ (Allocation 2,0) |+ (Allocation 3,32))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED
