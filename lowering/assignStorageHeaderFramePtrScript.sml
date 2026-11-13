(* The dynamic array writes its clean header after its data prefix. *)
Theory assignStorageHeaderFramePtr
Ancestors
  assignStorageBlockFramePtr assignBasePtrStorageLoop placeDynStorageEffect
  ptrDiscipline venomState words pred_set arithmetic

Theorem storage_key_update_commute:
  a <> b ==> key_update (key_update X a A) b B =
    key_update (key_update X b B) a A
Proof
  simp[key_update_def, EXTENSION] >> rpt strip_tac >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem assign_base_store_taint_header_commute:
  !i tn.
    (!h. h < i ==> head <> k+n2w h) ==>
    (if tr then
       (assign_base_store_taint_prefix LocTransient b k tn i) with t_trans :=
         key_update (assign_base_store_taint_prefix LocTransient b k tn i).t_trans head {}
     else
       (assign_base_store_taint_prefix LocStorage b k tn i) with t_stor :=
         key_update (assign_base_store_taint_prefix LocStorage b k tn i).t_stor head {}) =
    assign_base_store_taint_prefix (if tr then LocTransient else LocStorage) b k
      (if tr then tn with t_trans := key_update tn.t_trans head {}
       else tn with t_stor := key_update tn.t_stor head {}) i
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (Cases_on `tr` >> simp[assign_base_store_taint_prefix_def]) >>
  `head <> k+n2w i /\ (!h. h < i ==> head <> k+n2w h)` by
    (conj_tac
     >- (qpat_assum `!h. h < SUC i ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!h. h < SUC i ==> _` (qspec_then `h` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  qpat_x_assum `!tt. (!h. h < i ==> _) ==> _` (qspec_then `tn` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `tr` >>
  gvs[assign_base_store_taint_prefix_def, storage_key_update_commute,
    assign_base_store_taint_frame, taint_component_equality]
QED

Theorem assign_base_store_frame_header:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    (b+32w) (k+1w) s0 tn0 n v tv /\
  mload (w2n b) s0 = value /\ mem_word_taint tn0.t_mem (w2n b) = {} /\
  (!h. h < n ==> k <> (k+1w)+n2w h) ==>
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (SUC n)
    (((if tr then tstore else sstore) k value v) with vs_inst_idx := index)
    (if tr then tv with t_trans := key_update tv.t_trans k {}
     else tv with t_stor := key_update tv.t_stor k {})
Proof
  strip_tac >>
  `assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
      b k tn0 1 =
   (if tr then tn0 with t_trans := key_update tn0.t_trans k {}
    else tn0 with t_stor := key_update tn0.t_stor k {})` by
    (CONV_TAC (LAND_CONV (RAND_CONV numLib.num_CONV)) >>
     Cases_on `tr` >> simp[assign_base_store_taint_prefix_def,
       WORD_MULT_CLAUSES, WORD_ADD_0]) >>
  `assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
      b k tn0 (SUC n) =
   assign_base_store_taint_prefix (if tr then LocTransient else LocStorage)
      (b+32w) (k+1w)
      (if tr then tn0 with t_trans := key_update tn0.t_trans k {}
       else tn0 with t_stor := key_update tn0.t_stor k {}) n` by
    (qspecl_then [`n`,`1`,`if tr then LocTransient else LocStorage`,`b`,`k`,`tn0`]
       mp_tac assign_base_store_taint_prefix_append >>
     simp[WORD_MULT_CLAUSES, WORD_ADD_0, DECIDE ``1+n = SUC n``]) >>
  mp_tac (Q.INST [`i` |-> `n`,`tn` |-> `tn0`,`b` |-> `(b:bytes32)+32w`,
    `k` |-> `(k:bytes32)+1w`,`head` |-> `k`,`tr` |-> `tr`]
    (SPEC_ALL assign_base_store_taint_header_commute)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `((if tr then tstore else sstore) k value
     (store_copy_prefix (if tr then LocTransient else LocStorage)
       (b+32w) (k+1w) s0 n)) =
    store_copy_prefix (if tr then LocTransient else LocStorage) b k s0 (SUC n)` by
    (mp_tac (Q.INST [`j` |-> `n`,`ew` |-> `1`,
       `loc` |-> `if tr then LocTransient else LocStorage`,
       `b` |-> `b`,`k` |-> `k`,`s` |-> `s0`,`x` |-> `value`]
       (SPEC_ALL place_dyn_prefix_header_flat)) >>
     simp[place_dyn_prefix_flat, ADD1, ADD_COMM] >>
     Cases_on `tr` >> simp[]) >>
  Cases_on `tr` >>
  gvs[assign_base_store_frame_def, taint_component_equality,
    venom_state_component_equality, sstore_def, tstore_def,
    assign_base_store_prefix_frame]
QED

