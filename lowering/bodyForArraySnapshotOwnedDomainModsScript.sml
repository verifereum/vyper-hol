(* The captured buffer and the reusable item live in distinct allocations.
   The pointer certificate can stay at capture: the scalar address slice
   inherits the saved operand's provenance. *)
Theory bodyForArraySnapshotOwnedDomainMods
Ancestors
  bodyForArrayHeaderMods bodyPtrDefs ptrDiscipline exprSimProps loweringPosts
  loweringShapeDefs abiDecodeStaticProps venomMemDefs venomState
  valueEncoding words finite_map arithmetic

Theorem for_array_snapshot_owned_domain_mods:
  ptr_mem_ok cx aty (ArrayV av) base_op Gc tc capture /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV stv bd) /\
  eval_operand base_op capture = SOME bw /\
  op_prov G (Var xs) = op_prov Gc base_op /\
  lookup_var xs u = SOME (bw + n2w delta) /\
  op_taint tn (Var xs) = {} /\ not_fresh_at saCopy xs /\
  delta + type_memory_size stv <= type_memory_size (ArrayTV stv bd) /\
  type_memory_size dtv = type_memory_size stv /\
  (0 < type_memory_size (ArrayTV stv bd) ==>
    ?aid b cap0. FLOOKUP u.vs_allocas aid = SOME (b,cap0) /\
      aid < saExpr.cs_next_id /\ b <= w2n bw /\
      w2n bw + type_memory_size (ArrayTV stv bd) <= b + cap0) /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,aidItem) ee G tn u /\
  type_memory_size dtv <= cap /\ alloca_inv u /\
  u.vs_alloca_next < dimword (:256) ==>
  w2n (bw + n2w delta) = w2n bw + delta /\
  (0 < type_memory_size stv ==>
    not_fresh_at saCopy xs /\ lookup_var xs u = SOME (bw + n2w delta) /\
    ptr_covers G tn xs u (type_memory_size stv)) /\
  lookup_var xd u = SOME dw /\ FLOOKUP u.vs_allocas aidItem = SOME (w2n dw,cap) /\
  ptr_covers G tn xd u cap /\
  w2n (bw + n2w delta) + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/
     w2n (bw + n2w delta) + type_memory_size stv <= u.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= u.vs_alloca_next) /\
  (w2n (bw + n2w delta) + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n (bw + n2w delta))
Proof
  strip_tac >>
  qhdtm_x_assum `for_array_item_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  qhdtm_x_assum `alloca_inv`
    (strip_assume_tac o REWRITE_RULE [alloca_inv_def]) >>
  qabbrev_tac `extent = type_memory_size (ArrayTV stv bd)` >>
  Q.SUBGOAL_THEN
    `w2n bw + delta + type_memory_size stv < dimword (:256) /\
     (type_memory_size stv = 0 \/ w2n bw + delta + type_memory_size stv <= u.vs_alloca_next) /\
     (w2n bw + delta + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n bw + delta)`
    (map_every assume_tac o CONJUNCTS)
  >- (Cases_on `extent = 0`
     >- (`w2n bw < dimword (:256)` by simp[w2n_lt] >> decide_tac) >>
     `0 < extent` by decide_tac >>
     qpat_x_assum `0 < extent ==> _` (drule_then strip_assume_tac) >>
     `b + cap0 <= u.vs_alloca_next` by
       (qpat_assum `alloca_next_valid u` (mp_tac o REWRITE_RULE [alloca_next_valid_def]) >>
        disch_then (qspecl_then [`aid`,`b`,`cap0`] mp_tac) >> simp[]) >>
     `aid <> aidItem` by decide_tac >>
     `b + cap0 <= w2n dw \/ w2n dw + cap <= b` by
       (qpat_assum `allocas_non_overlapping u`
          (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
        disch_then (qspecl_then [`aid`,`aidItem`,`b`,`cap0`,`w2n dw`,`cap`] mp_tac) >> simp[]) >>
     decide_tac) >>
  `w2n (bw + n2w delta) = w2n bw + delta` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  `0 < type_memory_size stv ==> ptr_covers G tn xs u (type_memory_size stv)` by
    (strip_tac >>
     `extent <> 0` by decide_tac >>
     `type_memory_size (ArrayTV stv bd) <> 0` by fs[Abbr `extent`] >>
     `?p b sz. base_op = Var p /\ FLOOKUP Gc p = SOME (b,sz) /\
        b <= w2n bw /\ w2n bw + extent <= b+sz` by
       (qhdtm_x_assum `ptr_mem_ok` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
        disch_then (qspecl_then [`ArrayTV stv bd`,`bw`] mp_tac) >>
        simp[Abbr `extent`,val_footprint_def,val_store_size_def]) >>
     `FLOOKUP G xs = SOME (b,sz)` by fs[op_prov_def] >>
     simp[ptr_covers_def] >> qexistsl_tac [`b`,`sz`] >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED
