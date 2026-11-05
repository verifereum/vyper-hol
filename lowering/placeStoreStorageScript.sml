(*
 * place_store_value_run (placeStore) at a slot in storage or transient
 * storage, of a type other than a DynArray: a word by one SSTORE or
 * TSTORE; an aggregate laid out at the place's type in memory (through a
 * fresh buffer when the value's type differs and is not a bytestring),
 * then copied word by word to the slots (one MLOAD and store for at most
 * 32 bytes).
 *
 * TOP-LEVEL: place_store_value_storage_run
 *)

Theory placeStoreStorage
Ancestors
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode accountsRelProps
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState fragGasSeq fragGasPath arithmetic venomExecSemantics venomInst exprLoweringProps

Theorem place_store_literal_load[local]:
  step_inst_base (mk_inst id MLOAD [Lit sw] [tmp]) s =
  OK (update_var tmp (mload (w2n sw) s) s)
Proof
  irule emitHelperPropsTheory.step_MLOAD >> simp[eval_operand_def]
QED

Theorem place_store_updated_slot[local]:
  ~s.vs_call_ctx.cc_static ==>
  step_inst_base
    (mk_inst id (if tr then TSTORE else SSTORE) [Lit k; Var tmp] [])
    (update_var tmp w s) =
  OK ((if tr then tstore else sstore) k w (update_var tmp w s))
Proof
  strip_tac >> Cases_on `tr` >>
  simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operands_def,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* A checked single storage/transient store boundary. *)
Theorem place_store_slot_path[local]:
  !tr k w s ctx func bb id.
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id (if tr then TSTORE else SSTORE) [Lit k; Lit w] []) ==>
    gas_marked_path F ctx func s 0
      (OK (((if tr then tstore else sstore) k w s)
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!x. lookup_var x ((if tr then tstore else sstore) k w s) = lookup_var x s)
Proof
  rpt strip_tac
  >- (`gas_path_edge ctx func s 0
         (OK (((if tr then tstore else sstore) k w s)
           with vs_inst_idx := SUC s.vs_inst_idx))` by
        (`step_inst_base
            (mk_inst id (if tr then TSTORE else SSTORE) [Lit k; Lit w] []) s =
          OK ((if tr then tstore else sstore) k w s)` by
           (Cases_on `tr` >>
            simp[step_inst_base_def, mk_inst_def, exec_write2_def,
                 eval_operands_def, eval_operand_def]) >>
         drule_at (Pat `get_instruction _ _ = _`) tuple_straight_line_edge >>
         simp[mk_inst_def, is_terminator_def] >>
         disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
         Cases_on `tr` >> simp[is_terminator_def]) >>
      simp[gas_marked_path_def] >>
      metis_tac[gas_path_rules, gas_path_edge_normal, ADD_0])
  >> Cases_on `tr` >> simp[tstore_def, sstore_def, lookup_var_def]
QED

Theorem place_store_load_slot_path[local]:
  !tr sw k s ctx func bb id tmp.
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst id MLOAD [Lit sw] [tmp];
       mk_inst (id+1) (if tr then TSTORE else SSTORE) [Lit k; Var tmp] []]
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    gas_marked_path F ctx func s 0
      (OK (((if tr then tstore else sstore) k (mload (w2n sw) s)
        (update_var tmp (mload (w2n sw) s) s))
        with vs_inst_idx := s.vs_inst_idx + 2)) /\
    (!x. x <> tmp ==>
      lookup_var x ((if tr then tstore else sstore) k (mload (w2n sw) s)
        (update_var tmp (mload (w2n sw) s) s)) = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
      `run_inst_seq code s = OK
         ((if tr then tstore else sstore) k (mload (w2n sw) s)
           (update_var tmp (mload (w2n sw) s) s))` by
        simp[Abbr `code`, run_inst_seq_def, place_store_literal_load,
             place_store_updated_slot] >>
      drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
      simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      Cases_on `tr` >> gvs[gas_marked_path_def, mk_inst_def, is_terminator_def]) >>
  Cases_on `tr` >>
  simp[tstore_def, sstore_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Boundary probe: the second child has three slots (length and two
   capacity words). A source Bytes[1] copies two slots; slot 5 is untouched
   and dead when the new length at slot 3 is one. Slot 4 byte 0 is live. *)
Theorem place_store_bytes_child_probe[local]:
  !st. lookup_storage 3w st = 1w ==>
    dead_bytes st 0 (ArrayTV (BaseTV (BytesT (Dynamic 64))) (Fixed 2)) 5 0 /\
    dead_bytes st 3 (BaseTV (BytesT (Dynamic 64))) 5 0 /\
    ~dead_bytes st 0 (ArrayTV (BaseTV (BytesT (Dynamic 64))) (Fixed 2)) 4 0 /\
    ~dead_bytes st 3 (BaseTV (BytesT (Dynamic 64))) 4 0 /\
    ~dead_bytes st 3 (BaseTV (BytesT (Dynamic 64))) 2 0
Proof
  gen_tac >> strip_tac >>
  `!i:num. i < 2 <=> i = 0 \/ i = 1` by decide_tac >>
  simp[dead_bytes_def, dyn_bytes_dead_def, type_slot_size_def,
       vfmConstantsTheory.word_size_def, wordsTheory.w2n_n2w] >>
  conj_tac
  >- (qexists_tac `1` >> simp[]) >>
  gen_tac >> Cases_on `i = 0` >- simp[] >>
  Cases_on `i = 1` >> simp[]
QED

Theorem place_store_dead_tuple_component:
  !types i elem st base j b.
    oEL i types = SOME elem /\
    dead_bytes st (base + tuple_prefix_slot_size i types) elem j b ==>
    dead_bytes st base (TupleTV types) j b
Proof
  Induct >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> disj2_tac >>
  gvs[dead_bytes_def] >> first_x_assum irule >>
  qexistsl_tac [`elem`, `n`] >> asm_rewrite_tac[GSYM ADD_ASSOC]
QED

Theorem place_store_dead_struct_component:
  !fields id delta elem st base j b.
    struct_field_slot fields id = SOME (delta,elem) /\
    dead_bytes st (base + delta) elem j b ==>
    dead_bytes st base (StructTV fields) j b
Proof
  Induct >> simp[struct_field_slot_def, dead_bytes_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac >>
  gvs[AllCaseEqs(), dead_bytes_def] >>
  PairCases_on `z` >> gvs[] >>
  disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  `base' + type_slot_size r + z0 = base' + (z0 + type_slot_size r)` by
    decide_tac >> asm_rewrite_tac[]
QED

Theorem place_store_dead_subregion:
  !root path delta leaf.
    storage_subregion root path delta leaf ==>
    !base st j b. dead_bytes st (base + delta) leaf j b ==>
      dead_bytes st base root j b
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  rpt strip_tac >> gvs[]
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume place_store_dead_subregion[fixed]:
  simp[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  first_x_assum drule >> disch_then irule >>
  `base' + Num i * type_slot_size root + rest =
   base' + (rest + Num i * type_slot_size root)` by decide_tac >>
  asm_rewrite_tac[]
QED

Resume place_store_dead_subregion[dynamic]:
  `dead_bytes st (base' + 1 + Num i * type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     `base' + 1 + Num i * type_slot_size root + rest =
      base' + (rest + (Num i * type_slot_size root + 1))` by decide_tac >>
     asm_rewrite_tac[]) >>
  simp[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  IF_CASES_TAC
  >- (`base' + (Num i * type_slot_size root + 1) =
       base' + 1 + Num i * type_slot_size root` by decide_tac >>
      asm_rewrite_tac[]) >>
  drule (cj 1 dead_bytes_range) >> strip_tac >> simp[] >> decide_tac
QED

Resume place_store_dead_subregion[struct]:
  irule place_store_dead_struct_component >>
  goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
  first_x_assum drule >> disch_then irule >>
  asm_rewrite_tac[GSYM ADD_ASSOC]
QED

Resume place_store_dead_subregion[tuple]:
  irule place_store_dead_tuple_component >>
  goal_assum (drule_at Any) >>
  first_x_assum drule >> disch_then irule >>
  `base' + tuple_prefix_slot_size (Num i) types + rest =
   base' + (rest + tuple_prefix_slot_size (Num i) types)` by decide_tac >>
  asm_rewrite_tac[]
QED

Finalise place_store_dead_subregion

Theorem place_store_dead_tuple_frame:
  !types i elem base lo len st st'.
    oEL i types = SOME elem /\
    base + tuple_prefix_slot_size i types <= lo /\
    lo + len <= base + tuple_prefix_slot_size i types + type_slot_size elem /\
    base + type_slot_size (TupleTV types) <= dimword (:256) /\
    (!q. ~(lo <= w2n q /\ w2n q < lo + len) ==>
         lookup_storage q st' = lookup_storage q st) /\
    (!j b. ~(lo <= j /\ j < lo + len) /\
       dead_bytes st (base + tuple_prefix_slot_size i types) elem j b ==>
       dead_bytes st' (base + tuple_prefix_slot_size i types) elem j b) ==>
    !j b. ~(lo <= j /\ j < lo + len) /\
      dead_bytes st base (TupleTV types) j b ==>
      dead_bytes st' base (TupleTV types) j b
Proof
  Induct >- simp[listTheory.oEL_def] >>
  gen_tac >> Cases_on `i`
  >- (simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
           type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >>
      `dead_bytes_list st' (base' + type_slot_size h) types j b =
       dead_bytes_list st (base' + type_slot_size h) types j b` by
        (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
       type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> gvs[] >>
  (Cases_on `dead_bytes st base' h j b`
  >- (disj1_tac >>
      `dead_bytes st' base' h j b = dead_bytes st base' h j b` by
        (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  gvs[] >> disj2_tac >>
  first_x_assum (drule_at (Pat `oEL _ _ = _`)) >>
  disch_then (qspec_then `base' + type_slot_size h` mp_tac) >>
  simp[GSYM ADD_ASSOC, type_slot_size_def, dead_bytes_def] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  qexistsl_tac [`len`, `lo`] >> simp[] >> metis_tac[])
QED

Theorem place_store_dead_struct_frame:
  !fields id off elem base lo len st st'.
    struct_field_slot fields id = SOME (off,elem) /\
    base + off <= lo /\ lo + len <= base + off + type_slot_size elem /\
    base + type_slot_size (StructTV fields) <= dimword (:256) /\
    (!q. ~(lo <= w2n q /\ w2n q < lo + len) ==>
         lookup_storage q st' = lookup_storage q st) /\
    (!j b. ~(lo <= j /\ j < lo + len) /\
       dead_bytes st (base + off) elem j b ==>
       dead_bytes st' (base + off) elem j b) ==>
    !j b. ~(lo <= j /\ j < lo + len) /\
      dead_bytes st base (StructTV fields) j b ==>
      dead_bytes st' base (StructTV fields) j b
Proof
  Induct >- simp[struct_field_slot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h0 = id`
  >- (simp[struct_field_slot_def, type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >>
      `dead_bytes_fields st' (base' + type_slot_size elem) fields j b =
       dead_bytes_fields st (base' + type_slot_size elem) fields j b` by
        (irule (cj 3 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  simp[struct_field_slot_def, type_slot_size_def, dead_bytes_def,
       AllCaseEqs()] >>
  rpt strip_tac >> PairCases_on `z` >> gvs[] >>
  (Cases_on `dead_bytes st base' h1 j b`
   >- (disj1_tac >>
       `dead_bytes st' base' h1 j b = dead_bytes st base' h1 j b` by
         (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
          first_x_assum irule >>
          `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
          simp[wordsTheory.w2n_n2w] >> decide_tac) >>
       asm_rewrite_tac[]) >>
   gvs[] >> disj2_tac >>
   first_x_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
   disch_then (qspec_then `base' + type_slot_size h1` mp_tac) >>
   simp[GSYM ADD_ASSOC, type_slot_size_def, dead_bytes_def] >>
   disch_then irule >> goal_assum (drule_at Any) >>
   qexistsl_tac [`len`, `lo`] >> simp[] >> metis_tac[])
QED

Theorem place_store_dead_subregion_frame:
  !root path delta leaf.
    storage_subregion root path delta leaf ==>
    !base st st' j b.
    0 < type_slot_size leaf /\
    (!q. ~(base+delta <= w2n q /\
           w2n q < base+delta+type_slot_size leaf) ==>
         lookup_storage q st' = lookup_storage q st) /\
    ~(base+delta <= j /\ j < base+delta+type_slot_size leaf) /\
    base + type_slot_size root <= dimword (:256) /\
    dead_bytes st base root j b ==>
    dead_bytes st' base root j b
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp_tac (srw_ss())
    [Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  strip_tac >> rpt (first_x_assum SUBST_ALL_TAC) >>
  rpt gen_tac >> disch_tac >>
  all_tac
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume place_store_dead_subregion_frame[struct]:
  qpat_x_assum `?delta' elem rest. _` strip_assume_tac >>
  qpat_x_assum `delta = _` SUBST_ALL_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD_ASSOC]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_struct_frame >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
   goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
   qexistsl_tac [`type_slot_size leaf`, `base' + delta' + rest`] >>
   simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       disch_then irule >>
       drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >>
       strip_tac >> simp[GSYM ADD_ASSOC] >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
   decide_tac)
QED
Resume place_store_dead_subregion_frame[tuple]:
  qpat_x_assum `_ /\ ?elem rest. _` strip_assume_tac >>
  qpat_x_assum `delta = _` SUBST_ALL_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD_ASSOC]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_tuple_frame >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   goal_assum (drule_at (Pat `oEL _ _ = _`)) >>
   goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
   qexistsl_tac [`type_slot_size leaf`,
     `base' + tuple_prefix_slot_size (Num i) types + rest`] >>
   simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
   conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       disch_then irule >>
       drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >>
       strip_tac >> simp[GSYM ADD_ASSOC] >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
   decide_tac)
QED
Resume place_store_dead_subregion_frame[fixed]:
  gvs[] >> rpt strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  gvs[dead_bytes_def, type_slot_size_def] >>
  rename1 `dead_bytes st (base' + k * type_slot_size root) root j b` >>
  (qexists_tac `k` >> simp[] >>
  `k * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `k = Num i`
  >- (qpat_x_assum `k = Num i` SUBST_ALL_TAC >>
      first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
      disch_then irule >> simp[GSYM ADD_ASSOC] >>
      qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  `dead_bytes st' (base' + k * type_slot_size root) root j b =
   dead_bytes st (base' + k * type_slot_size root) root j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     rename1 `base' + k * type_slot_size root <= idx` >>
     `idx < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w] >>
     Cases_on `k < Num i`
     >- (`k * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         decide_tac) >>
     `Num i * type_slot_size root + type_slot_size root <= k * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> decide_tac) >>
     decide_tac) >>
  asm_rewrite_tac[])
QED
Resume place_store_dead_subregion_frame[dynamic]:
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!delta. storage_subregion _ _ _ _ ==> _` (mk_asm "ih") >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `lookup_storage (n2w base') st' = lookup_storage (n2w base') st` by
    (first_x_assum irule >>
     `base' < dimword (:256)` by
       (gvs[type_slot_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `base' + type_slot_size (ArrayTV _ _) <= _` mp_tac >>
  simp_tac (srw_ss()) [type_slot_size_def] >> disch_tac >>
  qpat_x_assum `dead_bytes st base' (ArrayTV _ _) j b` mp_tac >>
  simp_tac (srw_ss()) [Once dead_bytes_def] >> strip_tac >>
  pure_once_rewrite_tac [dead_bytes_def] >>
  rename1 `k < n` >>
  (qexists_tac `k` >> simp[] >>
   Cases_on `k < w2n (lookup_storage (n2w base') st)`
   >- (gvs[] >>
       `k * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
         (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
       Cases_on `k = Num i`
       >- (gvs[] >>
           asm_x "ih" (drule_at (Pat `storage_subregion _ _ _ _`)) >>
           disch_then irule >> simp[GSYM ADD_ASSOC] >>
           qexists_tac `st` >> asm_rewrite_tac[]) >>
       `dead_bytes st' (base' + (k * type_slot_size root + 1)) root j b =
        dead_bytes st (base' + (k * type_slot_size root + 1)) root j b` by
         (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
          first_x_assum irule >>
          rename1 `base' + (k * type_slot_size root + 1) <= idx` >>
          `idx < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
          simp[wordsTheory.w2n_n2w] >>
          Cases_on `k < Num i`
          >- (`k * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          `Num i * type_slot_size root + type_slot_size root <= k * type_slot_size root` by
            (irule vyperLookupStorageTheory.array_index_element_end_bound >> decide_tac) >>
          decide_tac) >>
       asm_rewrite_tac[]) >>
   gvs[])
QED
Finalise place_store_dead_subregion_frame

Theorem place_store_storage_dead_subregion_frame:
  !cx tr mid name subs rootk root path delta leaf st st' j b.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta leaf /\
    0 < type_slot_size leaf /\
    (!q. ~(w2n rootk + delta <= w2n q /\
           w2n q < w2n rootk + delta + type_slot_size leaf) ==>
         lookup_storage q st' = lookup_storage q st) /\
    ~(w2n rootk + delta <= j /\
      j < w2n rootk + delta + type_slot_size leaf) /\
    storage_dead cx tr st j b ==>
    storage_dead cx tr st' j b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [storage_dead_def] >> strip_tac >>
  `dead_bytes st' (w2n slot) tv j b` suffices_by
    (rpt strip_tac >> simp_tac (srw_ss()) [storage_dead_def] >>
     goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  Cases_on `(slot,tv) = (rootk,root)`
  >- (gvs[] >>
      (irule place_store_dead_subregion_frame >>
       conj_tac >- (fs[wordsTheory.dimword_def] >> decide_tac) >>
       goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[])) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv)
       (w2n rootk) (type_slot_size root)` by
    (first_x_assum irule >> conj_tac
     >- (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `dead_bytes st' (w2n slot) tv j b = dead_bytes st (w2n slot) tv j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w] >>
     gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem place_store_subregion_agree:
  !cx tr mid name subs rootk root path delta leaf k st1 st2 st1' st2'.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta leaf /\
    w2n k = w2n rootk + delta /\ 0 < type_slot_size leaf /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    (!q. ~(w2n k <= w2n q /\ w2n q < w2n k + type_slot_size leaf) ==>
       lookup_storage q st1' = lookup_storage q st1 /\
       lookup_storage q st2' = lookup_storage q st2) /\
    (!i b. i < type_slot_size leaf /\ b < 32 /\
       ~dead_bytes st1' (w2n k) leaf (w2n k+i) b ==>
       EL b (word_to_bytes (lookup_storage (k+n2w i) st1') T) =
       EL b (word_to_bytes (lookup_storage (k+n2w i) st2') T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr st1') st1' st2'
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr st1' (w2n q) b` >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k + type_slot_size leaf`
  >- suspend "inside"
  >> suspend "outside"
QED
Resume place_store_subregion_agree[inside]:
  qpat_x_assum `w2n rootk + type_slot_size root <= _`
    (assume_tac o SRULE [wordsTheory.dimword_def, ADD_COMM]) >>
  `~dead_bytes st1' (w2n k) leaf (w2n q) b` by
    (strip_tac >>
     `dead_bytes st1' (w2n rootk) root (w2n q) b` by
       (drule place_store_dead_subregion >>
        disch_then (qspec_then `w2n rootk` mp_tac) >>
        asm_rewrite_tac[] >> metis_tac[]) >>
     qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [storage_dead_def] >>
     qexistsl_tac [`mid`, `name`, `subs`, `rootk`, `root`] >>
     simp[wordsTheory.dimword_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[]) >>
  `k + n2w (w2n q - w2n k) = q` by
    (qpat_x_assum `w2n k = _` kall_tac >>
     `w2n q - w2n k < dimword (:256)` by
       (qspec_then `q` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
     `w2n k + (w2n q - w2n k) = w2n q` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  first_x_assum (qspecl_then [`w2n q - w2n k`, `b`] mp_tac) >>
  simp[] >> gvs[ADD_COMM]
QED
Resume place_store_subregion_agree[outside]:
  `~storage_dead cx tr st1 (w2n q) b` by
    (strip_tac >>
     `storage_dead cx tr st1' (w2n q) b` suffices_by metis_tac[] >>
     irule place_store_storage_dead_subregion_frame >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     qexists_tac `st1` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp_tac (srw_ss()) [storage_agree_def] >>
  disch_then (qspecl_then [`q`, `b`] mp_tac) >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED
Finalise place_store_subregion_agree

Theorem place_store_updates_lookup:
  !xs a st.
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) =
    case FILTER (\kv. FST kv = a) (REVERSE xs) of
      [] => lookup_storage a st
    | kv::rest => SND kv
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[listTheory.FILTER_APPEND_DISTRIB] >>
  Cases_on `FILTER (\kv. FST kv = a) (REVERSE xs)` >>
  simp[] >> Cases_on `h` >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `q = a` >> simp[]
QED

Theorem place_store_updates_miss:
  !xs a st.
    ~MEM a (MAP FST xs) ==>
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) =
    lookup_storage a st
Proof
  rpt strip_tac >> rewrite_tac[place_store_updates_lookup] >>
  `FILTER (\kv. FST kv = a) (REVERSE xs) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
          listTheory.MEM_REVERSE] >>
     gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

Theorem place_store_updates_hit:
  !xs a w st.
    MEM (a,w) xs /\
    (!kv. MEM kv xs /\ FST kv = a ==> SND kv = w) ==>
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) = w
Proof
  rpt strip_tac >> rewrite_tac[place_store_updates_lookup] >>
  Cases_on `FILTER (\kv. FST kv = a) (REVERSE xs)`
  >- (gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
          listTheory.MEM_REVERSE] >>
      first_x_assum (qspec_then `(a,w)` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum irule >>
  `MEM h (FILTER (\kv. FST kv = a) (REVERSE xs))` by simp[] >>
  gvs[listTheory.MEM_FILTER, listTheory.MEM_REVERSE]
QED

Theorem place_store_apply_writes_fold:
  !writes k st.
    apply_writes k writes st =
    FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st
      (MAP (\(off,v). (k + n2w off,v)) writes)
Proof
  Induct >> simp[vyperStorageTheory.apply_writes_def] >>
  Cases_on `h` >> simp[vyperStorageTheory.apply_writes_def,
    GSYM wordsTheory.word_add_n2w, ADD_COMM]
QED

Theorem place_store_bytes_live_bound:
  !l src_cap dst_cap st base i b.
    l <= src_cap /\ src_cap <= dst_cap /\
    w2n (lookup_storage (n2w base) st) = l /\
    i < 1 + word_size dst_cap /\ b < 32 /\
    ~dyn_bytes_dead st base dst_cap (base+i) b ==>
    i < 1 + word_size src_cap
Proof
  rpt gen_tac >> strip_tac >> Cases_on `i = 0` >- simp[] >>
  gvs[dyn_bytes_dead_def, vfmConstantsTheory.word_size_def] >>
  spose_not_then assume_tac >>
  `(src_cap + 31) DIV 32 < i` by decide_tac >>
  gvs[arithmeticTheory.DIV_LT_X] >> decide_tac
QED

Theorem place_store_bytes_memory_capacity:
  !src dst bs a mem.
    val_in_memory (BaseTV (BytesT (Dynamic src))) (BytesV bs) a mem =
    val_in_memory (BaseTV (BytesT (Dynamic dst))) (BytesV bs) a mem
Proof
  simp[valueEncodingTheory.val_in_memory_def]
QED

Theorem place_store_string_memory_capacity:
  !src dst s a mem.
    val_in_memory (BaseTV (StringT src)) (StringV s) a mem =
    val_in_memory (BaseTV (StringT dst)) (StringV s) a mem
Proof
  simp[valueEncodingTheory.val_in_memory_def]
QED

Theorem place_store_apply_writes_header:
  !writes k st w.
    MEM (0,w) writes /\
    (!off v. MEM (off,v) writes ==> off < dimword (:256) /\
      (off = 0 ==> v = w)) ==>
    lookup_storage k (apply_writes k writes st) = w
Proof
  rpt strip_tac >> rewrite_tac[place_store_apply_writes_fold] >>
  irule place_store_updates_hit >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  reverse conj_tac >- (qexists_tac `0` >> simp[wordsTheory.WORD_ADD_0]) >>
  Cases >> simp[] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `n2w p_1 = (0w:bytes32)` by
    (metis_tac[wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.WORD_ADD_0]) >>
  gvs[wordsTheory.n2w_11]
QED

Theorem place_store_dyn_bytes_header:
  !cap bs writes k st.
    encode_dyn_bytes_slots cap bs = SOME writes /\
    w2n k + 1 + word_size cap <= dimword (:256) ==>
    lookup_storage k (apply_writes k writes st) = n2w (LENGTH bs)
Proof
  rpt gen_tac >> strip_tac >>
  `value_has_type (BaseTV (BytesT (Dynamic cap))) (BytesV bs)` by
    (gvs[vyperStorageTheory.encode_dyn_bytes_slots_def,
         vyperTypingTheory.value_has_type_def, AllCaseEqs()]) >>
  `encode_value (BaseTV (BytesT (Dynamic cap))) (BytesV bs) = SOME writes` by
    simp[vyperStorageTheory.encode_value_def] >>
  irule place_store_apply_writes_header >> reverse conj_tac
  >- (gvs[vyperStorageTheory.encode_dyn_bytes_slots_def, AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`MEM off (MAP FST writes)` by
        (simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      drule_all (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
      simp[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  strip_tac >> gvs[vyperStorageTheory.encode_dyn_bytes_slots_def,
    AllCaseEqs(), indexedListsTheory.MEM_MAPi] >> gvs[]
QED

(* Both dynamic bytes and strings use encode_dyn_bytes_slots; keeping
   the coverage boundary here avoids duplicating the identical arithmetic. *)
Theorem place_store_dyn_bytes_live_bound:
  !src_cap dst_cap bs writes k st i b.
    LENGTH bs <= src_cap /\ src_cap <= dst_cap /\
    encode_dyn_bytes_slots dst_cap bs = SOME writes /\
    w2n k + 1 + word_size dst_cap <= dimword (:256) /\
    i < 1 + word_size dst_cap /\ b < 32 /\
    ~dyn_bytes_dead (apply_writes k writes st) (w2n k) dst_cap (w2n k+i) b ==>
    i < 1 + word_size src_cap
Proof
  rpt strip_tac >>
  drule_all place_store_dyn_bytes_header >> strip_tac >>
  irule place_store_bytes_live_bound >>
  goal_assum (drule_at (Pat `~dyn_bytes_dead _ _ _ _ _`)) >>
  qexists_tac `w2n (n2w (LENGTH bs) : bytes32)` >>
  simp[wordsTheory.w2n_n2w] >>
  `LENGTH bs MOD dimword (:256) <= LENGTH bs` by
    simp[arithmeticTheory.MOD_LESS_EQ] >> decide_tac
QED

Theorem place_store_bytestring_live_copy:
  !tv v off mem k writes st src_cap dst_cap i b.
    (tv = BaseTV (BytesT (Dynamic dst_cap)) \/ tv = BaseTV (StringT dst_cap)) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    (case v of BytesV bs => LENGTH bs <= src_cap
             | StringV s => LENGTH s <= src_cap | _ => F) /\
    src_cap <= dst_cap /\ encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+i) b ==>
    i < 1 + word_size src_cap /\
    EL b (word_to_bytes
      (lookup_storage (n2w (w2n k+i)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mem_word_at (off+32*i) mem) T)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (qpat_x_assum `tv = _ \/ tv = _` strip_assume_tac >> gvs[] >>
      Cases_on `v` >>
      gvs[vyperTypingTheory.value_has_type_def,
          vyperStorageTheory.encode_value_def, dead_bytes_def,
          vyperValueTheory.type_slot_size_def] >>
      gvs[wordsTheory.dimword_def, AC ADD_ASSOC ADD_COMM] >>
      irule (SRULE [wordsTheory.dimword_def, AC ADD_ASSOC ADD_COMM]
        place_store_dyn_bytes_live_bound) >>
      goal_assum (drule_at (Pat `encode_dyn_bytes_slots _ _ = _`)) >>
      goal_assum (drule_at (Pat `~dyn_bytes_dead _ _ _ _ _`)) >> simp[]) >>
  drule_all storageCopyLiveTheory.encode_value_memory_live >> simp[]
QED

Theorem place_store_encoded_copy_agree:
  !cx tr mid name subs rootk root path delta tv base writes v n read_word st1 st2.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta tv /\
    base = w2n rootk + delta /\ 0 < type_slot_size tv /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    n <= type_slot_size tv /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
       ~dead_bytes (apply_writes (n2w base) writes st1) base tv (base+i) b ==>
       i < n /\
       EL b (word_to_bytes (lookup_storage (n2w (base+i))
         (apply_writes (n2w base) writes st1)) T) =
       EL b (word_to_bytes (read_word i) T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes (n2w base) writes st1))
      (apply_writes (n2w base) writes st1)
      (FOLDL (\st i. update_storage (n2w (base+i)) (read_word i) st)
        st2 (COUNT_LIST n))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `apply_writes (n2w start) writes st1` >>
  `start < dimword (:256)` by decide_tac >>
  irule place_store_subregion_agree >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexists_tac `(n2w start):bytes32` >>
  goal_assum (drule_at (Pat `storage_agree _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  `w2n ((n2w start):bytes32) = start` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `start = _` (mk_asm "origin") >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.word_add_n2w] >>
  conj_tac >- suspend "frame" >> suspend "live"
QED
Resume place_store_encoded_copy_agree[frame]:
  gen_tac >> disch_tac >> conj_tac
  >- (rewrite_tac[place_store_apply_writes_fold] >>
      irule place_store_updates_miss >>
      simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
           pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      rename1 `MEM (off,word) writes` >>
      `off < type_slot_size tv` by
        (irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
         goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
         simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      `start + off < dimword (:256)` by decide_tac >>
      gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  rename1 `FOLDL (\st i. update_storage (n2w start + n2w i) (rd i) st) st2 (COUNT_LIST n)` >>
  `~MEM q (MAP FST (MAP (\i. ((n2w start + n2w i):bytes32,rd i))
       (COUNT_LIST n)))` by
    (simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
          rich_listTheory.MEM_COUNT_LIST] >>
     rpt strip_tac >>
     `start + i < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  drule place_store_updates_miss >>
  disch_then (qspec_then `st2` mp_tac) >> simp[rich_listTheory.FOLDL_MAP]
QED
Resume place_store_encoded_copy_agree[live]:
  reverse conj_tac >- (asm "origin" mp_tac >> simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st) st2 (COUNT_LIST n)` >>
  `i < n /\
   EL b (word_to_bytes (lookup_storage (n2w (start+i))
     (apply_writes (n2w start) writes st1)) T) =
   EL b (word_to_bytes (rd i) T)` by
    (first_x_assum irule >> simp[ADD_COMM]) >>
  `lookup_storage (n2w start + n2w i)
     (FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st)
       st2 (COUNT_LIST n)) = rd i` suffices_by
    gvs[GSYM wordsTheory.word_add_n2w] >>
  `MEM ((n2w start + n2w i):bytes32,rd i)
     (MAP (\j. (n2w start + n2w j,rd j)) (COUNT_LIST n))` by
    (simp[listTheory.MEM_MAP, rich_listTheory.MEM_COUNT_LIST] >>
     qexists_tac `i` >> simp[]) >>
  drule place_store_updates_hit >>
  disch_then (qspec_then `st2` mp_tac) >>
  simp[rich_listTheory.FOLDL_MAP, listTheory.MEM_MAP,
       rich_listTheory.MEM_COUNT_LIST] >>
  impl_tac >- (rpt strip_tac >> gvs[] >>
    `i < dimword (:256)` by decide_tac >>
    `j < dimword (:256)` by decide_tac >>
    gvs[wordsTheory.n2w_11]) >> simp[]
QED
Finalise place_store_encoded_copy_agree

Theorem place_store_alloc_buffer_path:
  !func cenv cx es sa sm buf sz s ctx.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    fn_has_code sa sm func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      (FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
       (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
        w2n w = s.vs_alloca_next))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `emitted_insts sa sm = [inst] /\
   sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++ [inst]` by
    suspend "layout" >>
  `step_inst_base inst s = OK u /\
   ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    suspend "execution" >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    suspend "path" >>
  `FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
   (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
    w2n w = s.vs_alloca_next)` suffices_by
    (disch_tac >>
     qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `w`] >>
     suspend "transport") >>
  suspend "address"
QED
Resume place_store_alloc_buffer_path[layout]:
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[Abbr `inst`] >>
  gvs[emitHelperTheory.emit_op_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
Resume place_store_alloc_buffer_path[execution]:
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def] >> Cases_on `step_inst_base inst s` >> simp[]) >>
  simp[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
       exec_alloca_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (strip_tac >> gvs[update_var_def]) >>
  PairCases_on `x` >> strip_tac >> gvs[update_var_def]
QED
Resume place_store_alloc_buffer_path[path]:
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `get_instruction _ _ = _`) tuple_straight_line_edge >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  simp[gas_marked_path_def] >>
  metis_tac[gas_path_rules, gas_path_edge_normal, ADD_0]
QED
Resume place_store_alloc_buffer_path[address]:
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
           exec_alloca_def, eval_operand_def] >> strip_tac >>
      gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  disj1_tac >>
  qpat_x_assum `!aid entry. _` drule >>
  gvs[]
QED
Resume place_store_alloc_buffer_path[transport]:
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       eval_operand_def, lookup_var_def, local_region_def] >>
  metis_tac[eval_operand_def, lookup_var_def, local_region_def]
QED
Finalise place_store_alloc_buffer_path

Theorem place_store_alloc_source_disjoint:
  !s sa w sz src len.
    (FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
     (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
      w2n w = s.vs_alloca_next)) /\
    src + len <= s.vs_alloca_next /\
    (!aid b size. FLOOKUP s.vs_allocas aid = SOME (b,size) /\
       sa.cs_next_id <= aid ==> src + len <= b \/ b + size <= src) ==>
    regions_disjoint src len (w2n w) sz
Proof
  rpt gen_tac >> strip_tac >>
  simp[regions_disjoint_def] >> metis_tac[LESS_EQ_REFL, ADD_COMM]
QED

(* C1.1.n DESIGN ONLY: counted recursive interface (not an assertion).
   Proposed entry predicate E cenv ctx dty sty dtv stv v is the following
   universally quantified contract. For ALL dst src sa sb func s dw sw,
     compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
     (!x. dst = Var x ==> not_fresh_at sa x) /\
     (!x. src = Var x ==> not_fresh_at sa x) /\
     eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
     val_in_memory stv v (w2n sw) s.vs_memory /\
     w2n sw + type_memory_size stv < dimword (:256) /\
     w2n dw + type_memory_size dtv < dimword (:256) /\
     regions_disjoint (w2n sw) (type_memory_size stv)
                      (w2n dw) (type_memory_size dtv) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
     s.vs_inst_idx = LENGTH sa.cs_current_insts
   implies EXISTS t,
     gas_marked_path F ctx func s 0 (OK t) /\
     val_in_memory dtv v (w2n dw) t.vs_memory /\
     typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts.
   The rank theorem should have EXACTLY the hypotheses of typed_copy_rank_entry
   and conclusion E instead of typed_copy_entry. No continuation-to-path
   implication is assumed. The checked word boundary below is stronger than
   this entry's word instance (no source freshness, bounds or disjointness).

   Array consumer, slow path: set N = LENGTH values, hs = hd = 0 for fixed
   arrays and hs = hd = 32 for dynamic arrays. ss,ds are evaluated element
   memory sizes, equal to compiler element sizes. At the cond block entry
   (index 0), invariant I(i,q), relative to original s, is:
     i <= N /\ lookup_var counter q = SOME (n2w i) /\ ~q.vs_halted /\
     q.vs_current_bb = cond_lbl /\ q.vs_inst_idx = 0 /\
     gas_marked_path F ctx func s 0 (OK q) /\
     val_in_memory stv v (w2n sw) q.vs_memory /\
     (!j. j < i ==> val_in_memory detv (EL j values)
          (w2n dw + hd + j*ds) q.vs_memory) /\
     typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s q.
   Also retain base/length operands at their original values and all loop
   temporaries allocated before the child compiler state; these variables
   are not_fresh_at child_sa, NOT necessarily not_fresh_at outer sa.
   Fixed typing gives N=count. Dynamic typing gives N<=source_cap<=dest_cap
   and N<dimword; MLOAD/GT/ISZERO/ASSERT must be executed and MSTORE establishes
   the destination length header, retained by each child frame. Zero length
   exits without a child call. Child addresses are sw+hs+i*ss, dw+hd+i*ds;
   full-region bounds prove no word wrap, and disjoint full regions imply
   disjoint child regions. Rank(element)<rank(array) supplies E for EL i.
   At child entry use its actual compiler block/index, not the body label:
   the address prefix has already advanced the index. Child E returns its
   own exit block/index, which may differ after nested loops. Execute the
   increment/ASSIGN/JMP suffix from THAT exit, re-enter cond_lbl at index 0.
   Compose prefix, child and suffix zero-count paths using path transitivity;
   finite induction on N-i justifies repetition, not an unbounded back-edge
   rule. At i=N execute LT/ISZERO/JNZ to exit_lbl, index 0, then match sb.
   Frame composition and child disjointness preserve earlier elements and
   source memory; reassemble val_in_memory only at exit. Fast fixed copy
   and dynamic copy need separate actual counted MCOPY/loop boundaries;
   the above invariant does not certify those dispatch branches.

   Sequential fields consumer: zip destination/source types, evaluated types
   and values (structs select source type by ALOOKUP name as in the compiler).
   At field k retain original base operands, source val_in_memory, the full
   outer state frame and val_in_memory for each destination field j<k at
   dw+SUM(previous destination sizes). Source offset is SUM(previous selected
   source sizes), including the struct compiler's traversal order. Distinct
   names, metadata consistency and existing field-layout lemmas must justify
   this selection/order, not an assumed identity of source/destination sizes.
   Execute both compile_with_byte_offset prefixes, apply E for that field's
   smaller rank with its actual child_sa/child_sb, then compose with the tail
   list induction at updated offsets. Child frames preserve original bases
   and preceding fields; whole-region disjointness preserves source values.
   Empty lists use the reflexive zero path at the unchanged compiler endpoint.
   Missing source fields must be ruled out by typing before taking a child.
   No arrays/fields/bytes fast-path proof is claimed by this design artifact.
*)
Theorem place_store_typed_word_path:
  !cenv ctx func tenv dst dty src sty sa sb stv dtv v sw dw s.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    is_word_type dty /\ type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_word_widening >> strip_tac >> gvs[] >>
  `type_memory_size dtv = 32` by suspend "size" >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[entryDecodePropsTheory.val_in_memory_word] >>
  drule_all typedMemoryCopyTheory.typed_copy_word_run_seq >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by suspend "prefix" >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    suspend "no_gas" >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    suspend "path" >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_typed_word_path[size]:
  qpat_x_assum `is_word_type dty` mp_tac >>
  qpat_x_assum `evaluate_type tenv dty = SOME dtv` mp_tac >>
  Cases_on `dty` >> simp[is_word_type_def]
  >~ [`FlagT`]
  >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[valueEncodingTheory.type_memory_size_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, evaluate_type_def, valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, evaluate_type_def, valueEncodingTheory.type_memory_size_def, AllCaseEqs()]
QED
Resume place_store_typed_word_path[prefix]:
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  qexists_tac `l` >> rewrite_tac[]
QED
Resume place_store_typed_word_path[no_gas]:
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def] >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED
Resume place_store_typed_word_path[path]:
  drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[gas_marked_path_def]
QED
Resume place_store_typed_word_path[post]:
  `typedMemoryCopy$typed_copy_state_frame sa (w2n dw) 32 s
     (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[Abbr `u`, typedMemoryCopyTheory.typed_copy_word_state_frame] >>
  `val_in_memory dtv v (w2n dw) u.vs_memory` by
    (drule_all entryDecodePropsTheory.val_in_memory_word >>
     disch_then (fn th => rewrite_tac[th]) >>
     simp[Abbr `u`, valueEncodingPropsTheory.mstore_mem_word_at_same,
          GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `u`, mstore_def, update_var_def] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def, same_blocks_def] >>
  metis_tac[]
QED
Finalise place_store_typed_word_path

(* Lift a GAS-free emitted prefix without exposing continuation semantics. *)
Theorem place_store_emitted_seq_path:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                     rich_listTheory.DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> rewrite_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[gas_marked_path_def]
QED

Theorem place_store_copy_dynamic_path:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((mcopy (w2n d) (w2n a) (w2n w) s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_dynamic_run_seq >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_copy_memory_dynamic_def,
          emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
          emit_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
                   mk_inst_def]) >>
  conj_tac >- (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  gvs[same_blocks_def]
QED

Theorem place_store_copy_fixed_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  n < dimword (:256) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n d) (w2n a) n s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  Cases_on `n = 0`
  >- (simp[contextTheory.compile_copy_memory_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  Cases_on `n` >> gvs[contextTheory.compile_copy_memory_def] >> strip_tac >>
  drule_all valueCopyTheory.emit_mcopy_run >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
          emit_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
                   mk_inst_def]) >>
  conj_tac >- (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  gvs[same_blocks_def]
QED

Theorem place_store_offset_path:
  compile_with_byte_offset ptr0 off sa = (op,sb) /\
  eval_operand ptr0 s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand op t = SOME (w + n2w off) /\
      t.vs_memory = s.vs_memory /\
      (!dst len. typedMemoryCopy$typed_copy_state_frame sa dst len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[contextTheory.compile_with_byte_offset_def, comp_return_def] >>
      qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           wordsTheory.WORD_ADD_0,
           typedMemoryCopyTheory.typed_copy_state_frame_def,
           venom_state_component_equality,
           typedMemoryCopyTheory.typed_copy_frame_def]) >>
  drule_all typedMemoryCopyTheory.typed_copy_offset_run_seq >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_with_byte_offset_def] >>
     simp[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def,
          emit_def, comp_ignore_bind_def, emitHelperTheory.emit_inst_def, fresh_id_def,
          comp_return_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_offset_path[post]:
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, same_blocks_def] >>
  conj_tac
  >- (simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
           venom_state_component_equality,
           typedMemoryCopyTheory.typed_copy_frame_def,
           lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >> simp[]) >>
  gvs[same_blocks_def]
QED
Finalise place_store_offset_path

Theorem place_store_bytestring_path:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  mem_word_at (w2n a) s.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n d) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all valueCopyTheory.store_bytestring_run_exact >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    suspend "no_gas" >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_bytestring_path[no_gas]:
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED
Resume place_store_bytestring_path[post]:
  `val_in_memory tv v (w2n d) t.vs_memory` by
    (asm_rewrite_tac[] >> irule valueCopyTheory.mcopy_val_in_memory >> simp[]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `typedMemoryCopy$typed_copy_state_frame sa (w2n d) (type_memory_size tv) s
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     conj_tac
     >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
     simp[typedMemoryCopyTheory.typed_copy_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
         decide_tac) >>
     simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
          MAX_DEF]) >>
  gvs[same_blocks_def] >> metis_tac[]
QED
Finalise place_store_bytestring_path

(* Shared actual-execution contract for recursive normalization. *)
Definition place_store_counted_entry_def:
  place_store_counted_entry cenv ctx dty sty dtv stv v <=>
    !dst src sa sb func s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      regions_disjoint (w2n sw) (type_memory_size stv)
                       (w2n dw) (type_memory_size dtv) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem place_store_counted_word_entry:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v ==>
  place_store_counted_entry cenv ctx dty sty dtv stv v
Proof
  strip_tac >> rw[place_store_counted_entry_def] >>
  drule_all place_store_typed_word_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[ADD_COMM]
QED

(* List alignment uses the library relation, not a second entries concept. *)
Theorem place_store_counted_fields_cons:
  LIST_REL
    (\(dty,dtv) (sty,stv,v).
       type_memory_bytes cenv dty = type_memory_size dtv /\
       type_memory_bytes cenv sty = type_memory_size stv /\
       place_store_counted_entry cenv ctx dty sty dtv stv v)
    ((dty,dtv)::ds) ((sty,stv,v)::ss) <=>
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  place_store_counted_entry cenv ctx dty sty dtv stv v /\
  LIST_REL
    (\(dty,dtv) (sty,stv,v).
       type_memory_bytes cenv dty = type_memory_size dtv /\
       type_memory_bytes cenv sty = type_memory_size stv /\
       place_store_counted_entry cenv ctx dty sty dtv stv v) ds ss
Proof
  simp[CONJ_ASSOC]
QED

Theorem place_store_counted_entry_offset_path:
  place_store_counted_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n sw + soff) (type_memory_size stv)
                   (w2n dw + doff) (type_memory_size dtv) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_mono,
              cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                                  cs_extends_trans]) >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typedMemoryCopyTheory.typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. src = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_fresh,
              typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac place_store_offset_path) >>
  disch_then (qspecl_then [`dw`, `s`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q1` strip_assume_tac) >>
  `eval_operand src q1 = SOME sw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qpat_assum `compile_with_byte_offset src _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac place_store_offset_path) >>
  disch_then (qspecl_then [`sw`, `q1`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q2` strip_assume_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_fresh] >>
  `eval_operand dp q2 = SOME (dw + n2w doff)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[place_store_counted_entry_def] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `q2`, `dw + n2w doff`, `sw + n2w soff`] mp_tac) >>
  (impl_tac >- metis_tac[ADD_COMM]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >>
  `gas_marked_path F ctx func s 0 (OK q2)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `ci_mono sa s2` by (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  simp[] >> conj_tac >- metis_tac[ADD_COMM] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `q1` >> conj_tac >- metis_tac[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  qexists_tac `s1` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `q2` >> conj_tac >- metis_tac[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  qexists_tac `s2` >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem place_store_counted_tuple_path:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw.
  LIST_REL (\(dty,dtv) (sty,stv,v).
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    place_store_counted_entry cenv ctx dty sty dtv stv v)
    (ZIP (dtys,dtvs)) (ZIP (stys,ZIP (stvs,vs))) /\
  LENGTH dtys = LENGTH dtvs /\ LENGTH stys = LENGTH stvs /\ LENGTH stvs = LENGTH vs /\
  tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
  compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
  (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `vs` >>
      gvs[contextTheory.compile_store_memory_typed_def, comp_return_def,
          valueEncodingTheory.val_wf_def,
          valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def] >>
      qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def,
           venom_state_component_equality]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[] >>
  rename1 `place_store_counted_entry cenv ctx dty sty dtv stv v` >>
  gnvs[valueEncodingTheory.val_wf_def, valueEncodingTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty cs2 = (u,sc)` >>
  Cases_on `u` >>
  rename1 `compile_typed_copy_fields cenv dst src dtys stys _ _ sc = ((),sb)` >>
  rename1 `LIST_REL _ (ZIP (dtys,dtvs)) (ZIP (stys,ZIP (stvs,vs)))` >>
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs2` by
       metis_tac[typedMemoryCopyTheory.typed_copy_offset_mono] >>
     `ci_mono cs2 sc` by
       metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
     `ci_mono sc sb` by
       metis_tac[cj 2 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  qpat_assum `compile_with_byte_offset dst _ _ = _` mp_tac >>
  disch_then (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
    place_store_counted_entry_offset_path) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`sw`, `s`, `func`, `dw`] mp_tac) >>
  (impl_tac >- (simp[compileEnvTheory.regions_disjoint_def] >> decide_tac)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typedMemoryCopyTheory.typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> decide_tac) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `u` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> simp[] >> conj_tac
  >- (conj_tac
      >- (irule typedMemoryCopyTheory.typed_copy_frame_preserves_source >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`type_memory_size_list dtvs`,
        `doff + type_memory_size dtv + w2n dw`, `t.vs_memory`] >>
      gvs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> decide_tac) >>
      metis_tac[ADD_ASSOC]) >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >> qexists_tac `t` >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`] >>
      simp[ADD_COMM]) >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
  qexistsl_tac [`doff + type_memory_size dtv + w2n dw`,
    `type_memory_size_list dtvs`] >> simp[]
QED

(* compile_assign_value into (transient) storage, not a DynArray. *)
Theorem place_store_value_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (!et n. dty <> ArrayT et (Dynamic n)) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
