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
