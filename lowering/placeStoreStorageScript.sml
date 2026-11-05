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
         `i < dimword (:256)` by decide_tac >>
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
         `i < dimword (:256)` by decide_tac >>
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
         `i < dimword (:256)` by decide_tac >>
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
          `i < dimword (:256)` by decide_tac >>
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
  disch_tac >> gnvs[] >> rpt gen_tac >> disch_tac >> gnvs[] >>
  all_tac
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume place_store_dead_subregion_frame[struct]:
  gvs[] >> rpt strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_struct_frame >>
   conj_tac >- first_assum ACCEPT_TAC >>
   goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
   goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
   qexistsl_tac [`type_slot_size leaf`, `base' + delta' + rest`] >>
   simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       disch_then irule >>
       drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >>
       strip_tac >> simp[GSYM ADD_ASSOC] >>
       qexists_tac `st` >> simp[] >> metis_tac[]) >>
   decide_tac)
QED
Resume place_store_dead_subregion_frame[tuple]:
  gvs[] >> rpt strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_tuple_frame >>
   conj_tac >- first_assum ACCEPT_TAC >>
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
       qexists_tac `st` >> simp[] >> metis_tac[]) >>
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
  >- (gvs[] >>
      first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
      disch_then irule >> simp[GSYM ADD_ASSOC] >>
      qexists_tac `st` >> simp[] >> metis_tac[]) >>
  `dead_bytes st' (base' + k * type_slot_size root) root j b =
   dead_bytes st (base' + k * type_slot_size root) root j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     rename1 `base' + k * type_slot_size root <= idx` >>
     `idx < dimword (:256)` by decide_tac >>
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
           qexists_tac `st` >> simp[] >> metis_tac[]) >>
       `dead_bytes st' (base' + (k * type_slot_size root + 1)) root j b =
        dead_bytes st (base' + (k * type_slot_size root + 1)) root j b` by
         (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
          first_x_assum irule >>
          rename1 `base' + (k * type_slot_size root + 1) <= idx` >>
          `idx < dimword (:256)` by decide_tac >>
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
       conj_tac >- decide_tac >>
       goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       qexists_tac `st` >> simp[] >> metis_tac[])) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv)
       (w2n rootk) (type_slot_size root)` by
    (first_x_assum irule >> conj_tac
     >- (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `dead_bytes st' (w2n slot) tv j b = dead_bytes st (w2n slot) tv j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     `i < dimword (:256)` by decide_tac >>
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
  `~dead_bytes st1' (w2n k) leaf (w2n q) b` by
    (strip_tac >>
     `dead_bytes st1' (w2n rootk) root (w2n q) b` by
       (drule place_store_dead_subregion >>
        disch_then (qspec_then `w2n rootk` mp_tac) >>
        asm_rewrite_tac[] >> metis_tac[]) >>
     qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [storage_dead_def] >>
     qexistsl_tac [`mid`, `name`, `subs`, `rootk`, `root`] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
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
