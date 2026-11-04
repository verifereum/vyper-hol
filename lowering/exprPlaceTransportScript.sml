(* Constructor probes for delayed reads of provenance-bearing raw results. *)
Theory exprPlaceTransport
Ancestors
  exprSim placeProvenance vyperPlaceResultTyping compileEnv exprEffectStorage
  exprSimAggregateEncoding valueEncoding list rich_list
  vyperState vyperValue vyperValueOperation vyperMisc exprLoweringProps words

Theorem immutable_holds_read_transport:
  immutable_holds cenv cx t tv w es /\
  es2.immutables = es.immutables /\
  read_result cx tv es = (INL v,es) /\
  read_result cx tv es2 = (INL v,es2) ==>
  immutable_holds cenv cx t tv w es2
Proof
  simp[immutable_holds_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem vv_place_ptr_rel_storage_transport:
  vv_place_ptr_rel cenv cx es (StoragePlace tr slot tv) (LocatedValue t p) s /\
  eval_operand p.ptr_operand s2 = eval_operand p.ptr_operand s ==>
  vv_place_ptr_rel cenv cx es2 (StoragePlace tr slot tv) (LocatedValue t p) s2
Proof
  simp[vv_place_ptr_rel_storage]
QED

Theorem vv_place_ptr_rel_memory_transport:
  vv_place_ptr_rel cenv cx es (MemoryPlace id path) (LocatedValue t p) s /\
  eval_operand p.ptr_operand s2 = eval_operand p.ptr_operand s /\
  (!x. lookup_var x s2 = lookup_var x s) ==>
  vv_place_ptr_rel cenv cx es2 (MemoryPlace id path) (LocatedValue t p) s2
Proof
  simp[vv_place_ptr_rel_def, place_ptr_rel_def]
QED

(* A successful read from the old immutable is retained, not reconstructed
   from equality of an unrelated current value. *)
Theorem vv_place_ptr_rel_immutable_transport:
  vv_place_ptr_rel cenv cx es (ImmutablePlace src id path) (LocatedValue t p) s /\
  eval_operand p.ptr_operand s2 = eval_operand p.ptr_operand s /\
  es2.immutables = es.immutables /\
  read_result cx (PlaceR (ImmutablePlace src id path)) es = (INL v,es) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) es2 = (INL v,es2) ==>
  vv_place_ptr_rel cenv cx es2 (ImmutablePlace src id path) (LocatedValue t p) s2
Proof
  simp[vv_place_ptr_rel_immutable] >> rpt strip_tac >>
  drule_all immutable_holds_read_transport >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem vv_place_ptr_rel_live_root_read:
  vv_place_ptr_rel cenv cx es (MemoryPlace id []) (LocatedValue t p) s /\
  stmt_state_rel ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) t = SOME entry.type /\
  value_has_type entry.type entry.value ==>
  vv_holds cenv cx t (PlaceR (MemoryPlace id [])) (LocatedValue t p) es s
Proof
  simp[vv_place_ptr_rel_def, place_ptr_rel_def, mem_path_offset_def] >>
  rpt strip_tac >> gvs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  gvs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  simp[vv_holds_def, read_result_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, read_memory_path_def,
       evaluate_subscripts_def, lift_sum_def, return_def, WORD_ADD_0] >>
  rpt strip_tac >> irule val_in_memory_word_type >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* General root-pop probe: the source snapshot and the retained memory tail
   represent the same removed element.  No arbitrary history value is used. *)
Theorem root_pop_snapshot_memory:
  LENGTH xs < n /\
  val_in_memory (ArrayTV etv (Dynamic n))
    (ArrayV (DynArrayV (SNOC removed xs))) b s.vs_memory /\
  val_wf etv removed /\
  local_region cenv es.scopes s id b sz /\
  32 + n * type_memory_size etv <= sz /\
  locals_kept cenv es s s2 ==>
  read_popped (ArrayTV etv (Dynamic n))
    [ValueSubscript (IntV &(LENGTH xs))]
    (record_pop [] (ArrayV (DynArrayV (SNOC removed xs))) removed history) =
      SOME removed /\
  val_in_memory etv removed (b + 32 + LENGTH xs * type_memory_size etv)
    s2.vs_memory
Proof
  rpt strip_tac
  >- (irule root_pop_removed_element >> simp[evaluate_subscripts_def]) >>
  `val_in_memory etv removed (b + 32 + LENGTH xs * type_memory_size etv)
     s.vs_memory` by
    (qpat_x_assum `val_in_memory (ArrayTV _ _) _ _ _` mp_tac >>
     simp[val_in_memory_def] >> strip_tac >>
     drule elems_in_memory_EL >>
     disch_then (qspec_then `LENGTH xs` mp_tac) >> simp[EL_LENGTH_SNOC]) >>
  irule val_in_memory_footprint_agree >>
  conj_tac >- simp[] >>
  qexists_tac `s.vs_memory` >> simp[] >> sym_tac >>
  qpat_x_assum `locals_kept _ _ _ _` (mp_tac o REWRITE_RULE [locals_kept_def]) >>
  disch_then irule >> goal_assum (drule_at Any) >>
  drule val_footprint_le >> strip_tac >>
  `LENGTH xs * type_memory_size etv + type_memory_size etv <=
     n * type_memory_size etv` by
    (rewrite_tac[GSYM arithmeticTheory.MULT] >>
     irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
  simp[]
QED

(* Keeping the backend keeps both the decoded value and all dynamic length
   slots used by range/liveness checks. No claim about popped storage. *)
Theorem storage_holds_backend_transport:
  storage_holds cx tr t (PlaceR (StoragePlace tr slot leaf)) w es /\
  get_storage cx es2 tr = get_storage cx es tr ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr slot leaf)) w es2
Proof
  simp[storage_holds_def, read_result_def, read_place_def,
       read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, lift_option_def, vyperMiscTheory.option_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Non-root paths of a dynamic local start beyond its exempt length word. *)
Theorem mem_path_offset_dynamic_tail:
  path <> [] /\
  mem_path_offset (ArrayTV etv (Dynamic n)) path = SOME (k,tv) ==>
  32 <= k
Proof
  Cases_on `path` >> simp[mem_path_offset_def] >>
  Cases_on `h` >> simp[mem_step_offset_def] >>
  rename1 `ValueSubscript v` >> Cases_on `v` >>
  simp[mem_step_offset_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  PairCases_on `z` >> gvs[]
QED

(* Source reads, including read_popped, depend on these fields only. *)
Theorem read_result_preserved_fields:
  es2.scopes = es.scopes /\ es2.immutables = es.immutables /\
  (!tr. get_storage cx es2 tr = get_storage cx es tr) /\
  read_result cx tv es = (INL v,es) ==>
  read_result cx tv es2 = (INL v,es2)
Proof
  rpt strip_tac >> Cases_on `tv` >> gvs[read_result_def, return_def, raise_def] >>
  rename1 `read_place cx p es` >> Cases_on `p`
  >- (gvs[read_place_def, read_storage_slot_def,
          vyperStorageBackendTheory.get_storage_backend_eq, bind_def] >>
      gvs[lift_option_def, vyperMiscTheory.option_CASE_rator,
          AllCaseEqs(), return_def, raise_def])
  >- (rename1 `MemoryPlace id path` >>
      Cases_on `lookup_scopes id es.scopes` >>
      gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
          return_def, raise_def] >>
      rename1 `read_memory_path entry path` >>
      Cases_on `read_memory_path entry path` >>
      gvs[lift_sum_def, return_def, raise_def]) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[read_place_def, get_immutables_def, get_address_immutables_def,
      bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `FLOOKUP (get_source_immutables src imms) id` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) id` >>
  gvs[lift_option_type_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_subscripts (FST x) (SND x) l` >>
  gvs[lift_sum_def, return_def, raise_def]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Transport interface dependency: " ^ name) else ()
  end)
  [("mem_path_offset_dynamic_tail", mem_path_offset_dynamic_tail),
   ("read_result_preserved_fields", read_result_preserved_fields)];

Theorem mem_path_dynamic_local_frame:
  path <> [] /\
  mem_path_offset (ArrayTV etv (Dynamic n)) path = SOME (k,tv) /\
  local_region cenv es.scopes s id (w2n b) sz /\
  type_memory_size (ArrayTV etv (Dynamic n)) <= sz /\
  w2n b + sz <= dimword (:256) /\
  len <= type_memory_size tv /\
  locals_kept cenv es s s2 ==>
  mem_bytes_at (w2n (b + n2w k : bytes32)) len s2.vs_memory =
  mem_bytes_at (w2n (b + n2w k : bytes32)) len s.vs_memory
Proof
  strip_tac >> Cases_on `len = 0`
  >- simp[mem_bytes_at_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `32 <= k` by metis_tac[mem_path_offset_dynamic_tail] >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k : bytes32) = w2n b + k` by
    (Cases_on `b` >> fs[word_add_n2w]) >>
  simp[] >>
  qpat_x_assum `locals_kept _ _ _ _` mp_tac >>
  simp[locals_kept_def] >> strip_tac >>
  first_x_assum irule >>
  qexistsl_tac [`w2n b`, `id`, `sz`] >> simp[] >> decide_tac
QED

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag mem_path_dynamic_local_frame) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "Dynamic local frame dependency" else ()
end;

Theorem dynamic_local_header_frame[local]:
  local_ptrs_rel func cenv scopes s /\
  local_ptrs_rel func cenv scopes s2 /\
  lookup_scopes id scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ lookup_var p s2 = SOME w /\
  entry.type = ArrayTV et (Dynamic n) /\
  value_has_type entry.type entry.value ==>
  mem_bytes_at (w2n w) 32 s2.vs_memory =
  mem_bytes_at (w2n w) 32 s.vs_memory
Proof
  simp[local_ptrs_rel_def] >> rpt strip_tac >>
  ntac 2 (qpat_x_assum `!name entry p sz. _`
    (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac)) >>
  simp[] >> rpt strip_tac >> gvs[] >> Cases_on `entry.value` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      valueEncodingProofsTheory.mem_bytes_at_word]
QED

Theorem local_window_frame:
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_rel func cenv es.scopes s2 /\
  locals_kept cenv es s s2 /\
  (!id entry p sz. lookup_scopes id es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
     lookup_var p s2 = lookup_var p s) /\
  (!id entry. lookup_scopes id es.scopes = SOME entry /\
     dynarray_local cenv id ==>
     (?et n. entry.type = ArrayTV et (Dynamic n)) /\
     value_has_type entry.type entry.value) /\
  local_region cenv es.scopes s id b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s2.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  strip_tac >> Cases_on `dynarray_local cenv id`
  >- (qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
      simp[local_region_def] >> strip_tac >> gvs[] >>
      `(?et n. entry.type = ArrayTV et (Dynamic n)) /\
       value_has_type entry.type entry.value` by metis_tac[] >>
      `lookup_var p s2 = SOME w` by metis_tac[] >>
      `mem_bytes_at (w2n w) 32 s2.vs_memory =
       mem_bytes_at (w2n w) 32 s.vs_memory` by
        (irule dynamic_local_header_frame >> metis_tac[]) >>
      `32 <= sz` by
        (fs[local_ptrs_rel_def] >>
         qpat_x_assum `!name entry p sz. _ ==> ?w. _`
           (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac) >>
         simp[] >> rpt strip_tac >>
         gvs[type_memory_size_def]) >>
      `mem_bytes_at (w2n w + 32) (sz - 32) s2.vs_memory =
       mem_bytes_at (w2n w + 32) (sz - 32) s.vs_memory` by
        (qpat_x_assum `locals_kept _ _ _ _` mp_tac >>
         simp[locals_kept_def] >> strip_tac >> first_x_assum irule >>
         qexistsl_tac [`w2n w`, `id`, `sz`] >>
         simp[local_region_def] >> metis_tac[]) >>
      `mem_bytes_at (w2n w) sz s2.vs_memory =
       mem_bytes_at (w2n w) sz s.vs_memory` by
        (`sz = 32 + (sz - 32)` by decide_tac >>
         pop_assum (fn th => GEN_REWRITE_TAC (BINOP_CONV o RATOR_CONV o RAND_CONV) empty_rewrites [th]) >>
         simp[valueEncodingProofsTheory.mem_bytes_at_split_padded]) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >>
      qpat_x_assum `!off2 len2. _` irule >> simp[]) >>
  fs[locals_kept_def] >> first_x_assum irule >>
  qexistsl_tac [`b`, `id`, `sz`] >> simp[]
QED

Theorem local_window_frame_well_typed:
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_rel func cenv es.scopes s2 /\
  state_well_typed es /\ locals_kept cenv es s s2 /\
  (!id entry p sz. lookup_scopes id es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
     lookup_var p s2 = lookup_var p s) /\
  (!id entry. lookup_scopes id es.scopes = SOME entry /\
     dynarray_local cenv id ==> ?et n. entry.type = ArrayTV et (Dynamic n)) /\
  local_region cenv es.scopes s id b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s2.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  strip_tac >> irule local_window_frame >>
  goal_assum (drule_at (Pat `locals_kept _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  qexists_tac `func` >> simp[] >>
  metis_tac[vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Local window dependency: " ^ name) else ()
  end)
  [("dynamic_local_header_frame", dynamic_local_header_frame),
   ("local_window_frame", local_window_frame),
   ("local_window_frame_well_typed", local_window_frame_well_typed)];
