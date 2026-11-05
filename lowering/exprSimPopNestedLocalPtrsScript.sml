Theory exprSimPopNestedLocalPtrs
Ancestors
  exprSimPopNestedLocalMemory exprSimPopNestedLocalProps
  localPtrsProps compileEnv vyperLookup vyperPlaceStatePreservation
  vyperAssignPreservesType vyperTypeInvariants valueEncodingTyping
  exprSimProps vyperState vyperTyping valueEncoding valueEncodingProps
  venomState finite_map arithmetic

Theorem pop_path_updated_typed:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated ==>
  value_has_type tv updated
Proof
  strip_tac >> drule mem_path_offset_sound >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (irule evaluate_subscripts_type_metadata >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule assign_subscripts_replace_type_metadata >>
  conj_tac >- simp[] >>
  qexistsl [`a`, `tv`, `path`, `ArrayTV etv (Dynamic n)`,
            `ArrayV (DynArrayV (FRONT vs))`] >>
  simp[] >> gvs[value_has_type_def] >>
  conj_tac >- (simp[rich_listTheory.LENGTH_FRONT] >> decide_tac) >>
  irule FRONT_all_have_type >> simp[]
QED

(* The scopes interface deliberately ignores the new history: only the live
   value is encoded by local_ptrs_rel. *)
Theorem pop_path_local_ptrs_rel:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes id scopes = SOME entry /\
  lookup_scopes id scopes' = SOME (entry with <|value := updated; popped := hist|>) /\
  (!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j scopes) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  mutable_place_path entry.type path /\ value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  u.vs_memory = (mstore (w2n w + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (!q j sq. FLOOKUP cenv.ce_vars j = SOME (PtrVar (Var q) sq) ==>
             lookup_var q u = lookup_var q s) ==>
  local_ptrs_rel func cenv scopes' u
Proof
  strip_tac >>
  `local_backed func p s (w2n w) sz /\ w2n w + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
   val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     pure_rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name e q sq. _` drule_all >>
     strip_tac >> gvs[]) >>
  `local_region cenv scopes s id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!j b sq. j <> id /\ local_region cenv scopes s j b sq ==>
      regions_disjoint (w2n w) sz b sq` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  `value_has_type entry.type updated` by
    (drule_all pop_path_updated_typed >> simp[]) >>
  `val_wf entry.type updated` by
    (drule_all (cj 1 value_has_type_val_wf) >> simp[]) >>
  `val_in_memory entry.type updated (w2n w) u.vs_memory` by
    (drule_all val_in_memory_pop_path >> simp[]) >>
  `k + 32 <= sz` by
    (drule mem_path_offset_sound >> simp[type_memory_size_def]) >>
  irule local_ptrs_rel_write_local >>
  qexistsl_tac [`entry with <|value := updated; popped := hist|>`, `id`,
                `p`, `scopes`, `s`, `sz`, `w`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) sz b sz'` by metis_tac[] >>
      irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
      gvs[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  qpat_x_assum `val_in_memory _ updated _ u.vs_memory` mp_tac >>
  simp[ADD_COMM]
QED
