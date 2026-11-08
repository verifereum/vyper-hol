(* Ghost transport for an interior scalar write in a live local struct. *)
Theory augAssignPtrFieldStorePost
Ancestors
  augAssignPtrFieldStore augAssignPtrStore augAssignPtrFieldLoad
  bodyPtrDefs exprSimProps localPtrsProps valueEncoding valueEncodingProps
  stmtSimAssignAttr stmtSimAssignStore vyperLookup finite_map list compileEnv

Theorem local_contained_word_store_exterior:
  local_ptrs_rel fn cenv scopes s /\ name <> other /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ w2n a <= off /\ off+32 <= w2n a+sz /\
  lookup_scopes other scopes = SOME e /\
  FLOOKUP cenv.ce_vars other = SOME (PtrVar (Var q) sq) /\
  lookup_var q s = SOME b ==>
  val_wf e.type e.value /\
  (!i. w2n b <= i /\ i < w2n b + val_footprint e.type e.value ==>
       ~(off <= i /\ i < off+32))
Proof
  strip_tac >>
  `local_region cenv scopes s name (w2n a) sz /\
   local_region cenv scopes s other (w2n b) sq` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n a) sz (w2n b) sq` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_wf e.type e.value /\ type_memory_size e.type <= sq` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  drule val_footprint_le >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem ghost_local_field_word_store:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ fields_val_wf vals fs /\
  ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\ word_value v /\
  struct_field_offset flds fld + 32 <= sz /\
  lookup_scopes name scopes' = SOME
    (entry with <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>) /\
  (!n. n <> name ==> lookup_scopes n scopes' = lookup_scopes n es.scopes) ==>
  !n e q sq.
    lookup_scopes n scopes' = SOME e /\
    FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
    ptr_covers G tn q s sq /\
    !b mem. lookup_var q s = SOME b /\
      mem_agree_outside
        (tn.t_mem DIFF {i | w2n a + struct_field_offset flds fld <= i /\
                           i < w2n a + struct_field_offset flds fld + 32})
        (mstore (w2n a + struct_field_offset flds fld) (val_to_w256 v) s).vs_memory mem ==>
      val_in_memory e.type e.value (w2n b) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `n = name`
  >- (gvs[] >> conj_tac
      >- (fs[ghost_inv_def] >> metis_tac[]) >>
      rpt strip_tac >> gvs[val_in_memory_def] >>
      irule fields_in_memory_mstore_field_robust >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[ghost_inv_def] >>
      qpat_x_assum `!name entry p sz. _` drule >>
      disch_then drule >> simp[val_in_memory_def]) >>
  `lookup_scopes n es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt strip_tac >> irule mstore_robust_exterior >>
  conj_tac >- (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  qexistsl [`w2n a + struct_field_offset flds fld`, `s`, `tn.t_mem`, `val_to_w256 v`] >>
  simp[] >> conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  `name <> n` by simp[] >>
  `w2n a <= w2n a + struct_field_offset flds fld /\
   (w2n a + struct_field_offset flds fld) + 32 <= w2n a + sz` by decide_tac >>
  drule_all local_contained_word_store_exterior >> simp[]
QED

Theorem ghost_inv_write_local_field_word:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  find_containing_scope name es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ lookup_var dst s = SOME da /\
  w2n da = w2n a + struct_field_offset flds fld /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ fields_val_wf vals fs /\
  ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\ word_value v /\
  struct_field_offset flds fld + 32 <= sz /\
  eval_operand value s = SOME (val_to_w256 v) /\ op_taint tn value = {} ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++ (env |+ (name, entry with
      <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
    G (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n da) (val_to_w256 v) s) tn)
    ((mstore (w2n da) (val_to_w256 v) s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  irule ghost_inv_mstore_transport >> simp[] >>
  conj_tac
  >- (pure_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
      MATCH_MP_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC] ghost_local_field_word_store) >>
      simp[lookup_scopes_update, lookup_scopes_update_other]) >>
  metis_tac[]
QED
