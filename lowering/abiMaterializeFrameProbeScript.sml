Theory abiMaterializeFrameProbe
Ancestors
  abiEncodeMaterializeExec exprSim accountsRelProps compileEnv
  vfmState words arithmetic combin

(* A zero-length declared array ignores its sole element's slot, whereas
   a captured scalar at that slot still demands agreement. This is only
   the storage-interface probe, not a full materialization counterexample. *)
Theorem frame_probe_dead_element:
  lookup_storage 0w st = 0w ==>
  !b. b < 32 ==>
    dead_bytes st 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)) 1 b
Proof
  simp[dead_bytes_def, vyperValueTheory.type_slot_size_def]
QED

Theorem frame_probe_declared_agreement:
  lookup_storage 0w st = 0w ==>
  storage_agree (dead_bytes st 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)))
    st (update_storage 1w 1w st)
Proof
  strip_tac >> simp[storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = 1w` >-
    (gvs[] >> metis_tac[frame_probe_dead_element]) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

Theorem frame_probe_captured_disagreement:
  lookup_storage 1w st = 0w ==>
  ~storage_range_agree st (update_storage 1w 1w st) 1w (BaseTV BoolT)
Proof
  strip_tac >> strip_tac >> drule storage_range_agree_head >>
  simp[vyperValueTheory.type_slot_size_def, lookup_storage_def, update_storage_def,
       APPLY_UPDATE_THM] >> gvs[lookup_storage_def]
QED

Theorem frame_probe_zero_storage:
  lookup_storage 0w (K 0w) = 0w /\ lookup_storage 1w (K 0w) = 0w
Proof
  EVAL_TAC
QED

Theorem frame_probe_range_transport_fails:
  storage_agree (dead_bytes (K 0w) 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)))
    (K 0w) (update_storage 1w 1w (K 0w)) /\
  ~storage_range_agree (K 0w) (update_storage 1w 1w (K 0w))
    1w (BaseTV BoolT)
Proof
  metis_tac[frame_probe_zero_storage, frame_probe_declared_agreement,
    frame_probe_captured_disagreement]
QED

Definition frame_probe_context_def:
  frame_probe_context vis cx = cx with <|
    sources := [(cx.txn.target, [(NONE,
      [VariableDecl vis Storage "a" (ArrayT (BaseT BoolT) (Dynamic 1)) NONE])])];
    layouts := [(cx.txn.target, ([((NONE,"a"),0)],[]))] |>
End

Theorem frame_probe_declared_region:
  declared_storage_region (frame_probe_context vis cx) mid n subs = SOME (tr,w,tv) <=>
  mid = NONE /\ n = "a" /\ subs = [] /\ tr = F /\ w = 0w /\
    tv = ArrayTV (BaseTV BoolT) (Dynamic 1)
Proof
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def,
       frame_probe_context_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def,
       vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_for_module_def,
       vyperStateTheory.find_var_decl_by_name_def,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem frame_probe_actual_dead_slot:
  !b. b < 32 ==>
  storage_dead (frame_probe_context vis cx) F (K 0w) 1 b
Proof
  rpt strip_tac >> simp[storage_dead_def] >>
  qexistsl [`NONE`, `"a"`, `[]`, `0w`,
    `ArrayTV (BaseTV BoolT) (Dynamic 1)`] >>
  simp[frame_probe_declared_region, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, frame_probe_dead_element,
       frame_probe_zero_storage]
QED

Theorem frame_probe_actual_storage_agreement:
  storage_agree (storage_dead (frame_probe_context vis cx) F (K 0w))
    (K 0w) (update_storage 1w 1w (K 0w)) /\
  ~storage_range_agree (K 0w) (update_storage 1w 1w (K 0w))
    1w (BaseTV BoolT)
Proof
  conj_tac
  >- (simp[storage_agree_def] >> rpt strip_tac >>
      Cases_on `k = 1w`
      >- (gvs[] >> metis_tac[frame_probe_actual_dead_slot]) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]) >>
  metis_tac[frame_probe_range_transport_fails]
QED
