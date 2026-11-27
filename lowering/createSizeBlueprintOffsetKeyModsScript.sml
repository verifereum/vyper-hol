(* Constant lookups in the linked substitution environment have source declarations. *)
Theory createSizeBlueprintOffsetKeyMods
Ancestors
  alist constSubstMods list pair vyperAST

Theorem lookup_snoc_origin[local]:
  ALOOKUP (xs ++ [(k,v)]) q = SOME r ==>
  ALOOKUP xs q = SOME r \/ (q = k /\ r = v)
Proof
  Cases_on `ALOOKUP xs q` >> simp[ALOOKUP_APPEND, ALOOKUP_def] >>
  Cases_on `k = q` >> gvs[]
QED

Theorem module_consts_env_mods_key:
  !src tops acc s id r.
    ALOOKUP (module_consts_env_mods src tops acc) (s,id) = SOME r ==>
    ALOOKUP acc (s,id) = SOME r \/
    (s = src /\ ?v e ty slot. MEM (VariableDecl v (Constant e) id ty slot) tops)
Proof
  Induct_on `tops` >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis decl id ty slot` >> Cases_on `decl` >>
  simp[module_consts_env_mods_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac)
  >- (drule lookup_snoc_origin >> simp[] >> metis_tac[])
  >- metis_tac[]
QED

Theorem consts_env_mods_acc_key[local]:
  !mods acc s id r.
    ALOOKUP (consts_env_mods_acc mods acc) (s,id) = SOME r ==>
    ALOOKUP acc (s,id) = SOME r \/
    (?tops. MEM (s,tops) mods /\ ?v e ty slot. MEM (VariableDecl v (Constant e) id ty slot) tops)
Proof
  Induct >> simp[consts_env_mods_acc_def] >>
  simp[pairTheory.FORALL_PROD, consts_env_mods_acc_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac)
  >- (drule_then strip_assume_tac module_consts_env_mods_key >> metis_tac[])
  >- metis_tac[]
QED

Theorem consts_env_modules_order_mem[local]:
  !mods m. MEM m (consts_env_modules_order mods) ==> MEM m mods
Proof
  Induct >> simp[consts_env_modules_order_def, pairTheory.FORALL_PROD] >>
  qx_gen_tac `src` >> Cases_on `src` >> simp[MEM_APPEND] >> metis_tac[]
QED

Theorem consts_env_mods_key:
  !mods s id r. ALOOKUP (consts_env_mods mods) (s,id) = SOME r ==>
    ?tops. MEM (s,tops) mods /\ ?v e ty slot. MEM (VariableDecl v (Constant e) id ty slot) tops
Proof
  rw[consts_env_mods_def] >> drule consts_env_mods_acc_key >>
  simp[] >> metis_tac[consts_env_modules_order_mem]
QED
