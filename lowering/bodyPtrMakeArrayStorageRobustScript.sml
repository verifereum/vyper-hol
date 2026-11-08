(* Only live bytes of a decoded storage value need to be untainted. *)
Theory bodyPtrMakeArrayStorageRobust
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProps valueEncodingProofs list
  accountsRelProps exprSimStorageCopy compileEnv words ptrDiscipline venomState

Theorem copy_bytes_taint_agree_outside:
  copy_bytes st bs n D dst mem /\
  (!i j. i < n /\ j < 32 /\ ~D (bs+i) j ==>
    dst+32*i+j NOTIN tainted) /\
  mem_agree_outside tainted mem m ==>
  copy_bytes st bs n D dst m
Proof
  simp[copy_bytes_def] >> rpt strip_tac >>
  `dst+32*i+b NOTIN tainted` by metis_tac[arithmeticTheory.ADD_ASSOC] >>
  `mem_bytes_at (dst+32*i+b) 1 mem =
   mem_bytes_at (dst+32*i+b) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  `EL 0 (mem_bytes_at (dst+32*i+b) 1 mem) =
   EL 0 (mem_bytes_at (dst+32*i+b) 1 m)` by simp[] >>
  gvs[EL_mem_bytes_at] >> metis_tac[]
QED

Theorem storage_live_memory_robust_decode:
  !bs st. well_formed_type_value tv /\ slots_in_range st bs tv /\
  decode_value st bs tv = SOME v /\
  storage_live_memory st bs tv dst mem /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst+32*i+j IN tainted ==>
    dead_bytes st bs tv (bs+i) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> irule decode_value_live_memory >> simp[] >>
  qexistsl_tac [`bs`, `st`] >> simp[] >>
  gvs[storage_live_memory_def] >>
  irule copy_bytes_taint_agree_outside >>
  qexistsl_tac [`mem`, `tainted`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem copied_storage_robust_decode:
  !cx tr st rt a keys. well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_read_live cx tr st a tv /\
  storage_agree (storage_dead cx tr st) st rt /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (b+32*i) mem = lookup_storage (a+n2w i) rt) /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)) /\
  (!key j. j IN key_taint keys key ==>
    storage_dead cx tr rt (w2n key) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v b m
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac storage_live_memory_robust_decode >>
  qexistsl_tac [`w2n a`, `st`] >> simp[] >>
  conj_tac
  >- (irule copied_storage_live_memory >> metis_tac[]) >>
  rpt strip_tac >>
  `storage_dead cx tr rt (w2n (a+n2w i)) j` by
    metis_tac[arithmeticTheory.ADD_ASSOC] >>
  drule storage_agree_storage_dead >> disch_then (gvs o single) >>
  `storage_dead cx tr st (w2n (a+n2w i)) j` by metis_tac[] >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_read_live_def] >>
  disch_then drule >> strip_tac >>
  `w2n a + i < dimword (:256)` by decide_tac >>
  `w2n (a+n2w i) = w2n a+i` by
    (Cases_on `a` >> fs[wordsTheory.word_add_n2w]) >>
  gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem stor_taint_ok_key_dead:
  stor_taint_ok cx tn s /\
  j IN key_taint (if tr then tn.t_trans else tn.t_stor) key ==>
  storage_dead cx tr
    (if tr then contract_transient s else contract_storage s) (w2n key) j
Proof
  Cases_on `tr` >>
  simp[stor_taint_ok_def, key_taint_def, cx_dead_def,
       contract_transient_def, contract_storage_def,
       pred_setTheory.SUBSET_DEF] >> rpt strip_tac
  >- (qpat_x_assum `!x. x IN tn.t_trans ==> _`
        (qspec_then `(key,j)` mp_tac) >>
      Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >> simp[]) >>
  qpat_x_assum `!x. x IN tn.t_stor ==> _`
    (qspec_then `(key,j)` mp_tac) >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  simp[vfmStateTheory.lookup_account_def]
QED

Theorem copy_prefix_robust_decode:
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_read_live cx tr st a tv /\
  storage_agree (storage_dead cx tr st) st
    (if tr then contract_transient sbase else contract_storage sbase) /\
  copy_prefix (if tr then LocTransient else LocStorage) a b n sbase n sf /\
  type_slot_size tv <= n /\ stor_taint_ok cx tnbase sbase /\
  (!i j. i < n /\ j < 32 /\ b+32*i+j IN tnf.t_mem ==>
    j IN key_taint (if tr then tnbase.t_trans else tnbase.t_stor) (a+n2w i)) ==>
  !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory tv v b m
Proof
  strip_tac >> match_mp_tac copied_storage_robust_decode >>
  qexistsl_tac [`cx`, `tr`, `st`,
    `if tr then contract_transient sbase else contract_storage sbase`,
    `a`, `if tr then tnbase.t_trans else tnbase.t_stor`] >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `i < n` by decide_tac >> drule_all copy_prefix_word >>
      Cases_on `tr` >>
      simp[copy_runtime_word_def, sload_def, tload_def]) >>
  rpt strip_tac >> metis_tac[stor_taint_ok_key_dead]
QED
