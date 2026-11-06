(* Robust decoding augments, rather than replaces, the counted CFG witness. *)
Theory bodyPtrMakeArrayStorageEndpoint
Ancestors
  bodyPtrMakeArrayStorageInstalled bodyPtrMakeArrayStorageProbe
  exprSimStorageCopy exprSimCopy bodyPtrDefs ptrDiscipline venomState
  storageDecodeMemory valueEncoding words

Theorem storage_copy_robust_ptr_endpoint:
  compile_word_copy_loop src (Var dst) n (if tr then LocTransient else LocStorage)
    LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  copy_old_operand sa src /\ not_fresh_at sa dst /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  allocas_from 0 s /\ ~s.vs_halted /\ b+32*n < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_range_agree st (if tr then contract_transient s else contract_storage s) a tv /\
  (!k j. w2n a <= w2n k /\ w2n k < w2n a + type_slot_size tv /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tv (w2n k) j) /\ type_slot_size tv <= n ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_prefix (if tr then LocTransient else LocStorage) a b n s n t /\
    copy_static t = copy_static s /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    mem_agree_outside {i | b <= i /\ i < b+32*n} t.vs_memory s.vs_memory /\
    ptr_covers H tm dst t (32*n) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i j. i < n /\ j < 32 /\ b+32*i+j IN tm.t_mem ==>
      j IN key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w i)) /\
    (!i. i < b \/ b+32*n <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==> val_in_memory tv v b m)
Proof
  strip_tac >>
  Q.SUBGOAL_THEN
    `(if tr then LocTransient else LocStorage) = LocStorage \/
     (if tr then LocTransient else LocStorage) = LocTransient` assume_tac
  >- (Cases_on `tr` >> simp[]) >>
  drule_all compile_storage_copy_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `tm` strip_assume_tac)))) >>
  `!i j. i < n /\ j < 32 /\ b+32*i+j IN tm.t_mem ==>
    j IN key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w i)` by
    (Cases_on `tr` >> gvs[]) >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  match_mp_tac (Q.INST [
    `rt` |-> `if tr then contract_transient s else contract_storage s`,
    `keys` |-> `if tr then tn.t_trans else tn.t_stor`]
    copied_storage_range_robust_decode) >> simp[] >>
  rpt strip_tac >>
  `i < n` by decide_tac >>
  drule_all copy_prefix_word >>
  Cases_on `tr` >> simp[copy_runtime_word_def, sload_def, tload_def,
    contract_storage_def, contract_transient_def]
QED
