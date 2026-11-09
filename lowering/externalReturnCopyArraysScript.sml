(* Task-owned array representation interfaces; no typedMemoryCopy import. *)
Theory externalReturnCopyArrays
Ancestors
  externalReturnCopyDynamic externalReturnCopyBulk externalReturnCopyArrayLoop fragExec valueEncoding valueEncodingProps
  valueEncodingProofs vyperTypeSystem vyperTypeArgFits vyperTyping
  vyperValue list pair alist sorting arithmetic words context compileEnv

Theorem return_copy_default_widening:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  default_value stv = default_value dtv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[cj 1 arg_type_fits_default_value]
QED

Theorem return_copy_sarray_element:
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
  i < n ==>
  val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    (off + i * type_memory_size tv) mem
Proof
  rw[val_in_memory_sarray] >> Cases_on `ALOOKUP kvs i` >> simp[] >>
  metis_tac[kvs_in_memory_lookup]
QED

Theorem return_copy_sparse_member:
  !kvs tv n i v.
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  MEM (i,v) kvs ==> i < n /\ ALOOKUP kvs i = SOME v
Proof
  rpt gen_tac >> simp[value_has_type_def] >> strip_tac >>
  `ALL_DISTINCT (MAP FST kvs)` by metis_tac[SORTED_lt_ALL_DISTINCT] >>
  qpat_x_assum `SORTED _ _` kall_tac >>
  Induct_on `kvs` >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def] >> rpt strip_tac >> gvs[] >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem return_copy_kvs_members:
  !kvs off tv mem.
  kvs_in_memory kvs off tv mem <=>
  !i v. MEM (i,v) kvs ==>
    val_in_memory tv v (off + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> Cases >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem return_copy_sarray_indexed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (!i. i < n ==>
    val_in_memory tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
      (off + i * type_memory_size tv) mem) ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem
Proof
  strip_tac >> rewrite_tac[val_in_memory_sarray] >> conj_tac
  >- (rewrite_tac[return_copy_kvs_members] >> rpt strip_tac >>
      drule_all return_copy_sparse_member >> strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem return_copy_sparse_lookup_wf:
  !kvs tv n i. kvs_val_wf kvs tv n ==>
    val_wf tv (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
Proof
  Induct >> simp[val_wf_def, cj 1 val_wf_default_value_proof] >>
  Cases >> simp[val_wf_def] >> rpt strip_tac >>
  Cases_on `q = i` >> gvs[] >> metis_tac[]
QED

Theorem return_copy_sarray_representation:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) off mem ==>
  (!i. i < N ==>
    val_wf stv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v) /\
    val_wf dtv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v) /\
    val_in_memory stv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
      (off + i * type_memory_size stv) mem) /\
  (!mem' dstoff.
    (!i. i < N ==> val_in_memory dtv
      (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
      (dstoff + i * type_memory_size dtv) mem') ==>
    val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) dstoff mem')
Proof
  strip_tac >> drule_all return_copy_default_widening >> strip_tac >>
  conj_tac
  >- (rpt strip_tac
      >- (irule return_copy_sparse_lookup_wf >> qexists_tac `N` >> fs[val_wf_def])
      >- (asm_rewrite_tac[] >> irule return_copy_sparse_lookup_wf >>
          qexists_tac `N` >> fs[val_wf_def])
      >> metis_tac[return_copy_sarray_element]) >>
  rpt strip_tac >> irule return_copy_sarray_indexed >> gvs[]
QED

Theorem return_copy_elems_indexed:
  !vs off tv mem.
  elems_in_memory vs off tv mem <=>
  !i. i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases >> simp[ADD_CLAUSES, MULT_CLAUSES] >>
      rpt strip_tac >> first_x_assum drule >> simp[ADD_ASSOC]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  pure_rewrite_tac[LT_SUC, EL, HD, TL, MULT_CLAUSES, ADD_ASSOC] >> simp[]
QED

Theorem return_copy_elems_wf_indexed:
  !vs tv. elems_val_wf vs tv <=>
    !i. i < LENGTH vs ==> val_wf tv (EL i vs)
Proof
  Induct >> simp[val_wf_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases >> simp[]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem return_copy_dynarray_representation:
  val_in_memory (ArrayTV tv (Dynamic C)) (ArrayV (DynArrayV vs)) off mem <=>
  mem_word_at off mem = n2w (LENGTH vs) /\
  (!i. i < LENGTH vs ==> val_in_memory tv (EL i vs)
     (off + 32 + i * type_memory_size tv) mem)
Proof
  simp[val_in_memory_def, return_copy_elems_indexed]
QED

Theorem return_copy_dynarray_wf:
  val_wf (ArrayTV tv (Dynamic C)) (ArrayV (DynArrayV vs)) <=>
  LENGTH vs <= C /\ (!i. i < LENGTH vs ==> val_wf tv (EL i vs))
Proof
  simp[val_wf_def, return_copy_elems_wf_indexed]
QED

Theorem return_copy_static_fits:
  (!sty dty. arg_type_fits sty dty /\ ~is_abi_dynamic sf dty ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys /\
     ~EXISTS (is_abi_dynamic sf) dtys ==> stys = dtys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_abi_dynamic_def] >>
  gvs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> fs[]
QED

Theorem return_copy_static_widening:
  type_widens_to tenv sty dty /\ ~is_abi_dynamic sf dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  stv = dtv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  drule (cj 1 return_copy_static_fits) >>
  disch_then (qspec_then `sf` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem return_copy_sarray_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  (!i. f i = (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)) /\
  N < dimword (:256) /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (!i. i < N /\ 0 < val_footprint stv (f i) ==>
    w2n sw + i * type_memory_size stv + val_footprint stv (f i) < dimword (:256) /\
    (w2n sw + i * type_memory_size stv + val_footprint stv (f i) <= w2n dw \/
     w2n dw + N * type_memory_size dtv <= w2n sw + i * type_memory_size stv)) /\
  (!i dp sp a b s dw sw.
    i < N /\ compile_store_memory_typed cenv dp dty sp sty a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp s = SOME dw /\ eval_operand sp s = SOME sw /\
    val_wf stv (f i) /\ val_in_memory stv (f i) (w2n sw) s.vs_memory /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (0 < val_footprint stv (f i) ==>
      w2n sw + val_footprint stv (f i) < dimword (:256) /\
      (w2n sw + val_footprint stv (f i) <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
        return_copy_frame a (w2n dw) (type_memory_size dtv) s t) (\r. F)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n dw) t.vs_memory /\
      return_copy_frame sa (w2n dw) (type_memory_size (ArrayTV dtv (Fixed N))) s t) (\r. F)
Proof
  strip_tac >> drule_all return_copy_sarray_representation >> strip_tac >>
  `!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i) /\
    val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) s.vs_memory` by
    metis_tac[] >>
  `frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
      (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      return_copy_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)` by
    (qpat_x_assum `!i. f i = _` kall_tac >>
     qpat_x_assum `value_has_type _ _` kall_tac >>
     qpat_x_assum `val_wf (ArrayTV stv _) _` kall_tac >>
     qpat_x_assum `val_wf (ArrayTV dtv _) _` kall_tac >>
     qpat_x_assum `val_in_memory (ArrayTV _ _) _ _ _` kall_tac >>
     qpat_x_assum `!mem' dstoff. _` kall_tac >>
     Cases_on `type_memory_size dtv = type_memory_size stv /\ ~is_abi_dynamic cenv.ce_struct_fields dty`
     >- (`stv = dtv` by metis_tac[return_copy_static_widening] >>
         qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
         irule return_copy_sarray_bulk_frag >> simp[] >>
         goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
     irule return_copy_sarray_slow_frag >> simp[] >>
     goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
     qexists_tac `stv` >> fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >> simp[type_memory_size_def] >>
  metis_tac[]
QED

Theorem return_copy_dynarray_frag:
  compile_copy_dynarray_typed cenv dst dty capacity src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (dty = sty ==> stv = dtv) /\
  LENGTH vs <= capacity /\ capacity < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic capacity)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n sw) s.vs_memory /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n dw + 32 + capacity * type_memory_size dtv < dimword (:256) /\
  (!i. i < LENGTH vs /\ 0 < val_footprint stv (EL i vs) ==>
    w2n sw + 32 + i * type_memory_size stv + val_footprint stv (EL i vs) < dimword (:256) /\
    (w2n sw + 32 + i * type_memory_size stv + val_footprint stv (EL i vs) <= w2n dw \/
     w2n dw + 32 + capacity * type_memory_size dtv <= w2n sw + 32 + i * type_memory_size stv)) /\
  (!i dp sp a b s dw sw.
    i < LENGTH vs /\ compile_store_memory_typed cenv dp dty sp sty a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp s = SOME dw /\ eval_operand sp s = SOME sw /\
    val_wf stv (EL i vs) /\ val_in_memory stv (EL i vs) (w2n sw) s.vs_memory /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (0 < val_footprint stv (EL i vs) ==>
      w2n sw + val_footprint stv (EL i vs) < dimword (:256) /\
      (w2n sw + val_footprint stv (EL i vs) <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw)) ==>
    frag_exec ctx a b (\u. u = s)
      (\t. val_in_memory dtv (EL i vs) (w2n dw) t.vs_memory /\
        return_copy_frame a (w2n dw) (type_memory_size dtv) s t) (\r. F)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Dynamic capacity)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
      return_copy_frame sa (w2n dw) (type_memory_size (ArrayTV dtv (Dynamic capacity))) s t) (\r. F)
Proof
  strip_tac >>
  fs[return_copy_dynarray_wf, return_copy_dynarray_representation] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    fs[mem_word_at_eq_mload] >>
  `frag_exec ctx sa sb (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = n2w (LENGTH vs) /\
      (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
        (w2n dw + 32 + i * type_memory_size dtv) t.vs_memory) /\
      return_copy_frame sa (w2n dw) (32 + capacity * type_memory_size dtv) s t) (\r. F)` by
    (Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty`
     >- (`stv = dtv` by metis_tac[] >>
         qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
         ho_match_mp_tac return_copy_dynarray_bulk_frag >> simp[] >>
         goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
         simp[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
     ho_match_mp_tac return_copy_dynarray_slow_frag >>
     fs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >>
  simp[return_copy_dynarray_representation, type_memory_size_def]
QED
