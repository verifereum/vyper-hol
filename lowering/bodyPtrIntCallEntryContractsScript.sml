Theory bodyPtrIntCallEntryContracts
Ancestors
  bodyPtrDefs intCallCallee ptrDiscipline finite_map words list
  valueEncoding compileEnv venomState

(* Values waiting to be materialized are not yet locals of ghost_inv.
   Robustness concerns the represented value, not padding in its allocation. *)
Definition intcall_local_value_def:
  intcall_local_value entry p sz G tn (s:venom_state) <=>
    val_wf entry.type entry.value /\ ptr_covers G tn p s sz /\
    ?w. lookup_var p s = SOME w /\
        w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next /\
        !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
            val_in_memory entry.type entry.value (w2n w) m
End

Definition intcall_completed_def:
  intcall_completed env cenv G tn s <=>
    !name entry. FLOOKUP env name = SOME entry ==>
      ?p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
             intcall_local_value entry p sz G tn s
End

Definition intcall_pending_def:
  intcall_pending env cenv caps G tn (s:venom_state) <=>
    EVERY (\(name,stack,op).
      ?entry off sz w.
        FLOOKUP env name = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type <= sz /\
        eval_operand op s = SOME w /\ op_taint tn op = {} /\
        if stack then
          32 <= sz /\
          (!b m. mem_word_at b m = w ==> val_in_memory entry.type entry.value b m)
        else
          ?p. op = Var p /\ intcall_local_value entry p sz G tn s) caps
End

(* This boundary is indexed by the actual callee parameters, not an
   existential entry ghost invented from the semantic state relation. *)
Definition intcall_entry_memory_def:
  intcall_entry_memory ce params src argbase PG tn (s:venom_state) <=>
    !i entry off sz. i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP src (FST (EL i params)) = SOME entry /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
      ?b n. EL (argbase+i) PG = SOME (b,n) /\
        b <= w2n (EL (argbase+i) s.vs_params) /\
        w2n (EL (argbase+i) s.vs_params) + sz <= b+n /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory entry.type entry.value
            (w2n (EL (argbase+i) s.vs_params)) m)
End

Definition intcall_entry_return_def:
  intcall_entry_return ce has_rb d PG (s:venom_state) <=>
    if has_rb then ?off sz bw capacity b n.
      ce.ce_return_buf = SOME (MemLoc off sz) /\ d = SOME (bw,capacity) /\
      HD s.vs_params = bw /\ HD PG = SOME (b,n) /\
      b <= w2n bw /\ w2n bw + capacity <= b+n
    else ce.ce_return_buf = NONE /\ d = NONE
End

(* Ownership is deliberately separate from correctness of the input value.
   Only outgoing fresh copies (and the fresh return buffer) satisfy it. *)
Definition intcall_owned_sites_def:
  intcall_owned_sites lo first ops G (s:venom_state) <=>
    EVERY (\op. !b n. op_prov G op = SOME (b,n) ==>
      lo <= b /\ b+n <= s.vs_alloca_next /\
      ?aid. first <= aid /\ FLOOKUP s.vs_allocas aid = SOME (b,n)) ops
End

Theorem intcall_materialize_empty:
  intcall_completed FEMPTY cenv G tn s /\
  intcall_pending env cenv [] G tn s
Proof
  simp[intcall_completed_def, intcall_pending_def]
QED

Theorem intcall_completed_bind:
  intcall_completed env cenv G tn s /\
  intcall_local_value entry p sz G tn s ==>
  intcall_completed (env |+ (name,entry))
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var p) sz)) G tn s
Proof
  rw[intcall_completed_def, FLOOKUP_UPDATE] >>
  Cases_on `name' = name` >> gvs[] >> metis_tac[]
QED

Theorem intcall_pending_drop_bind:
  intcall_pending src cenv caps G tn s /\
  EVERY (\(nm,stack,op). nm <> name) caps ==>
  intcall_pending src
    (cenv with ce_vars := cenv.ce_vars |+ (name,loc)) caps G tn s
Proof
  simp[intcall_pending_def, EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[]
QED

Theorem intcall_completed_ghost_inv:
  intcall_completed env cenv G tn s /\
  (!name. lookup_scopes name es.scopes = FLOOKUP env name) /\
  return_buf_ptr d cenv G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  ghost_inv d cenv cx es G tn s
Proof
  rw[ghost_inv_def] >>
  fs[intcall_completed_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[intcall_local_value_def] >> metis_tac[]
QED

Theorem intcall_entry_empty:
  intcall_entry_memory ce [] src argbase PG tn s /\
  (intcall_entry_return ce F d PG s <=> ce.ce_return_buf = NONE /\ d = NONE) /\
  intcall_owned_sites lo first [] G s
Proof
  simp[intcall_entry_memory_def, intcall_entry_return_def, intcall_owned_sites_def]
QED

Theorem intcall_entry_captured_pending:
  internal_args_rel ce params src argbase s.vs_params s.vs_alloca_next s.vs_memory /\
  intcall_entry_memory ce params src argbase PG tn s /\
  ce1.ce_vars = ce.ce_vars /\ LENGTH caps = LENGTH params /\
  (!i. i < LENGTH params ==> ?p.
    EL i caps = (FST (EL i params), SND (EL i params), Var p) /\
    lookup_var p t = SOME (EL (argbase+i) s.vs_params) /\
    FLOOKUP G' p = EL (argbase+i) PG /\ op_taint tn' (Var p) = {}) /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) ==>
  intcall_pending src ce1 caps G' tn' t
Proof
  strip_tac >> simp[intcall_pending_def, EVERY_EL] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH params ==> ?p. _` drule >> strip_tac >>
  qpat_x_assum `internal_args_rel _ _ _ _ _ _ _` mp_tac >>
  simp[internal_args_rel_def] >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH params ==> ?off sz entry. _` drule >> strip_tac >>
  simp[] >> qexists_tac `EL (argbase+i) s.vs_params` >>
  simp[eval_operand_def] >>
  Cases_on `SND (EL i params)` >> gvs[] >>
  simp[intcall_local_value_def] >>
  `val_footprint entry.type entry.value <= sz` by metis_tac[] >>
  qpat_x_assum `intcall_entry_memory _ _ _ _ _ _ _` mp_tac >>
  simp[intcall_entry_memory_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[ptr_covers_def] >> metis_tac[]
QED

Theorem intcall_entry_captured_return:
  intcall_entry_return ce has_rb d PG s /\
  (has_rb ==> ?p sz.
    ce1.ce_return_buf = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME (HD s.vs_params) /\
    FLOOKUP G p = HD PG /\ op_taint tn (Var p) = {}) ==>
  return_buf_ptr d ce1 G tn t
Proof
  Cases_on `has_rb` >>
  simp[intcall_entry_return_def] >> rpt strip_tac >>
  simp[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem intcall_owned_sites_below_disjoint:
  intcall_owned_sites lo first ops G s /\ MEM op ops /\
  op_prov G op = SOME (b,n) /\ off+sz <= lo ==>
  regions_disjoint off sz b n
Proof
  simp[intcall_owned_sites_def, EVERY_MEM, regions_disjoint_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> decide_tac
QED
