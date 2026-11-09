(* Reservation for the installed actual-entry environment. *)
Theory bodyIntCallActualEntryReservation
Ancestors
  bodyIntCallActualEntryReserved bodyIntCallActualEntryResource
  bodyIntCallActualEntryFields bodyIntCallBodyTrace intCallCallee
  compileEnv context emitHelper exprLoweringProps finite_map list rich_list
  arithmetic ASCIInumbers

Theorem internal_entry_installed_reserved:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  ALL_DISTINCT (MAP FST params) /\
  (!i. i < LENGTH params ==>
    ?off sz. FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz)) /\
  (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==>
    MEM n (MAP FST params)) /\
  (!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar p sz)) /\
  ce.ce_imm_alloca = NONE ==>
  local_ptrs_reserved (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) st1
Proof
  strip_tac >> Cases_on `ctor /\ imm_len > 0`
  >- suspend "constructor" >>
  drule compile_internal_function_entry_no_reservation >>
  disch_then (fn th => fs[th, comp_bind_def, comp_return_def]) >>
  pairarg_tac >> gvs[] >> PairCases_on `pr` >> gvs[] >>
  drule_all compile_internal_prologue_reserved >>
  simp[local_ptrs_reserved_def] >> metis_tac[]
QED

Resume internal_entry_installed_reserved[constructor]:
  gvs[] >> `0 < imm_len` by decide_tac >>
  drule_all compile_internal_function_entry_ctor_stages >> strip_tac >>
  PairCases_on `ar` >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = ((stage_ce,caps,rpc),sc)` >>
  rename1 `compile_fixed_region_with_id _ sc = ((rid,buf),sr)` >>
  rename1 `materialize_internal_params stage_ce caps sr = (ce2,sm)` >>
  `(case rt of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); comp_return () od
       else comp_return ()
     | NONE => comp_return ()) sm = ((),st1)` by
    (Cases_on `rt` >> Cases_on `ce.ce_returns_count > 0` >> fs[comp_return_def]) >>
  drule_all internal_ctor_entry_stage_shapes >> strip_tac >>
  `local_ptrs_reserved ce2 sm` by
    (drule_all internal_entry_prefix_caps_reserved >> simp[]) >>
  drule compile_fixed_region_with_id_result >> strip_tac >>
  `EVERY (\c. SND (SND c) <> Var (STRING #"%" (toString sc.cs_next_var))) caps` by
    (drule internal_entry_prefix_stages >> strip_tac >>
     drule compile_internal_param_decls_shape >> strip_tac >>
     qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     disch_tac >> gvs[] >> simp[EVERY_EL] >> rpt strip_tac >>
     gvs[toString_inj]) >>
  `local_ptrs_reserved
    (ce2 with ce_imm_alloca := SOME (Var (STRING #"%" (toString sc.cs_next_var)))) sm` by
    (irule materialize_internal_params_install_imm >>
     conj_tac >- simp[] >> qexistsl [`caps`, `stage_ce`, `sr`] >>
     simp[not_fresh_at_def, toString_inj]) >>
  drule_all local_ptrs_reserved_next_var >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Finalise internal_entry_installed_reserved
