(* Concrete parameter slots before the internal prologue. *)
Theory bodyIntCallArgMetadata
Ancestors
  bodyIntCallArgs bodyIntCallEntryEnv bodyIntCallTypeEval entryArgPtrs entryStateRel
  structFieldsProps compileVyper compileEnv exprSimAggregateLayout list

Theorem build_compile_env_param_slots:
  ALL_DISTINCT (MAP FST args) ==>
  EVERY (\a. ?off.
    FLOOKUP
      (build_compile_env tops vis mut name args ret ss use_trans).ce_vars
      (FST a) =
    SOME (MemLoc off
      (type_memory_bytes
        (build_compile_env tops vis mut name args ret ss use_trans) (SND a))))
    args
Proof
  strip_tac >>
  `EVERY (\a. ?off.
     FLOOKUP (FST (allocate_args
       (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY))
       (FST a) = SOME (MemLoc off
         (type_mem_bytes (get_struct_fields (make_struct_fields_map tops))
           (SND a)))) args` by
    metis_tac[allocate_args_lookup] >>
  ` (build_compile_env tops vis mut name args ret ss use_trans).ce_vars =
    FST (allocate_args (get_struct_fields (make_struct_fields_map tops))
      args 0 FEMPTY)` by
    (simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  simp[GSYM type_mem_bytes_type_memory_bytes,
       build_compile_env_ce_struct_fields]
QED

Theorem build_compile_env_param_slot_size:
  ALL_DISTINCT (MAP FST args) /\ MEM (n,ty) args /\
  FLOOKUP (build_compile_env tops vis mut name args ret ss use_trans).ce_vars n =
    SOME (MemLoc off sz) ==>
  sz = type_memory_bytes
    (build_compile_env tops vis mut name args ret ss use_trans) ty
Proof
  strip_tac >> drule build_compile_env_param_slots >>
  simp[EVERY_MEM] >> disch_then drule >> simp[] >>
  metis_tac[var_location_11, optionTheory.SOME_11]
QED

Theorem build_compile_env_param_slot_evaluated_size:
  ALL_DISTINCT (MAP FST args) /\ MEM (n,ty) args /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  evaluate_type (type_env tops) ty = SOME tv /\
  FLOOKUP (build_compile_env tops vis mut name args ret ss use_trans).ce_vars n =
    SOME (MemLoc off sz) ==>
  sz = type_memory_size tv
Proof
  strip_tac >> drule_all build_compile_env_param_slot_size >>
  drule_all build_compile_env_type_memory_bytes >> simp[]
QED

Theorem bind_arguments_indexed_memory_entry:
  bind_arguments tenv args vals = SOME env /\
  ALL_DISTINCT (MAP FST args) /\ i < LENGTH args ==>
  ?tv. evaluate_type tenv (SND (EL i args)) = SOME tv /\
       FLOOKUP env (FST (EL i args)) =
         SOME <|assignable := T; type := tv; value := EL i vals; popped := []|> /\
       val_wf tv (EL i vals)
Proof
  strip_tac >> drule_all bind_arguments_lookup_index >> strip_tac >>
  qexists_tac `tv` >> simp[] >> irule bind_arguments_memory_wf >> metis_tac[]
QED

Theorem build_compile_env_supported_param_slot_size:
  ALL_DISTINCT (MAP FST args) /\ MEM (n,ty) args /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_value_type tops ty /\ get_module_code cx NONE = SOME tops /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP (build_compile_env tops vis mut name args ret ss use_trans).ce_vars n =
    SOME (MemLoc off sz) ==>
  sz = type_memory_size tv
Proof
  strip_tac >> drule_all supported_value_evaluate_type_get_tenv >>
  strip_tac >> irule build_compile_env_param_slot_evaluated_size >>
  metis_tac[]
QED

Theorem internal_arg_indexed_slot_capacity:
  bind_arguments (get_tenv cx) args vals = SOME env /\
  ALL_DISTINCT (MAP FST args) /\ i < LENGTH args /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  EVERY (supported_value_type tops o SND) args /\
  get_module_code cx NONE = SOME tops /\
  expr_sim_inv caller cx src_env src_es /\
  MAP expr_type es = MAP SND args /\
  FLOOKUP (build_compile_env tops vis mut name args ret ss use_trans).ce_vars
    (FST (EL i args)) = SOME (MemLoc off sz) ==>
  ?tv. evaluate_type (get_tenv cx) (SND (EL i args)) = SOME tv /\
       FLOOKUP env (FST (EL i args)) =
         SOME <|assignable := T; type := tv; value := EL i vals; popped := []|> /\
       val_wf tv (EL i vals) /\
       sz = type_memory_size tv /\
       sz = type_memory_bytes caller (expr_type (EL i es)) /\
       sz <= MAX 32 (type_memory_bytes caller (expr_type (EL i es)))
Proof
  strip_tac >> drule_all bind_arguments_indexed_memory_entry >> strip_tac >>
  `MEM (EL i args) args` by simp[EL_MEM] >>
  `MEM (FST (EL i args), SND (EL i args)) args` by simp[] >>
  `supported_value_type tops (SND (EL i args))` by
    (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `sz = type_memory_size tv` by
    (irule build_compile_env_supported_param_slot_size >> metis_tac[]) >>
  `i < LENGTH es` by
    metis_tac[LENGTH_MAP] >>
  `expr_type (EL i es) = SND (EL i args)` by
    metis_tac[EL_MAP] >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  qexists_tac `tv` >> simp[]
QED
