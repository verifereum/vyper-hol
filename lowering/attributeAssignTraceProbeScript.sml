Theory attributeAssignTraceProbe
Ancestors
  stmtSimAssignStorage vyperStorageTrace vyperStorageBackend
  vyperInterpreter vyperState vyperValue list vyperContext vyperAST
  exprSimHyps vyperTypeInvariants vyperTypeSystem finite_map compileEnv
Libs
  monadsyntax

(* Operational evidence only: the global source/compiler invariants are
   deliberately not assumed to be inhabited by this conditional probe. *)
Theorem literal_field_trace_mismatch:
  es.storage_trace = [] /\
  eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld) es =
    (INL (StoragePlace tr a ftv),
     es with storage_trace := [StorageRoot tr slot (StructTV fs)]) /\
  write_storage_slot cx tr a ftv (evaluate_literal (IntL 0)) es = (res,out) ==>
  eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld))
      (Literal ann (IntL 0))) es =
    (res,out with storage_trace := [StorageRoot tr slot (StructTV fs)] ++ out.storage_trace) /\
  (out with storage_trace := [StorageRoot tr slot (StructTV fs)] ++ out.storage_trace) <> out
Proof
  strip_tac >>
  `write_storage_slot cx tr a ftv (evaluate_literal (IntL 0))
     (es with storage_trace := [StorageRoot tr slot (StructTV fs)]) =
     (res,out with storage_trace := [StorageRoot tr slot (StructTV fs)] ++ out.storage_trace)` by
    (`storage_trace_frame (write_storage_slot cx tr a ftv (evaluate_literal (IntL 0)))`
       by simp[storage_trace_frame_write_storage_slot] >>
     drule_all storage_trace_frame_result >>
     disch_then (qspec_then `[StorageRoot tr slot (StructTV fs)]` mp_tac) >> simp[]) >>
  conj_tac
  >- (simp[Once evaluate_def, bind_def, Once evaluate_def, return_def,
           read_result_def, write_place_def]) >>
  strip_tac >>
  pop_assum (mp_tac o AP_TERM ``\s. LENGTH s.storage_trace``) >>
  simp[]
QED

Definition probe_tops_def:
  probe_tops = [StructDecl "P" [("f", BaseT (UintT 256))];
    VariableDecl Private Storage "x" (StructT (NONE,"P")) (SOME 0)]
End

Definition probe_cx_def:
  probe_cx = empty_evaluation_context with
    <|stk := [(NONE,"probe")]; sources := [(0w,[(NONE,probe_tops)])];
      layouts := [(0w, ([( (NONE,"x"),0)], []))]|>
End

Definition probe_es_def:
  probe_es = empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>
End

Theorem probe_target:
  eval_target_place probe_cx
    (AttributeTarget (TopLevelNameTarget (NONE,"x")) "f") probe_es =
    (INL (StoragePlace F 0w (BaseTV (UintT 256))),
     probe_es with storage_trace :=
       [StorageRoot F 0 (StructTV [("f",BaseTV (UintT 256))])])
Proof
  EVAL_TAC >> simp[FUNION_FEMPTY_2, FLOOKUP_UPDATE, DRESTRICT_FUPDATE] >> EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[wordsTheory.WORD_ADD_0]
QED

Definition probe_env_def:
  probe_env : typing_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY |+ ((NONE,"x"),Type (StructT (NONE,"P")));
    type_defs := get_tenv probe_cx; fn_sigs := FEMPTY;
    flag_members := FEMPTY; event_fields := FEMPTY |>
End

Theorem probe_context_typed:
  context_well_typed probe_cx
Proof
  EVAL_TAC
QED

Theorem probe_env_context:
  env_context_consistent probe_env probe_cx
Proof
  simp[env_context_consistent_def, probe_env_def] >>
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def]
QED

Theorem probe_env_scopes:
  env_scopes_consistent probe_env probe_cx probe_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem probe_env_immutables:
  env_immutables_consistent probe_env probe_cx probe_es
Proof
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  gvs[find_var_decl_by_name_def]
QED

Theorem probe_functions_typed:
  functions_well_typed probe_cx
Proof
  simp[functions_well_typed_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> simp[probe_cx_def, empty_evaluation_context_def,
    empty_call_txn_def, get_module_code_def] >>
  rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  gvs[probe_tops_def, lookup_callable_function_def, lookup_function_def]
QED

Theorem probe_region:
  declared_storage_region probe_cx mid n subs =
    if mid = NONE /\ n = "x" /\ subs = [] then
      SOME (F,0w,StructTV [("f",BaseTV (UintT 256))])
    else NONE
Proof
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def,
    probe_cx_def, empty_evaluation_context_def, empty_call_txn_def,
    get_module_code_def] >>
  rw[] >> EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  simp[FUNION_FEMPTY_2, FLOOKUP_UPDATE, DRESTRICT_FUPDATE] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem probe_storage_info:
  storage_var_info probe_cx mid n =
    if mid = NONE /\ n = "x" then
      SOME (F,0,StructTV [("f",BaseTV (UintT 256))]) else NONE
Proof
  simp[vyperLookupStorageTheory.storage_var_info_def,
    probe_cx_def, empty_evaluation_context_def, empty_call_txn_def,
    get_module_code_def] >>
  rw[] >> EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  simp[FUNION_FEMPTY_2, FLOOKUP_UPDATE, DRESTRICT_FUPDATE] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem probe_layout_safe:
  storage_layout_safe probe_cx
Proof
  simp[vyperStorageLayoutSafetyTheory.storage_layout_safe_def,
    vyperLookupStorageTheory.well_formed_layout_def, probe_storage_info,
    probe_region, vyperStorageLayoutSafetyTheory.nonreentrant_slot_separated_def,
    probe_cx_def, empty_evaluation_context_def] >>
  rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem probe_storage_wf:
  contract_storage_well_formed probe_cx probe_es
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
    vyperLookupStorageTheory.well_formed_storage_def,
    vyperLookupStorageTheory.storage_var_in_range_def,
    probe_storage_info, probe_region] >>
  rw[AllCaseEqs()] >> gvs[] >>
  simp[vyperLookupStorageTheory.slots_in_range_def,
       vyperLookupStorageTheory.word_slot_canonical_def] >>
  EVAL_TAC >>
  `w2n (storage 0w) < 2 ** 256` by
    (qspec_then `storage 0w : bytes32` mp_tac wordsTheory.w2n_lt >>
     simp[wordsTheory.dimword_def]) >>
  qpat_x_assum `w2n _ < _` mp_tac >>
  CONV_TAC (LAND_CONV EVAL) >>
  simp[wordsTheory.n2w_w2n]
QED

Definition probe_cenv_def:
  probe_cenv = (ARB : compile_env) with
    <|ce_struct_fields := FEMPTY |+ ("P",[("f",BaseT (UintT 256),32)]);
      ce_hashmap_info := (\nsid. NONE);
      ce_module_var_type := (\nsid. if nsid = (NONE,"x") then
        SOME (StructT (NONE,"P")) else NONE)|>
End

Theorem probe_inv:
  expr_sim_inv probe_cenv probe_cx probe_env probe_es
Proof
  simp[expr_sim_inv_def, env_consistent_def, probe_env_context,
    probe_env_scopes, probe_env_immutables, probe_context_typed,
    probe_functions_typed, probe_storage_wf, probe_layout_safe] >>
  EVAL_TAC >> rw[AllCaseEqs()] >> gvs[] >> EVAL_TAC >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs(), lookup_flag_def,
      find_var_decl_by_name_def, nsid_to_string_def,
      vyperValueTheory.evaluate_type_def] >> EVAL_TAC >>
  qexistsl [`(NONE,"P")`, `[("f",BaseT (UintT 256))]`] >> EVAL_TAC
QED

Theorem probe_body_pre:
  expr_body_pre probe_cenv probe_cx probe_env
    (Literal (BaseT (UintT 256)) (IntL 0)) probe_es
Proof
  simp[expr_body_pre_def, probe_inv] >>
  rpt conj_tac >> EVAL_TAC >> simp[] >>
  qexists `[]` >> EVAL_TAC >>
  simp[] >> simp[relationTheory.irreflexive_def] >> rpt strip_tac >>
  drule relationTheory.TC_CASES1_E >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Definition probe_write_out_def:
  probe_write_out = SND
    (write_storage_slot probe_cx F 0w (BaseTV (UintT 256)) (IntV 0) probe_es)
End

Theorem probe_write:
  write_storage_slot probe_cx F 0w (BaseTV (UintT 256)) (IntV 0) probe_es =
    (INL (),probe_write_out)
Proof
  simp[write_storage_slot_eq, probe_write_out_def] >> EVAL_TAC >> simp[]
QED

Definition probe_out_def:
  probe_out = probe_write_out with storage_trace :=
    [StorageRoot F 0 (StructTV [("f",BaseTV (UintT 256))])] ++ probe_write_out.storage_trace
End

Theorem probe_run:
  eval_stmt probe_cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (NONE,"x")) "f"))
      (Literal (BaseT (UintT 256)) (IntL 0))) probe_es = (INL (),probe_out)
Proof
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, return_def, probe_target,
    read_result_def, write_place_def, probe_out_def] >>
  `storage_trace_frame (write_storage_slot probe_cx F 0w (BaseTV (UintT 256)) (IntV 0))`
    by simp[storage_trace_frame_write_storage_slot] >>
  mp_tac probe_write >> disch_then (mp_then Any mp_tac storage_trace_frame_result) >>
  simp[] >> disch_then (qspec_then
    `[StorageRoot F 0 (StructTV [("f",BaseTV (UintT 256))])]` mp_tac) >>
  simp[probe_es_def, empty_state_def, vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem probe_metadata:
  get_module_code probe_cx NONE = SOME probe_tops /\
  find_var_decl_by_name "x" probe_tops =
    SOME (StorageVarDecl F (StructT (NONE,"P")), "x") /\
  lookup_var_slot_from_layout probe_cx F NONE "x" = SOME 0 /\
  ALOOKUP (get_struct_fields probe_cenv.ce_struct_fields
    (nsid_to_string (NONE,"P"))) "f" = SOME (BaseT (UintT 256),32) /\
  struct_field_offset_slots (get_struct_fields probe_cenv.ce_struct_fields
    (nsid_to_string (NONE,"P"))) "f" = 0 /\
  evaluate_type (get_tenv probe_cx) (BaseT (UintT 256)) = SOME (BaseTV (UintT 256))
Proof
  EVAL_TAC
QED

Theorem probe_rhs:
  (do result <- eval_expr probe_cx (Literal (BaseT (UintT 256)) (IntL 0));
      read_result probe_cx result od) probe_es = (INL (IntV 0),probe_es)
Proof
  simp[Once evaluate_def, bind_def, return_def, read_result_def,
    vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem probe_out_different:
  probe_out <> probe_write_out
Proof
  simp[probe_out_def] >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``\s. LENGTH s.storage_trace``) >> simp[]
QED

Theorem frozen_assign_attr_storage_source_false:
  ~(!cx cenv env lctx src id fld sid fty fsz e es res es' ts tr id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv /\
                 encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
                 write_storage_slot cx tr
                   (n2w slot + n2w (struct_field_offset_slots
                      (get_struct_fields cenv.ce_struct_fields
                         (nsid_to_string sid)) fld))
                   ftv v es1 = (res, es') /\
                 !u st.
                   storage_dead cx tr
                     (update_storage
                        (n2w slot + n2w (struct_field_offset_slots
                           (get_struct_fields cenv.ce_struct_fields
                              (nsid_to_string sid)) fld)) u st) =
                   storage_dead cx tr st))
Proof
  disch_then (qspecl_then
    [`probe_cx`, `probe_cenv`, `probe_env`, `ARB`, `NONE`, `"x"`, `"f"`,
     `(NONE,"P")`, `BaseT (UintT 256)`, `32`,
     `Literal (BaseT (UintT 256)) (IntL 0)`, `probe_es`, `INL ()`,
     `probe_out`, `probe_tops`, `F`, `"x"`, `0`] mp_tac) >>
  simp[probe_run, probe_body_pre, probe_metadata, stmtSimTheory.stmt_res_ok_def,
    is_word_type_def, expr_type_def, probe_rhs] >>
  simp[wordsTheory.WORD_ADD_0, probe_write, probe_out_different,
    EQ_SYM_EQ]
QED
