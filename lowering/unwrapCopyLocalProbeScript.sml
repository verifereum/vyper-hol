Theory unwrapCopyLocalProbe
Ancestors
  exprLowering venomExecSemantics venomState valueEncoding exprSim
  compileEnv vyperState vyperContext exprLoweringProps venomInst fcgDefs relation
  vyperStorage vyperLookupStorage context fragExec finite_map
Libs
  wordsLib

(* The old scope contains a local absent from the current source state. *)
Definition local_probe_start_def:
  local_probe_start = update_var "oldptr" 0w
    (sstore 32w 7w (init_venom_state "entry"))
End

Definition local_probe_env_def:
  local_probe_env = (ARB:compile_env) with <| ce_vars := FEMPTY |+ ("old", PtrVar (Var "oldptr") 32);
                       ce_var_type := (\n. NONE);
                       ce_module_vars := FEMPTY; ce_is_ctor := F;
                       ce_imm_alloca := NONE |>
End

Definition local_probe_source_def:
  local_probe_source = empty_state with
    <| accounts := local_probe_start.vs_accounts; outcomes := SOME [] |>
End

Definition local_probe_old_def:
  local_probe_old = local_probe_source with scopes :=
    [FEMPTY |+ ("old", <| assignable := T; type := BaseTV (UintT 256);
                          value := IntV 0 |>)]
End

Definition local_probe_insts_def:
  local_probe_insts = [mk_inst 0 ALLOCA [Lit 32w] ["%1"];
                       mk_inst 1 SLOAD [Lit 32w] ["%2"];
                       mk_inst 2 MSTORE [Var "%1"; Var "%2"] []]
End

Definition local_probe_func_def:
  local_probe_func = mk_raw_function "probe"
    [<| bb_label := "entry";
        bb_instructions := local_probe_insts ++ [mk_inst 3 STOP [] []] |>]
End

Definition local_probe_ctx_def:
  local_probe_ctx = mk_venom_context [local_probe_func] (SOME "probe")
End

Definition local_probe_sm_def:
  local_probe_sm = <| cs_next_var := 1; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition local_probe_value_def:
  local_probe_value = ArrayV (SArrayV [(0, IntV 7)])
End

Definition local_probe_sb_def:
  local_probe_sb = SND (unwrap_value local_probe_env
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Lit 32w) LocStorage)) local_probe_sm)
End

Theorem local_probe_compile:
  unwrap_value local_probe_env
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Lit 32w) LocStorage)) local_probe_sm =
    (Var "%1", local_probe_sb) /\
  local_probe_sb.cs_current_bb = "entry" /\
  local_probe_sb.cs_current_insts = local_probe_insts /\
  local_probe_sb.cs_next_id = 3 /\ local_probe_sb.cs_blocks = []
Proof
  EVAL_TAC
QED

Theorem local_probe_old_region:
  local_region local_probe_env local_probe_old.scopes local_probe_start "old" 0 32 /\
  ~dynarray_local local_probe_env "old"
Proof
  EVAL_TAC >> simp[]
QED

Theorem local_probe_no_calls:
  fn_directly_calls local_probe_ctx = (\x y. F)
Proof
  simp[FUN_EQ_THM, fn_directly_calls_def] >>
  rpt gen_tac >> EVAL_TAC >> Cases_on `x = "probe"` >> gvs[] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem local_probe_state_rel:
  state_rel local_probe_func local_probe_env empty_evaluation_context
    local_probe_source local_probe_start
Proof
  EVAL_TAC >> simp[]
QED

Theorem local_probe_stmt_state_rel:
  stmt_state_rel local_probe_ctx local_probe_func local_probe_env
    empty_evaluation_context local_probe_source local_probe_start
Proof
  simp[stmt_state_rel_def, local_probe_state_rel, immutable_alloca_sep_def,
       local_probe_env_def, alloca_room_def, local_probe_no_calls,
       Once TC_CASES1] >> EVAL_TAC >> simp[Once TC_CASES1] >>
  simp[Once TC_CASES1]
QED

Theorem local_probe_storage_holds:
  storage_holds empty_evaluation_context F
    (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Value local_probe_value) 32w
    local_probe_source
Proof
  EVAL_TAC >> simp[decode_value_def, slots_in_range_def] >> EVAL_TAC >> simp[]
QED

Theorem local_probe_vv_post:
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 1) ==>
  vv_post local_probe_ctx local_probe_func local_probe_env empty_evaluation_context e
    local_probe_old local_probe_sm local_probe_sm local_probe_start local_probe_source
    (Value local_probe_value)
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Lit 32w) LocStorage)) local_probe_start
Proof
  strip_tac >>
  simp[vv_post_def, local_probe_stmt_state_rel, vv_holds_def, mk_ptr_def,
       vv_at_def, local_probe_storage_holds] >> EVAL_TAC >> simp[] >>
  simp[decode_value_def, slots_in_range_def] >> EVAL_TAC >> simp[]
QED

Theorem local_probe_has_code:
  fn_has_code local_probe_sm local_probe_sb local_probe_func
Proof
  simp[fn_has_code_def, emitted_blocks_def, local_probe_compile,
       local_probe_sm_def, local_probe_func_def, mk_raw_function_def,
       lookup_block_def] >> EVAL_TAC >> simp[]
QED

Theorem local_probe_storage_antecedent:
  unwrap_value local_probe_env
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Lit 32w) LocStorage)) local_probe_sm = (Var "%1", local_probe_sb) /\
  ((mk_ptr (Lit 32w) LocStorage).ptr_location = LocStorage \/
   (mk_ptr (Lit 32w) LocStorage).ptr_location = LocTransient) /\
  ~is_word_type (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
  local_ptrs_reserved local_probe_env local_probe_sm /\
  local_probe_sm.cs_next_var <= local_probe_sm.cs_next_var /\
  local_probe_sm.cs_next_id <= local_probe_sm.cs_next_id /\
  fn_has_code local_probe_sm local_probe_sb local_probe_func /\
  fn_inst_ids_distinct local_probe_func /\
  (!x. (mk_ptr (Lit 32w) LocStorage).ptr_operand = Var x ==>
       not_fresh_at local_probe_sm x) /\
  (!tvt. evaluate_type (get_tenv empty_evaluation_context)
            (ArrayT (BaseT (UintT 256)) (Fixed 1)) = SOME tvt ==>
     type_memory_bytes local_probe_env (ArrayT (BaseT (UintT 256)) (Fixed 1)) =
       type_memory_size tvt /\ type_memory_size tvt < 2 ** 64)
Proof
  simp[local_probe_has_code, local_probe_compile, mk_ptr_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (simp[local_ptrs_reserved_def, local_probe_env_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      simp[not_fresh_at_def, local_probe_sm_def]) >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition local_probe_final_def:
  local_probe_final = (mstore 0 7w (update_var "%2" 7w (update_var "%1" 0w
    (local_probe_start with <| vs_allocas := FEMPTY |+ (0,(0,32));
                               vs_alloca_next := 32 |>)))) with vs_inst_idx := 3
End

Theorem local_probe_run:
  run_inst_seq local_probe_insts local_probe_start =
    OK (local_probe_final with vs_inst_idx := 0)
Proof
  EVAL_TAC
QED

Theorem local_probe_controls:
  ~local_probe_start.vs_halted /\
  local_probe_start.vs_current_bb = local_probe_sm.cs_current_bb /\
  local_probe_start.vs_inst_idx = LENGTH local_probe_sm.cs_current_insts
Proof
  EVAL_TAC
QED

Theorem local_probe_changed:
  mem_bytes_at 0 32 local_probe_start.vs_memory <> 
    mem_bytes_at 0 32 local_probe_final.vs_memory /\
  ~locals_kept local_probe_env local_probe_old local_probe_start local_probe_final
Proof
  reverse conj_tac
  >- (simp[locals_kept_def] >>
      qexistsl_tac [`"old"`, `0`, `32`, `0`, `32`] >>
      simp[local_probe_old_region] >> EVAL_TAC) >>
  EVAL_TAC
QED
