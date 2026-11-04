Theory fnFrameBoundaryEntryParams
Ancestors
  frameRel frameViewFacts stackPlanGen stackPlanTypes stackModel
  callLayoutDefs venomExecSemantics venomState venomInst list rich_list
  arithmetic words unitShapeDefs venomWf phiBlock cfgHelpers
  livenessAnalysisProps cfgAnalysisProps

(* Installing the symbolic parameter names emits no code. *)
Theorem parameter_stack_fold:
  !insts ps.
    FOLDL (\s inst. s with ps_stack :=
      stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps insts =
    ps with ps_stack := ps.ps_stack ++
      MAP (\inst. Var (HD inst.inst_outputs)) insts
Proof
  Induct >> simp[stack_push_def, SNOC_APPEND] >>
  rpt gen_tac >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* A compact diagnostic family: canonical shape does not bound its length. *)
Theorem canonical_param_genlist:
  !n k names.
    canonical_entry_params_from k
      (GENLIST (\j. mk_inst (k+j) PARAM [Lit (n2w (k+j))]
                       [names (k+j)]) n)
Proof
  Induct >> simp[GENLIST_CONS, canonical_entry_params_from_def,
                param_inst_at_def, mk_inst_def, is_param_opcode_def,
                combinTheory.o_DEF, ADD_CLAUSES] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`SUC k`, `names`] mp_tac) >>
  simp[mk_inst_def, ADD_CLAUSES] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `GENLIST f n` >>
  qmatch_goalsub_abbrev_tac `GENLIST g n` >>
  `f = g` by simp[Abbr `f`, Abbr `g`, FUN_EQ_THM, ADD_COMM] >>
  gvs[]
QED

(* Closed arithmetic discriminator only, NOT a counterexample to the task. *)
Theorem param_index_wrap_discriminator:
  w2n (n2w (dimword (:256)) : 256 word) = 0 /\
  dimword (:256) <> 0
Proof
  simp[w2n_n2w, dimword_def] >> EVAL_TAC
QED

Theorem wrapped_param_reads_first:
  !s id out.
    s.vs_params <> [] ==>
    step_inst_base
      (mk_inst id PARAM [Lit (n2w (dimword (:256)))] [out]) s =
    OK (update_var out (HD s.vs_params) s)
Proof
  rpt gen_tac >> Cases_on `s.vs_params` >>
  simp[step_inst_base_def, mk_inst_def, w2n_n2w]
QED

(* Compact straight-line family used only by the index-range probe. *)
Definition entry_probe_name_def:
  entry_probe_name i = REPLICATE i #"p"
End

Definition entry_probe_params_def:
  entry_probe_params n = GENLIST
    (\i. mk_inst i PARAM [Lit (n2w i)] [entry_probe_name i]) n
End

Definition entry_probe_sink_def:
  entry_probe_sink n = mk_inst n SINK
    (MAP (\i. Var (entry_probe_name i)) (GENLIST I n)) []
End

Definition entry_probe_block_def:
  entry_probe_block n = <|bb_label := "entry";
    bb_instructions := entry_probe_params n ++ [entry_probe_sink n]|>
End

Definition entry_probe_fn_def:
  entry_probe_fn n = <|fn_name := "entry_test";
    fn_blocks := [entry_probe_block n];
    fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                    ica_user_return_count := NONE|>;
    fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
    fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE|>
End

Theorem entry_probe_name_inj[simp]:
  !i j. entry_probe_name i = entry_probe_name j <=> i = j
Proof
  rpt gen_tac >> eq_tac >- (disch_then (mp_tac o AP_TERM ``LENGTH : string -> num``) >>
    simp[entry_probe_name_def]) >> simp[]
QED

Theorem get_params_prefix:
  !prefix body.
    EVERY (\i. is_param_opcode i.inst_opcode) prefix /\
    no_param_insts body ==>
    get_params (prefix ++ body) = prefix
Proof
  Induct
  >- (qx_gen_tac `suffix` >> Cases_on `suffix` >>
      simp[get_params_def, no_param_insts_def]) >>
  simp[get_params_def]
QED

Theorem entry_probe_get_params:
  get_params (entry_probe_block n).bb_instructions = entry_probe_params n
Proof
  simp[entry_probe_block_def] >> irule get_params_prefix >>
  simp[entry_probe_params_def, EVERY_GENLIST, entry_probe_sink_def,
       mk_inst_def, no_param_insts_def, is_param_opcode_def]
QED

Theorem entry_probe_no_retpc:
  ~fn_has_retpc (entry_probe_fn n)
Proof
  simp[fn_has_retpc_def, entry_probe_fn_def, entry_probe_get_params,
       entry_probe_params_def, EVERY_GENLIST, EXISTS_MEM, MEM_GENLIST,
       mk_inst_def] >> rpt strip_tac >> gvs[]
QED

(* The proposed SINK witness is rejected by the codegen input contract. *)
Theorem entry_probe_sink_not_ready:
  !n. ~codegen_ready_fn (entry_probe_fn n)
Proof
  simp[codegen_ready_fn_def, entry_probe_fn_def, entry_probe_block_def,
       EVERY_APPEND, codegen_ready_inst_def, entry_probe_sink_def,
       mk_inst_def, is_pre_codegen_opcode_def]
QED

Definition entry_ret_probe_def:
  entry_ret_probe = (entry_probe_fn 0) with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
       [mk_inst 0 PARAM [Lit 0w] ["p"];
        mk_inst 1 RETPC_PARAM [Lit 1w] ["retpc"];
        mk_inst 2 RET [Var "p"; Var "retpc"] []]|>]
End

Theorem entry_ret_probe_opcodes_ready:
  EVERY codegen_ready_inst
    (HD entry_ret_probe.fn_blocks).bb_instructions
Proof
  EVAL_TAC
QED

Theorem entry_ret_probe_ready:
  codegen_ready_fn entry_ret_probe
Proof
  simp[codegen_ready_fn_def] >> rpt conj_tac >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[] >> dsimp[]
  >- (qexistsl [`0`, `2`] >> simp[] >> qx_gen_tac `path` >>
      Cases_on `path` >> simp[]) >>
  qexistsl [`1`, `2`] >> simp[] >> qx_gen_tac `path` >>
  Cases_on `path` >> simp[]
QED

Theorem entry_ret_probe_opaque_vars:
  !x. (retpc_var entry_ret_probe x <=> x = "retpc") /\
      ~gas_var entry_ret_probe x
Proof
  gen_tac >> simp[retpc_var_def, gas_var_def] >>
  once_rewrite_tac[copy_phi_var_cases] >>
  simp[entry_ret_probe_def, entry_probe_fn_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       MEM_FLAT, MEM_MAP] >>
  dsimp[] >> rpt strip_tac >> disj1_tac >> rpt strip_tac >> gvs[]
QED

Theorem entry_ret_probe_opaque_ok:
  opaque_use_ok entry_ret_probe
Proof
  simp[opaque_use_ok_def, entry_ret_probe_opaque_vars] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  simp[retpc_use_ok_def] >> qexists_tac `[Var "p"]` >> simp[]
QED

Theorem entry_ret_probe_reachable:
  reachable_fn entry_ret_probe = entry_ret_probe
Proof
  irule reachable_fn_single_block >>
  simp[entry_ret_probe_def, entry_probe_fn_def, mk_inst_def]
QED

Theorem entry_ret_probe_retpc_shape:
  retpc_shape_ok entry_ret_probe
Proof
  simp[retpc_shape_ok_def, entry_ret_probe_reachable,
       entry_ret_probe_opaque_vars] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  qexistsl [`[Var "p"]`, `"retpc"`] >>
  simp[entry_ret_probe_opaque_vars]
QED

Theorem entry_ret_probe_plan:
  !ps. ps.ps_stack = [] ==>
    prepare_params_plan (liveness_analyze entry_ret_probe) entry_ret_probe ps =
    ([], ps with ps_stack := [Var "p"; Var "retpc"])
Proof
  rpt strip_tac >> EVAL_TAC >> gvs[operand_to_string_def] >> EVAL_TAC
QED

Definition entry_bind_pairs_def:
  entry_bind_pairs pairs s =
    FOLDL (\st (x,v). update_var x v st) s pairs
End

Theorem entry_bind_pairs_normal:
  !pairs s. entry_bind_pairs pairs s =
    s with vs_vars := FOLDL (\m (x,v). m |+ (x,v)) s.vs_vars pairs
Proof
  Induct >- simp[entry_bind_pairs_def] >>
  Cases >> rpt gen_tac >>
  simp[entry_bind_pairs_def, update_var_def] >>
  first_x_assum (qspec_then `s with vs_vars := s.vs_vars |+ (q,r)` mp_tac) >>
  simp[entry_bind_pairs_def, update_var_def]
QED

Theorem entry_bind_pairs_lookup:
  !pairs s x v.
    ALL_DISTINCT (MAP FST pairs) /\ MEM (x,v) pairs ==>
    FLOOKUP (entry_bind_pairs pairs s).vs_vars x = SOME v
Proof
  rpt strip_tac >>
  simp[entry_bind_pairs_normal, finite_mapTheory.fupdate_list_foldl,
       alistTheory.FLOOKUP_FUPDATE_LIST] >>
  `ALOOKUP (REVERSE pairs) x = SOME v` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
  simp[]
QED

Theorem entry_bind_pairs_preserves:
  (entry_bind_pairs pairs s).vs_params = s.vs_params /\
  (entry_bind_pairs pairs s).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[entry_bind_pairs_normal]
QED

Theorem entry_bind_pairs_empty[simp]:
  entry_bind_pairs [] s = s
Proof
  simp[entry_bind_pairs_def]
QED

Theorem entry_bind_pairs_singleton[simp]:
  entry_bind_pairs [(x,v)] s = update_var x v s
Proof
  simp[entry_bind_pairs_def]
QED

Definition entry_param_shape_def:
  entry_param_shape s inst <=>
    ?idx out. inst.inst_operands = [Lit idx] /\
      inst.inst_outputs = [out] /\
      (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/
       inst.inst_opcode = RETPC_PARAM) /\
      (inst.inst_opcode <> RETPC_PARAM ==> w2n idx < LENGTH s.vs_params)
End

Definition entry_param_pairs_def:
  entry_param_pairs s insts = MAP (\inst.
    (HD inst.inst_outputs,
     if inst.inst_opcode = RETPC_PARAM then s.vs_return_pc_token
     else EL (w2n (case HD inst.inst_operands of Lit idx => idx | _ => 0w)) s.vs_params)) insts
End

Theorem entry_param_step:
  entry_param_shape s inst ==>
  step_inst fuel ctx inst s =
    OK (entry_bind_pairs (entry_param_pairs s [inst]) s)
Proof
  rw[entry_param_shape_def] >>
  simp[step_inst_non_invoke, step_inst_base_def,
       entry_param_pairs_def, update_var_def]
QED

Theorem entry_param_run_insts:
  !insts s. EVERY (entry_param_shape s) insts ==>
    run_insts fuel ctx insts s =
      OK (entry_bind_pairs (entry_param_pairs s insts) s)
Proof
  Induct >- simp[analysisSimDefsTheory.run_insts_def,
                 entry_param_pairs_def] >>
  rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  drule entry_param_step >> disch_tac >>
  simp[Once analysisSimDefsTheory.run_insts_def] >>
  first_x_assum (qspec_then
    `entry_bind_pairs (entry_param_pairs s [h]) s` mp_tac) >>
  simp[entry_param_shape_def, entry_bind_pairs_preserves] >>
  simp[entry_param_pairs_def, entry_bind_pairs_def,
       entry_bind_pairs_normal, update_var_def] >>
  disch_then irule >> gvs[EVERY_MEM, entry_param_shape_def]
QED

Theorem entry_param_skip_prefix:
  EVERY (entry_param_shape s) insts /\
  bb.bb_instructions = insts ++ suffix ==>
  exec_block fuel ctx bb (s with vs_inst_idx := 0) =
  exec_block fuel ctx bb
    ((entry_bind_pairs (entry_param_pairs s insts) s) with
      vs_inst_idx := LENGTH insts)
Proof
  strip_tac >>
  qspec_then `insts` mp_tac phiBlockTheory.exec_block_skip_prefix_non_invoke >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `0`] mp_tac) >>
  simp[ADD_CLAUSES] >> disch_then irule >>
  simp[entry_param_run_insts, EL_APPEND_EQN] >>
  gvs[EVERY_MEM, entry_param_shape_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[is_terminator_def]
QED

Definition entry_ret_family_def:
  entry_ret_family n = (entry_probe_fn 0) with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
      entry_probe_params n ++
      [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"];
       mk_inst (SUC n) RET
         (MAP (\i. Var (entry_probe_name i)) (GENLIST I n) ++
          [Var "retpc"]) []]|>]
End

Theorem entry_ret_family_opcodes_ready:
  EVERY codegen_ready_inst
    (HD (entry_ret_family n).fn_blocks).bb_instructions
Proof
  simp[entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       EVERY_APPEND, EVERY_GENLIST, codegen_ready_inst_def,
       mk_inst_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
       is_unlowered_internal_call_opcode_def, dead_stack_marker_def,
       MEM_MAP]
QED

Theorem entry_ret_family_small:
  (HD (entry_ret_family 1).fn_blocks).bb_instructions =
    [mk_inst 0 PARAM [Lit 0w] [""];
     mk_inst 1 RETPC_PARAM [Lit 1w] ["retpc"];
     mk_inst 2 RET [Var ""; Var "retpc"] []]
Proof
  EVAL_TAC
QED

Theorem entry_ret_family_get_params:
  get_params (HD (entry_ret_family n).fn_blocks).bb_instructions =
    entry_probe_params n ++
      [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]]
Proof
  qspec_then `entry_probe_params n ++
    [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]]` mp_tac get_params_prefix >>
  disch_then (qspec_then `[mk_inst (SUC n) RET
    (MAP (\i. Var (entry_probe_name i)) (GENLIST I n) ++ [Var "retpc"]) []]` mp_tac) >>
  simp[entry_ret_family_def, entry_probe_params_def, EVERY_APPEND,
       EVERY_GENLIST, mk_inst_def, no_param_insts_def, is_param_opcode_def]
QED

Theorem entry_ret_family_has_retpc:
  fn_has_retpc (entry_ret_family n)
Proof
  simp[fn_has_retpc_def, entry_ret_family_get_params,
       EXISTS_APPEND, mk_inst_def]
QED

Theorem entry_probe_name_not_retpc[simp]:
  entry_probe_name i <> "retpc"
Proof
  Cases_on `i` >> simp[entry_probe_name_def, REPLICATE]
QED

Theorem entry_ret_family_reachable:
  reachable_fn (entry_ret_family n) = entry_ret_family n
Proof
  irule reachable_fn_single_block >>
  simp[entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       EVERY_APPEND, EVERY_GENLIST, mk_inst_def]
QED

Theorem entry_ret_family_opaque_vars:
  !x. (retpc_var (entry_ret_family n) x <=> x = "retpc") /\
      ~gas_var (entry_ret_family n) x
Proof
  gen_tac >> simp[retpc_var_def, gas_var_def] >>
  once_rewrite_tac[copy_phi_var_cases] >>
  simp[entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       MEM_FLAT, MEM_MAP, MEM_GENLIST] >>
  dsimp[] >> rpt strip_tac >> disj1_tac >> rpt strip_tac >> gvs[]
QED

Theorem entry_ret_family_opaque_ok:
  opaque_use_ok (entry_ret_family n)
Proof
  simp[opaque_use_ok_def, entry_ret_family_opaque_vars,
       entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       fn_insts_def, fn_insts_blocks_def, MEM_FLAT, MEM_MAP, MEM_GENLIST,
       mk_inst_def] >> rpt strip_tac >> gvs[] >>
  simp[retpc_use_ok_def, MEM_MAP] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_ret_family_retpc_shape:
  retpc_shape_ok (entry_ret_family n)
Proof
  simp[retpc_shape_ok_def, entry_ret_family_reachable,
       entry_ret_family_opaque_vars] >>
  simp[entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       fn_insts_def, fn_insts_blocks_def, MEM_FLAT, MEM_MAP, MEM_GENLIST,
       EVERY_APPEND, EVERY_GENLIST, mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl [`MAP (\i. Var (entry_probe_name i)) (GENLIST I n)`, `"retpc"`] >>
  simp[entry_ret_family_opaque_vars]
QED

Theorem entry_ret_family_inst_wf:
  fn_inst_wf (entry_ret_family n)
Proof
  simp[fn_inst_wf_def, entry_ret_family_def, entry_probe_params_def,
       MEM_GENLIST, mk_inst_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_wf_def, mk_inst_def]
QED

Theorem entry_ret_family_ssa:
  ssa_form (entry_ret_family n)
Proof
  `!m. FLAT (GENLIST (\i. [entry_probe_name i]) m) =
        GENLIST entry_probe_name m` by
    (Induct >> simp[GENLIST, FLAT_SNOC]) >>
  simp[ssa_form_def, entry_ret_family_def, entry_probe_params_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       MAP_GENLIST, combinTheory.o_DEF, ALL_DISTINCT_APPEND,
       ALL_DISTINCT_GENLIST, MEM_GENLIST]
QED

Theorem entry_ret_family_single_use:
  single_use_form (entry_ret_family n)
Proof
  simp[passSharedDefsTheory.single_use_form_def,
       passSharedDefsTheory.var_use_count_block_def,
       entry_ret_family_def, entry_probe_params_def, FILTER_APPEND,
       passSharedDefsTheory.sue_count_exempt_def, is_param_opcode_def,
       mk_inst_def, FILTER_EQ_NIL, EVERY_GENLIST] >>
  gen_tac >> qmatch_goalsub_abbrev_tac `FILTER p xs` >>
  `FILTER p xs = []` by
    simp[FILTER_EQ_NIL, Abbr `p`, Abbr `xs`, EVERY_GENLIST,
         is_param_opcode_def] >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem entry_ret_family_wf:
  wf_function (entry_ret_family n)
Proof
  simp[wf_function_def, fn_labels_def, fn_has_entry_def,
       fn_succs_closed_def, fn_inst_ids_distinct_def,
       entry_ret_family_def, entry_probe_params_def,
       bb_succs_def, mk_inst_def, MAP_GENLIST, combinTheory.o_DEF,
       ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST, MEM_GENLIST] >>
  simp[bb_well_formed_def, EL_APPEND_EQN, EL_GENLIST, is_terminator_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> Cases_on `i < n` >> gvs[is_terminator_def] >>
      Cases_on `i = n` >> gvs[is_terminator_def] >>
      `i = n + 1` by decide_tac >> gvs[is_terminator_def])
  >- (rpt strip_tac >> Cases_on `j < n` >> gvs[] >>
      Cases_on `j = n` >> gvs[] >>
      `j = n + 1` by decide_tac >> gvs[]) >>
  Cases_on `n` >>
  simp[GENLIST_CONS, LAST_DEF, LAST_APPEND, get_successors_def,
       is_terminator_def, FILTER_EQ_NIL, EVERY_GENLIST,
       MAP_GENLIST, combinTheory.o_DEF, get_label_def,
       MEM_MAP, MEM_FILTER, MEM_GENLIST] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_ret_family_canonical:
  canonical_param_prefix (entry_ret_family n)
Proof
  `!m k. param_insts_from k
    (GENLIST (\i. mk_inst (k+i) PARAM [Lit (n2w (k+i))]
       [entry_probe_name (k+i)]) m)` by
    (Induct >> simp[GENLIST_CONS, param_insts_from_def, param_inst_at_def,
                   mk_inst_def, is_param_opcode_def, combinTheory.o_DEF] >>
     gen_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
     simp[mk_inst_def, ADD_CLAUSES] >> disch_tac >>
     qmatch_asmsub_abbrev_tac `GENLIST f m` >>
     qmatch_goalsub_abbrev_tac `GENLIST g m` >>
     `f = g` by simp[Abbr `f`, Abbr `g`, FUN_EQ_THM, ADD_COMM] >>
     gvs[]) >>
  simp[canonical_param_prefix_def, entry_ret_family_def] >>
  irule canonical_entry_params_from_prepend_users >>
  simp[entry_probe_params_def, EVERY_GENLIST,
       canonical_entry_params_from_def, param_inst_at_def,
       no_param_insts_def, mk_inst_def, is_param_opcode_def] >>
  first_x_assum (qspecl_then [`n`, `0`] mp_tac) >> simp[mk_inst_def]
QED

Theorem entry_ret_family_entry_dominates:
  fn_dominates (entry_ret_family n) "entry" "entry"
Proof
  simp[fn_dominates_def, fn_reachable_def, fn_entry_label_def,
       entry_block_def, entry_ret_family_def, relationTheory.RTC_REFL] >>
  rpt strip_tac >> Cases_on `path` >> gvs[]
QED

Theorem entry_ret_family_dominance:
  def_dominates_uses (entry_ret_family n)
Proof
  mp_tac entry_ret_family_entry_dominates >>
  simp[entry_ret_family_def, entry_probe_params_def, mk_inst_def] >>
  disch_tac >>
  simp[def_dominates_uses_def, entry_ret_family_def,
       entry_probe_params_def, MEM_GENLIST, mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  simp[MEM_MAP, MEM_GENLIST] >> rpt strip_tac >> gvs[] >>
  simp[def_available_at_def]
  >- (qexists_tac `mk_inst i PARAM [Lit (n2w i)] [entry_probe_name i]` >>
      simp[mk_inst_def, MEM_GENLIST] >>
      qexistsl [`i`, `n+1`] >>
      simp[EL_APPEND_EQN, EL_GENLIST]) >>
  qexists_tac `mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]` >>
  simp[mk_inst_def] >> qexistsl [`n`, `n+1`] >>
  simp[EL_APPEND_EQN, EL_GENLIST]
QED

Theorem entry_ret_family_no_preds:
  cfg_preds_of (cfg_analyze (entry_ret_family n)) lbl = []
Proof
  simp[cfg_analyze_preds, entry_ret_family_def,
       cfgDefsTheory.build_preds_def, cfgDefsTheory.build_succs_def,
       cfgDefsTheory.init_succs_def, cfgDefsTheory.init_preds_def,
       cfgDefsTheory.fmap_lookup_list_def] >>
  Cases_on `n` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, entry_probe_params_def,
       GENLIST_CONS, bb_succs_def, LAST_DEF, LAST_APPEND,
       get_successors_def, mk_inst_def, is_terminator_def,
       MEM_MAP, MEM_FILTER, MEM_GENLIST, MAP_GENLIST,
       combinTheory.o_DEF, get_label_def]
  >- (IF_CASES_TAC >> simp[]) >>
  `FILTER IS_SOME (GENLIST (\x. NONE : string option) n' ++ [NONE]) = []` by
    simp[FILTER_EQ_NIL, EVERY_GENLIST] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> IF_CASES_TAC >> simp[]
QED

Theorem entry_ret_family_no_phis:
  collect_phis (HD (entry_ret_family n).fn_blocks).bb_instructions = []
Proof
  Cases_on `n` >> simp[entry_ret_family_def, entry_probe_params_def,
    GENLIST_CONS, livenessDefsTheory.collect_phis_def, mk_inst_def]
QED

Theorem entry_ret_family_ready:
  codegen_ready_fn (entry_ret_family n)
Proof
  simp[codegen_ready_fn_def, entry_ret_family_canonical,
       entry_ret_family_wf, entry_ret_family_inst_wf, entry_ret_family_ssa,
       entry_ret_family_dominance, entry_ret_family_single_use] >>
  simp[cfgDefsTheory.cfg_is_normalized_def, entry_ret_family_no_preds] >>
  `(entry_ret_family n).fn_blocks =
    [HD (entry_ret_family n).fn_blocks]` by simp[entry_ret_family_def] >>
  `entry_block (entry_ret_family n) =
    SOME (HD (entry_ret_family n).fn_blocks)` by
    simp[entry_block_def, entry_ret_family_def] >>
  simp[block_entries_ready_def, phi_operands_ready_def,
       entry_ret_family_no_preds, entry_ret_family_no_phis,
       entry_ret_family_opcodes_ready] >>
  qpat_x_assum `_ = [HD _]` (fn th => once_rewrite_tac[th]) >>
  simp[entry_ret_family_no_phis, entry_ret_family_opcodes_ready]
QED

(* The long member is admitted by every source-side contract. *)
Theorem entry_ret_family_wrapped_contracts:
  codegen_ready_fn (entry_ret_family (SUC (dimword (:256)) )) /\
  retpc_shape_ok (entry_ret_family (SUC (dimword (:256)) )) /\
  opaque_use_ok (entry_ret_family (SUC (dimword (:256)) ))
Proof
  simp[entry_ret_family_ready, entry_ret_family_retpc_shape,
       entry_ret_family_opaque_ok]
QED

(* This checked read differs from the natural-position incoming value.
   It is an index probe, not a refutation of the existential task theorem. *)
Theorem entry_ret_family_wrapped_read:
  !s id out.
    step_inst_base
      (mk_inst id PARAM [Lit (n2w (dimword (:256)))] [out])
      (s with vs_params :=
        GENLIST (\i. if i = 0 then 0w else 1w) (SUC (dimword (:256)))) =
      OK (update_var out 0w
        (s with vs_params :=
          GENLIST (\i. if i = 0 then 0w else 1w) (SUC (dimword (:256))))) /\
    EL (dimword (:256))
      (GENLIST (\i. if i = 0 then 0w else 1w) (SUC (dimword (:256))) :
         256 word list) = 1w
Proof
  simp[step_inst_base_def, mk_inst_def, w2n_n2w, EL_GENLIST,
       param_index_wrap_discriminator]
QED

Theorem entry_ret_family_small_plan_ops:
  FST (prepare_params_plan (liveness_analyze (entry_ret_family 1))
    (entry_ret_family 1) (init_cleanup_plan_state NONE [] 0 0)) = []
Proof
  EVAL_TAC
QED

Theorem entry_ret_family_small_plan_stack:
  (SND (prepare_params_plan (liveness_analyze (entry_ret_family 1))
    (entry_ret_family 1) (init_cleanup_plan_state NONE [] 0 0))).ps_stack =
    [Var ""; Var "retpc"]
Proof
  EVAL_TAC
QED

(* RET exposes the whole final source state as well as its return values.
   Thus an equal successful RET result cannot hide different variable maps. *)
Theorem entry_ret_probe_result_state:
  step_inst_base (mk_inst id RET ops []) s = IntRet vals t ==> t = s
Proof
  simp[step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Exact-premise audit ledger (C1.2.3.7).

   Checked: entry_ret_family_wrapped_contracts supplies the three source
   contracts at n = SUC(dimword(:256)); get_params and has_retpc are exact
   for arbitrary n.  The small_plan_* EVAL facts check the n=1 branch.
   Checked subsequently: entry_ret_family_all_live proves membership for
   every ordinary name and retpc at n+1.  entry_ret_family_prepare_params
   proves the arbitrary-n empty-code formula from an empty symbolic stack;
   entry_ret_family_prepare_cleanup simplifies the initialized state.
   entry_ret_family_first_non_param checks RET is the first non-param.

   Checked planner projections: init_cleanup_plan_state leaves the spill
   allocator and spilled map unchanged.  At spill_base=0 one may choose a
   context region with base=end=0 and matching function name; the frozen
   statement does not require a valid/well-formed context plan.  SOSpill
   bounds are then vacuous.  These choices still need explicit checked
   context_memory_rel/shared_state_rel instances, not just totality.

   Entry relation: frameRelScript 107-118 constrains the source parameter
   length to n and assembly stack to ra::REVERSE params++rest.  It imposes
   no stack-height cap.  For param_ops=[] choose prog=[AsmLabel "entry"]
   and pc=0; lo/o2pc are definitionally the required maps and asm_block_at
   holds.  Existing blockSimHelpers$asm_step_label (163-168) handles the
   single label, without inspecting stack length.  asmSemScript 927-966
   and its asm_push_val/dup/swap rules do not impose a 1024 cap; these are
   assembly semantics, not EVM resource semantics.  No forced assembly
   failure has been identified for this no-op prefix.

   Existential state: fn_frame_inv only fixes selected shared state and
   frame-view values; by itself it does not identify vs_p with the canonical
   prefix state.  However RET returns IntRet values s with its WHOLE input
   state unchanged (checked entry_ret_probe_result_state).  exec_block's
   RET branch at venomExecSemanticsScript 1691-1704 returns that state;
   block fuel is not decremented for PARAM/RET.  A successful source-prefix
   run followed by RET thus exposes its final vars and instruction index.
   At the required final index, equal exec_block results should force
   vs_p equal to that final source state.  The arbitrary-n execution and
   this inversion are UNPROVED; they must include successful eval_operands
   (no undefined values), not assume that an Error result is informative.

   Minimal remaining path: symbolic all-live/planner equation; successful
   source PARAM-prefix+RET result (with wrapped source lookups); RET-result
   inversion at the required index; plan_stack_rel discrepancy at the Dth
   ordinary output.  frame_view_vars_lookup and the checked opaque-variable
   classification leave this ordinary output unchanged.  Finally construct
   every other frozen premise and rule out every assembly step-count with
   the required PC.  No theorem-level counterexample is asserted here.
*)

Theorem entry_ret_family_preorder_entry[local]:
  MEM "entry" (cfg_analyze (entry_ret_family n)).cfg_dfs_pre
Proof
  `entry_block (entry_ret_family n) =
    SOME (HD (entry_ret_family n).fn_blocks)` by
    simp[entry_block_def, entry_ret_family_def] >>
  drule cfg_analyze_preorder_entry_first >> strip_tac >>
  `(HD (entry_ret_family n).fn_blocks).bb_label = "entry"` by
    simp[entry_ret_family_def] >>
  Cases_on `(cfg_analyze (entry_ret_family n)).cfg_dfs_pre` >> gvs[]
QED

Theorem entry_ret_family_all_live:
  !n v. MEM v (MAP entry_probe_name (GENLIST I n) ++ ["retpc"]) ==>
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n+1))
Proof
  rpt strip_tac >>
  qspec_then `entry_ret_family n` mp_tac
    livenessAnalysisPropsTheory.live_vars_at_uses >>
  simp_tac pure_ss [entry_ret_family_wf, LET_THM] >>
  disch_then irule >>
  simp_tac (srw_ss()) [entry_ret_family_preorder_entry] >>
  qexists `HD (entry_ret_family n).fn_blocks` >>
  simp[entry_ret_family_wf, entry_ret_family_preorder_entry,
       entry_ret_family_def, lookup_block_def, FIND_thm,
       entry_probe_params_def, EL_APPEND_EQN, inst_uses_def, mk_inst_def,
       passSharedDefsTheory.MEM_operand_vars_eq_Var, MEM_MAP] >>
  gvs[MEM_MAP]
QED

Theorem entry_ret_family_first_non_param[local]:
  FIND (\inst. ~is_param_opcode inst.inst_opcode)
    (HD (entry_ret_family n).fn_blocks).bb_instructions =
  SOME (mk_inst (SUC n) RET
    (MAP (\i. Var (entry_probe_name i)) (GENLIST I n) ++ [Var "retpc"]) [])
Proof
  `!xs ys. EVERY (\inst. is_param_opcode inst.inst_opcode) xs ==>
    FIND (\inst. ~is_param_opcode inst.inst_opcode) (xs ++ ys) =
    FIND (\inst. ~is_param_opcode inst.inst_opcode) ys` by
    (Induct >> simp[FIND_thm] >> rpt strip_tac >> gvs[FIND_thm]) >>
  simp[entry_ret_family_def, entry_probe_params_def, EVERY_GENLIST,
       mk_inst_def, is_param_opcode_def, FIND_thm]
QED

Theorem entry_ret_family_prepare_params:
  !n ps. ps.ps_stack = [] ==>
    prepare_params_plan (liveness_analyze (entry_ret_family n))
      (entry_ret_family n) ps =
    ([], FOLDL (\s inst. s with ps_stack :=
        stack_push (Var (HD inst.inst_outputs)) s.ps_stack)
      ps (entry_probe_params n ++
        [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]]))
Proof
  rpt strip_tac >>
  `FILTER (\v. ~MEM (operand_to_string v)
      (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n+1)))
    (MAP (\i. Var (entry_probe_name i)) (GENLIST I n) ++ [Var "retpc"]) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, operand_to_string_def] >>
     rpt strip_tac >> gvs[] >> irule entry_ret_family_all_live >> simp[MEM_MAP, operand_to_string_def] >>
     metis_tac[]) >>
  simp[prepare_params_plan_def, entry_ret_family_get_params,
       entry_ret_family_first_non_param, parameter_stack_fold,
       stackPlanOpsTheory.popmany_plan_def, optimistic_swap_plan_def,
       entry_probe_params_def, MAP_MAP_o, combinTheory.o_DEF,
       mk_inst_def, is_terminator_def] >>
  `(HD (entry_ret_family n).fn_blocks).bb_label = "entry"` by
    simp[entry_ret_family_def] >>
  gvs[MAP_GENLIST, combinTheory.o_DEF, stackPlanOpsTheory.popmany_plan_def]
QED

Theorem entry_ret_family_prepare_cleanup:
  prepare_params_plan (liveness_analyze (entry_ret_family n))
    (entry_ret_family n) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
  ([], (init_cleanup_plan_state ch growth spill_base lbl_ctr) with ps_stack :=
    MAP (\i. Var (entry_probe_name i)) (GENLIST I n) ++ [Var "retpc"])
Proof
  qspec_then `n` mp_tac entry_ret_family_prepare_params >>
  disch_then (qspec_then `init_cleanup_plan_state ch growth spill_base lbl_ctr` mp_tac) >>
  simp[init_cleanup_plan_state_def, init_plan_state_def, parameter_stack_fold,
       entry_probe_params_def, MAP_GENLIST, mk_inst_def, combinTheory.o_DEF]
QED

Theorem entry_ret_family_prepare_alloc:
  ps.ps_stack = [] /\
  prepare_params_plan (liveness_analyze (entry_ret_family n))
    (entry_ret_family n) ps = (ops, ps') ==>
  ps'.ps_alloc = ps.ps_alloc
Proof
  strip_tac >> drule entry_ret_family_prepare_params >>
  simp[parameter_stack_fold] >> strip_tac >> gvs[]
QED

Theorem entry_ret_family_prepare_spilled:
  ps.ps_stack = [] /\
  prepare_params_plan (liveness_analyze (entry_ret_family n))
    (entry_ret_family n) ps = (ops, ps') ==>
  ps'.ps_spilled = ps.ps_spilled
Proof
  strip_tac >> drule entry_ret_family_prepare_params >>
  simp[parameter_stack_fold] >> strip_tac >> gvs[]
QED
