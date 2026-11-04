Theory fnFrameBoundaryEntryParams
Ancestors
  frameRel frameViewFacts stackPlanGen stackPlanTypes stackModel
  callLayoutDefs venomExecSemantics venomState venomInst list rich_list
  arithmetic words unitShapeDefs venomWf phiBlock

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
