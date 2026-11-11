Theory fnFrameBoundaryEntryParams
Ancestors
  asmFrame allocMono frameRel frameViewFacts stackPlanGen stackPlanTypes stackModel stackPlanOps doSwapSim cleanOpsSim strongPrefixSim planAlign stackOpSim planWf prefixExec blockSimHelpers foldlSim
  callLayoutDefs venomExecSemantics venomState venomInst list rich_list pred_set
  arithmetic words unitShapeDefs venomWf phiBlock cfgHelpers
  livenessAnalysisProps cfgAnalysisProps asmSem planExec fnFrameTerminalPrep codegenRel contextCodegenRel mixedPrefixSim prefixSim livenessProofs

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
  qspec_then `insts` mp_tac runInstsPropsTheory.exec_block_skip_prefix >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `0`] mp_tac) >>
  simp[ADD_CLAUSES] >> disch_then irule >>
  simp[entry_param_run_insts, EL_APPEND_EQN] >>
  gvs[EVERY_MEM, entry_param_shape_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[is_terminator_def]
QED

(* One MSTORE consumer per parameter keeps every parameter live after
   the prefix, so preparing the parameters emits no code.  The return PC is
   copied by an ASSIGN before them, so it is the last live variable there and
   the optimistic swap is a no-op.  Every instruction has at most two stack
   operands, so the family meets the codegen arity bound for every n. *)
Definition entry_ret_nops_def:
  entry_ret_nops n =
    GENLIST (\i. mk_inst (n+2+i) MSTORE [Lit 0w; Var (entry_probe_name i)] []) n
End

Definition entry_ret_family_def:
  entry_ret_family n = (entry_probe_fn 0) with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
      entry_probe_params n ++
      [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"];
       mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"]] ++
      entry_ret_nops n ++
      [mk_inst (2*n+2) RET [Var "rpc"] []]|>]
End

Theorem entry_probe_name_not_opaque[simp]:
  entry_probe_name i <> "retpc" /\ "retpc" <> entry_probe_name i /\
  entry_probe_name i <> "rpc" /\ "rpc" <> entry_probe_name i
Proof
  Cases_on `i` >> simp[entry_probe_name_def, REPLICATE]
QED

Theorem entry_ret_family_opcodes_ready:
  EVERY codegen_ready_inst
    (HD (entry_ret_family n).fn_blocks).bb_instructions
Proof
  simp[entry_ret_family_def, entry_probe_fn_def, entry_probe_params_def,
       entry_ret_nops_def,
       EVERY_APPEND, EVERY_GENLIST, codegen_ready_inst_def,
       mk_inst_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
       is_unlowered_internal_call_opcode_def, dead_stack_marker_def,
       compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, get_label_def]
QED

Theorem entry_ret_family_single[local]:
  (entry_ret_family n).fn_blocks = [HD (entry_ret_family n).fn_blocks]
Proof
  simp[entry_ret_family_def]
QED

Theorem entry_ret_family_blocks[local]:
  (HD (entry_ret_family n).fn_blocks).bb_label = "entry" /\
  LENGTH (HD (entry_ret_family n).fn_blocks).bb_instructions = 2 * n + 3 /\
  lookup_block "entry" (entry_ret_family n).fn_blocks =
    SOME (HD (entry_ret_family n).fn_blocks) /\
  fn_insts (entry_ret_family n) =
    (HD (entry_ret_family n).fn_blocks).bb_instructions
Proof
  simp[entry_ret_family_def, lookup_block_def, FIND_thm, fn_insts_def,
       fn_insts_blocks_def, entry_probe_params_def, entry_ret_nops_def]
QED

Theorem entry_ret_family_mem[local]:
  MEM inst (HD (entry_ret_family n).fn_blocks).bb_instructions <=>
    (?i. i < n /\ inst = mk_inst i PARAM [Lit (n2w i)] [entry_probe_name i]) \/
    inst = mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"] \/
    inst = mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"] \/
    (?i. i < n /\
         inst = mk_inst (n+2+i) MSTORE [Lit 0w; Var (entry_probe_name i)] []) \/
    inst = mk_inst (2*n+2) RET [Var "rpc"] []
Proof
  simp[entry_ret_family_def, entry_probe_params_def, entry_ret_nops_def,
       MEM_GENLIST] >> metis_tac[]
QED

Theorem entry_ret_family_el_param[local]:
  !k. k < n ==>
    EL k (HD (entry_ret_family n).fn_blocks).bb_instructions =
    mk_inst k PARAM [Lit (n2w k)] [entry_probe_name k]
Proof
  simp[entry_ret_family_def, entry_probe_params_def, EL_APPEND_EQN,
       EL_GENLIST]
QED

Theorem entry_ret_family_el_retpc[local]:
  !k. k = n ==>
    EL k (HD (entry_ret_family n).fn_blocks).bb_instructions =
    mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]
Proof
  simp[entry_ret_family_def, entry_probe_params_def, EL_APPEND_EQN]
QED

Theorem entry_ret_family_el_assign[local]:
  !k. k = n + 1 ==>
    EL k (HD (entry_ret_family n).fn_blocks).bb_instructions =
    mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"]
Proof
  simp[entry_ret_family_def, entry_probe_params_def, EL_APPEND_EQN,
       rich_listTheory.EL_CONS]
QED

Theorem entry_ret_family_el_nop[local]:
  !k. n + 2 <= k /\ k < 2 * n + 2 ==>
    EL k (HD (entry_ret_family n).fn_blocks).bb_instructions =
    mk_inst k MSTORE [Lit 0w; Var (entry_probe_name (k - (n + 2)))] []
Proof
  rpt strip_tac >>
  simp[entry_ret_family_def, entry_probe_params_def, entry_ret_nops_def,
       EL_APPEND_EQN, EL_GENLIST, rich_listTheory.EL_CONS, mk_inst_def]
QED

Theorem entry_ret_family_el_ret[local]:
  !k. k = 2 * n + 2 ==>
    EL k (HD (entry_ret_family n).fn_blocks).bb_instructions =
    mk_inst (2*n+2) RET [Var "rpc"] []
Proof
  simp[entry_ret_family_def, entry_probe_params_def, entry_ret_nops_def,
       EL_APPEND_EQN, rich_listTheory.EL_CONS]
QED

Theorem entry_ret_family_offsets_used:
  offset_outputs_used (entry_ret_family n)
Proof
  simp[offset_outputs_used_def, entry_ret_family_blocks, EVERY_MEM,
       entry_ret_family_mem] >>
  rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem entry_ret_family_small:
  (HD (entry_ret_family 1).fn_blocks).bb_instructions =
    [mk_inst 0 PARAM [Lit 0w] [""];
     mk_inst 1 RETPC_PARAM [Lit 1w] ["retpc"];
     mk_inst 2 ASSIGN [Var "retpc"] ["rpc"];
     mk_inst 3 MSTORE [Lit 0w; Var ""] [];
     mk_inst 4 RET [Var "rpc"] []]
Proof
  EVAL_TAC
QED

Theorem entry_ret_family_get_params:
  get_params (HD (entry_ret_family n).fn_blocks).bb_instructions =
    entry_probe_params n ++
      [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]]
Proof
  `(HD (entry_ret_family n).fn_blocks).bb_instructions =
     (entry_probe_params n ++
      [mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]]) ++
     (mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"] ::
      entry_ret_nops n ++ [mk_inst (2*n+2) RET [Var "rpc"] []])` by
    simp[entry_ret_family_def] >>
  pop_assum SUBST1_TAC >> irule get_params_prefix >>
  simp[entry_probe_params_def, entry_ret_nops_def, EVERY_APPEND,
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
       entry_ret_nops_def, EVERY_APPEND, EVERY_GENLIST, mk_inst_def]
QED

Theorem entry_ret_family_opaque_vars:
  !x. (retpc_var (entry_ret_family n) x <=> x = "retpc" \/ x = "rpc") /\
      ~gas_var (entry_ret_family n) x
Proof
  `copy_phi_var RETPC_PARAM (entry_ret_family n) "retpc"` by
    (irule copy_phi_var_seed >>
     qexists_tac `mk_inst n RETPC_PARAM [Lit (n2w n)] ["retpc"]` >>
     simp[entry_ret_family_blocks, entry_ret_family_mem, mk_inst_def]) >>
  `copy_phi_var RETPC_PARAM (entry_ret_family n) "rpc"` by
    (irule copy_phi_var_assign >>
     qexistsl_tac [`mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"]`, `"retpc"`] >>
     simp[entry_ret_family_blocks, entry_ret_family_mem, mk_inst_def]) >>
  gen_tac >> rewrite_tac[retpc_var_def, gas_var_def] >> conj_tac
  >- (eq_tac
      >- (once_rewrite_tac[copy_phi_var_cases] >>
          simp[entry_ret_family_blocks, entry_ret_family_mem, PULL_EXISTS] >>
          rpt strip_tac >> gvs[mk_inst_def]) >>
      strip_tac >> gvs[]) >>
  irule copy_phi_var_no_seed >>
  simp[entry_ret_family_blocks, entry_ret_family_mem, PULL_EXISTS] >>
  rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem entry_ret_family_opaque_ok:
  opaque_use_ok (entry_ret_family n)
Proof
  simp[opaque_use_ok_def, entry_ret_family_opaque_vars,
       entry_ret_family_blocks, entry_ret_family_mem, PULL_EXISTS] >>
  rpt strip_tac >> gvs[mk_inst_def, retpc_use_ok_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem entry_ret_family_retpc_shape:
  retpc_shape_ok (entry_ret_family n)
Proof
  simp[retpc_shape_ok_def, entry_ret_family_reachable,
       entry_ret_family_opaque_vars, entry_ret_family_blocks,
       entry_ret_family_mem, PULL_EXISTS] >>
  rpt strip_tac >> gvs[mk_inst_def] >>
  qexistsl_tac [`[]`, `"rpc"`] >> simp[]
QED

Theorem entry_ret_family_inst_wf:
  fn_inst_wf (entry_ret_family n)
Proof
  once_rewrite_tac[fn_inst_wf_def] >>
  once_rewrite_tac[entry_ret_family_single] >>
  simp[entry_ret_family_mem, PULL_EXISTS] >>
  rpt strip_tac >> simp[inst_wf_def, mk_inst_def]
QED

Theorem entry_ret_family_ssa:
  ssa_form (entry_ret_family n)
Proof
  `!m. FLAT (GENLIST (\i. [entry_probe_name i]) m) =
        GENLIST entry_probe_name m` by
    (Induct >> simp[GENLIST, FLAT_SNOC]) >>
  `!m. FLAT (GENLIST (\i. [] : string list) m) = []` by
    (Induct >> simp[GENLIST, FLAT_SNOC]) >>
  simp[ssa_form_def, entry_ret_family_def, entry_probe_params_def,
       entry_ret_nops_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       MAP_GENLIST, combinTheory.o_DEF, ALL_DISTINCT_APPEND,
       ALL_DISTINCT_GENLIST, MEM_GENLIST] >>
  rpt strip_tac >> gvs[]
QED

Theorem filter_genlist_unique_le1[local]:
  !m f P. (!i j. i < m /\ j < m /\ P (f i) /\ P (f j) ==> i = j) ==>
    LENGTH (FILTER P (GENLIST f m)) <= 1
Proof
  Induct >> simp[GENLIST, FILTER_SNOC] >> rpt strip_tac >>
  IF_CASES_TAC
  >- (`FILTER P (GENLIST f m) = []` suffices_by simp[] >>
      simp[FILTER_EQ_NIL, EVERY_GENLIST] >> rpt strip_tac >>
      qpat_x_assum `!i j. i < SUC m /\ _ ==> _`
        (qspecl_then [`i`, `m`] mp_tac) >> simp[]) >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum `!i j. i < SUC m /\ _ ==> _`
    (qspecl_then [`i`, `j`] mp_tac) >> simp[]
QED

Theorem entry_ret_family_single_use:
  single_use_form (entry_ret_family n)
Proof
  rw[passSharedDefsTheory.single_use_form_def,
     passSharedDefsTheory.var_use_count_block_def, entry_ret_family_def,
     FILTER_APPEND] >>
  `FILTER (\inst. ~sue_count_exempt inst.inst_opcode /\
                  MEM (Var v) inst.inst_operands) (entry_probe_params n) = []` by
    simp[FILTER_EQ_NIL, entry_probe_params_def, EVERY_GENLIST, mk_inst_def,
         passSharedDefsTheory.sue_count_exempt_def, is_param_opcode_def] >>
  `LENGTH (FILTER (\inst. ~sue_count_exempt inst.inst_opcode /\
                  MEM (Var v) inst.inst_operands) (entry_ret_nops n)) <= 1 /\
   (v = "rpc" ==>
    FILTER (\inst. ~sue_count_exempt inst.inst_opcode /\
                  MEM (Var v) inst.inst_operands) (entry_ret_nops n) = [])` by
    (simp[entry_ret_nops_def] >> conj_tac
     >- (irule filter_genlist_unique_le1 >>
         simp[mk_inst_def, passSharedDefsTheory.sue_count_exempt_def,
              is_param_opcode_def] >>
         rpt strip_tac >> gvs[]) >>
     simp[FILTER_EQ_NIL, EVERY_GENLIST, mk_inst_def]) >>
  Cases_on `v = "rpc"` >>
  gvs[mk_inst_def, passSharedDefsTheory.sue_count_exempt_def,
      is_param_opcode_def]
QED

Theorem entry_ret_family_ids_distinct[local]:
  ALL_DISTINCT (HD (entry_ret_family n).fn_blocks).bb_instructions
Proof
  irule (Q.ISPEC `\inst. inst.inst_id` ALL_DISTINCT_MAP) >>
  simp[entry_ret_family_def, entry_probe_params_def, entry_ret_nops_def,
       MAP_GENLIST, combinTheory.o_DEF, mk_inst_def, ALL_DISTINCT_APPEND,
       ALL_DISTINCT_GENLIST, MEM_GENLIST]
QED

Theorem entry_ret_family_succs[local]:
  bb_succs (HD (entry_ret_family n).fn_blocks) = []
Proof
  `!bb. bb.bb_instructions <> [] ==>
     bb_succs bb = nub (REVERSE (get_successors (LAST bb.bb_instructions)))` by
    (rpt strip_tac >> simp[bb_succs_def] >>
     Cases_on `bb.bb_instructions` >> gvs[]) >>
  pop_assum (qspec_then `HD (entry_ret_family n).fn_blocks` mp_tac) >>
  simp[entry_ret_family_def] >> disch_then kall_tac >>
  simp[get_successors_def, mk_inst_def, is_terminator_def, get_label_def,
       nub_def]
QED

Theorem entry_ret_family_wf:
  wf_function (entry_ret_family n)
Proof
  `bb_well_formed (HD (entry_ret_family n).fn_blocks)` by
    (rewrite_tac[bb_well_formed_def] >> rpt conj_tac
     >- simp[entry_ret_family_def]
     >- simp[entry_ret_family_def, LAST_APPEND_CONS, LAST_DEF, mk_inst_def,
             is_terminator_def]
     >- (rpt strip_tac >> fs[entry_ret_family_blocks] >>
         `MEM (EL i (HD (entry_ret_family n).fn_blocks).bb_instructions)
            (HD (entry_ret_family n).fn_blocks).bb_instructions` by
           (irule EL_MEM >> simp[entry_ret_family_blocks]) >>
         `EL i (HD (entry_ret_family n).fn_blocks).bb_instructions =
          EL (2 * n + 2) (HD (entry_ret_family n).fn_blocks).bb_instructions` by
           (simp[entry_ret_family_el_ret] >>
            qpat_x_assum `MEM _ _` mp_tac >> simp[entry_ret_family_mem] >>
            rpt strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
         qpat_x_assum `EL i _ = EL _ _` mp_tac >>
         simp[ALL_DISTINCT_EL_IMP, entry_ret_family_ids_distinct,
              entry_ret_family_blocks]) >>
     rpt strip_tac >>
     `MEM (EL j (HD (entry_ret_family n).fn_blocks).bb_instructions)
        (HD (entry_ret_family n).fn_blocks).bb_instructions` by
       (irule EL_MEM >> simp[]) >>
     qpat_x_assum `MEM _ _` mp_tac >> simp[entry_ret_family_mem] >>
     rpt strip_tac >> gvs[mk_inst_def]) >>
  `fn_inst_ids_distinct (entry_ret_family n)` by
    simp[fn_inst_ids_distinct_def, entry_ret_family_def,
         entry_probe_params_def, entry_ret_nops_def, MAP_GENLIST,
         combinTheory.o_DEF, mk_inst_def, ALL_DISTINCT_APPEND,
         ALL_DISTINCT_GENLIST, MEM_GENLIST] >>
  simp[wf_function_def, fn_labels_def, fn_has_entry_def,
       fn_succs_closed_def] >>
  once_rewrite_tac[entry_ret_family_single] >>
  simp[entry_ret_family_succs]
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
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule canonical_entry_params_from_prepend_users >>
  simp[entry_probe_params_def, entry_ret_nops_def, EVERY_GENLIST,
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

Theorem entry_ret_family_avail[local]:
  !d u v. d < u /\ u < 2 * n + 3 /\
    MEM v (EL d (HD (entry_ret_family n).fn_blocks).bb_instructions).inst_outputs ==>
    def_available_at (entry_ret_family n) (HD (entry_ret_family n).fn_blocks)
      (SOME (EL u (HD (entry_ret_family n).fn_blocks).bb_instructions)) v
Proof
  rpt strip_tac >> simp[def_available_at_def] >>
  qexistsl_tac [`HD (entry_ret_family n).fn_blocks`,
    `EL d (HD (entry_ret_family n).fn_blocks).bb_instructions`] >>
  `MEM (HD (entry_ret_family n).fn_blocks) (entry_ret_family n).fn_blocks` by
    simp[entry_ret_family_def] >>
  simp[entry_ret_family_blocks, entry_ret_family_entry_dominates, EL_MEM] >>
  qexistsl_tac [`d`, `u`] >> simp[entry_ret_family_blocks]
QED

Theorem entry_ret_family_dominance:
  def_dominates_uses (entry_ret_family n)
Proof
  rewrite_tac[def_dominates_uses_def] >> rpt gen_tac >>
  once_rewrite_tac[entry_ret_family_single] >> rewrite_tac[MEM] >>
  strip_tac >> gvs[MEM_EL, entry_ret_family_blocks] >>
  rename1 `u < 2 * n + 3` >>
  Cases_on `u < n`
  >- gvs[entry_ret_family_el_param, mk_inst_def] >>
  Cases_on `u = n`
  >- gvs[entry_ret_family_el_retpc, mk_inst_def] >>
  Cases_on `u = n + 1`
  >- (gvs[] >>
      qspecl_then [`n`, `n + 1`, `"retpc"`] mp_tac entry_ret_family_avail >>
      simp[entry_ret_family_el_retpc, entry_ret_family_el_assign,
           mk_inst_def]) >>
  Cases_on `u < 2 * n + 2`
  >- (qspecl_then [`u - (n + 2)`, `u`, `entry_probe_name (u - (n + 2))`]
        mp_tac entry_ret_family_avail >>
      simp[entry_ret_family_el_param, entry_ret_family_el_nop, mk_inst_def,
           GSYM MEM_EL]) >>
  `u = 2 * n + 2` by decide_tac >> gvs[] >>
  qspecl_then [`n + 1`, `2 * n + 2`, `"rpc"`] mp_tac entry_ret_family_avail >>
  simp[entry_ret_family_el_assign, entry_ret_family_el_ret, mk_inst_def]
QED

Theorem entry_ret_family_no_preds:
  cfg_preds_of (cfg_analyze (entry_ret_family n)) lbl = []
Proof
  simp[cfg_analyze_preds] >> once_rewrite_tac[entry_ret_family_single] >>
  simp[cfgDefsTheory.build_preds_def, cfgDefsTheory.build_succs_def,
       cfgDefsTheory.init_succs_def, cfgDefsTheory.init_preds_def,
       cfgDefsTheory.fmap_lookup_list_def, finite_mapTheory.FLOOKUP_UPDATE,
       entry_ret_family_blocks, entry_ret_family_succs] >>
  rw[]
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
  simp[block_entries_ready_def, phi_operands_ready_def, phis_at_joins_def,
       entry_ret_family_no_preds, entry_ret_family_no_phis,
       entry_ret_family_opcodes_ready] >>
  qpat_x_assum `_ = [HD _]` (fn th => once_rewrite_tac[th]) >>
  simp[entry_ret_family_no_phis, entry_ret_family_opcodes_ready,
       entry_ret_family_offsets_used]
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
  rpt gen_tac >> conj_tac
  >- (qmatch_goalsub_abbrev_tac `step_inst_base _ t` >>
      `t.vs_params <> [] /\ HD t.vs_params = 0w` by
        (unabbrev_all_tac >>
         pure_rewrite_tac[venom_state_accfupds, combinTheory.K_THM] >>
         once_rewrite_tac[GENLIST_CONS] >>
         rewrite_tac[HD, NOT_CONS_NIL] >> BETA_TAC >> rewrite_tac[]) >>
      drule wrapped_param_reads_first >>
      disch_then (qspecl_then [`id`, `out`] mp_tac) >>
      asm_rewrite_tac[]) >>
  simp[EL_GENLIST, param_index_wrap_discriminator]
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
   entry_ret_family_first_non_param checks the ASSIGN copying retpc is the
   first non-param, and entry_ret_family_live_last makes retpc the last live
   name there, so the optimistic swap emits nothing.

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
   prefix state.  From the required index the block copies retpc into rpc,
   skips the NOPs, and its RET returns the whole state
   (entry_ret_family_tail_exec).  Equal exec_block results therefore give
   vs_p the canonical prefix state's value for every name but rpc
   (entry_ret_family_witness_lookup), including the Dth ordinary output.

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

Theorem entry_ret_family_live_uses[local]:
  !idx v. idx < 2 * n + 3 /\
    MEM v (inst_uses (EL idx (HD (entry_ret_family n).fn_blocks).bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" idx)
Proof
  rpt strip_tac >>
  qspecl_then [`entry_ret_family n`, `"entry"`,
    `HD (entry_ret_family n).fn_blocks`, `idx`, `v`] mp_tac
    livenessProofsTheory.live_vars_at_uses >>
  simp_tac pure_ss [entry_ret_family_wf, LET_THM] >>
  disch_then irule >>
  simp[entry_ret_family_preorder_entry, entry_ret_family_blocks]
QED

Theorem entry_ret_family_live_range[local]:
  !i j v. i <= j /\ j <= 2 * n + 3 /\
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" j) /\
    (!k. i <= k /\ k < j ==>
       ~MEM v (inst_defs
         (EL k (HD (entry_ret_family n).fn_blocks).bb_instructions))) ==>
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" i)
Proof
  rpt strip_tac >>
  qspecl_then [`entry_ret_family n`, `"entry"`,
    `HD (entry_ret_family n).fn_blocks`, `i`, `j`, `v`] mp_tac
    livenessProofsTheory.live_vars_at_propagate_range >>
  simp_tac pure_ss [entry_ret_family_wf, LET_THM] >>
  disch_then irule >>
  simp[entry_ret_family_preorder_entry, entry_ret_family_blocks]
QED

Theorem entry_ret_family_live_forward[local]:
  !i j v. i <= j /\ j <= 2 * n + 3 /\
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" i) /\
    (!k. i <= k /\ k < j ==>
       ~MEM v (inst_defs
         (EL k (HD (entry_ret_family n).fn_blocks).bb_instructions))) ==>
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" j) \/
    ?k. i <= k /\ k < j /\
      MEM v (inst_uses
        (EL k (HD (entry_ret_family n).fn_blocks).bb_instructions))
Proof
  rpt strip_tac >>
  qspecl_then [`entry_ret_family n`, `"entry"`,
    `HD (entry_ret_family n).fn_blocks`, `i`, `j`, `v`] mp_tac
    livenessProofsTheory.live_vars_at_forward_or_used >>
  simp_tac pure_ss [entry_ret_family_wf, LET_THM] >>
  disch_then irule >>
  simp[entry_ret_family_preorder_entry, entry_ret_family_blocks]
QED

Theorem entry_ret_family_live_transfer[local]:
  !idx. idx < 2 * n + 3 ==>
    live_vars_at (liveness_analyze (entry_ret_family n)) "entry" idx =
    liveness_transfer (entry_ret_family n).fn_blocks
      (EL idx (HD (entry_ret_family n).fn_blocks).bb_instructions)
      (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (SUC idx))
Proof
  rpt strip_tac >>
  qspecl_then [`entry_ret_family n`, `"entry"`,
    `HD (entry_ret_family n).fn_blocks`, `idx`] mp_tac
    livenessProofsTheory.live_vars_at_transfer >>
  simp_tac pure_ss [entry_ret_family_wf, LET_THM] >>
  disch_then irule >>
  simp[entry_ret_family_preorder_entry, entry_ret_family_blocks]
QED

(* The block has no successors, so nothing is live at its end. *)
Theorem entry_ret_family_live_exit[local]:
  live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (2 * n + 3) = []
Proof
  `cfg_reachable_of (cfg_analyze (entry_ret_family n)) "entry"` by
    (mp_tac (Q.SPEC `entry_ret_family n` cfg_analyze_reachable_sets) >>
     simp[entry_ret_family_wf, EXTENSION] >>
     metis_tac[entry_ret_family_preorder_entry]) >>
  mp_tac (Q.INST [`fn` |-> `entry_ret_family n`, `lbl` |-> `"entry"`]
    livenessProofsTheory.liveness_convergence) >>
  simp[entry_ret_family_wf, livenessBlockProofsTheory.liveness_instrs_def,
       livenessBlockProofsTheory.liveness_out_def,
       cfgHelpersTheory.cfg_analyze_succs, entry_ret_family_blocks] >>
  once_rewrite_tac[entry_ret_family_single] >>
  simp[cfgDefsTheory.build_succs_def, cfgDefsTheory.init_succs_def,
       cfgDefsTheory.fmap_lookup_list_def, finite_mapTheory.FLOOKUP_UPDATE,
       entry_ret_family_blocks, entry_ret_family_succs,
       livenessDefsTheory.same_vars_set, livenessDefsTheory.live_vars_at_def]
QED

Theorem entry_ret_family_all_live:
  !n v. MEM v (MAP entry_probe_name (GENLIST I n) ++ ["retpc"]) ==>
    MEM v (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n+1))
Proof
  rpt gen_tac >> rewrite_tac[MEM_APPEND, MEM, OR_CLAUSES] >> strip_tac
  >- (gvs[MEM_MAP, MEM_GENLIST] >>
      qmatch_goalsub_rename_tac `entry_probe_name y` >>
      `MEM (entry_probe_name y)
         (live_vars_at (liveness_analyze (entry_ret_family n)) "entry"
           (n + 2 + y))` by
        (irule entry_ret_family_live_uses >>
         simp[entry_ret_family_el_nop, mk_inst_def, inst_uses_def,
              passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
      irule entry_ret_family_live_range >>
      qexists_tac `n + 2 + y` >> simp[] >>
      rpt strip_tac >>
      Cases_on `k = n + 1`
      >- gvs[entry_ret_family_el_assign, mk_inst_def, inst_defs_def] >>
      `n + 2 <= k /\ k < 2 * n + 2` by decide_tac >>
      gvs[entry_ret_family_el_nop, mk_inst_def, inst_defs_def]) >>
  irule entry_ret_family_live_uses >>
  simp[entry_ret_family_el_assign, mk_inst_def, inst_uses_def,
       passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

(* retpc is used only by the ASSIGN, so it is the name the ASSIGN appends
   last to the live list. *)
Theorem entry_ret_family_live_last[local]:
  live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n + 1) <> [] /\
  LAST (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n + 1)) =
    "retpc"
Proof
  `!k. n + 2 <= k /\ k < 2 * n + 3 ==>
     ~MEM "retpc" (inst_defs
        (EL k (HD (entry_ret_family n).fn_blocks).bb_instructions)) /\
     ~MEM "retpc" (inst_uses
        (EL k (HD (entry_ret_family n).fn_blocks).bb_instructions))` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `k = 2 * n + 2`
     >- simp[entry_ret_family_el_ret, mk_inst_def, inst_defs_def,
             inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     `k < 2 * n + 2` by decide_tac >>
     simp[entry_ret_family_el_nop, mk_inst_def, inst_defs_def,
          inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM "retpc"
     (live_vars_at (liveness_analyze (entry_ret_family n)) "entry" (n + 2))` by
    (strip_tac >>
     qspecl_then [`n + 2`, `2 * n + 3`, `"retpc"`] mp_tac
       entry_ret_family_live_forward >>
     impl_tac >- simp[] >>
     simp[entry_ret_family_live_exit] >> metis_tac[]) >>
  `SUC (n + 1) = n + 2` by decide_tac >>
  qspec_then `n + 1` mp_tac entry_ret_family_live_transfer >>
  impl_tac >- decide_tac >>
  disch_then SUBST1_TAC >> pop_assum SUBST1_TAC >>
  simp[livenessDefsTheory.liveness_transfer_def,
       livenessDefsTheory.live_update_def, entry_ret_family_el_assign,
       mk_inst_def, inst_defs_def, livenessDefsTheory.ordered_inst_uses_def,
       python_stack_operands_def, venomInstTheory.operand_vars_def,
       venomInstTheory.operand_var_def, MEM_FILTER]
QED

Theorem entry_ret_family_first_non_param[local]:
  FIND (\inst. ~is_param_opcode inst.inst_opcode)
    (HD (entry_ret_family n).fn_blocks).bb_instructions =
  SOME (mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"])
Proof
  `!xs ys. EVERY (\inst. is_param_opcode inst.inst_opcode) xs ==>
    FIND (\inst. ~is_param_opcode inst.inst_opcode) (xs ++ ys) =
    FIND (\inst. ~is_param_opcode inst.inst_opcode) ys` by
    (Induct >> simp[FIND_thm] >> rpt strip_tac >> gvs[FIND_thm]) >>
  simp[entry_ret_family_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[entry_probe_params_def, EVERY_GENLIST, mk_inst_def,
       is_param_opcode_def, FIND_thm]
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
  `(HD (entry_ret_family n).fn_blocks).bb_label = "entry"` by
    simp[entry_ret_family_def] >>
  simp[prepare_params_plan_def, entry_ret_family_get_params,
       entry_ret_family_first_non_param, parameter_stack_fold,
       stackPlanOpsTheory.popmany_plan_def, optimistic_swap_plan_def,
       entry_probe_params_def, MAP_MAP_o, combinTheory.o_DEF,
       mk_inst_def, is_terminator_def, entry_ret_family_live_last,
       dfgDefsTheory.operand_equiv_def] >>
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

Definition entry_wrap_inputs_def:
  entry_wrap_inputs = GENLIST (\i. if i = 0 then 0w else 1w : 256 word)
    (SUC (dimword (:256)))
End

Theorem entry_ret_family_wrap_param_shape:
  s.vs_params = entry_wrap_inputs ==>
  EVERY (entry_param_shape s)
    (get_params (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_instructions)
Proof
  strip_tac >>
  `LENGTH s.vs_params = SUC (dimword (:256))` by
    (asm_rewrite_tac[entry_wrap_inputs_def] >>
     rewrite_tac[LENGTH_GENLIST]) >>
  rewrite_tac[entry_ret_family_get_params, entry_probe_params_def,
              EVERY_APPEND, EVERY_DEF, EVERY_GENLIST] >>
  simp[entry_param_shape_def, mk_inst_def, w2n_n2w] >>
  rpt strip_tac >>
  `i MOD dimword (:256) < dimword (:256)` by
    simp[DIVISION] >>
  qpat_x_assum `i MOD _ < _` mp_tac >>
  CONV_TAC (LAND_CONV EVAL) >> decide_tac
QED

Definition entry_ret_prefix_state_def:
  entry_ret_prefix_state n s =
    (entry_bind_pairs (entry_param_pairs s
      (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions)) s)
      with vs_inst_idx := n+1
End

Theorem entry_ret_family_param_pairs:
  entry_param_pairs s
    (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions) =
  GENLIST (\i. (entry_probe_name i,
    EL (i MOD dimword (:256)) s.vs_params)) n ++
    [("retpc", s.vs_return_pc_token)]
Proof
  simp[entry_param_pairs_def, entry_ret_family_get_params,
       entry_probe_params_def, MAP_GENLIST, mk_inst_def,
       combinTheory.o_DEF, w2n_n2w]
QED

Theorem entry_ret_family_pairs_distinct:
  ALL_DISTINCT (MAP FST (entry_param_pairs s
    (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions)))
Proof
  simp[entry_ret_family_param_pairs, MAP_GENLIST, combinTheory.o_DEF,
       ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST, MEM_GENLIST]
QED

Theorem entry_ret_prefix_lookup:
  !i n s. i < n ==>
    FLOOKUP (entry_ret_prefix_state n s).vs_vars (entry_probe_name i) =
    SOME (EL (i MOD dimword (:256)) s.vs_params)
Proof
  rpt strip_tac >> simp[entry_ret_prefix_state_def] >>
  irule entry_bind_pairs_lookup >>
  simp[entry_ret_family_pairs_distinct, entry_ret_family_param_pairs,
       MEM_GENLIST] >> metis_tac[]
QED

Theorem entry_ret_prefix_retpc_lookup:
  FLOOKUP (entry_ret_prefix_state n s).vs_vars "retpc" =
    SOME s.vs_return_pc_token
Proof
  simp[entry_ret_prefix_state_def] >> irule entry_bind_pairs_lookup >>
  simp[entry_ret_family_pairs_distinct, entry_ret_family_param_pairs]
QED

Theorem entry_ret_prefix_wrapped_lookup:
  s.vs_params = entry_wrap_inputs ==>
  FLOOKUP (entry_ret_prefix_state (SUC (dimword (:256))) s).vs_vars
    (entry_probe_name (dimword (:256))) = SOME 0w
Proof
  strip_tac >>
  simp[entry_ret_prefix_lookup] >>
  asm_rewrite_tac[entry_wrap_inputs_def] >>
  once_rewrite_tac[GENLIST_CONS] >> rewrite_tac[HD] >>
  BETA_TAC >> rewrite_tac[]
QED

Theorem entry_keeper_step[local]:
  step_inst_base (mk_inst id MSTORE [Lit 0w; Var x] []) s =
    case FLOOKUP s.vs_vars x of
      NONE => Error "undefined operand"
    | SOME v => OK (mstore 0 v s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, lookup_var_def]
QED

Theorem entry_keeper_vars[local,simp]:
  (mstore off v s).vs_vars = s.vs_vars
Proof
  simp[mstore_def]
QED

Theorem entry_ret_family_nop_skip[local]:
  !d k s rv u. k + d = 2 * n + 2 /\ n + 2 <= k /\
    exec_block fuel ctx (HD (entry_ret_family n).fn_blocks)
      (s with vs_inst_idx := k) = IntRet rv u ==>
    u.vs_vars = s.vs_vars
Proof
  Induct
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      once_rewrite_tac[exec_block_def] >>
      simp[get_instruction_def, entry_ret_family_blocks,
           entry_ret_family_el_ret, step_inst_non_invoke, mk_inst_def,
           step_inst_base_def, eval_operands_def, eval_operand_def,
           lookup_var_def] >>
      Cases_on `FLOOKUP s.vs_vars "rpc"` >> simp[FRONT_DEF] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < 2 * n + 2 /\ k < 2 * n + 3` by decide_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  simp[get_instruction_def, entry_ret_family_blocks, entry_ret_family_el_nop,
       step_inst_non_invoke, SRULE [mk_inst_def] entry_keeper_step,
       is_terminator_def, mk_inst_def] >>
  Cases_on `FLOOKUP s.vs_vars (entry_probe_name (k - (n + 2)))` >> simp[] >>
  rename1 `FLOOKUP s.vs_vars _ = SOME v` >> strip_tac >>
  qpat_x_assum `!k s rv u. _`
    (qspecl_then [`SUC k`, `mstore 0 v (s with vs_inst_idx := k)`] mp_tac) >>
  simp[] >> disch_then irule >> decide_tac
QED

Theorem entry_ret_family_suffix_exists[local]:
  !d k s r. k + d = 2 * n + 2 /\ n + 2 <= k /\
    FLOOKUP s.vs_vars "rpc" = SOME r /\
    (!i. k - (n + 2) <= i /\ i < n ==>
         ?v. FLOOKUP s.vs_vars (entry_probe_name i) = SOME v) ==>
    ?u. exec_block fuel ctx (HD (entry_ret_family n).fn_blocks)
          (s with vs_inst_idx := k) =
          IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u /\
        u.vs_vars = s.vs_vars
Proof
  Induct
  >- (rpt strip_tac >> gvs[] >>
      once_rewrite_tac[exec_block_def] >>
      simp[get_instruction_def, entry_ret_family_blocks,
           entry_ret_family_el_ret, step_inst_non_invoke, mk_inst_def,
           step_inst_base_def, eval_operands_def, eval_operand_def,
           lookup_var_def, FRONT_DEF]) >>
  rpt gen_tac >> strip_tac >>
  `k < 2 * n + 2 /\ k < 2 * n + 3` by decide_tac >>
  `?v. FLOOKUP s.vs_vars (entry_probe_name (k - (n + 2))) = SOME v` by
    (first_x_assum irule >> decide_tac) >>
  once_rewrite_tac[exec_block_def] >>
  simp[get_instruction_def, entry_ret_family_blocks, entry_ret_family_el_nop,
       step_inst_non_invoke, SRULE [mk_inst_def] entry_keeper_step,
       is_terminator_def, mk_inst_def] >>
  qpat_x_assum `!k s r. _`
    (qspecl_then [`SUC k`, `mstore 0 v (s with vs_inst_idx := k)`, `r`] mp_tac) >>
  simp[]
QED

(* Successful execution of the stores preserves variables, not memory. *)
Theorem entry_ret_family_tail_exec[local]:
  !fuel ctx t rv u. t.vs_inst_idx = n + 1 /\
    exec_block fuel ctx (HD (entry_ret_family n).fn_blocks) t = IntRet rv u ==>
    ?r. FLOOKUP t.vs_vars "retpc" = SOME r /\
        u.vs_vars = (update_var "rpc" r t).vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  simp[get_instruction_def, entry_ret_family_blocks,
       entry_ret_family_el_assign, step_inst_non_invoke, mk_inst_def,
       step_inst_base_def, eval_operand_def, lookup_var_def,
       is_terminator_def] >>
  Cases_on `FLOOKUP t.vs_vars "retpc"` >> simp[] >>
  rename1 `FLOOKUP t.vs_vars "retpc" = SOME r` >> strip_tac >>
  irule entry_ret_family_nop_skip >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `n` >> simp[]
QED

Theorem entry_ret_family_tail_exists[local]:
  t.vs_inst_idx = n + 1 /\ FLOOKUP t.vs_vars "retpc" = SOME r /\
  (!i. i < n ==> ?v. FLOOKUP t.vs_vars (entry_probe_name i) = SOME v) ==>
  ?u. exec_block fuel ctx (HD (entry_ret_family n).fn_blocks) t =
        IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u /\
      u.vs_vars = (update_var "rpc" r t).vs_vars
Proof
  strip_tac >> once_rewrite_tac[exec_block_def] >>
  simp[get_instruction_def, entry_ret_family_blocks,
       entry_ret_family_el_assign, step_inst_non_invoke, mk_inst_def,
       step_inst_base_def, eval_operand_def, lookup_var_def,
       is_terminator_def] >>
  irule entry_ret_family_suffix_exists >>
  simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `n` >> simp[]
QED

Theorem entry_ret_family_exec[local]:
  EVERY (entry_param_shape s)
    (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions) ==>
  ?u. exec_block fuel ctx (HD (entry_ret_family n).fn_blocks)
    (s with vs_inst_idx := 0) =
      IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u /\
    u.vs_vars = (update_var "rpc" s.vs_return_pc_token
                  (entry_ret_prefix_state n s)).vs_vars
Proof
  strip_tac >>
  `?suffix. (HD (entry_ret_family n).fn_blocks).bb_instructions =
     get_params (HD (entry_ret_family n).fn_blocks).bb_instructions ++
     suffix` by
    (qexists_tac `[mk_inst (n+1) ASSIGN [Var "retpc"] ["rpc"]] ++
       entry_ret_nops n ++ [mk_inst (2*n+2) RET [Var "rpc"] []]` >>
     rewrite_tac[entry_ret_family_get_params] >>
     simp[entry_ret_family_def] >>
     rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  drule_all entry_param_skip_prefix >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  `LENGTH (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions) =
     n + 1` by simp[entry_ret_family_get_params, entry_probe_params_def] >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[GSYM entry_ret_prefix_state_def] >>
  `(entry_ret_prefix_state n s).vs_inst_idx = n + 1` by
    simp[entry_ret_prefix_state_def] >>
  irule entry_ret_family_tail_exists >>
  simp[entry_ret_prefix_retpc_lookup, entry_ret_prefix_lookup]
QED

Theorem entry_ret_family_wrap_exec:
  s.vs_params = entry_wrap_inputs ==>
  ?u. exec_block fuel ctx
    (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks)
    (s with vs_inst_idx := 0) =
      IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u /\
    u.vs_vars = (update_var "rpc" s.vs_return_pc_token
       (entry_ret_prefix_state (SUC (dimword (:256))) s)).vs_vars
Proof
  strip_tac >> irule entry_ret_family_exec >>
  irule entry_ret_family_wrap_param_shape >> first_assum ACCEPT_TAC
QED

(* A state at the required index whose run matches the canonical run
   agrees with the canonical prefix state on every name but rpc. *)
Theorem entry_ret_family_witness_lookup[local]:
  EVERY (entry_param_shape s)
    (get_params (HD (entry_ret_family n).fn_blocks).bb_instructions) /\
  t.vs_inst_idx = n + 1 /\
  exec_block fuel ctx (HD (entry_ret_family n).fn_blocks)
    (s with vs_inst_idx := 0) =
  exec_block fuel ctx (HD (entry_ret_family n).fn_blocks) t ==>
  !x. x <> "rpc" ==>
    FLOOKUP t.vs_vars x = FLOOKUP (entry_ret_prefix_state n s).vs_vars x
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule entry_ret_family_exec >>
  disch_then (qspecl_then [`fuel`, `ctx`]
    (qx_choose_then `u` strip_assume_tac)) >>
  `exec_block fuel ctx (HD (entry_ret_family n).fn_blocks) t =
     IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u` by metis_tac[] >>
  drule_all entry_ret_family_tail_exec >> strip_tac >>
  qpat_x_assum `u.vs_vars = _` mp_tac >>
  simp[update_var_def] >>
  disch_then (mp_tac o Q.AP_TERM `\vars. FLOOKUP vars x`) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem entry_ret_family_wrap_witness:
  s.vs_params = entry_wrap_inputs /\
  t.vs_inst_idx = SUC (dimword (:256)) + 1 /\
  exec_block fuel ctx
    (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks)
    (s with vs_inst_idx := 0) =
  exec_block fuel ctx
    (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks) t ==>
  FLOOKUP t.vs_vars (entry_probe_name (dimword (:256))) = SOME 0w
Proof
  strip_tac >>
  drule entry_ret_family_wrap_param_shape >> strip_tac >>
  mp_tac (Q.INST [`n` |-> `SUC (dimword (:256))`]
    entry_ret_family_witness_lookup) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qspec_then `entry_probe_name (dimword (:256))` mp_tac) >>
  rewrite_tac[entry_probe_name_not_opaque] >>
  disch_then SUBST1_TAC >>
  irule entry_ret_prefix_wrapped_lookup >> first_assum ACCEPT_TAC
QED


Definition entry_wrap_source_def:
  entry_wrap_source = (init_venom_state "entry") with
    <|vs_params := entry_wrap_inputs; vs_return_pc_token := 0w|>
End

Definition entry_wrap_region_def:
  entry_wrap_region = <|sr_fn_name := "entry_test";
    sr_spill_base := 0; sr_spill_end := 0; sr_plan := []|>
End

Definition entry_wrap_context_def:
  entry_wrap_context = <|cp_regions := [entry_wrap_region];
    cp_max_static_eom := 0; cp_peak_spill_end := 0; cp_initial_fmp := 0|>
End

Definition entry_wrap_asm_def:
  entry_wrap_asm = <|
    as_stack := 0w :: REVERSE entry_wrap_inputs;
    as_memory := entry_wrap_source.vs_memory;
    as_accounts := entry_wrap_source.vs_accounts;
    as_transient := entry_wrap_source.vs_transient;
    as_returndata := entry_wrap_source.vs_returndata;
    as_logs := entry_wrap_source.vs_logs; as_pc := 0;
    as_call_ctx := entry_wrap_source.vs_call_ctx;
    as_tx_ctx := entry_wrap_source.vs_tx_ctx;
    as_block_ctx := entry_wrap_source.vs_block_ctx;
    as_code := entry_wrap_source.vs_code;
    as_prev_hashes := entry_wrap_source.vs_prev_hashes;
    as_outcomes := entry_wrap_source.vs_outcomes;
    as_requests := entry_wrap_source.vs_requests;
    as_pending_deletions := entry_wrap_source.vs_pending_deletions;
    as_gas_readings := []|>
End

Theorem entry_wrap_entry_rel:
  fn_entry_state_rel entry_wrap_context
    (entry_ret_family (SUC (dimword (:256))))
    entry_wrap_source entry_wrap_asm 0w []
Proof
  `!m. LENGTH (get_params (HD (entry_ret_family m).fn_blocks).bb_instructions) = m+1` by
    (gen_tac >> simp[entry_ret_family_get_params, entry_probe_params_def]) >>
  `LENGTH entry_wrap_inputs = SUC (dimword (:256))` by
    rewrite_tac[entry_wrap_inputs_def, LENGTH_GENLIST] >>
  `!m. (HD (entry_ret_family m).fn_blocks).bb_label = "entry"` by
    (gen_tac >> simp[entry_ret_family_def]) >>
  simp[fn_entry_state_rel_def, entry_wrap_context_def,
       entry_wrap_source_def, entry_wrap_asm_def, entry_ret_family_has_retpc,
       init_venom_state_def,
       contextCodegenRelTheory.context_memory_rel_def,
       shared_state_rel_def, codegenRelTheory.venom_asm_terminal_rel_def] >>
  simp[entry_ret_family_def]
QED

Theorem entry_wrap_asm_inversion:
  asm_steps lo o2pc [AsmLabel "entry"] k entry_wrap_asm = AsmOK t /\
  t.as_pc = 1 ==>
  k = 1 /\ t = asm_next entry_wrap_asm
Proof
  Cases_on `k`
  >- simp[asm_steps_def, entry_wrap_asm_def] >>
  Cases_on `n`
  >- simp[asm_steps_def, entry_wrap_asm_def, asm_step_def, asm_next_def] >>
  simp[asm_steps_def, entry_wrap_asm_def, asm_step_def, asm_next_def]
QED

Definition entry_wrap_plan_def:
  entry_wrap_plan = (init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
    MAP (\i. Var (entry_probe_name i)) (GENLIST I (SUC (dimword (:256)))) ++
    [Var "retpc"]
End

Theorem entry_wrap_frozen_premises:
  SND (compute_label_offsets [AsmLabel "entry"]) =
    SND (compute_label_offsets [AsmLabel "entry"]) /\
  build_offset_to_pc [AsmLabel "entry"] = build_offset_to_pc [AsmLabel "entry"] /\
  liveness_analyze (entry_ret_family (SUC (dimword (:256)))) =
    liveness_analyze (entry_ret_family (SUC (dimword (:256)))) /\
  codegen_ready_fn (entry_ret_family (SUC (dimword (:256)))) /\
  retpc_shape_ok (entry_ret_family (SUC (dimword (:256)))) /\
  opaque_use_ok (entry_ret_family (SUC (dimword (:256)))) /\
  init_cleanup_plan_state NONE [] 0 0 = init_cleanup_plan_state NONE [] 0 0 /\
  prepare_params_plan (liveness_analyze (entry_ret_family (SUC (dimword (:256)))))
    (entry_ret_family (SUC (dimword (:256)))) (init_cleanup_plan_state NONE [] 0 0) =
      ([], entry_wrap_plan) /\
  MEM entry_wrap_region entry_wrap_context.cp_regions /\
  entry_wrap_region.sr_fn_name = (entry_ret_family (SUC (dimword (:256)))).fn_name /\
  entry_wrap_region.sr_spill_base <= 0 /\
  entry_wrap_plan.ps_alloc.sa_next_offset <= entry_wrap_region.sr_spill_end /\
  (!off. MEM (SOSpill off) [] ==> off < dimword (:256)) /\
  fn_entry_state_rel entry_wrap_context (entry_ret_family (SUC (dimword (:256))))
    entry_wrap_source entry_wrap_asm 0w [] /\
  asm_block_at [AsmLabel "entry"] entry_wrap_asm.as_pc
    (execute_plan entry_wrap_context.cp_initial_fmp
      (SOLabel (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_label :: []))
Proof
  rewrite_tac[entry_ret_family_wrapped_contracts, entry_wrap_entry_rel,
       entry_ret_family_prepare_cleanup, entry_wrap_plan_def] >>
  pure_rewrite_tac[plan_state_accfupds, combinTheory.K_THM] >>
  `!m. (HD (entry_ret_family m).fn_blocks).bb_label = "entry" /\
         (entry_ret_family m).fn_name = "entry_test"` by
    (gen_tac >> simp[entry_ret_family_def, entry_probe_fn_def]) >>
  asm_rewrite_tac[] >>
  simp[entry_wrap_context_def, entry_wrap_region_def,
       entry_ret_family_def, entry_probe_fn_def,
       init_cleanup_plan_state_def, init_plan_state_def,
       entry_wrap_asm_def, execute_plan_def, asm_block_at_def] >>
  simp[init_spill_alloc_def, exec_stack_op_def]
QED

Theorem entry_wrap_finite_witness_checks:
  entry_wrap_context.cp_initial_fmp = 0 /\
  entry_wrap_region.sr_spill_base = 0 /\
  entry_wrap_region.sr_spill_end = 0 /\
  (0w : 256 word) <> 1w
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem entry_wrap_plan_position:
  EL 1 (REVERSE entry_wrap_plan.ps_stack) =
    Var (entry_probe_name (dimword (:256)))
Proof
  `!n. EL 1 (REVERSE
      (MAP (\i. Var (entry_probe_name i)) (GENLIST I (SUC n)) ++ [Var "retpc"])) =
      Var (entry_probe_name n)` by
    (gen_tac >> simp[REVERSE_APPEND, EL_REVERSE, EL_APPEND_EQN,
                     EL_MAP, EL_GENLIST]) >>
  rewrite_tac[entry_wrap_plan_def, plan_state_accfupds, combinTheory.K_THM] >>
  asm_rewrite_tac[]
QED

Theorem entry_wrap_asm_position:
  EL 1 (asm_next entry_wrap_asm).as_stack = 1w
Proof
  `!n. EL 0 (REVERSE (GENLIST (\i. if i = 0 then 0w else 1w :256 word) (SUC n))) =
        (if n = 0 then 0w else 1w)` by
    (gen_tac >> simp[EL_REVERSE, EL_GENLIST]) >>
  rewrite_tac[asm_next_def, entry_wrap_asm_def, asm_state_accfupds,
              asm_state_accessors, combinTheory.K_THM, EL] >>
  once_rewrite_tac[ONE] >> rewrite_tac[EL, TL, GSYM ONE] >>
  rewrite_tac[GSYM (CONJUNCT1 EL), entry_wrap_inputs_def] >>
  asm_rewrite_tac[param_index_wrap_discriminator]
QED

Theorem entry_wrap_frame_impossible:
  FLOOKUP vp.vs_vars (entry_probe_name (dimword (:256))) = SOME 0w ==>
  ~fn_frame_inv ctx entry_wrap_context lo
    (entry_ret_family (SUC (dimword (:256)))) 0w []
    entry_wrap_asm.as_memory entry_wrap_plan vp (asm_next entry_wrap_asm)
Proof
  rpt strip_tac >>
  `plan_stack_rel lo
    (frame_view (entry_ret_family (SUC (dimword (:256)))) 0w vp)
    entry_wrap_plan.ps_stack (asm_next entry_wrap_asm).as_stack` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[fn_frame_inv_def, APPEND_NIL] >>
     strip_tac >> gvs[contextCodegenRelTheory.context_venom_asm_rel_def]) >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `1 < LENGTH entry_wrap_plan.ps_stack` by
    (rewrite_tac[entry_wrap_plan_def, plan_state_accfupds,
                 combinTheory.K_THM, LENGTH_APPEND, LENGTH_MAP, LENGTH_GENLIST] >>
     simp[]) >>
  fs[codegenRelTheory.plan_stack_rel_def] >>
  first_x_assum (qspec_then `1` mp_tac) >>
  asm_rewrite_tac[entry_wrap_plan_position, entry_wrap_asm_position] >>
  simp[dead_stack_marker_def, codegenRelTheory.operand_val_def, frame_view_vars_lookup,
       entry_ret_family_opaque_vars] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem entry_wrap_no_conclusion:
  ~(?n t vp.
    asm_steps (SND (compute_label_offsets [AsmLabel "entry"]))
      (build_offset_to_pc [AsmLabel "entry"]) [AsmLabel "entry"] n
      entry_wrap_asm = AsmOK t /\
    t.as_pc = entry_wrap_asm.as_pc +
      LENGTH (execute_plan entry_wrap_context.cp_initial_fmp
        (SOLabel (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_label :: [])) /\
    exec_block fuel ctx (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks)
      (entry_wrap_source with vs_inst_idx := 0) =
    exec_block fuel ctx (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks) vp /\
    vp.vs_inst_idx = LENGTH (get_params
      (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_instructions) /\
    fn_frame_inv ctx entry_wrap_context
      (SND (compute_label_offsets [AsmLabel "entry"]))
      (entry_ret_family (SUC (dimword (:256)))) 0w []
      entry_wrap_asm.as_memory entry_wrap_plan vp t)
Proof
  strip_tac >>
  `!m. LENGTH (get_params (HD (entry_ret_family m).fn_blocks).bb_instructions) = m+1` by
    (gen_tac >> simp[entry_ret_family_get_params, entry_probe_params_def]) >>
  `FLOOKUP vp.vs_vars (entry_probe_name (dimword (:256))) = SOME 0w` by
    (mp_tac (Q.INST [`s` |-> `entry_wrap_source`, `t` |-> `vp`]
       entry_ret_family_wrap_witness) >>
     disch_then irule >>
     asm_rewrite_tac[] >> simp[entry_wrap_source_def]) >>
  `t.as_pc = 1` by
    (qpat_x_assum `t.as_pc = _` mp_tac >>
     simp[entry_wrap_asm_def, entry_wrap_context_def, execute_plan_def,
          exec_stack_op_def]) >>
  drule_all entry_wrap_asm_inversion >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`lo` |-> `SND (compute_label_offsets [AsmLabel "entry"])`]
    entry_wrap_frame_impossible) >> simp[]
QED

(* A concrete instance of the frozen implication is false.  The huge list is
   kept symbolic; entry_wrap_finite_witness_checks supplies finite EVAL evidence. *)
Theorem entry_params_frame_sim_counterexample:
  ~((SND (compute_label_offsets [AsmLabel "entry"]) =
       SND (compute_label_offsets [AsmLabel "entry"]) /\
     build_offset_to_pc [AsmLabel "entry"] = build_offset_to_pc [AsmLabel "entry"] /\
     liveness_analyze (entry_ret_family (SUC (dimword (:256)))) =
       liveness_analyze (entry_ret_family (SUC (dimword (:256)))) /\
     codegen_ready_fn (entry_ret_family (SUC (dimword (:256)))) /\
     retpc_shape_ok (entry_ret_family (SUC (dimword (:256)))) /\
     opaque_use_ok (entry_ret_family (SUC (dimword (:256)))) /\
     init_cleanup_plan_state NONE [] 0 0 = init_cleanup_plan_state NONE [] 0 0 /\
     prepare_params_plan (liveness_analyze (entry_ret_family (SUC (dimword (:256)))))
       (entry_ret_family (SUC (dimword (:256)))) (init_cleanup_plan_state NONE [] 0 0) =
         ([], entry_wrap_plan) /\
     MEM entry_wrap_region entry_wrap_context.cp_regions /\
     entry_wrap_region.sr_fn_name = (entry_ret_family (SUC (dimword (:256)))).fn_name /\
     entry_wrap_region.sr_spill_base <= 0 /\
     entry_wrap_plan.ps_alloc.sa_next_offset <= entry_wrap_region.sr_spill_end /\
     (!off. MEM (SOSpill off) [] ==> off < dimword (:256)) /\
     fn_entry_state_rel entry_wrap_context (entry_ret_family (SUC (dimword (:256))))
       entry_wrap_source entry_wrap_asm 0w [] /\
     asm_block_at [AsmLabel "entry"] entry_wrap_asm.as_pc
       (execute_plan entry_wrap_context.cp_initial_fmp
         (SOLabel (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_label :: [])))
    ==>
    ?n t vp.
      asm_steps (SND (compute_label_offsets [AsmLabel "entry"]))
        (build_offset_to_pc [AsmLabel "entry"]) [AsmLabel "entry"] n
        entry_wrap_asm = AsmOK t /\
      t.as_pc = entry_wrap_asm.as_pc +
        LENGTH (execute_plan entry_wrap_context.cp_initial_fmp
          (SOLabel (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_label :: [])) /\
      exec_block fuel ctx (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks)
        (entry_wrap_source with vs_inst_idx := 0) =
      exec_block fuel ctx (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks) vp /\
      vp.vs_inst_idx = LENGTH (get_params
        (HD (entry_ret_family (SUC (dimword (:256)))).fn_blocks).bb_instructions) /\
      fn_frame_inv ctx entry_wrap_context
        (SND (compute_label_offsets [AsmLabel "entry"]))
        (entry_ret_family (SUC (dimword (:256)))) 0w []
        entry_wrap_asm.as_memory entry_wrap_plan vp t)
Proof
  rewrite_tac[entry_wrap_frozen_premises, entry_wrap_no_conclusion]
QED

(* Local simulations use the incoming assembly memory as a proof-only
   source baseline; operand evaluation depends only on the variable map. *)
Theorem entry_context_to_local_memory:
  context_venom_asm_rel cplan lo ps vs st ==>
  venom_asm_rel lo ps (vs with vs_memory := st.as_memory) st
Proof
  `!op. operand_val (vs with vs_memory := st.as_memory) lo op =
        operand_val vs lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[context_venom_asm_rel_def, venom_asm_rel_def,
       plan_stack_rel_def, plan_spill_rel_def, memory_rel_def]
QED

Theorem entry_local_memory_footprint:
  venom_asm_rel lo ps (vs with vs_memory := m0) st ==>
  memory_rel ps.ps_alloc m0 st.as_memory
Proof
  simp[venom_asm_rel_def]
QED

Theorem entry_local_to_context_memory:
  venom_asm_rel lo ps (vs with vs_memory := m0) st /\
  context_memory_rel cplan vs.vs_memory m0 /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  ps.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  context_venom_asm_rel cplan lo ps vs st
Proof
  strip_tac >>
  `!op. operand_val (vs with vs_memory := m0) lo op =
        operand_val vs lo op` by
    (Cases >> simp[operand_val_def]) >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    (irule context_memory_rel_local_prefix >>
     qexistsl_tac [`ps.ps_alloc`, `m0`, `r`] >>
     gvs[venom_asm_rel_def]) >>
  gvs[context_venom_asm_rel_def, venom_asm_rel_def,
      plan_stack_rel_def, plan_spill_rel_def, operand_val_def]
QED

Theorem entry_local_footprint_outside_closure:
  memory_rel alloc m0 m1 /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end /\
  ~closure_spill_byte ctx cplan name b ==>
  read_byte b m1 = read_byte b m0
Proof
  strip_tac >>
  `~(alloc.sa_spill_base <= b /\ b < alloc.sa_next_offset)` by
    (strip_tac >>
     qpat_x_assum `~closure_spill_byte _ _ _ _` mp_tac >>
     simp[closure_spill_byte_def, fcgDefsTheory.fcg_path_def] >>
     qexists `r` >> simp[relationTheory.RTC_REFL]) >>
  gvs[memory_rel_def]
QED

Theorem entry_context_mixed_prefix:
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  context_venom_asm_rel cplan lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  ps' = apply_prefix_ops initial_fmp lo ops ps /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
        context_venom_asm_rel cplan lo ps' vs st' /\
        memory_rel ps'.ps_alloc st.as_memory st'.as_memory
Proof
  rpt strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule_all mixed_prefix_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >>
  drule entry_local_memory_footprint >> strip_tac >>
  gvs[] >>
  irule entry_local_to_context_memory >>
  conj_tac >- (qexists `r` >> simp[]) >>
  qexists `st.as_memory` >> gvs[context_venom_asm_rel_def]
QED

(* The initialized entry allocator supports cleanup below SWAP16. *)
Theorem entry_cleanup_deep_initialized_probe:
  FST (popmany_plan [Var "a"]
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      [Var "a"; Var "b"; Var "c"; Var "d"; Var "e"; Var "f";
       Var "g"; Var "h"; Var "i"; Var "j"; Var "k"; Var "l";
       Var "m"; Var "n"; Var "o"; Var "p"; Var "q"; Var "r"])) =
    GENLIST (\i. SOSpill (32 * i)) 18 ++
    MAP SORestore (0 :: GENLIST (\i. 32 * (16 - i)) 16 ++ [544]) ++
    [SOPop 1]
Proof
  EVAL_TAC
QED

Theorem param_insts_from_entry_shape:
  !insts k s.
    param_insts_from k insts /\
    k + LENGTH insts <= LENGTH s.vs_params /\
    k + LENGTH insts < dimword (:256) ==>
    EVERY (entry_param_shape s) insts
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[param_insts_from_def] >> strip_tac >>
  conj_tac
  >- (gvs[param_inst_at_def, entry_param_shape_def,
          is_param_opcode_iff, LENGTH_EQ_NUM_compute] >>
      simp[w2n_n2w] >> decide_tac) >>
  first_x_assum irule >> qexists `SUC k` >> simp[] >> decide_tac
QED

Theorem bounded_entry_param_shape:
  !fn cplan s st ra rest.
    codegen_ready_fn fn /\ fn_entry_state_rel cplan fn s st ra rest /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) ==>
    EVERY (entry_param_shape s) (get_params (HD fn.fn_blocks).bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `canonical_entry_params_from 0 (HD fn.fn_blocks).bb_instructions` by
    (Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, canonical_param_prefix_def]) >>
  drule canonical_entry_params_from_sound >> strip_tac >>
  `get_params (HD fn.fn_blocks).bb_instructions = users ++ fmp ++ retpc` by
    (asm_rewrite_tac[] >> irule get_params_prefix >>
     gvs[param_insts_from_append, param_insts_from_def,
         param_inst_at_def, EVERY_APPEND, EVERY_MEM] >>
     metis_tac[is_param_opcode_def]) >>
  `~EXISTS (\inst. inst.inst_opcode = RETPC_PARAM) users` by
    (gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  gvs[fn_entry_state_rel_def, fn_has_retpc_def, EXISTS_APPEND,
      param_insts_from_append, param_insts_from_def] >>
  `EVERY (entry_param_shape s) users` by
    (irule param_insts_from_entry_shape >> qexists `0` >> simp[] >> decide_tac) >>
  simp[] >>
  gvs[entry_param_shape_def, param_inst_at_def, LENGTH_EQ_NUM_compute] >>
  simp[w2n_n2w] >> decide_tac
QED

Theorem get_params_suffix:
  !insts. ?suffix. insts = get_params insts ++ suffix
Proof
  Induct >- simp[get_params_def] >> simp[get_params_def] >>
  Cases_on `is_param_opcode h.inst_opcode` >> simp[] >> metis_tac[]
QED

Theorem bounded_entry_param_skip:
  !fuel ctx fn cplan s st ra rest.
    codegen_ready_fn fn /\ fn_entry_state_rel cplan fn s st ra rest /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) ==>
    exec_block fuel ctx (HD fn.fn_blocks) (s with vs_inst_idx := 0) =
    exec_block fuel ctx (HD fn.fn_blocks)
      ((entry_bind_pairs
          (entry_param_pairs s (get_params (HD fn.fn_blocks).bb_instructions)) s)
        with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  rpt strip_tac >> irule entry_param_skip_prefix >>
  conj_tac >- metis_tac[get_params_suffix] >>
  irule bounded_entry_param_shape >> metis_tac[]
QED

Theorem entry_shape_flat_outputs:
  !insts s. EVERY (entry_param_shape s) insts ==>
    FLAT (MAP (\i. i.inst_outputs) insts) =
    MAP (\i. HD i.inst_outputs) insts
Proof
  Induct >> simp[entry_param_shape_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem bounded_entry_param_outputs_distinct:
  !fn cplan s st ra rest.
    codegen_ready_fn fn /\ fn_entry_state_rel cplan fn s st ra rest /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) ==>
    ALL_DISTINCT
      (MAP (\i. HD i.inst_outputs) (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  rpt strip_tac >>
  `EVERY (entry_param_shape s) (get_params (HD fn.fn_blocks).bb_instructions)` by
    (irule bounded_entry_param_shape >> metis_tac[]) >>
  drule entry_shape_flat_outputs >> disch_then (SUBST1_TAC o SYM) >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  Cases_on `fn.fn_blocks` >>
  gvs[codegen_ready_fn_def, canonical_param_prefix_def, ssa_form_def,
      fn_insts_def, fn_insts_blocks_def] >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem entry_param_output_retpc_iff:
  !fn s inst.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ entry_param_shape s inst ==>
    (retpc_var fn (HD inst.inst_outputs) <=> inst.inst_opcode = RETPC_PARAM)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (HD inst.inst_outputs) inst.inst_outputs` by
    gvs[entry_param_shape_def] >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (simp[retpc_var_def] >> irule copy_phi_var_seed >>
      qexists `inst` >> simp[]) >>
  simp[] >> irule noncopy_output_not_retpc >> simp[] >>
  qexists `inst` >>
  gvs[entry_param_shape_def]
QED

Theorem entry_param_frame_lookup:
  !fn ra s insts inst.
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    EVERY (entry_param_shape s) insts /\ MEM inst insts /\
    ALL_DISTINCT (MAP (\i. HD i.inst_outputs) insts) ==>
    FLOOKUP
      (frame_view fn ra (entry_bind_pairs (entry_param_pairs s insts) s)).vs_vars
      (HD inst.inst_outputs) =
    SOME (if inst.inst_opcode = RETPC_PARAM then ra
      else EL (w2n (case HD inst.inst_operands of Lit idx => idx | _ => 0w)) s.vs_params)
Proof
  rpt strip_tac >>
  `entry_param_shape s inst` by metis_tac[EVERY_MEM] >>
  drule_all entry_param_output_retpc_iff >> strip_tac >>
  `FLOOKUP (entry_bind_pairs (entry_param_pairs s insts) s).vs_vars
      (HD inst.inst_outputs) =
    SOME (if inst.inst_opcode = RETPC_PARAM then s.vs_return_pc_token
      else EL (w2n (case HD inst.inst_operands of Lit idx => idx | _ => 0w)) s.vs_params)` by
    (irule entry_bind_pairs_lookup >>
     simp[entry_param_pairs_def, MAP_MAP_o, combinTheory.o_DEF] >>
     simp[MEM_MAP] >> qexists `inst` >> simp[]) >>
  simp[frame_view_vars_lookup] >> Cases_on `inst.inst_opcode = RETPC_PARAM` >> simp[]
QED

Theorem param_insts_from_el:
  !insts k j. param_insts_from k insts /\ j < LENGTH insts ==>
    param_inst_at (k + j) (EL j insts)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `j` >>
  simp[param_insts_from_def, ADD_CLAUSES] >> strip_tac >>
  first_x_assum (qspecl_then [`SUC k`, `n`] mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem canonical_get_params_layout:
  !fn params.
    codegen_ready_fn fn /\
    params = get_params (HD fn.fn_blocks).bb_instructions ==>
    param_insts_from 0 params /\
    ?ordinary ret.
      params = ordinary ++ ret /\
      EVERY (\i. i.inst_opcode <> RETPC_PARAM) ordinary /\
      (ret = [] \/ ?i. ret = [i] /\ i.inst_opcode = RETPC_PARAM)
Proof
  rpt gen_tac >> strip_tac >>
  `canonical_entry_params_from 0 (HD fn.fn_blocks).bb_instructions` by
    (Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, canonical_param_prefix_def]) >>
  drule canonical_entry_params_from_sound >> strip_tac >>
  `params = users ++ fmp ++ retpc` by
    (gvs[] >> irule get_params_prefix >>
     gvs[param_insts_from_append, param_insts_from_def,
         param_inst_at_def, EVERY_APPEND, EVERY_MEM] >>
     metis_tac[is_param_opcode_def]) >>
  (conj_tac >- metis_tac[] >>
   qexistsl [`users ++ fmp`, `retpc`] >>
   gvs[EVERY_APPEND, EVERY_MEM])
QED

Theorem bounded_entry_param_frame_values:
  !fn cp s st ra rest params j.
    codegen_ready_fn fn /\ fn_entry_state_rel cp fn s st ra rest /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    LENGTH params < dimword (:256) /\ j < LENGTH params ==>
    FLOOKUP
      (frame_view fn ra (entry_bind_pairs (entry_param_pairs s params) s)).vs_vars
      (HD (EL j params).inst_outputs) =
    SOME (EL j (s.vs_params ++ if fn_has_retpc fn then [ra] else []))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (entry_param_shape s) params` by
    (gvs[] >> irule bounded_entry_param_shape >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. HD i.inst_outputs) params)` by
    (gvs[] >> irule bounded_entry_param_outputs_distinct >> simp[] >> metis_tac[]) >>
  `MEM (EL j params) (fn_insts fn)` by
    (qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
     Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, canonical_param_prefix_def,
         fn_insts_def, fn_insts_blocks_def] >>
     metis_tac[MEM_EL, MEM_APPEND]) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL j params) params` by simp[EL_MEM] >>
  drule_all entry_param_frame_lookup >>
  disch_then (qspec_then `ra` mp_tac) >>
  strip_tac >>
  `param_insts_from 0 params` by metis_tac[canonical_get_params_layout] >>
  `param_inst_at j (EL j params)` by
    (drule_all param_insts_from_el >> simp[]) >>
  drule_all canonical_get_params_layout >> strip_tac >>
  `fn_has_retpc fn <=> EXISTS (\i. i.inst_opcode = RETPC_PARAM) params` by
    gvs[fn_has_retpc_def] >>
  `LENGTH s.vs_params = LENGTH params - (if fn_has_retpc fn then 1 else 0)` by
    (Cases_on `fn_has_retpc fn` >> gvs[fn_entry_state_rel_def] >> decide_tac) >>
  `~EXISTS (\i. i.inst_opcode = RETPC_PARAM) ordinary` by
    (gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `params = get_params _` kall_tac >>
  gvs[EXISTS_APPEND, param_inst_at_def, w2n_n2w] >>
  Cases_on `j < LENGTH ordinary` >>
  gvs[EL_APPEND1, EL_APPEND2, EVERY_EL] >>
  `j = LENGTH ordinary` by decide_tac >> gvs[]
QED

Theorem bounded_entry_param_stack_rel:
  !fn cp s st ra rest lo params vp.
    codegen_ready_fn fn /\ fn_entry_state_rel cp fn s st ra rest /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    LENGTH params < dimword (:256) /\
    vp = (entry_bind_pairs (entry_param_pairs s params) s)
      with vs_inst_idx := LENGTH params ==>
    plan_stack_rel lo (frame_view fn ra vp)
      (MAP (\i. Var (HD i.inst_outputs)) params)
      ((if fn_has_retpc fn then [ra] else []) ++ REVERSE s.vs_params)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH params = LENGTH (s.vs_params ++ if fn_has_retpc fn then [ra] else [])` by
    (Cases_on `fn_has_retpc fn` >> gvs[fn_entry_state_rel_def]) >>
  `!j. j < LENGTH params ==>
    FLOOKUP (frame_view fn ra vp).vs_vars (HD (EL j params).inst_outputs) =
    SOME (EL j (s.vs_params ++ if fn_has_retpc fn then [ra] else []))` by
    (rpt strip_tac >>
     `FLOOKUP (frame_view fn ra vp).vs_vars =
      FLOOKUP (frame_view fn ra (entry_bind_pairs (entry_param_pairs s params) s)).vs_vars` by
       gvs[frame_view_def] >>
     simp[] >> irule bounded_entry_param_frame_values >>
     gvs[] >> metis_tac[]) >>
  `((if fn_has_retpc fn then [ra] else []) ++ REVERSE s.vs_params) =
    REVERSE (s.vs_params ++ if fn_has_retpc fn then [ra] else [])` by
    (Cases_on `fn_has_retpc fn` >> simp[]) >>
  qpat_x_assum `vp = _` kall_tac >>
  qpat_x_assum `params = get_params _` kall_tac >>
  simp[plan_stack_rel_def, EL_REVERSE, EL_MAP, operand_val_def] >>
  rpt strip_tac >> disj2_tac >>
  qpat_x_assum `!j. _` (qspec_then `LENGTH params - 1 - i` mp_tac) >>
  gvs[] >> decide_tac
QED

Theorem bounded_entry_installed_context_rel:
  !fn cp s st ra rest lo params vp ps0 ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\ fn_entry_state_rel cp fn s st ra rest /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    LENGTH params < dimword (:256) /\
    vp = (entry_bind_pairs (entry_param_pairs s params) s)
      with vs_inst_idx := LENGTH params /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr ==>
    context_venom_asm_rel cp lo
      (ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params)
      (frame_view fn ra vp)
      (st with as_stack :=
        (if fn_has_retpc fn then [ra] else []) ++ REVERSE s.vs_params)
Proof
  rpt gen_tac >> strip_tac >>
  `plan_stack_rel lo (frame_view fn ra vp)
    (MAP (\i. Var (HD i.inst_outputs)) params)
    ((if fn_has_retpc fn then [ra] else []) ++ REVERSE s.vs_params)` by
    (irule bounded_entry_param_stack_rel >> metis_tac[]) >>
  simp[context_venom_asm_rel_def] >>
  conj_tac >- gvs[] >>
  gvs[init_cleanup_plan_state_def, init_plan_state_def,
      plan_spill_rel_def, frame_view_def, entry_bind_pairs_normal,
      fn_entry_state_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def]
QED

Theorem entry_do_swap_prefix_spill_wf:
  !dist ps ops ps' lo initial_fmp.
    do_swap dist ps = (ops,ps') /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) ==>
    prefix_spill_wf initial_fmp lo ops ps
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist <= 16`
  >- (Cases_on `dist = 0` >>
      gvs[do_swap_def, prefix_spill_wf_def, spill_op_wf_def]) >>
  `16 < dist` by decide_tac >>
  `ALL_DISTINCT (top_n (dist + 1) ps.ps_stack)` by
    simp[top_n_def, ALL_DISTINCT_TAKE] >>
  `EVERY (\off. off < dimword (:256))
    (FST (spill_alloc_n [] ps.ps_alloc (top_n (dist + 1) ps.ps_stack)))` by
    (qspecl_then [`dist`, `ps`] mp_tac do_swap_big_decompose >>
     simp[LET_THM] >> strip_tac >>
     gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  irule do_swap_prefix_spill_wf_from_generated_spills >>
  simp[] >> qexistsl [`dist`, `ps'`] >> simp[] >>
  irule do_swap_generated_spills_prefix_wf_bounds >> simp[]
QED

Theorem entry_pop_one_step_some:
  !item ps dist.
    stack_get_depth item ps.ps_stack = SOME dist ==>
    pop_one_step item ps =
      (FST (do_swap dist ps) ++ [SOPop 1],
       (SND (do_swap dist ps)) with ps_stack :=
         stack_pop 1 (SND (do_swap dist ps)).ps_stack)
Proof
  rpt strip_tac >> simp[pop_one_step_def] >>
  Cases_on `dist = 0` >- simp[do_swap_def] >>
  Cases_on `do_swap dist ps` >> simp[]
QED

Theorem entry_pop_one_step_structural:
  !item ps ops ps'.
    pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    ALL_DISTINCT ps'.ps_stack /\
    DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth item ps.ps_stack`
  >- gvs[pop_one_step_def] >>
  rename1 `stack_get_depth item ps.ps_stack = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  drule_all entry_pop_one_step_some >> strip_tac >>
  drule_all do_swap_structural_layout_wf >> strip_tac >>
  gvs[stack_pop_def, ALL_DISTINCT_TAKE] >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_TAKE]
QED

Theorem entry_pop_one_step_sim:
  !item ps ops ps' lo o2pc prog vs st initial_fmp.
    pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_pop_one_step_structural >> strip_tac >>
  Cases_on `stack_get_depth item ps.ps_stack`
  >- (gvs[pop_one_step_def] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_depth item ps.ps_stack = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  drule_all entry_pop_one_step_some >> strip_tac >>
  Cases_on `do_swap dist ps` >>
  rename1 `do_swap dist ps = (swap_ops, ps2)` >>
  gvs[] >>
  `prefix_spill_wf initial_fmp lo swap_ops ps` by
    (irule entry_do_swap_prefix_spill_wf >> simp[] >> metis_tac[]) >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all do_swap_venom_asm_rel_layout >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `0 < LENGTH ps2.ps_stack` by
    (drule do_swap_length >> simp[] >> decide_tac) >>
  `is_simple_stack_op (SOPop 1)` by simp[is_simple_stack_op_def] >>
  `FST (stack_op_wf lo (SOPop 1) (LENGTH ps2.ps_stack))` by
    simp[stack_op_wf_def] >>
  `asm_block_at prog st'.as_pc (exec_stack_op initial_fmp (SOPop 1))` by
    gvs[execute_plan_def] >>
  qpat_x_assum `venom_asm_rel lo ps vs st` kall_tac >>
  drule_all simple_op_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st''` >> conj_tac
  >- (simp[execute_plan_def] >> irule asm_steps_compose_ok >>
      qexists `st'` >> gvs[execute_plan_def]) >>
  gvs[apply_simple_op_def, execute_plan_def, stack_pop_def]
QED

Theorem entry_pop_steps_sim:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    plan_steps pop_one_step items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  Induct
  >- (rpt gen_tac >> simp[plan_steps_def] >> strip_tac >>
      gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `pop_one_step h ps` >>
  rename1 `pop_one_step h ps = (ops1, ps1)` >>
  Cases_on `plan_steps pop_one_step items ps1` >>
  rename1 `plan_steps pop_one_step items ps1 = (ops2, ps2)` >>
  gvs[plan_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `!off. MEM (SOSpill off) ops1 ==> off < dimword (:256)` by gvs[] >>
  `!off. MEM (SOSpill off) ops2 ==> off < dimword (:256)` by gvs[] >>
  drule_all entry_pop_one_step_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp ops2)` by gvs[] >>
  qpat_x_assum `!off. MEM (SOSpill off) ops2 ==> _` (assume_tac o SRULE []) >>
  first_x_assum drule_all >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st''` >> simp[] >> irule asm_steps_compose_ok >>
  qexists `st'` >> simp[]
QED

Theorem entry_pop_fold_sim:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    FOLDL pop_foldl_body ([],ps) items = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  pure_rewrite_tac[pop_foldl_body_eq_foldl_body, GSYM plan_steps_eq_foldl] >>
  ACCEPT_TAC entry_pop_steps_sim
QED

Theorem popmany_individual_sim_structural:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    popmany_individual items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> pure_rewrite_tac[popmany_individual_eq_foldl] >>
  strip_tac >> drule_all entry_pop_fold_sim >> simp[]
QED

Theorem popmany_plan_sim_structural:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `items = []`
  >- (gvs[popmany_plan_def] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- ( qpat_x_assum `_ /\ _` strip_assume_tac >>
       `LENGTH items < LENGTH ps.ps_stack` by
        (irule contiguous_top_stack_bound >> simp[]) >>
       `LENGTH items <= 16` by gvs[is_contiguous_top_def] >>
       drule_all popmany_plan_contiguous_sim >>
       disch_then (qspec_then `o2pc` strip_assume_tac) >>
       qexists `st'` >> simp[] >>
       qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
       Cases_on `items` >- gvs[] >>
       simp[popmany_plan_def] >>
       Cases_on `do_swap (LENGTH (h::t)) ps` >>
       rename1 `do_swap _ ps = (swap_ops, ps2)` >>
       strip_tac >> gvs[] >>
       drule_all do_swap_structural_layout_wf >> strip_tac >>
       gvs[stack_pop_def, ALL_DISTINCT_TAKE] >>
       gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_TAKE]) >>
  `popmany_individual items ps = (ops,ps')` by
    (drule_all popmany_plan_noncontig_new >> simp[]) >>
  drule_all popmany_individual_sim_structural >> simp[]
QED

Theorem entry_context_popmany_sim:
  !items ps ops ps' cp lo o2pc prog vs st initial_fmp r.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    context_venom_asm_rel cp lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cp.cp_regions /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      context_venom_asm_rel cp lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      memory_rel ps'.ps_alloc st.as_memory st'.as_memory /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule_all popmany_plan_sim_structural >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `context_venom_asm_rel cplan lo ps vs st` >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    gvs[context_venom_asm_rel_def] >>
  drule_all entry_local_to_context_memory >> strip_tac >>
  drule entry_local_memory_footprint >> strip_tac >>
  qexists `st'` >> simp[]
QED

Theorem entry_context_popmany_outside_closure:
  !items ps ops ps' cp lo o2pc prog vs st initial_fmp r ctx name.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    context_venom_asm_rel cp lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      context_venom_asm_rel cp lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~closure_spill_byte ctx cp name b ==>
        read_byte b st'.as_memory = read_byte b st.as_memory) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_context_popmany_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> simp[] >> rpt strip_tac >>
  irule entry_local_footprint_outside_closure >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem param_insts_flat_outputs:
  !params k. param_insts_from k params ==>
    FLAT (MAP (\i. i.inst_outputs) params) =
    MAP (\i. HD i.inst_outputs) params
Proof
  Induct >> simp[param_insts_from_def] >> rpt strip_tac >>
  `h.inst_outputs = [HD h.inst_outputs]` by
    (gvs[param_inst_at_def] >> Cases_on `h.inst_outputs` >> gvs[] >>
     Cases_on `t'` >> gvs[]) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `h.inst_outputs = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ready_entry_param_outputs_distinct:
  !fn. codegen_ready_fn fn ==>
    ALL_DISTINCT
      (MAP (\i. HD i.inst_outputs) (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  rpt strip_tac >>
  `param_insts_from 0 (get_params (HD fn.fn_blocks).bb_instructions)` by
    (irule (cj 1 canonical_get_params_layout) >> qexists `fn` >> simp[]) >>
  drule param_insts_flat_outputs >> disch_then (SUBST1_TAC o SYM) >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  Cases_on `fn.fn_blocks` >>
  gvs[codegen_ready_fn_def, canonical_param_prefix_def, ssa_form_def,
      fn_insts_def, fn_insts_blocks_def] >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem entry_installed_structural:
  !fn params ps0 pi ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    pi = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params ==>
    FOLDL (\s inst. s with ps_stack :=
      stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps0 params = pi /\
    spill_alloc_layout_wf pi.ps_alloc pi.ps_spilled /\
    ALL_DISTINCT pi.ps_stack /\
    DISJOINT (set pi.ps_stack) (FDOM pi.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule ready_entry_param_outputs_distinct >> strip_tac >>
  gvs[parameter_stack_fold, init_cleanup_plan_state_def, init_plan_state_def,
      init_spill_alloc_def, spill_alloc_layout_wf_def, MAP_MAP_o,
      ALL_DISTINCT_MAP, combinTheory.o_DEF] >>
  `MAP (\i. Var (HD i.inst_outputs)) (get_params (HD fn.fn_blocks).bb_instructions) =
   MAP Var (MAP (\i. HD i.inst_outputs) (get_params (HD fn.fn_blocks).bb_instructions))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  simp[] >> irule ALL_DISTINCT_MAP_INJ >> simp[]
QED

Theorem entry_optimistic_swap_sim_structural:
  !dfg inst next_live next_is_term ps ops ps' lo o2pc prog vs st initial_fmp.
    optimistic_swap_plan dfg inst next_live next_is_term ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  Cases_on `next_is_term` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `inst.inst_outputs = []` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `next_live = []` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST next_live))`
  >- (simp[] >> strip_tac >> gvs[] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  simp[] >> Cases_on `stack_get_depth (Var (LAST next_live)) ps.ps_stack`
  >- (simp[] >> strip_tac >> gvs[] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_depth _ ps.ps_stack = SOME dist` >> simp[] >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (irule entry_do_swap_prefix_spill_wf >> simp[] >> metis_tac[]) >>
  drule_all do_swap_structural_layout_wf >> strip_tac >>
  drule_all do_swap_venom_asm_rel_layout >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> gvs[]
QED

Theorem entry_context_optimistic_swap_outside_closure:
  !dfg inst next_live next_is_term ps ops ps' cp lo o2pc prog vs st initial_fmp r ctx name.
    optimistic_swap_plan dfg inst next_live next_is_term ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    context_venom_asm_rel cp lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      context_venom_asm_rel cp lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~closure_spill_byte ctx cp name b ==>
        read_byte b st'.as_memory = read_byte b st.as_memory) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule_all entry_optimistic_swap_sim_structural >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `context_venom_asm_rel cplan lo ps vs st` >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    gvs[context_venom_asm_rel_def] >>
  drule_all entry_local_to_context_memory >> strip_tac >>
  drule entry_local_memory_footprint >> strip_tac >>
  qexists `st'` >> simp[] >> rpt strip_tac >>
  irule entry_local_footprint_outside_closure >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem entry_prepare_params_context_sim:
  !ps0 ch growth spill_base lbl_ctr params fn pi liveness ops ps1
   cplan lo o2pc prog vv st initial_fmp r ctx name.
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    params = get_params (HD fn.fn_blocks).bb_instructions /\
    pi = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params /\
    codegen_ready_fn fn /\
    prepare_params_plan liveness fn ps0 = (ops,ps1) /\
    (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
    context_venom_asm_rel cplan lo pi vv st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      context_venom_asm_rel cplan lo ps1 vv st' /\
      (!b. ~closure_spill_byte ctx cplan name b ==>
        read_byte b st'.as_memory = read_byte b st.as_memory) /\
      r.sr_spill_base <= ps1.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `context_venom_asm_rel cplan lo installed vv st` >>
  `ps1.ps_alloc.sa_spill_base = spill_base` by
    (drule prepare_params_plan_spill_base >>
     gvs[init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]) >>
  Cases_on `params = []`
  >- (`installed = ps0` by
        gvs[init_cleanup_plan_state_def, init_plan_state_def] >>
      gvs[prepare_params_plan_def] >>
      qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  `FOLDL (\s inst. s with ps_stack := stack_push (Var (HD inst.inst_outputs)) s.ps_stack)
    ps0 params = installed /\
   spill_alloc_layout_wf installed.ps_alloc installed.ps_spilled /\
   ALL_DISTINCT installed.ps_stack /\
   DISJOINT (set installed.ps_stack) (FDOM installed.ps_spilled)` by
    (irule entry_installed_structural >> metis_tac[]) >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  pure_rewrite_tac[prepare_params_plan_def, LET_THM] >> BETA_TAC >>
  qpat_assum `params = get_params _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `FOLDL _ ps0 params = installed` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `params <> []` (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead installed` >>
  Cases_on `popmany_plan dead installed` >>
  rename1 `popmany_plan dead installed = (pop_ops, ps2)` >>
  pure_rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `optimistic_swap_plan dfg_empty (LAST params) live term ps2` >>
  Cases_on `optimistic_swap_plan dfg_empty (LAST params) live term ps2` >>
  rename1 `optimistic_swap_plan _ _ _ _ ps2 = (swap_ops, ps3)` >>
  simp[pairTheory.UNCURRY_DEF, pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `pop_ops ++ swap_ops = ops` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ps3 = ps1` SUBST_ALL_TAC >>
  `r.sr_spill_base <= ps2.ps_alloc.sa_spill_base` by
    (drule optimistic_swap_plan_spill_base >> simp[]) >>
  `ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule optimistic_swap_plan_next_offset >> decide_tac) >>
  qpat_x_assum `ps0 = _` kall_tac >>
  qpat_x_assum `params = _` kall_tac >>
  qpat_x_assum `installed = _` kall_tac >>
  qpat_x_assum `FOLDL _ _ _ = _` kall_tac >>
  qpat_x_assum `codegen_ready_fn _` kall_tac >>
  qpat_x_assum `Abbrev (dead = _)` kall_tac >>
  qpat_x_assum `Abbrev (live = _)` kall_tac >>
  qpat_x_assum `Abbrev (term = _)` kall_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `!off. MEM (SOSpill off) pop_ops ==> off < dimword (:256)` by gvs[] >>
  `!off. MEM (SOSpill off) swap_ops ==> off < dimword (:256)` by gvs[] >>
  drule_all entry_context_popmany_outside_closure >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp swap_ops)` by gvs[] >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base` by simp[] >>
  drule_all entry_context_optimistic_swap_outside_closure >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  qexists `st''` >> conj_tac
  >- (simp[] >> irule asm_steps_compose_ok >> qexists `st'` >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem entry_local_run_frame_inv:
  !a top rest lo o2pc prog n t cplan ps fn ra vp ctx r.
    a.as_stack = top ++ rest /\
    asm_steps lo o2pc prog n (a with as_stack := top) = AsmOK t /\
    context_venom_asm_rel cplan lo ps (frame_view fn ra vp) t /\
    ~vp.vs_halted /\ n2w cplan.cp_initial_fmp = vp.vs_initial_fmp /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      read_byte b t.as_memory = read_byte b a.as_memory) /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?a'. asm_steps lo o2pc prog n a = AsmOK a' /\
      a'.as_pc = t.as_pc /\
      fn_frame_inv ctx cplan lo fn ra rest a.as_memory ps vp a'
Proof
  rpt gen_tac >> strip_tac >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `a with as_stack := top ++ rest = a` by
    simp[asm_state_component_equality] >>
  qexists `t with as_stack := t.as_stack ++ rest` >>
  conj_tac >- metis_tac[] >>
  simp[fn_frame_inv_def] >> qexists `r` >> simp[]
QED
