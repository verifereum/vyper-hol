(* Inputs whose inlined output breaks the pointer conjunct of
 * function_inliner_pass_correct_stmt's conclusion or splits a
 * revert-forwarding pair, and the premise that now excludes each.
 * The first four meet the pointer conjunct of inliner_stage_inv; each of the
 * first three fails inliner_shape_ok, and its witness states the negation of
 * the exact clause added for it, while the split pair fails
 * inliner_input_guard by its revert-forwarding clause. Each of the four met
 * every syntactic premise as it stood before its clause was added; that was
 * kernel-checked at the time on this branch (commit bfcf26f436). The last two
 * meet every syntactic premise. o1_src_inv, the run-state premises and the
 * allocation bounds are about states: they are not evaluable here and were
 * never checked for any of these inputs.
 *
 * TOP-LEVEL:
 *   inliner_phi_cover_witness       -- a PHI missing a predecessor
 *   inliner_retpc_arity_witness     -- the return-PC slot binds a PARAM
 *   inliner_param_dalloca_name_witness -- PARAM and DALLOCA share a name
 *   inliner_rdc_split_witness       -- the call site splits an RDC pair
 *   inliner_rfp_cut_witness         -- inlining creates an RDC pair
 *   inliner_two_root_arg_witness    -- a readonly argument with two roots
 *)
Theory functionInlinerReviewWitness
Ancestors
  functionInlinerShapeCheck codegenReadyCompute contextCodegenRel
  functionInlinerPtrWitness functionInlinerContract functionInlinerPtrCheck
  functionInlinerDefs o1SourceUnitCheck o1PassContract ptrOkCheck
  ptrDiscipline pointerConfinedDefs unitShapeDefs callLayoutDefs
  defsReachCheck dretDesugarDefs fcgDefs memLocDefs vyperCompiler
  venomInst venomWf list pred_set
Libs
  finite_mapLib wordsLib

(* ===== Shared facts ===== *)

(* With no PARAM, the pointer-parameter map does not matter. *)
Theorem no_param_ptr_roots:
  EVERY (\i. i.inst_opcode <> PARAM) (fn_insts fn) ==>
  ptr_roots P fn = ptr_roots (K {}) fn
Proof
  rw[ptr_roots_def, EXTENSION, EVERY_MEM] >> metis_tac[]
QED

Theorem no_param_ptr_roots_list:
  EVERY (\i. i.inst_opcode <> PARAM) (fn_insts fn) ==>
  ptr_roots P fn =
    set (opcode_root_list ALLOCA fn ++ opcode_root_list DALLOCA fn ++
         param_root_list (K [] fn.fn_name) fn)
Proof
  strip_tac >> drule no_param_ptr_roots >> simp[inline_root_list_set] >>
  disch_then kall_tac >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

(* reachable_fn with the CFG closures replaced by the computed analysis. *)
Definition reachable_fn_eval_def:
  reachable_fn_eval fn =
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
             MAP (\inst.
               if inst.inst_opcode = PHI then
                 inst with inst_operands :=
                   filter_phi_ops
                     (FILTER (\l. cfg_reachable_of (cfg_analyze fn) l /\
                                  MEM bb.bb_label
                                    (cfg_succs_of (cfg_analyze fn) l))
                        (MAP (\bb. bb.bb_label) fn.fn_blocks))
                     inst.inst_operands
               else inst) bb.bb_instructions)
        (FILTER (\bb. cfg_reachable_of (cfg_analyze fn) bb.bb_label)
           fn.fn_blocks)
End

Theorem reachable_fn_eval:
  wf_function fn ==> reachable_fn fn = reachable_fn_eval fn
Proof
  strip_tac >>
  `fn_reachable fn = cfg_reachable_of (cfg_analyze fn)` by
    simp[FUN_EQ_THM, fn_reachable_cfg_analyze] >>
  `!lbl. reachable_inst fn lbl =
         \inst. if inst.inst_opcode = PHI then
                  inst with inst_operands :=
                    filter_phi_ops
                      (FILTER (\l. cfg_reachable_of (cfg_analyze fn) l /\
                                   MEM lbl (cfg_succs_of (cfg_analyze fn) l))
                         (MAP (\bb. bb.bb_label) fn.fn_blocks))
                      inst.inst_operands
                else inst` by
    simp[FUN_EQ_THM, reachable_inst_def, reachable_preds_def,
         fn_cfg_edge_cfg_analyze] >>
  asm_simp_tac std_ss [reachable_fn_def, reachable_fn_eval_def]
QED

(* The pointer conjunct of inliner_stage_inv, by evaluation. *)
Theorem stage_ptr_ok_from_eval:
  inline_ptr_ok_check C /\ reachable_ctx C = C /\
  EVERY (\fn. wf_function fn /\ fn_ptr_ok_check (ctx_ptr_param_list C) fn /\
              fn_ptr_ok_check (ctx_ptr_param_list C) (reachable_fn_eval fn))
    C.ctx_functions ==>
  ?P W. (!nm. W nm SUBSET P nm) /\
        EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
          C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)
Proof
  strip_tac >>
  qexistsl_tac [`\nm. set (ctx_ptr_param_list C nm)`,
                `ctx_write_param_set C`] >>
  simp[inline_ptr_ok_check_sound, ctx_write_param_set_subset] >>
  fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  drule reachable_fn_eval >> disch_then SUBST1_TAC >>
  qspecl_then [`ctx_ptr_param_list C`, `fn`] mp_tac fn_ptr_ok_check_sound >>
  qspecl_then [`ctx_ptr_param_list C`, `reachable_fn_eval fn`] mp_tac
    fn_ptr_ok_check_sound >>
  simp[]
QED

Theorem every_defs_reach_uses_check[local]:
  EVERY fn_defs_reach_uses_check fns ==> EVERY fn_defs_reach_uses fns
Proof
  rw[EVERY_MEM, fn_defs_reach_uses_check_sound]
QED

Definition witness_rank_def:
  witness_rank (nm:string) = if nm = "entry" then 1n else 0
End

val shape_tac =
  irule inliner_shape_check_sound >> conj_tac
  >- (irule every_defs_reach_uses_check >> EVAL_TAC)
  >> qexists_tac `witness_rank` >> EVAL_TAC;

val guard_tac =
  rewrite_tac[inliner_input_guard_def] >> conj_tac
  >- (match_mp_tac rfp_self_contained_check_guard >> EVAL_TAC)
  >> EVAL_TAC;

val premises_tac =
  rpt conj_tac
  >- EVAL_TAC
  >- guard_tac
  >> irule stage_ptr_ok_from_eval >> EVAL_TAC;

(* The clauses of inliner_shape_ok that reject the review's inputs. *)
Theorem shape_ok_phis_cover[local]:
  inliner_shape_ok C ==>
  EVERY fn_phis_cover_preds (reachable_ctx C).ctx_functions
Proof
  simp[inliner_shape_ok_def]
QED

Theorem shape_ok_retpc[local]:
  inliner_shape_ok C /\ MEM caller (reachable_ctx C).ctx_functions /\
  MEM inst (fn_insts caller) /\ MEM callee (reachable_ctx C).ctx_functions /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee.fn_name :: args ==>
  IS_SOME (fn_retpc_param callee)
Proof
  simp[inliner_shape_ok_def] >> metis_tac[]
QED

Theorem shape_ok_param_once[local]:
  inliner_shape_ok C /\ MEM fn (reachable_ctx C).ctx_functions ==>
  EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) = 1)
    (FLAT (MAP (\i. i.inst_outputs)
       (FILTER (\i. i.inst_opcode = PARAM) (fn_insts fn))))
Proof
  simp[inliner_shape_ok_def] >> strip_tac >>
  qpat_x_assum `EVERY (\fn. canonical_param_prefix fn /\ _) _`
    (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[EVERY_MEM]
QED

Theorem guard_rfp[local]:
  inliner_input_guard C /\ MEM fn (reachable_ctx C).ctx_functions /\
  MEM bb fn.fn_blocks /\ revert_forward_pair bb i j ==>
  revert_forward_pair
    (bb with bb_instructions := DROP i bb.bb_instructions) 0 (j - i)
Proof
  simp[inliner_input_guard_def] >> metis_tac[]
QED

(* A pointer variable defined by copying a non-pointer. *)
Theorem nonptr_copy_refutes_fn_ptr_ok:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var u] /\ MEM v inst.inst_outputs /\
  v IN fn_pv P fn /\ u NOTIN fn_pv P fn ==>
  ~fn_ptr_ok P fn
Proof
  rpt strip_tac >> fs[fn_ptr_ok_def] >>
  first_x_assum (qspecl_then [`inst`, `v`] mp_tac) >> simp[]
QED

(* ===== Finding 4: PARAM and DALLOCA share an output name ===== *)

Definition name_share_ctx_def:
  name_share_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 ALLOCA [Lit 32w] ["local"];
             mk_inst 1 INVOKE [Label "callee"; Var "local"] [];
             mk_inst 2 STOP [] []]];
       mk_raw_function "callee"
         [witness_block "callee"
            [mk_inst 10 PARAM [Lit 0w] ["x"];
             mk_inst 11 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 12 MSTORE [Var "x"; Lit 1w] [];
             mk_inst 13 DALLOCA [Lit 32w] ["x"];
             mk_inst 14 MSTORE [Var "x"; Lit 2w] [];
             mk_inst 15 RET [Var "pc"] []]]]
      (SOME "entry")
End

(* After inlining, "inl0_x" is both a copy of the caller's ALLOCA and the
   DALLOCA's output, so the store through it mixes the two regions. *)
Theorem name_share_out_not_ptr_ok:
  ~fn_ptr_ok P (HD (function_inliner_ctx 0 name_share_ctx).ctx_functions)
Proof
  qabbrev_tac `fn = HD (function_inliner_ctx 0 name_share_ctx).ctx_functions` >>
  `EVERY (\i. i.inst_opcode <> PARAM) (fn_insts fn)` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `alloca_roots fn = set ["local"]` by
    (simp_tac std_ss [witness_alloca_roots_list, Abbr `fn`] >> EVAL_TAC) >>
  `ptr_roots P fn = set ["local"; "inl0_x"]` by
    (asm_simp_tac std_ss [no_param_ptr_roots_list] >> AP_TERM_TAC >>
     unabbrev_all_tac >> EVAL_TAC) >>
  `ptr_roots P fn DIFF alloca_roots fn = set ["inl0_x"]` by
    (simp[EXTENSION] >> gen_tac >> eq_tac >> rw[] >> simp[]) >>
  `OPTION_MAP (MEM "inl0_x") (pv_closure fn ["local"]) = SOME T /\
   OPTION_MAP (MEM "inl0_x") (pv_closure fn ["inl0_x"]) = SOME T` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"inl0_x" IN pointer_derived_vars fn (set ["local"]) /\
   "inl0_x" IN pointer_derived_vars fn (set ["inl0_x"])` by
    metis_tac[witness_closure_member] >>
  irule witness_mixed_write_refutes_fn_ptr_ok >>
  qexistsl_tac [`EL 7 (fn_insts fn)`, `THE (mem_write_ops (EL 7 (fn_insts fn)))`,
                `"inl0_x"`] >>
  asm_simp_tac std_ss [] >> unabbrev_all_tac >> EVAL_TAC
QED

Theorem name_share_fails_param_once[local]:
  ?fn. MEM fn (reachable_ctx name_share_ctx).ctx_functions /\
       ~EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) = 1)
          (FLAT (MAP (\i. i.inst_outputs)
             (FILTER (\i. i.inst_opcode = PARAM) (fn_insts fn))))
Proof
  qexists_tac `EL 1 name_share_ctx.ctx_functions` >> EVAL_TAC
QED

Theorem name_share_not_shape_ok[local]:
  ~inliner_shape_ok name_share_ctx
Proof
  strip_tac >> strip_assume_tac name_share_fails_param_once >>
  drule_all shape_ok_param_once >> asm_rewrite_tac[]
QED

Theorem inliner_param_dalloca_name_witness:
  C = name_share_ctx /\ C' = function_inliner_ctx 0 C ==>
  lowering_context_ok C /\ ~inliner_shape_ok C /\
  (?fn. MEM fn (reachable_ctx C).ctx_functions /\
        ~EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) = 1)
           (FLAT (MAP (\i. i.inst_outputs)
              (FILTER (\i. i.inst_opcode = PARAM) (fn_insts fn))))) /\
  inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  !P. ~EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
         C'.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `(function_inliner_ctx 0 name_share_ctx).ctx_functions =
     [HD (function_inliner_ctx 0 name_share_ctx).ctx_functions]` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  simp[name_share_out_not_ptr_ok, name_share_not_shape_ok,
       name_share_fails_param_once] >> premises_tac
QED

(* ===== Finding 2: the return-PC slot binds a user PARAM ===== *)

Definition arity_ctx_def:
  arity_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 JNZ [Lit 0w; Label "call"; Label "done"] []];
          witness_block "call"
            [mk_inst 1 INVOKE [Label "callee"] [];
             mk_inst 2 STOP [] []];
          witness_block "done" [mk_inst 3 STOP [] []]];
       mk_raw_function "callee"
         [witness_block "callee"
            [mk_inst 10 PARAM [Lit 0w] ["x"];
             mk_inst 11 ALLOCA [Lit 32w] ["a"];
             mk_inst 12 CALLDATASIZE [] ["c"];
             mk_inst 13 JNZ [Var "c"; Label "l"; Label "r"] []];
          witness_block "l"
            [mk_inst 14 ASSIGN [Var "x"] ["m"];
             mk_inst 15 JMP [Label "j"] []];
          witness_block "r"
            [mk_inst 16 ASSIGN [Var "a"] ["m"];
             mk_inst 17 JMP [Label "j"] []];
          witness_block "j"
            [mk_inst 18 MLOAD [Var "m"] ["v"];
             mk_inst 19 REVERT [Lit 0w; Lit 0w] []]]]
      (SOME "entry")
End

(* The callee has no RETPC_PARAM, so the rotated return-PC literal binds
   "x"; its copy "inl0_m" then joins a pointer with a constant. *)
Theorem arity_out_not_ptr_ok:
  ~fn_ptr_ok P (HD (function_inliner_ctx 0 arity_ctx).ctx_functions)
Proof
  qabbrev_tac `fn = HD (function_inliner_ctx 0 arity_ctx).ctx_functions` >>
  `EVERY (\i. i.inst_opcode <> PARAM) (fn_insts fn)` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `ptr_roots P fn = set ["inl0_a"]` by
    (asm_simp_tac std_ss [no_param_ptr_roots_list] >> AP_TERM_TAC >>
     unabbrev_all_tac >> EVAL_TAC) >>
  `OPTION_MAP (MEM "inl0_m") (pv_closure fn ["inl0_a"]) = SOME T /\
   OPTION_MAP (MEM "inl0_x") (pv_closure fn ["inl0_a"]) = SOME F` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"inl0_m" IN pointer_derived_vars fn (set ["inl0_a"]) /\
   "inl0_x" NOTIN pointer_derived_vars fn (set ["inl0_a"])` by
    metis_tac[witness_closure_member] >>
  `"inl0_m" IN fn_pv P fn /\ "inl0_x" NOTIN fn_pv P fn` by
    asm_rewrite_tac[fn_pv_def] >>
  irule nonptr_copy_refutes_fn_ptr_ok >>
  qexistsl_tac [`EL 8 (fn_insts fn)`, `"inl0_x"`, `"inl0_m"`] >>
  asm_simp_tac std_ss [] >> unabbrev_all_tac >> EVAL_TAC
QED

Theorem arity_fails_retpc[local]:
  ?caller inst callee args.
    MEM caller (reachable_ctx arity_ctx).ctx_functions /\
    MEM inst (fn_insts caller) /\
    MEM callee (reachable_ctx arity_ctx).ctx_functions /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee.fn_name :: args /\
    ~IS_SOME (fn_retpc_param callee)
Proof
  qexistsl_tac [`HD arity_ctx.ctx_functions`,
                `EL 1 (fn_insts (HD arity_ctx.ctx_functions))`,
                `EL 1 arity_ctx.ctx_functions`, `[]`] >>
  EVAL_TAC
QED

Theorem arity_not_shape_ok[local]:
  ~inliner_shape_ok arity_ctx
Proof
  strip_tac >> strip_assume_tac arity_fails_retpc >>
  drule_all shape_ok_retpc >> asm_rewrite_tac[]
QED

Theorem inliner_retpc_arity_witness:
  C = arity_ctx /\ C' = function_inliner_ctx 0 C ==>
  lowering_context_ok C /\ ~inliner_shape_ok C /\
  (?caller inst callee args.
     MEM caller (reachable_ctx C).ctx_functions /\
     MEM inst (fn_insts caller) /\
     MEM callee (reachable_ctx C).ctx_functions /\
     inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee.fn_name :: args /\
     ~IS_SOME (fn_retpc_param callee)) /\
  inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  !P. ~EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
         C'.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `(function_inliner_ctx 0 arity_ctx).ctx_functions =
     [HD (function_inliner_ctx 0 arity_ctx).ctx_functions]` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> simp[arity_out_not_ptr_ok, arity_not_shape_ok,
                            arity_fails_retpc] >>
  premises_tac
QED

(* ===== Finding 1: a PHI that does not cover its block's predecessors ===== *)

(* "done" is reached from "left", "site1" and "site2"; its PHI names only the
   last two. Inlining the reverting callee leaves both unreachable. *)
Definition phi_cover_blocks_def:
  phi_cover_blocks =
    [witness_block "entry"
       [mk_inst 0 ALLOCA [Lit 32w] ["ptr"];
        mk_inst 1 JNZ [Lit 1w; Label "site"; Label "left"] []];
     witness_block "left" [mk_inst 2 JMP [Label "done"] []];
     witness_block "site"
       [mk_inst 3 INVOKE [Label "reverter"] [];
        mk_inst 4 JNZ [Lit 1w; Label "site1"; Label "site2"] []];
     witness_block "site1" [mk_inst 5 JMP [Label "done"] []];
     witness_block "site2" [mk_inst 6 JMP [Label "done"] []];
     witness_block "done"
       [mk_inst 7 PHI [Label "site1"; Var "ptr"; Label "site2"; Var "ptr"]
          ["w"];
        mk_inst 8 EQ [Var "ptr"; Var "w"] ["same"];
        mk_inst 9 STOP [] []]]
End

Definition phi_cover_reverter_def:
  phi_cover_reverter =
    mk_raw_function "reverter"
      [witness_block "reverter"
         [mk_inst 10 RETPC_PARAM [Lit 0w] ["pc"];
          mk_inst 11 REVERT [Lit 0w; Lit 0w] []]]
End

Definition phi_cover_ctx_def:
  phi_cover_ctx =
    mk_venom_context
      [mk_raw_function "entry" phi_cover_blocks; phi_cover_reverter]
      (SOME "entry")
End

Theorem phi_cover_fails_phis_cover[local]:
  ~EVERY fn_phis_cover_preds (reachable_ctx phi_cover_ctx).ctx_functions
Proof
  strip_tac >>
  `EVERY phis_cover_preds_check (reachable_ctx phi_cover_ctx).ctx_functions`
    by fs[EVERY_MEM, phis_cover_preds_check_complete] >>
  pop_assum mp_tac >> EVAL_TAC
QED

Theorem phi_cover_not_shape_ok[local]:
  ~inliner_shape_ok phi_cover_ctx
Proof
  strip_tac >> drule shape_ok_phis_cover >>
  rewrite_tac[phi_cover_fails_phis_cover]
QED

(* The pruned output, evaluated once. *)
val phi_cover_out_eval =
  EVAL ``reachable_fn_eval
           (HD (function_inliner_ctx 0 phi_cover_ctx).ctx_functions)``;

Theorem phi_cover_out_not_ptr_ok:
  ~fn_ptr_ok P
     (reachable_fn (HD (function_inliner_ctx 0 phi_cover_ctx).ctx_functions))
Proof
  qabbrev_tac `out = HD (function_inliner_ctx 0 phi_cover_ctx).ctx_functions` >>
  `wf_function out` by (unabbrev_all_tac >> EVAL_TAC) >>
  drule reachable_fn_eval >> disch_then SUBST1_TAC >>
  unabbrev_all_tac >> rewrite_tac[phi_cover_out_eval] >>
  qmatch_goalsub_abbrev_tac `fn_ptr_ok P fn` >>
  `EVERY (\i. i.inst_opcode <> PARAM) (fn_insts fn)` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `ptr_roots P fn = set ["ptr"]` by
    (asm_simp_tac std_ss [no_param_ptr_roots_list] >> AP_TERM_TAC >>
     unabbrev_all_tac >> EVAL_TAC) >>
  `OPTION_MAP (MEM "ptr") (pv_closure fn ["ptr"]) = SOME T /\
   OPTION_MAP (MEM "w") (pv_closure fn ["ptr"]) = SOME F` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"ptr" IN pointer_derived_vars fn (set ["ptr"]) /\
   "w" NOTIN pointer_derived_vars fn (set ["ptr"])` by
    metis_tac[witness_closure_member] >>
  `"ptr" IN fn_pv P fn /\ "w" NOTIN fn_pv P fn` by
    asm_rewrite_tac[fn_pv_def] >>
  irule witness_mixed_eq_refutes_fn_ptr_ok >>
  qexistsl_tac [`EL 5 (fn_insts fn)`, `"ptr"`, `"w"`] >>
  asm_simp_tac std_ss [] >> unabbrev_all_tac >> EVAL_TAC
QED

Theorem inliner_phi_cover_witness:
  C = phi_cover_ctx /\ C' = function_inliner_ctx 0 C ==>
  ~lowering_context_ok C /\ ~inliner_shape_ok C /\
  ~EVERY fn_phis_cover_preds (reachable_ctx C).ctx_functions /\
  inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  !P. ~EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
         C'.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `(function_inliner_ctx 0 phi_cover_ctx).ctx_functions =
     [HD (function_inliner_ctx 0 phi_cover_ctx).ctx_functions]` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> simp[phi_cover_out_not_ptr_ok] >>
  `reachable_ctx phi_cover_ctx = phi_cover_ctx` by EVAL_TAC >>
  `phi_cover_ctx.ctx_functions =
     [mk_raw_function "entry" phi_cover_blocks; phi_cover_reverter]` by
    EVAL_TAC >>
  rpt conj_tac
  >- EVAL_TAC
  >- ACCEPT_TAC phi_cover_not_shape_ok
  >- rewrite_tac[GSYM NOT_EVERY, phi_cover_fails_phis_cover]
  >- guard_tac
  >> irule stage_ptr_ok_from_eval >> EVAL_TAC
QED

(* ===== Finding 3: a revert-forwarding pair split by the call site ===== *)

Definition rdc_split_ctx_def:
  rdc_split_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 ALLOCA [Lit 32w] ["p"];
             mk_inst 1 ASSIGN [Lit 0w] ["zero"];
             mk_inst 2 INVOKE [Label "helper"] [];
             mk_inst 3 RETURNDATACOPY [Var "p"; Var "zero"; Lit 1w] [];
             mk_inst 4 REVERT [Var "p"; Lit 1w] []]];
       mk_raw_function "helper"
         [witness_block "helper"
            [mk_inst 10 RETPC_PARAM [Lit 0w] ["pc"];
             mk_inst 11 RET [Var "pc"] []]]]
      (SOME "entry")
End

(* The RETURNDATACOPY's source resolves to 0 only through the ASSIGN before
   the call; the return block the inliner splits off starts at the copy. *)
Theorem rdc_pair_in_input:
  revert_forward_pair (HD (HD rdc_split_ctx.ctx_functions).fn_blocks) 3 4
Proof
  simp[revert_forward_pair_def] >> EVAL_TAC >> simp[]
QED

Theorem rdc_pair_split_in_output:
  ~revert_forward_pair
     (EL 1 (HD (function_inliner_ctx 0 rdc_split_ctx).ctx_functions).fn_blocks)
     0 1
Proof
  simp[revert_forward_pair_def] >> EVAL_TAC >> simp[]
QED

Theorem rdc_not_guard[local]:
  ~inliner_input_guard rdc_split_ctx
Proof
  strip_tac >>
  drule (Q.INST [`fn` |-> `HD rdc_split_ctx.ctx_functions`,
                 `bb` |-> `HD (HD rdc_split_ctx.ctx_functions).fn_blocks`,
                 `i` |-> `3`, `j` |-> `4`] guard_rfp) >>
  rewrite_tac[GSYM rfp_check_eq] >> EVAL_TAC
QED

Theorem inliner_rdc_split_witness:
  C = rdc_split_ctx /\ C' = function_inliner_ctx 0 C ==>
  lowering_context_ok C /\ inliner_shape_ok C /\ ~inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  revert_forward_pair (HD (HD C.ctx_functions).fn_blocks) 3 4 /\
  ~revert_forward_pair (EL 1 (HD C'.ctx_functions).fn_blocks) 0 1
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[rdc_pair_in_input, rdc_pair_split_in_output, rdc_not_guard] >>
  rpt conj_tac
  >- EVAL_TAC
  >- shape_tac
  >> irule stage_ptr_ok_from_eval >> EVAL_TAC
QED

(* ===== Finding 5: a forwarded argument with two roots ===== *)

(* The inliner's input when the pinned compiler, with vyperlang/vyper#5237,
   compiles a readonly internal call on `(a if c else b)[1]`: "s" is
   assigned on both paths, and the forwarding replaced the argument's copy
   with "p", which an ADD derives from "s". *)
Definition two_root_arg_ctx_def:
  two_root_arg_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 CALLDATASIZE [] ["c"];
             mk_inst 1 ALLOCA [Lit 64w] ["a"];
             mk_inst 2 ALLOCA [Lit 64w] ["b"];
             mk_inst 3 JNZ [Var "c"; Label "then"; Label "else"] []];
          witness_block "then"
            [mk_inst 4 ASSIGN [Var "a"] ["s"];
             mk_inst 5 JMP [Label "join"] []];
          witness_block "else"
            [mk_inst 6 ASSIGN [Var "b"] ["s"];
             mk_inst 7 JMP [Label "join"] []];
          witness_block "join"
            [mk_inst 8 ADD [Var "s"; Lit 32w] ["p"];
             mk_inst 9 INVOKE [Label "callee"; Var "p"] ["r"];
             mk_inst 10 STOP [] []]];
       mk_raw_function "callee"
         [witness_block "callee"
            [mk_inst 20 PARAM [Lit 0w] ["x"];
             mk_inst 21 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 22 MLOAD [Var "x"] ["v"];
             mk_inst 23 RET [Var "v"; Var "pc"] []]]]
      (SOME "entry")
End

(* The argument "p" has two roots, but no write reaches the callee's
   parameter (its write-reaching set is empty), so the input meets every
   syntactic premise; inlining removes the call, and the output keeps the
   pointer conjunct. *)
Theorem inliner_two_root_arg_witness:
  C = two_root_arg_ctx /\ C' = function_inliner_ctx 0 C ==>
  inliner_shape_ok C /\ inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  ctx_write_param_set C "callee" = {} /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn))
    C'.ctx_functions /\
  ?P W. (!nm. W nm SUBSET P nm) /\
        EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
          C'.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C')
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac
  >- shape_tac
  >- guard_tac
  >- (irule stage_ptr_ok_from_eval >> EVAL_TAC)
  >- (EVAL_TAC >> simp[])
  >- EVAL_TAC
  >> irule stage_ptr_ok_from_eval >> EVAL_TAC
QED

(* ===== Revert-forward pairs the inliner creates ===== *)

(* Inlining turns the callee's PARAM into an ASSIGN of the caller's literal,
   which makes the copy and revert a revert-forward pair in the output
   whose source resolves only through that ASSIGN. *)
Definition rfp_cut_ctx_def:
  rfp_cut_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 INVOKE [Label "callee"; Lit 0w] [];
             mk_inst 1 STOP [] []]];
       mk_raw_function "callee"
         [witness_block "callee"
            [mk_inst 10 PARAM [Lit 0w] ["z"];
             mk_inst 11 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 12 ALLOCA [Lit 32w] ["p"];
             mk_inst 13 RETURNDATACOPY [Var "p"; Var "z"; Lit 0w] [];
             mk_inst 14 REVERT [Var "p"; Lit 0w] []]]]
      (SOME "entry")
End

Definition rfp_cut_out_block_def:
  rfp_cut_out_block =
    EL 2 (HD (function_inliner_ctx 0 rfp_cut_ctx).ctx_functions).fn_blocks
End

(* The input meets every syntactic premise; the inlined callee block holds a
   pair at (3,4) whose source resolves only through the inlined PARAM, so
   the pair is gone once the block is cut at 3. The cut clause is therefore
   a guard on the input, not part of the shape the output keeps. *)
Theorem inliner_rfp_cut_witness:
  C = rfp_cut_ctx ==>
  inliner_shape_ok C /\ inliner_input_guard C /\
  (?P W. (!nm. W nm SUBSET P nm) /\
         EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C)) /\
  revert_forward_pair rfp_cut_out_block 3 4 /\
  ~revert_forward_pair
     (rfp_cut_out_block with
        bb_instructions := DROP 3 rfp_cut_out_block.bb_instructions) 0 1
Proof
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac
  >- shape_tac
  >- guard_tac
  >- (irule stage_ptr_ok_from_eval >> EVAL_TAC)
  >> rewrite_tac[GSYM rfp_check_eq] >> EVAL_TAC
QED
