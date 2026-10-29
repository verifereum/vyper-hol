(*
 * A first body slice of the lowering simulation (#625)
 *
 * Lemmas in the form of the statement lemmas of stmtLoweringProps: frag_exec
 * (fragExec) from stmt_state_rel at the fragment's start to stmt_state_rel
 * at its end, under fn_has_code, fn_inst_ids_distinct and
 * local_ptrs_reserved.  The sub-fragments (a right-hand side, a condition,
 * branch bodies) enter as hypotheses of the same shape, stated at the
 * source state where they run, so the lemmas compose with each other and
 * with the general statement and expression induction.  A declaration's
 * ALLOCA keeps its base below 2 ** 256 through alloca_room, which
 * stmt_state_rel carries.  Constructor declarations additionally require
 * the allocation-prefix guard that keeps their stores off immutables;
 * runtime declarations use the trivial cap = 0 guard.
 *
 * TOP-LEVEL:
 *   expr_frag               — an expression's fragment, in the form the
 *                             statement lemmas take it
 *   word_value              — a value held in one word as val_to_w256
 *   emit_op_frag            — one instruction that writes a word computed
 *                             from the state to a fresh variable
 *   compile_name_word_frag  — slice 1: reading a word local
 *   compile_annassign_word_frag — slice 1: declaring a word local
 *   compile_if_frag         — slice 2: an if/else
 *   compile_safe_add_runtime_error — slice 3: a checked uint256 addition
 *                             whose source result is a RuntimeError aborts
 *   compile_safe_add_overflow_frag — the Venom side of slice 3
 *
 * Helpers:
 *   stmt_state_rel_exec_alloca, stmt_state_rel_declare_word,
 *   eval_name_word, lower_value_name_word, step_name_word,
 *   eval_stmt_if_success, eval_stmt_annassign_value, compile_if_parts,
 *   compile_if_taken_branch, if_branch_to_exit, compile_annassign_word_parts,
 *   bounded_int_op_add_overflow, word_value_in_memory, word_value_wf
 *)

Theory loweringSlice
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps venomMemDefs immutableMemoryFrame immutableRelation
  immutableEncoding
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperEvalExprPreservesScopesDom
  vyperEvalPreservesScopes vyperStatePreservation arithmeticProps
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState
Libs
  monadsyntax

(* ===== Expression fragments ===== *)

(* The fragment of expression e lowered as a value of type ty, run from a
   state related at es, the source state where e is evaluated: it reaches
   its end related at the source state after e, with the operand holding
   e's forced value, and keeps the variables handed out before it and the
   allocations made before it.  This is compile_expr_correct's conclusion
   as a frag_exec; getting it from compile_expr_correct through
   frag_exec_run_inst_seq also needs that a run_inst_seq without INVOKE
   keeps the existing allocations, which compile_expr_correct does not
   state. *)
Definition expr_frag_def:
  expr_frag ctx func cenv cx ty e es R <=>
    !sa sb op v es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL v, es') /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. stmt_state_rel func cenv cx es' s /\
             eval_operand op s = SOME (val_to_w256 v) /\
             (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x s = SOME w) /\
             (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                      FLOOKUP s.vs_allocas aid = SOME b)) R
End

(* ===== Reading a word local ===== *)

(* A value held in one memory word under its plain encoding val_to_w256:
   the values mstore_establishes_val_in_memory_prim covers.  BytesV, the
   value of address and bytesN locals, is left out, as it is there: how it
   sits in its word depends on the type, so it needs its own memory lemma
   before the slice can cover those locals. *)
Definition word_value_def:
  word_value v <=>
    (?b. v = BoolV b) \/ (?n. v = IntV n) \/ (?k. v = FlagV k) \/
    (?n. v = DecimalV n)
End

Theorem word_value_in_memory:
  !ty v off s.
    word_value v ==>
    val_in_memory ty v off (mstore off (val_to_w256 v) s).vs_memory
Proof
  rw[word_value_def] >> simp[mstore_establishes_val_in_memory_prim]
QED

Theorem word_value_wf:
  !ty v. word_value v /\ type_memory_size ty = 32 ==> val_wf ty v
Proof
  rw[word_value_def] >> simp[val_wf_def]
QED

(* One instruction that computes w from the state and writes it to a fresh
   variable, and changes nothing else. *)
Theorem emit_op_frag:
  !ctx func cenv cx es opc args sa op sb s0 w R.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (stmt_state_rel func cenv cx es s0 ==>
     !out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. stmt_state_rel func cenv cx es s /\ eval_operand op s = SOME w /\
           (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory) R
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[venomInstTheory.mk_inst_def] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> gvs[] >>
  qexists_tac `update_var out w s0` >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, stmt_state_rel_inst_idx] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `out = x` >> gvs[lookup_var_def]
QED

Theorem eval_name_word:
  !cx ann id es entry.
    lookup_scopes id es.scopes = SOME entry ==>
    (do result <- eval_expr cx (Name ann id); read_result cx result od) es =
      (INL entry.value, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, read_result_def, read_place_def,
          read_memory_path_def, evaluate_subscripts_def, lift_sum_def,
          lift_option_type_def, ignore_bind_def] >>
     `lookup_scopes_val id es.scopes = SOME entry.value` by
       (qpat_x_assum `lookup_scopes _ _ = _` mp_tac >>
        qspec_tac (`es.scopes`, `scs`) >>
        Induct >> simp[lookup_scopes_def, lookup_scopes_val_def] >>
        rpt strip_tac >> Cases_on `FLOOKUP h id` >> gvs[]) >>
     simp[return_def]
QED

Theorem lower_value_name_word:
  !cenv ty ann id p sz sa op sb.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lower_value compile_expr cenv ty (Name ann id) sa = (op, sb) ==>
    emit_op MLOAD [Var p] sa = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, compile_name_vv_def,
       unwrap_value_def, contextTheory.compile_ptr_load_def,
       contextTheory.mk_ptr_def, comp_return_def,
       vyperASTTheory.expr_type_def]
QED

(* The MLOAD of a word local's pointer reads the local's value. *)
Theorem step_name_word:
  !func cenv cx es s id p sz entry n out.
    stmt_state_rel func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    step_inst_base (mk_inst n MLOAD [Var p] [out]) s =
      OK (update_var out (val_to_w256 entry.value) s)
Proof
  rpt strip_tac >>
  `?w. lookup_var p s = SOME w /\
       val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  `mload (w2n w) s = val_to_w256 entry.value` by
    (fs[word_value_def] >> gvs[val_in_memory_prim, mem_word_at_eq_mload]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule step_MLOAD >> simp[eval_operand_def]
QED

(* Slice lemma 1, the read: a word local held through its pointer loads
   with one MLOAD of the pointer, and the source reads the same value. *)
Theorem compile_name_word_frag:
  !ctx func cenv cx ty ann id es R p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    (do result <- eval_expr cx (Name ann id); read_result cx result od) es =
      (INL entry.value, es) /\
    expr_frag ctx func cenv cx ty (Name ann id) es R
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  simp[expr_frag_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all lower_value_name_word >> strip_tac >>
  irule frag_exec_conseq >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
                           `val_to_w256 entry.value`, `R`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> strip_tac >>
      drule_all step_name_word >> simp[]) >>
  strip_tac >> first_x_assum (irule_at Any) >> simp[]
QED

(* ===== Declaring a word local ===== *)

(* Initialized constructor immutables occupy a reserved prefix.  This is
   independent of the allocation frontier: even a repeated ALLOCA must
   return a region above this cap. *)
Definition immutable_prefix_bound_def:
  immutable_prefix_bound cenv addr src (es:evaluation_state) cap <=>
    !name tv v off.
      FLOOKUP cenv.ce_vars (module_var_key (src,name)) =
        SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables addr of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      off + type_memory_size tv <= cap
End

(* Admissibility supplies the footprint well-formedness needed by memory
   transport; no canonical-padding assumption is imposed on immutables. *)
Theorem immutable_admissible_val_wf:
  (!tv v. immutable_value_admissible tv v ==> val_wf tv v) /\
  (!vs tvs. immutable_fields_admissible tvs vs ==> fields_val_wf vs tvs) /\
  (!vs tv. EVERY (immutable_value_admissible tv) vs ==> elems_val_wf vs tv) /\
  (!kvs tv n.
     EVERY (\(k,v). k < n /\ immutable_value_admissible tv v) kvs ==>
     kvs_val_wf kvs tv n) /\
  (!vs tvs. immutable_tuple_admissible tvs vs ==> tuple_val_wf vs tvs)
Proof
  ho_match_mp_tac val_wf_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY (qmatch_goalsub_rename_tac
         `immutable_value_admissible tv _ ==> val_wf tv _` >> Cases_on `tv`) >>
  TRY (qmatch_goalsub_rename_tac `BaseTV bt` >> Cases_on `bt`) >>
  TRY (qmatch_goalsub_rename_tac `BytesT bound` >> Cases_on `bound`) >>
  TRY (qmatch_goalsub_rename_tac `ArrayTV _ bound` >> Cases_on `bound`) >>
  TRY (qmatch_goalsub_rename_tac `immutable_fields_admissible tvs _` >>
       Cases_on `tvs` >>
       TRY (qmatch_goalsub_rename_tac
              `immutable_fields_admissible (field::_) _` >>
            PairCases_on `field`)) >>
  TRY (qmatch_goalsub_rename_tac `immutable_tuple_admissible tvs _` >>
       Cases_on `tvs`) >>
  simp[immutable_value_admissible_def, val_wf_def, type_memory_size_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  FIRST [BasicProvers.TOP_CASE_TAC >> gvs[immutable_value_admissible_def],
         fs[ETA_THM] >> NO_TAC,
         metis_tac[immutableEncodingProofsTheory.immutable_capacity_roundup,
                   arithmeticTheory.LESS_EQ_TRANS]]
QED

(* Transport the semantic immutable relation by capacity-sized memory
   agreement, without strengthening it to canonical padding. *)
Theorem immutables_rel_mem_agree:
  !cenv addr src ctor es s t.
    immutables_rel cenv addr src ctor es s /\
    t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (ctor ==> !name tv v off.
      FLOOKUP cenv.ce_vars (module_var_key (src,name)) =
        SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables addr of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      mem_bytes_at off (type_memory_size tv) t.vs_memory =
        mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
    immutables_rel cenv addr src ctor es t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ctor`
  >- (fs[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name tv v byte_offset. _ ==> _ /\ _` drule_all >> strip_tac >>
      `mem_bytes_at byte_offset (type_memory_size tv) t.vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by metis_tac[] >>
      simp[] >> irule val_in_memory_mem_agree >>
      conj_tac >- metis_tac[immutable_admissible_val_wf] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[]) >>
  fs[immutables_rel_def] >> metis_tac[]
QED

Theorem immutables_rel_mstore_alloca:
  !func cenv cx es s inst b sz at w.
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s /\
    immutable_alloca_sep func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= at /\ at + 32 <= b + sz ==>
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
      (mstore at w s)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH (mstore at w s).vs_memory` by
    (simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF] >>
     IF_CASES_TAC >> decide_tac) >>
  `(mstore at w s).vs_data_section = s.vs_data_section` by simp[mstore_def] >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  fs[immutable_alloca_sep_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
  irule mstore_mem_bytes_at_disjoint >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem immutables_rel_mstore_outside_prefix:
  immutables_rel cenv addr src ctor es s /\
  (ctor ==> immutable_prefix_bound cenv addr src es cap) /\ cap <= at ==>
  immutables_rel cenv addr src ctor es (mstore at w s)
Proof
  strip_tac >> Cases_on `ctor`
  >- (fs[immutables_rel_def, immutable_prefix_bound_def] >>
      simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
      `immutable_value_admissible tv v /\
       byte_offset + type_memory_size tv <= LENGTH s.vs_memory /\
       val_in_memory tv v byte_offset s.vs_memory /\
       immutable_value_bytes_rel tv v
         (mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory)` by
        metis_tac[] >>
      `byte_offset + type_memory_size tv <= at` by
        (res_tac >> DECIDE_TAC) >>
      `mem_bytes_at byte_offset (type_memory_size tv)
         (mstore at w s).vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      `val_wf tv v` by metis_tac[immutable_admissible_val_wf] >>
      simp[] >> conj_tac
      >- (simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF] >>
          IF_CASES_TAC >> DECIDE_TAC) >>
      irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[]) >>
  fs[immutables_rel_def, mstore_def, LET_THM] >> metis_tac[]
QED

Theorem eval_stmt_annassign_value:
  !cx id typ e es es'.
    eval_stmt cx (AnnAssign id typ e) es = (INL (), es') ==>
    ?tyv tv es1 v es2 sc rest.
      evaluate_type (get_tenv cx) typ = SOME tyv /\
      eval_expr cx e es = (INL tv, es1) /\
      read_result cx tv es1 = (INL v, es2) /\
      lookup_scopes id es2.scopes = NONE /\ es2.scopes = sc :: rest /\
      es' = es2 with scopes :=
              (sc |+ (id, <| assignable := T; type := tyv; value := v; popped := [] |>))
              :: rest
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       LET_THM] >>
  strip_tac >>
  gvs[AllCaseEqs(), lift_option_type_def, raise_def, return_def] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def, raise_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  rename1 `read_result cx tv es1 = (INL v, es2)` >>
  qpat_x_assum `(case evaluate_type _ _ of NONE => _ | SOME _ => _) _ = _`
    mp_tac >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def] >> strip_tac >>
  qpat_x_assum `(case es2.scopes of [] => _ | _ => _) _ = _` mp_tac >>
  Cases_on `es2.scopes` >> simp[raise_def, set_scopes_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem local_region_exec_alloca[local]:
  !cenv scopes inst p s n t id b sz.
    inst.inst_outputs = [p] /\ not_local_ptr cenv scopes p /\
    exec_alloca inst s n = OK t /\ local_region cenv scopes t id b sz ==>
    local_region cenv scopes s id b sz
Proof
  rpt strip_tac >>
  `!q. q <> p ==> lookup_var q t = lookup_var q s` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- gvs[exec_alloca_def, LET_THM, lookup_var_def, update_var_def,
            FLOOKUP_UPDATE] >>
     rename1 `FLOOKUP _ _ = SOME pr` >> Cases_on `pr` >>
     gvs[exec_alloca_def, LET_THM, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE]) >>
  fs[local_region_def, not_local_ptr_def] >> metis_tac[]
QED

(* An ALLOCA of func whose output is no live local's pointer, run fresh or
   again, keeps stmt_state_rel and holds its region's base in its output.
   alloca_room keeps the base from wrapping. *)
Theorem stmt_state_rel_exec_alloca:
  !func cenv cx es s inst p n s1.
    stmt_state_rel func cenv cx es s /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
    inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
    exec_alloca inst s n = OK s1 ==>
    stmt_state_rel func cenv cx es s1 /\
    ?w. lookup_var p s1 = SOME w /\
        FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n w, w2n n)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `alloca_room func s1` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rw[] >>
     fs[stmt_state_rel_def] >> irule alloca_room_fields
     >- (qexists_tac `s with <| vs_allocas := s.vs_allocas |+
                                  (inst.inst_id, (s.vs_alloca_next, w2n n));
                                vs_alloca_next := s.vs_alloca_next + w2n n |>` >>
         simp[update_var_def] >>
         qspecl_then [`func`, `s`, `inst`, `n`] mp_tac alloca_room_fresh >>
         fs[FLOOKUP_DEF]) >>
     qexists_tac `s` >> simp[update_var_def]) >>
  `immutable_alloca_sep func cenv cx es s1` by
    (irule immutable_alloca_sep_exec_alloca >>
     qexistsl_tac [`inst`, `n`, `s`] >> fs[stmt_state_rel_def] >>
     rpt strip_tac >> qexists_tac `id` >>
     drule_all local_region_exec_alloca >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s1` by
    (qspecl_then [`func`, `cenv`, `es.scopes`, `s`, `s1`, `inst`, `p`, `n`]
       mp_tac local_ptrs_rel_exec_alloca >>
     impl_tac >- fs[stmt_state_rel_def, state_rel_def] >> simp[]) >>
  `alloca_inv s1` by metis_tac[alloca_inv_exec_alloca, stmt_state_rel_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s1` by
    (irule immutable_relation_same_bytes >> qexists_tac `s` >>
     qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs(), update_var_def, LET_THM] >> rw[] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `state_rel func cenv cx es s1` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `es`, `s`, `s1`] mp_tac
       state_rel_frame >>
     impl_tac >- (
       qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
       simp[exec_alloca_def, AllCaseEqs(), update_var_def, LET_THM] >>
       rw[] >> fs[stmt_state_rel_def,
                  vyperStateTheory.evaluation_state_component_equality]) >>
     simp[]) >>
  `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
                 base + sz < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def, LET_THM] >> strip_tac >> gvs[] >>
      fs[stmt_state_rel_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
      rpt strip_tac >> Cases_on `inst'.inst_id = inst.inst_id` >>
      gvs[FLOOKUP_UPDATE]
      >- (`inst' = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
      metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME r` >> PairCases_on `r` >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def] >> strip_tac >> gvs[] >>
  `r1 = w2n n` by (fs[stmt_state_rel_def] >> metis_tac[]) >>
  `r0 < dimword (:256)` by (res_tac >> DECIDE_TAC) >>
  fs[stmt_state_rel_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
     wordsTheory.w2n_n2w] >>
  metis_tac[]
QED

(* A declaration adds a tracked allocation region; all other live regions
   are transported through their preserved pointer variables. *)
Theorem immutable_alloca_sep_declare_local[local]:
  !func cenv cx es s es' t id entry p sz w inst.
    immutable_alloca_sep func cenv cx es s /\
    es'.immutables = es.immutables /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    lookup_scopes id es'.scopes = SOME entry /\
    (!n. n <> id ==> lookup_scopes n es'.scopes = lookup_scopes n es.scopes) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w /\
    (!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) ==>
    immutable_alloca_sep func cenv cx es' t
Proof
  rpt gen_tac >> strip_tac >>
  fs[immutable_alloca_sep_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  rename1 `local_region cenv es'.scopes t n b z` >>
  Cases_on `n = id`
  >- (gvs[local_region_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s n b z` by
    (fs[local_region_def] >>
     rename1 `FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) z)` >>
     `~not_local_ptr cenv es.scopes q` by
       (simp[not_local_ptr_def] >> metis_tac[]) >>
     metis_tac[]) >>
  metis_tac[]
QED

(* Storing a word into a new local's region, whose ALLOCA ran, binds the
   local in the innermost scope, assignable (a declaration) or not (a loop
   variable). *)
Theorem stmt_state_rel_declare_word:
  !func cenv cx es s id p sz w inst v tyv sc rest cap a.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 /\
    cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module es cap) ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         (sc |+ (id, <| assignable := a; type := tyv; value := v; popped := [] |>)) :: rest)
      (mstore (w2n w) (val_to_w256 v) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `s' = mstore (w2n w) (val_to_w256 v) s` >>
  qabbrev_tac `entry = <| assignable := a; type := tyv; value := v; popped := [] |>` >>
  qabbrev_tac `scs' = (sc |+ (id, entry)) :: rest` >>
  `s'.vs_vars = s.vs_vars /\ s'.vs_allocas = s.vs_allocas /\
   s'.vs_alloca_next = s.vs_alloca_next /\
   s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
   s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_tx_ctx = s.vs_tx_ctx /\
   s'.vs_block_ctx = s.vs_block_ctx /\ s'.vs_logs = s.vs_logs /\
   s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests /\
   s'.vs_immutables = s.vs_immutables /\
   s'.vs_data_section = s.vs_data_section` by
    simp[Abbr `s'`, mstore_def, LET_THM] >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
             regions_disjoint (w2n w) sz b sz'` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
     simp[]) >>
  `w2n w + sz <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> res_tac >> fs[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
             mem_bytes_at b sz' s.vs_memory =
             mem_bytes_at b sz' s'.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by metis_tac[] >>
     `b + sz' <= w2n w \/ w2n w + 32 <= b` by
       (fs[regions_disjoint_def] >> DECIDE_TAC) >>
     simp[Abbr `s'`] >> irule EQ_SYM >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `lookup_scopes id scs' = SOME entry /\
   !n. n <> id ==> lookup_scopes n scs' = lookup_scopes n es.scopes` by
    simp[Abbr `scs'`, lookup_scopes_def, FLOOKUP_UPDATE] >>
  `local_backed func p s (w2n w) sz` by
    (simp[local_backed_def] >> disj1_tac >> qexists_tac `inst` >> simp[]) >>
  `val_in_memory tyv v (w2n w) s'.vs_memory` by
    simp[Abbr `s'`, word_value_in_memory] >>
  `val_wf tyv v` by (irule word_value_wf >> simp[]) >>
  `local_ptrs_rel func cenv scs' s'` by
    (`entry.type = tyv /\ entry.value = v` by simp[Abbr `entry`] >>
     qspecl_then [`func`, `cenv`, `es.scopes`, `scs'`, `s`, `s'`, `id`,
                  `entry`, `p`, `sz`, `w`] mp_tac local_ptrs_rel_write_local >>
     impl_tac >- (fs[lookup_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
     simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s'` by
    (simp[Abbr `s'`] >> irule immutables_rel_mstore_outside_prefix >>
     conj_tac >- (qexists_tac `cap` >> simp[]) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `state_rel func cenv cx (es with scopes := scs') s'` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `es with scopes := scs'`, `s`,
                  `s'`] mp_tac state_rel_frame >>
     impl_tac >- (
       simp[vyperStateTheory.evaluation_state_component_equality] >>
       fs[stmt_state_rel_def]) >>
     simp[]) >>
  `alloca_inv s'` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room func s'` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `immutable_alloca_sep func cenv cx (es with scopes := scs') s'` by
    (irule immutable_alloca_sep_declare_local >>
     qexistsl_tac [`entry`, `es`, `id`, `inst`, `p`, `s`, `sz`, `w`] >>
     simp[] >> fs[stmt_state_rel_def, lookup_var_def]) >>
  fs[stmt_state_rel_def] >> metis_tac[]
QED

Theorem emit_inst_unit:
  !opc ops outs st x st'.
    emit_inst opc ops outs st = (x, st') ==>
    emit_inst opc ops outs st = ((), st')
Proof
  rpt strip_tac >> Cases_on `x` >> simp[]
QED

(* The ALLOCA that compile_stmt emits for a word local, run from s0. *)
Theorem annassign_alloca_frag[local]:
  !ctx func cenv cx es st st1 p sz s0 R cap.
    emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), st1) /\
    stmt_state_rel func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    cap <= s0.vs_alloca_next /\
    (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) ==> cap <= b) ==>
    ?s1 w. cap <= w2n w /\ lookup_var p s1 = SOME w /\
           FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w, sz) /\
           frag_exec ctx st st1 (\s. s = s0)
             (\s. s = s1 /\ stmt_state_rel func cenv cx es s) R
Proof
  rpt strip_tac >>
  imp_res_tac emit_inst_extends >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 =
   exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0
     (n2w sz : bytes32)` by
    simp[step_inst_base_def, venomInstTheory.mk_inst_def] >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (fs[exec_alloca_def] >> BasicProvers.every_case_tac >> simp[]) >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `A`, `p`, `n2w sz`, `s1`]
    mp_tac stmt_state_rel_exec_alloca >>
  impl_tac >- simp[] >> strip_tac >>
  `s0.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `cap <= w2n w` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, LET_THM] >>
     Cases_on `FLOOKUP s0.vs_allocas A.inst_id` >> simp[]
     >- (strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
                         wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
     rename1 `FLOOKUP s0.vs_allocas A.inst_id = SOME region` >>
     PairCases_on `region` >> strip_tac >>
     gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     `region0 < dimword (:256)` by
       (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
        res_tac >> DECIDE_TAC) >>
     fs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> metis_tac[]) >>
  qexistsl_tac [`s1 with vs_inst_idx := LENGTH st1.cs_current_insts`, `w`] >>
  gvs[lookup_var_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       IS_PREFIX_APPEND3, run_inst_seq_def, stmt_state_rel_inst_idx,
       is_terminator_def]
QED

(* The MSTORE that stores the right-hand side into the local's slot. *)
Theorem annassign_mstore_frag[local]:
  !w v p val_op ctx func cenv cx es' st st' Pre R.
    emit_void MSTORE [Var p; val_op] st = ((), st') /\
    (!s. Pre s ==>
         lookup_var p s = SOME w /\
         eval_operand val_op s = SOME (val_to_w256 v) /\
         stmt_state_rel func cenv cx es' (mstore (w2n w) (val_to_w256 v) s)) ==>
    frag_exec ctx st st' Pre (stmt_state_rel func cenv cx es') R
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    simp[venomInstTheory.mk_inst_def, is_terminator_def] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> first_x_assum drule >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [Var p; val_op] []) s =
     OK (mstore (w2n w) (val_to_w256 v) s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def, stmt_state_rel_inst_idx]
QED

(* The compile side of a word-local declaration: the ALLOCA, the right-hand
   side's fragment, and the MSTORE. *)
Theorem compile_annassign_word_parts:
  !cenv lctx ty id vtyp e st st' func p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), st') /\
    fn_has_code st st' func /\ local_ptrs_reserved cenv st /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    (!sa sb op. lower_value compile_expr cenv (expr_type e) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    ?sa sb vop.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sa) /\
      lower_value compile_expr cenv (expr_type e) e sa = (vop, sb) /\
      emit_void MSTORE [Var p; vop] sb = ((), st') /\
      cs_extends st sa /\ cs_extends sa sb /\ cs_extends sb st' /\
      fn_has_code sa sb func /\
      MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
      local_ptrs_reserved cenv sa /\ not_fresh_at sa p
Proof
  rpt gen_tac >> strip_tac >>
  `?st1 st2 st3 src_vv val_op.
     emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), st1) /\
     compile_expr cenv (expr_type e) e st1 = (src_vv, st2) /\
     unwrap_value cenv src_vv st2 = (val_op, st3) /\
     emit_void MSTORE [Var p; val_op] st3 = ((), st')` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_local_alloca_def, compile_assign_value_def,
          LET_THM] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_inst_unit >> metis_tac[]) >>
  `lower_value compile_expr cenv (expr_type e) e st1 = (val_op, st3)` by
    simp[lower_value_def, comp_bind_def] >>
  imp_res_tac emit_inst_unit >> imp_res_tac emit_inst_extends >>
  `cs_extends st st1 /\ cs_extends st1 st3 /\ cs_extends st3 st'` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code st1 st3 func /\ fn_has_code st1 st' func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (`?bb. lookup_block st1.cs_current_bb func.fn_blocks = SOME bb /\
           isPREFIX st1.cs_current_insts bb.bb_instructions` by
       metis_tac[fn_has_code_start, cs_extends_trans] >>
     `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p])
        bb.bb_instructions` by gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[lookup_block_fn_insts]) >>
  `local_ptrs_reserved cenv st1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `not_fresh_at st1 p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`st1`, `st3`, `val_op`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Slice lemma 1, the declaration: x: T = e for a word type T held through
   a pointer local.  The ALLOCA may run for the first time or again (in a
   loop); alloca_room in stmt_state_rel keeps a fresh ALLOCA's base from
   wrapping.  The immutable prefix cap bounds initialized immutables at the
   source post-state (the RHS may initialize more of them); both fresh and
   existing allocations start above the cap.  The RHS keeps this local's
   allocation and pointer, so the final store misses that prefix even if
   the RHS allocates other regions.  Runtime code can use cap = 0.
   The right-hand side is a word value at es, and its fragment is
   any expr_frag at es; its type annotation fills one word (32 bytes) of
   the local's region. *)
Theorem compile_annassign_word_frag:
  !ctx func cenv cx lctx ty id vtyp e st st' es es' R p sz cap.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), st') /\
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv st /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= sz /\ sz < dimword (:256) /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module es' cap) /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==>
           type_memory_size tyv = 32) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
               (INL v, es1) ==> word_value v) /\
    (!sa sb op. lower_value compile_expr cenv (expr_type e) e sa = (op, sb) ==>
                cs_extends sa sb) /\
    expr_frag ctx func cenv cx (expr_type e) e es R ==>
    frag_exec ctx st st'
      (\s. stmt_state_rel func cenv cx es s /\
           cap <= s.vs_alloca_next /\
           (!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> cap <= b))
      (stmt_state_rel func cenv cx es') R
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_annassign_value >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  `(do result <- eval_expr cx e; read_result cx result od) es =
     (INL v, es1)` by simp[bind_def] >>
  `word_value v` by metis_tac[] >>
  `type_memory_size tyv = 32` by fs[] >>
  `(cenv.ce_is_ctor ==>
      immutable_prefix_bound cenv cx.txn.target cenv.ce_module es1 cap)` by
    (fs[immutable_prefix_bound_def] >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists_tac `es1.scopes` >>
     qpat_x_assum `eval_expr cx e es = _`
       (strip_assume_tac o MATCH_MP eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es1.scopes p` by
    metis_tac[local_ptrs_reserved_not_live] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `id`, `vtyp`, `e`, `st`, `st'`, `func`,
               `p`, `sz`] mp_tac compile_annassign_word_parts >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`st1`, `st3`, `val_op`] strip_assume_tac) >>
  irule frag_exec_pointwise >> gen_tac >> BETA_TAC >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `st`, `st1`, `p`, `sz`,
               `s0`, `R`, `cap`] mp_tac annassign_alloca_frag >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qabbrev_tac `Q1 = \s. s = s1 /\ stmt_state_rel func cenv cx es s` >>
  qabbrev_tac `Q2 = \s.
    stmt_state_rel func cenv cx es1 s /\
    eval_operand val_op s = SOME (val_to_w256 v) /\
    (!x w. not_fresh_at st1 x /\ lookup_var x s1 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b)` >>
  `frag_exec ctx st1 st3 Q1 Q2 R` by
    (qpat_x_assum `expr_frag _ _ _ _ _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC[expr_frag_def] >>
     disch_then (qspecl_then [`st1`, `st3`, `val_op`, `v`, `es1`, `s1`]
                   mp_tac) >>
     impl_tac >- fs[] >> simp[Abbr `Q1`, Abbr `Q2`]) >>
  qspecl_then [`ctx`, `st`, `st1`, `st3`, `\s. s = s0`, `Q1`, `Q2`, `R`]
    mp_tac frag_exec_seq >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`Q2`, `st3`] >>
  rpt conj_tac
  >- metis_tac[cs_extends_trans] >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  qspecl_then [`w`, `v`, `p`, `val_op`] MATCH_MP_TAC annassign_mstore_frag >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[Abbr `Q2`] >> rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >> simp[] >>
  qspecl_then [`func`, `cenv`, `cx`, `es1`, `s`, `id`, `p`, `sz`, `w`,
               `mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]`,
               `v`, `tyv`, `sc`, `rest`, `cap`, `T`]
    MATCH_MP_TAC stmt_state_rel_declare_word >>
  fs[venomInstTheory.mk_inst_def]
QED

(* ===== if/else ===== *)

Theorem eval_stmt_if_success:
  !cx c ss1 ss2 es es'.
    eval_stmt cx (If c ss1 ss2) es = (INL (), es') ==>
    ?b es1 es2 sc rest.
      (do result <- eval_expr cx c; read_result cx result od) es =
        (INL (BoolV b), es1) /\
      eval_stmts cx (if b then ss1 else ss2)
        (es1 with scopes := FEMPTY :: es1.scopes) = (INL (), es2) /\
      es2.scopes = sc :: rest /\ es' = es2 with scopes := rest /\
      !n. n IN FDOM sc ==> lookup_scopes n rest = NONE
Proof
  rpt gen_tac >>
  `!x. x with scopes updated_by CONS FEMPTY =
       x with scopes := FEMPTY :: x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       finally_def, return_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `eval_expr cx c es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `switch_BoolV cx tv` >>
  Cases_on `switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2)
              (es1 with scopes := FEMPTY :: es1.scopes)` >>
  rename1 `_ = (r2, es2)` >> Cases_on `r2` >>
  simp[pop_scope_def] >> Cases_on `es2.scopes` >>
  simp[raise_def, return_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def, bind_def, read_result_empty_scope] >>
  Cases_on `read_result cx tv es1` >>
  rename1 `read_result cx tv es1 = (rv, ers)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `rv` >> simp[raise_def] >>
  rw[] >> gvs[raise_def]
  >> qpat_x_assum `eval_stmts _ _ _ = _`
       (mp_then Any mp_tac eval_stmts_new_in_head_not_in_tail) >>
  simp[]
QED

Theorem compile_if_parts:
  !cenv lctx ty c ss1 ss2 st st'.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') ==>
    ?cond_op s1 s4 s5 s6 s7 s8 s9 s10 s11 then_lbl else_lbl exit_lbl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      cs_extends s1 s4 /\ s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      s4.cs_next_var = s1.cs_next_var /\
      emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] s4 =
        ((), s5) /\
      new_block then_lbl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label exit_lbl] [] s7 = ((), s8)) /\
      new_block else_lbl s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label exit_lbl] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block exit_lbl s11 = (x11, st'))
Proof
  rpt gen_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  (fn (asl, w) =>
     MAP_EVERY (fn v => Cases_on `^v`)
       (filter (fn v => type_of v = oneSyntax.one_ty)
          (free_varsl (w :: asl))) (asl, w)) >>
  rename1 `fresh_label "then" s1 = (then_lbl, s2)` >>
  rename1 `fresh_label "else" s2 = (else_lbl, s3)` >>
  rename1 `fresh_label "if_exit" s3 = (exit_lbl, s4)` >>
  rename1 `emit_inst JNZ _ _ s4 = ((), s5)` >>
  rename1 `new_block then_lbl s5 = (x5, s6)` >>
  rename1 `compile_stmts _ _ _ ss1 s6 = ((), s7)` >>
  rename1 `new_block else_lbl s8 = (x8, s9)` >>
  rename1 `compile_stmts _ _ _ ss2 s9 = ((), s10)` >>
  strip_tac >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s4`, `s5`, `s6`, `s7`, `s8`, `s9`, `s10`, `s11`,
                `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  imp_res_tac fresh_label_props >>
  `cs_extends s1 s4` by
    metis_tac[cs_extends_fresh_label, cs_extends_trans] >>
  rpt conj_tac >> fs[] >>
  TRY (Cases_on `block_is_terminated s7` >> fs[comp_return_def] >> NO_TAC) >>
  TRY (Cases_on `block_is_terminated s10` >> fs[comp_return_def] >> NO_TAC) >>
  rpt strip_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
QED

(* A jump from a block's terminator into a branch whose body starts a fresh
   block and ends in a JMP to lbl, which closes the block: execution reaches
   lbl's start from a state satisfying the body's postcondition, or exits as
   the body does.  Results carry back to s0, from which sc was reached. *)
Theorem if_branch_to_exit:
  !ctx fn s0 sc jbb jnz sa sb sx sd lbl lbl' x P Q R.
    lookup_block sc.vs_current_bb fn.fn_blocks = SOME jbb /\
    get_instruction jbb sc.vs_inst_idx = SOME jnz /\
    is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE /\
    step_inst_base jnz sc = OK (jump_to sa.cs_current_bb sc) /\
    ~sc.vs_halted /\
    (!fuel r. run_from fuel ctx fn sc = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx fn s0 = r) /\
    sa.cs_current_insts = [] /\ P (jump_to sa.cs_current_bb sc) /\
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\
    emit_inst JMP [Label lbl] [] sb = ((), sx) /\
    new_block lbl' sx = (x, sd) /\ fn_has_code sa sd fn ==>
    (?s'. Q s' /\ ~s'.vs_halted /\
          !fuel r. run_from fuel ctx fn (jump_to lbl s') = r /\
                   (!e. r <> Error e) ==>
                   ?fuel'. run_from fuel' ctx fn s0 = r) \/
    (?fuel r. run_from fuel ctx fn s0 = r /\ exit_result r /\ R r)
Proof
  rpt strip_tac >>
  `cs_extends sb sx /\ cs_extends sx sd` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code sx sd fn` by metis_tac[fn_has_code_split] >>
  qspecl_then [`ctx`, `fn`, `sc`, `jbb`, `jnz`, `sa`, `sb`, `P`, `Q`, `R`]
    mp_tac frag_exec_enter >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> qexists_tac `s'` >>
      conj_tac >- fs[] >> conj_tac >- fs[] >> rpt strip_tac >>
      imp_res_tac emit_inst_extends >>
      qabbrev_tac `j = mk_inst sb.cs_next_id JMP [Label lbl] []` >>
      qabbrev_tac `jb = <| bb_label := sx.cs_current_bb;
                           bb_instructions := sx.cs_current_insts |>` >>
      `lookup_block s'.vs_current_bb fn.fn_blocks = SOME jb` by
        metis_tac[fn_has_code_new_block] >>
      `get_instruction jb s'.vs_inst_idx = SOME j` by
        simp[Abbr `jb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `j.inst_opcode = JMP /\ step_inst_base j s' = OK (jump_to lbl s')` by
        simp[Abbr `j`, venomInstTheory.mk_inst_def, step_jmp_behavior] >>
      `is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE` by
        simp[is_terminator_def] >>
      `run_from (SUC fuel) ctx fn s' = r` by
        metis_tac[run_from_jump_result] >>
      metis_tac[]) >>
  disj2_tac >> metis_tac[exit_result_not_error]
QED

(* The compile side of an If: the code the condition selects, from the JNZ
   after the condition to the JMP into the exit block. *)
Theorem compile_if_taken_branch:
  !cx cenv lctx ty c ss1 ss2 st st' b esA es2.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!ss sa sb. (ss = ss1 \/ ss = ss2) /\
                compile_stmts cenv lctx ty ss sa = ((), sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!ss sa sb esa esb. (ss = ss1 \/ ss = ss2) /\
       compile_stmts cenv lctx ty ss sa = ((), sb) /\
       sa.cs_current_insts = [] /\ eval_stmts cx ss esa = (INL (), esb) ==>
       ~block_is_terminated sb) /\
    eval_stmts cx (if b then ss1 else ss2) esA = (INL (), es2) ==>
    ?cond_op s1 s4 s5 s6 then_lbl else_lbl x5 sa sb sx sd exit_lbl lbl' x.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] s4 =
        ((), s5) /\
      new_block then_lbl s5 = (x5, s6) /\
      sa.cs_current_bb = (if b then then_lbl else else_lbl) /\
      sa.cs_current_insts = [] /\ st.cs_next_var <= sa.cs_next_var /\
      compile_stmts cenv lctx ty (if b then ss1 else ss2) sa = ((), sb) /\
      cs_extends sa sb /\
      emit_inst JMP [Label exit_lbl] [] sb = ((), sx) /\
      new_block lbl' sx = (x, sd) /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = [] /\
      !f. fn_has_code st st' f ==>
          fn_has_code st s1 f /\ fn_has_code s5 s6 f /\
          fn_has_code sa sd f /\ fn_has_code sa sb f
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_if_parts >> strip_tac >>
  imp_res_tac new_block_props >> imp_res_tac emit_inst_extends >>
  `~block_is_terminated (if b then s7 else s10)` by
    (Cases_on `b` >> gvs[] >> metis_tac[]) >>
  `?x11. new_block exit_lbl s11 = (x11, st')` by (Cases_on `b` >> fs[]) >>
  imp_res_tac new_block_props >>
  `!sa sb. (if block_is_terminated sa then sb = sa
            else emit_inst JMP [Label exit_lbl] [] sa = ((), sb)) ==>
           cs_extends sa sb /\ sa.cs_next_var = sb.cs_next_var` by
    (rw[] >> imp_res_tac emit_inst_extends >>
     metis_tac[cs_extends_refl, cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends st s1 /\ st.cs_next_var <= s1.cs_next_var /\
   cs_extends s6 s7 /\ s6.cs_next_var <= s7.cs_next_var /\
   cs_extends s9 s10 /\ s9.cs_next_var <= s10.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s7 s8 /\
   cs_extends s8 s9 /\ cs_extends s10 s11 /\ cs_extends s11 st' /\
   s7.cs_next_var = s8.cs_next_var` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  (* the branch the condition selects *)
  `?sa sb sx sd lbl' x.
     sa.cs_current_bb = (if b then then_lbl else else_lbl) /\
     sa.cs_current_insts = [] /\ st.cs_next_var <= sa.cs_next_var /\
     compile_stmts cenv lctx ty (if b then ss1 else ss2) sa = ((), sb) /\
     emit_inst JMP [Label exit_lbl] [] sb = ((), sx) /\
     new_block lbl' sx = (x, sd) /\
     cs_extends s6 sa /\ cs_extends sa sb /\ cs_extends sb sd /\
     cs_extends sd st'` by
    (Cases_on `b` >> fs[]
     >- (qexistsl_tac [`s6`, `s7`, `s8`, `s9`, `else_lbl`, `x8`] >>
         simp[cs_extends_refl] >>
         metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
     qexistsl_tac [`s9`, `s10`, `s11`, `st'`, `exit_lbl`, `x11`] >>
     simp[cs_extends_refl] >>
     metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends s1 st' /\ cs_extends st s5 /\ cs_extends s6 st' /\
   cs_extends st sa /\ cs_extends sa sd` by metis_tac[cs_extends_trans] >>
  `!f. fn_has_code st st' f ==>
       fn_has_code st s1 f /\ fn_has_code s5 s6 f /\ fn_has_code sa sd f /\
       fn_has_code sa sb f` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_refl,
              cs_extends_trans] >>
  qexistsl_tac [`cond_op`, `s1`, `s4`, `s5`, `s6`, `then_lbl`, `else_lbl`,
                `x5`, `sa`, `sb`, `sx`, `sd`, `exit_lbl`, `lbl'`, `x`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Slice lemma 2: an if/else.  The condition is any expr_frag at es; the
   branch bodies are fragments of the form of compile_stmts_correct, and
   a body that runs to its end from a fresh block leaves the block open
   (it does not end in a return), so it falls through to the exit. *)
Theorem compile_if_frag:
  !ctx func cenv cx lctx ty c ss1 ss2 st st' es es' R.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') /\
    eval_stmt cx (If c ss1 ss2) es = (INL (), es') /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv st /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_frag ctx func cenv cx (BaseT BoolT) c es R /\
    (!ss sa sb. (ss = ss1 \/ ss = ss2) /\
                compile_stmts cenv lctx ty ss sa = ((), sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!ss sa sb esa esb. (ss = ss1 \/ ss = ss2) /\
       compile_stmts cenv lctx ty ss sa = ((), sb) /\
       sa.cs_current_insts = [] /\ eval_stmts cx ss esa = (INL (), esb) ==>
       ~block_is_terminated sb) /\
    (!ss sa sb esa esb. (ss = ss1 \/ ss = ss2) /\
       compile_stmts cenv lctx ty ss sa = ((), sb) /\
       eval_stmts cx ss esa = (INL (), esb) /\
       fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
       frag_exec ctx sa sb (stmt_state_rel func cenv cx esa)
         (stmt_state_rel func cenv cx esb) R) ==>
    frag_exec ctx st st' (stmt_state_rel func cenv cx es)
      (stmt_state_rel func cenv cx es') R
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_if_success >> strip_tac >>
  qabbrev_tac `esA = es1 with scopes := FEMPTY :: es1.scopes` >>
  qspecl_then [`cx`, `cenv`, `lctx`, `ty`, `c`, `ss1`, `ss2`, `st`, `st'`,
               `b`, `esA`, `es2`] mp_tac compile_if_taken_branch >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  imp_res_tac emit_inst_extends >>
  `local_ptrs_reserved cenv sa` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `frag_exec ctx sa sb (stmt_state_rel func cenv cx esA)
     (stmt_state_rel func cenv cx es2) R` by
    (qpat_x_assum `!ss sa sb esa esb. _ ==> frag_exec _ _ _ _ _ _`
       (qspecl_then [`if b then ss1 else ss2`, `sa`, `sb`, `esA`, `es2`]
          mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (Cases_on `b` >> simp[] >> NO_TAC) >>
                  metis_tac[]) >>
     simp[]) >>
  PURE_REWRITE_TAC[frag_exec_def] >> rpt strip_tac >>
  qpat_x_assum `expr_frag _ _ _ _ _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC[expr_frag_def] >>
  disch_then (qspecl_then [`st`, `s1`, `cond_op`, `BoolV b`, `es1`, `s`]
                mp_tac) >>
  impl_tac >- fs[] >>
  PURE_REWRITE_TAC[frag_exec_def] >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> BETA_TAC >>
  impl_tac >- fs[] >> strip_tac
  >- (rename1 `eval_operand cond_op sv = _` >>
      qabbrev_tac `jnz = mk_inst s4.cs_next_id JNZ
                           [cond_op; Label then_lbl; Label else_lbl] []` >>
      qabbrev_tac `jbb = <| bb_label := s5.cs_current_bb;
                            bb_instructions := s5.cs_current_insts |>` >>
      `lookup_block sv.vs_current_bb fn.fn_blocks = SOME jbb` by
        (`sv.vs_current_bb = s5.cs_current_bb` by fs[] >>
         simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
      `get_instruction jbb sv.vs_inst_idx = SOME jnz` by
        fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `step_inst_base jnz sv = OK (jump_to sa.cs_current_bb sv)` by
        (qunabbrev_tac `jnz` >> simp[venomInstTheory.mk_inst_def] >>
         drule step_jnz_behavior >> disch_then (fn th => simp[th]) >>
         Cases_on `b` >> fs[val_to_w256_def]) >>
      `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
        simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
      `stmt_state_rel func cenv cx esA (jump_to sa.cs_current_bb sv)` by
        simp[Abbr `esA`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
      qspecl_then [`ctx`, `fn`, `s`, `sv`, `jbb`, `jnz`, `sa`, `sb`, `sx`,
                   `sd`, `exit_lbl`, `lbl'`, `x`,
                   `stmt_state_rel func cenv cx esA`,
                   `stmt_state_rel func cenv cx es2`, `R`]
        mp_tac if_branch_to_exit >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac
      >- (disj1_tac >> qexists_tac `jump_to exit_lbl s'` >>
          `stmt_state_rel func cenv cx (es2 with scopes := rest) s'` by
            (irule stmt_state_rel_pop_scope >> metis_tac[]) >>
          simp[stmt_state_rel_jump_to] >> fs[jump_to_def] >> metis_tac[]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

(* ===== Checked addition that overflows ===== *)

(* The source's unsigned 256-bit addition fails exactly when the words
   overflow. *)
Theorem bounded_int_op_add_overflow:
  !i1 i2 err.
    within_int_bound (Unsigned 256) i1 /\ within_int_bound (Unsigned 256) i2 /\
    bounded_int_op (Unsigned 256) (i1 + i2) = INR err ==>
    dimword (:256) <=
      w2n (val_to_w256 (IntV i1)) + w2n (val_to_w256 (IntV i2))
Proof
  rw[bounded_int_op_def, within_int_bound_def] >>
  `?n1 n2. i1 = &n1 /\ i2 = &n2` by
    metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[val_to_w256_def, integer_wordTheory.i2w_def, wordsTheory.w2n_n2w,
      wordsTheory.dimword_def, integerTheory.INT_ADD]
QED

(* compile_safe_add on unsigned 256-bit operands whose sum overflows: the
   ASSERT fails, so the fragment aborts with Revert_abort. *)
Theorem compile_safe_add_overflow_frag:
  !ctx x y ty st op st' P Q R.
    compile_safe_add x y ty st = (op, st') /\
    type_bits ty = 256 /\ ~is_signed_type ty /\
    (!s. P s ==> fresh_vars_wrt st s /\
         ?a b. eval_operand x s = SOME a /\ eval_operand y s = SOME b /\
               dimword (:256) <= w2n a + w2n b) /\
    (!s. R (Abort Revert_abort s)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_safe_add_unsigned_256_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> asm_rewrite_tac[] >>
  rpt strip_tac >> disj2_tac >>
  `fresh_vars_wrt st s /\
   ?a b. eval_operand x s = SOME a /\ eval_operand y s = SOME b /\
         dimword (:256) <= w2n a + w2n b` by metis_tac[] >>
  drule_all compile_safe_add_overflow >> strip_tac >>
  qexistsl_tac [`Revert_abort`, `ss'`] >> simp[]
QED

(* Slice lemma 3: a checked unsigned 256-bit addition whose source result is
   a RuntimeError aborts in the lowered code, which result_rel relates to the
   source error. *)
Theorem compile_safe_add_runtime_error:
  !ctx func ret_tv cenv cx tv x y ty st op st' P Q es' i1 i2 err.
    compile_safe_add x y ty st = (op, st') /\
    type_bits ty = 256 /\ ~is_signed_type ty /\
    within_int_bound (Unsigned 256) i1 /\ within_int_bound (Unsigned 256) i2 /\
    evaluate_binop (Unsigned 256) tv Add (IntV i1) (IntV i2) = INR err /\
    (!s. P s ==> fresh_vars_wrt st s /\
         eval_operand x s = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y s = SOME (val_to_w256 (IntV i2))) ==>
    err = RuntimeError "bounded_int_op bound" /\
    frag_exec ctx st st' P Q
      (result_rel func ret_tv cenv cx (INR (Error err), es'))
Proof
  rpt gen_tac >> strip_tac >>
  `bounded_int_op (Unsigned 256) (i1 + i2) = INR err` by
    fs[evaluate_binop_def] >>
  conj_tac >- (qpat_x_assum `bounded_int_op _ _ = _` mp_tac >>
               rw[bounded_int_op_def]) >>
  `dimword (:256) <=
   w2n (val_to_w256 (IntV i1)) + w2n (val_to_w256 (IntV i2))` by
    (irule bounded_int_op_add_overflow >> metis_tac[]) >>
  qspecl_then [`ctx`, `x`, `y`, `ty`, `st`, `op`, `st'`, `P`, `Q`,
               `result_rel func ret_tv cenv cx (INR (Error err), es')`]
    mp_tac compile_safe_add_overflow_frag >>
  impl_tac >- (simp[result_rel_def] >> metis_tac[]) >>
  simp[]
QED

(* Every slice is independent of the general compiler admissions. *)
val () = List.app
  (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("lowering slice proof is not closed: " ^ name)
    end)
  (DB.thms "loweringSlice");
