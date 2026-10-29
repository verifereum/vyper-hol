(*
 * Internal calls: the callee's prologue (#638)
 *
 * compile_internal_function starts every internal function with a
 * prologue: the return-buffer PARAM of a memory return, one PARAM per
 * argument (compile_internal_param_decls), RETPC_PARAM, the arguments'
 * pointers (materialize_internal_params: an ALLOCA and an MSTORE for a
 * stack-passed argument, the PARAM itself for a memory-passed one), and
 * the temporary return-value ALLOCA Python allocates.  Run from the state
 * setup_callee gives the INVOKE's callee, it establishes the statement
 * relation for the scope push_function builds from the arguments, where
 * the prologue leaves off: before the immutables reservation of a
 * constructor callee, the nonreentrant lock and the body.
 *
 * TOP-LEVEL:
 *   compile_internal_prologue   — the prologue as one compile action
 *   compile_internal_function_prologue — compile_internal_function is the
 *                                 prologue, then the rest of it
 *   internal_args_rel           — the arguments an INVOKE passes, for
 *                                 the scope the callee's body starts in
 *   internal_stack_size         — the bytes the stack-passed arguments'
 *                                 ALLOCAs take
 *   compile_internal_prologue_entry — from setup_callee, the prologue
 *                                 reaches its end in stmt_state_rel, with
 *                                 the return PC and buffer bound
 *   compile_internal_prologue_code — the prologue's code is one open
 *                                 block with no terminator or INVOKE, and
 *                                 its compile env holds every argument
 *                                 through a pointer handed out before the
 *                                 body (local_ptrs_reserved)
 *
 * Helpers:
 *   local_ptrs_rel_bind_ptr     — binding a name in scope to a region
 *                                 holding its value keeps local_ptrs_rel
 *   mat_pending, mat_inv, mat_frame — the materialization induction's
 *                                 invariants (proof-internal)
 *
 * alloca_room: under INVOKE's semantics the callee inherits the
 * caller's allocation frontier (setup_callee keeps vs_alloca_next), so
 * alloca_room at callee entry is not implied by the caller's state.  The
 * entry lemma takes it as a hypothesis on the entry state, for the call
 * site to discharge, and also takes the bound the materialization proof
 * uses directly: the frontier at the call plus internal_stack_size is
 * below 2 ** 256, so the arguments' ALLOCAs do not wrap.
 *)

Theory intCallCallee
Ancestors
  list rich_list finite_map
  fragExec localPtrsProps exprLoweringProps loweringHalt
  moduleLowering stmtLowering exprLowering emitHelper context compileEnv
  valueEncoding valueEncodingProps venomMemDefs
  venomExecSemantics venomInst venomState venomMemProps vyperState

(* ===== The prologue ===== *)

(* compile_internal_function up to the code that is not the prologue's: the
   immutables reservation of a constructor callee, the nonreentrant lock and
   the body.  It returns the compile env the body is compiled in and the
   return-PC operand. *)
Definition compile_internal_prologue_def:
  compile_internal_prologue cenv params has_return_buf ret_type =
    do return_buf_var <-
         (if has_return_buf then
            do param_op <- emit_op PARAM [Lit 0w];
               return (SOME param_op)
            od
          else return NONE);
       param_idx_start <- return (if has_return_buf then 1 else 0);
       params_result <- compile_internal_param_decls params param_idx_start;
       captured_params <- return (FST params_result);
       next_idx <- return (SND params_result);
       return_pc <- emit_op RETPC_PARAM [Lit (n2w next_idx)];
       cenv1 <- return
         (cenv with
            <| ce_return_buf :=
                 (case (return_buf_var, cenv.ce_return_buf) of
                    (SOME param_op, SOME (MemLoc _ sz)) =>
                      SOME (PtrVar param_op sz)
                  | _ => cenv.ce_return_buf);
               ce_return_pc := SOME (PtrVar return_pc 0) |>);
       cenv2 <- materialize_internal_params cenv1 captured_params;
       (case ret_type of
          SOME ret_ty =>
            if cenv.ce_returns_count > 0 then
              do compile_alloc_buffer (type_memory_bytes cenv ret_ty);
                 return ()
              od
            else return ()
        | NONE => return ());
       return (cenv2, return_pc)
    od
End

Theorem compile_internal_function_prologue:
  !cenv params has_return_buf is_nonreentrant nkey use_transient is_view
   is_ctor_context immutables_len body ret_type st cenv2 return_pc st1.
    compile_internal_prologue cenv params has_return_buf ret_type st =
      ((cenv2, return_pc), st1) ==>
    compile_internal_function cenv params has_return_buf is_nonreentrant
      nkey use_transient is_view is_ctor_context immutables_len body
      ret_type st =
    (do forced_alloc_id <-
          (if is_ctor_context /\ immutables_len > 0 then
             let touch_offset = if immutables_len > 32
                                then immutables_len - 32 else 0 in
             do alloc_result <- compile_alloc_buffer_with_id immutables_len;
                emit_op MLOAD [Lit (n2w touch_offset)];
                return (SOME (FST alloc_result))
             od
           else return NONE);
        (if is_nonreentrant then
           compile_nonreentrant_lock nkey use_transient is_view
         else return ());
        compile_stmts (cenv2 with ce_alloca_locals := T) NoLoop
          (case ret_type of SOME t => t | NONE => BaseT BoolT) body;
        cs <- comp_get;
        (if block_is_terminated cs then return ()
         else
           do (if is_nonreentrant then
                 compile_nonreentrant_unlock nkey use_transient is_view
               else return ());
              (case ret_type of
                 NONE => emit_inst RET [return_pc] []
               | SOME _ => emit_inst INVALID [] [])
           od);
        return forced_alloc_id
     od) st1
Proof
  rpt gen_tac >>
  simp[compile_internal_prologue_def, compile_internal_function_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

(* ===== Hypotheses ===== *)

(* The bytes the ALLOCAs of the stack-passed arguments take: the size of
   each one's slot in the compile env. *)
Definition internal_stack_size_def:
  internal_stack_size cenv [] = 0n /\
  internal_stack_size cenv ((name, is_stack) :: rest) =
    (if is_stack then
       (case FLOOKUP cenv.ce_vars name of
          SOME (MemLoc _ sz) => sz
        | _ => 0)
     else 0) + internal_stack_size cenv rest
End

(* The arguments args an INVOKE passes to an internal function compiled in
   cenv with parameters params (each with whether it is passed on the
   stack), for the scope env its body starts in, where the parameters'
   PARAM indices start at base (1 after a memory return's buffer, else 0),
   with the allocation frontier and memory at the call:
   - env binds exactly the parameters, which are distinct;
   - each parameter has a MemLoc slot in cenv, whose size fits its type,
     and a well-formed value;
   - a stack-passed parameter's slot holds at least a word, and its
     argument word is its value's encoding: a memory holding that word at
     some offset holds the value there;
   - a memory-passed parameter's argument points into the caller's memory
     below the frontier, at a region of the slot's size holding the value,
     and these regions are pairwise disjoint (the caller stages each in a
     buffer of its own, compile_stage_intcall_args);
   - the PARAM indices are in range and fit a word. *)
Definition internal_args_rel_def:
  internal_args_rel cenv params env (base:num) (args:bytes32 list) frontier
                    mem <=>
    ALL_DISTINCT (MAP FST params) /\
    FDOM env = set (MAP FST params) /\
    base + LENGTH params <= LENGTH args /\ LENGTH args < dimword (:256) /\
    (!i. i < LENGTH params ==>
       ?off sz entry.
         FLOOKUP cenv.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) /\
         FLOOKUP env (FST (EL i params)) = SOME entry /\
         type_memory_size entry.type <= sz /\
         val_wf entry.type entry.value /\
         if SND (EL i params) then
           32 <= sz /\
           !b m. mem_word_at b m = EL (base + i) args ==>
                 val_in_memory entry.type entry.value b m
         else
           w2n (EL (base + i) args) + sz <= frontier /\
           val_in_memory entry.type entry.value (w2n (EL (base + i) args))
             mem) /\
    (!i j offi szi offj szj.
       i < LENGTH params /\ j < LENGTH params /\ i <> j /\
       ~SND (EL i params) /\ ~SND (EL j params) /\
       FLOOKUP cenv.ce_vars (FST (EL i params)) = SOME (MemLoc offi szi) /\
       FLOOKUP cenv.ce_vars (FST (EL j params)) = SOME (MemLoc offj szj) ==>
       regions_disjoint (w2n (EL (base + i) args)) szi
                        (w2n (EL (base + j) args)) szj)
End

(* ===== The prologue's code ===== *)

Theorem compile_internal_param_decls_shape[local]:
  !ps idx st r st'.
    compile_internal_param_decls ps idx st = (r, st') ==>
    SND r = idx + LENGTH ps /\
    LENGTH (FST r) = LENGTH ps /\
    (!i. i < LENGTH ps ==>
         EL i (FST r) =
           (FST (EL i ps), SND (EL i ps),
            Var (STRING #"%" (toString (st.cs_next_var + i))))) /\
    st'.cs_next_var = st.cs_next_var + LENGTH ps /\
    st'.cs_next_id = st.cs_next_id + LENGTH ps /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts =
      st.cs_current_insts ++
      GENLIST (\i. mk_inst (st.cs_next_id + i) PARAM [Lit (n2w (idx + i))]
                     [STRING #"%" (toString (st.cs_next_var + i))])
        (LENGTH ps)
Proof
  Induct
  >- simp[compile_internal_param_decls_def, comp_return_def] >>
  Cases >> rpt gen_tac >>
  simp[compile_internal_param_decls_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rpt strip_tac >~ [`EL i _ = _`]
  >- (Cases_on `i` >> gvs[arithmeticTheory.ADD1]) >>
  simp[GENLIST_CONS, combinTheory.o_DEF, arithmeticTheory.ADD1] >>
  simp[GENLIST_FUN_EQ]
QED

(* Running the PARAMs binds each output to its argument. *)
Theorem run_inst_seq_params[local]:
  !n id idx nv s.
    idx + n <= LENGTH s.vs_params /\ LENGTH s.vs_params < dimword (:256) ==>
    ?s'.
      run_inst_seq
        (GENLIST (\i. mk_inst (id + i) PARAM [Lit (n2w (idx + i))]
                        [STRING #"%" (toString (nv + i))]) n) s = OK s' /\
      s' = s with vs_vars := s'.vs_vars /\
      (!i. i < n ==>
           lookup_var (STRING #"%" (toString (nv + i))) s' =
           SOME (EL (idx + i) s.vs_params)) /\
      (!x. (!i. i < n ==> x <> STRING #"%" (toString (nv + i))) ==>
           lookup_var x s' = lookup_var x s)
Proof
  Induct
  >- (rw[run_inst_seq_def] >> qexists_tac `s` >>
      simp[venomStateTheory.venom_state_component_equality]) >>
  rpt strip_tac >>
  `step_inst_base (mk_inst id PARAM [Lit (n2w idx)]
                     [STRING #"%" (toString nv)]) s =
   OK (update_var (STRING #"%" (toString nv)) (EL idx s.vs_params) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, wordsTheory.w2n_n2w]) >>
  last_x_assum (qspecl_then [`id + 1`, `idx + 1`, `nv + 1`,
    `update_var (STRING #"%" (toString nv)) (EL idx s.vs_params) s`]
    mp_tac) >>
  impl_tac >- simp[update_var_def] >> strip_tac >>
  `GENLIST (\i. mk_inst (id + i) PARAM [Lit (n2w (idx + i))]
                  [STRING #"%" (toString (nv + i))]) (SUC n) =
   mk_inst id PARAM [Lit (n2w idx)] [STRING #"%" (toString nv)] ::
   GENLIST (\i. mk_inst (id + 1 + i) PARAM [Lit (n2w (idx + 1 + i))]
                  [STRING #"%" (toString (nv + 1 + i))]) n` by
    simp[GENLIST_CONS, combinTheory.o_DEF, arithmeticTheory.ADD1,
         GENLIST_FUN_EQ] >>
  qexists_tac `s'` >> rpt conj_tac
  >- (qpat_x_assum `GENLIST _ (SUC n) = _` SUBST1_TAC >>
      simp[run_inst_seq_def] >>
      qpat_x_assum `run_inst_seq _ _ = OK s'` mp_tac >> simp[])
  >- (qpat_x_assum `s' = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV th))) >>
      simp[update_var_def])
  >- (Cases >> strip_tac
      >- (first_x_assum (qspec_then `STRING #"%" (toString nv)` mp_tac) >>
          simp[ASCIInumbersTheory.toString_inj] >>
          simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      first_x_assum (qspec_then `n'` mp_tac) >>
      simp[update_var_def, arithmeticTheory.ADD1]) >>
  rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      simp[arithmeticTheory.ADD1]) >>
  first_x_assum (qspec_then `0` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem materialize_internal_params_shape[local]:
  !caps cenv st cenv' st'.
    materialize_internal_params cenv caps st = (cenv', st') ==>
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id /\
    (?new. st'.cs_current_insts = st.cs_current_insts ++ new /\
           EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = MSTORE) new) /\
    (?vars. cenv' = cenv with ce_vars := vars) /\
    !n. ~MEM n (MAP FST caps) ==>
        FLOOKUP cenv'.ce_vars n = FLOOKUP cenv.ce_vars n
Proof
  Induct
  >- (simp[materialize_internal_params_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `cenv.ce_vars` >>
      simp[compileEnvTheory.compile_env_component_equality]) >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
          metis_tac[]) >>
      rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >> simp[] >~ [`emit_op _ _`]
      >- (simp[emit_op_def, emit_void_def, comp_bind_def,
               comp_ignore_bind_def, comp_return_def, fresh_id_def,
               fresh_var_def, emit_def] >>
          strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
          conj_tac >- (qexists_tac `vars` >> simp[]) >>
          rpt strip_tac >> gvs[FLOOKUP_UPDATE]) >>
      strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE]
QED

Theorem materialize_internal_params_reserved[local]:
 !caps cenv st cenv' st'.
 materialize_internal_params cenv caps st = (cenv',st') /\
 ALL_DISTINCT (MAP FST caps) /\
 ALL_DISTINCT (MAP (SND o SND) caps) /\
 (!n b op. MEM (n,b,op) caps ==>
    (?off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz)) /\
    (?p. op = Var p /\ not_fresh_at st p)) /\
 (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
    MEM n (MAP FST caps)) /\
 (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p /\
    (!m sz'. FLOOKUP cenv.ce_vars m = SOME (PtrVar (Var p) sz') ==> n = m)) /\
 (!n op sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar op sz) ==>
    ~MEM op (MAP (SND o SND) caps))
 ==> local_ptrs_reserved cenv' st'
Proof
  Induct
  >- (simp[materialize_internal_params_def, comp_return_def,
           local_ptrs_reserved_def] >> metis_tac[]) >>
  PairCases >> rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_assum `!n b op. _` (qspecl_then [`h0`,`h1`,`h2`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `h1` >>
  gvs[materialize_internal_params_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce caps cs` >>
  first_x_assum irule >> qexistsl_tac [`ce`,`cs`] >>
  simp[Abbr `ce`, Abbr `cs`, FLOOKUP_UPDATE] >>
  qpat_x_assum `materialize_internal_params _ _ _ = _` kall_tac >>
  (conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!n b op. _`
        (qspecl_then [`n`,`b`,`op`] mp_tac) >>
      simp[] >> strip_tac >>
      `n <> h0` by (strip_tac >> gvs[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      simp[] >>
      gvs[not_fresh_at_def] >> rpt strip_tac >>
      qpat_x_assum `!n. st.cs_next_var <= n ==> p' <> _` irule >> simp[]) >>
  conj_tac
  >- (rw[] >> gvs[AllCaseEqs()] >>
      qpat_x_assum `!n p sz. FLOOKUP _ _ = SOME (PtrVar (Var p) sz) ==> _`
        (fn th => imp_res_tac th) >>
      gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
      qpat_x_assum `!n op sz. FLOOKUP _ _ = SOME (PtrVar op sz) ==> _`
        (fn th => imp_res_tac th) >> gvs[]) >>
  conj_tac
  >- (rw[] >> gvs[AllCaseEqs()] >>
      qpat_x_assum `!n off sz. FLOOKUP _ _ = SOME (MemLoc off sz) ==> _`
        (fn th => imp_res_tac th) >> gvs[]) >>
  rw[] >> gvs[AllCaseEqs()] >>
  qpat_x_assum `!n op sz. FLOOKUP _ _ = SOME (PtrVar op sz) ==> _`
    (fn th => imp_res_tac th) >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `!n b op. MEM (n,b,op) caps ==> _` (fn th => drule th) >>
  disch_then strip_assume_tac >> gvs[not_fresh_at_def])
QED

(* ===== The arguments' pointers ===== *)

Theorem regions_disjoint_sym[local]:
  !b1 s1 b2 s2.
    regions_disjoint b1 s1 b2 s2 <=> regions_disjoint b2 s2 b1 s1
Proof
  rw[compileEnvTheory.regions_disjoint_def] >> metis_tac[]
QED

(* A live local's region lies below the frontier. *)
Theorem local_region_below_next[local]:
  !func cenv scopes ss n b sz.
    local_ptrs_rel func cenv scopes ss /\ local_region cenv scopes ss n b sz ==>
    b + sz <= ss.vs_alloca_next
Proof
  rw[local_ptrs_rel_def, local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

(* Binding a name in scope that no pointer held yet to a region holding its
   value that misses every other live local. *)
Theorem local_ptrs_rel_bind_ptr:
  !func cenv scopes ss name entry p sz w.
    local_ptrs_rel func cenv scopes ss /\
    lookup_scopes name scopes = SOME entry /\
    (!q sq. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sq)) /\
    lookup_var p ss = SOME w /\ local_backed func p ss (w2n w) sz /\
    w2n w + sz <= ss.vs_alloca_next /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) ss.vs_memory /\
    (!n b sz'. n <> name /\ local_region cenv scopes ss n b sz' ==>
               regions_disjoint (w2n w) sz b sz') ==>
    local_ptrs_rel func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      scopes ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> strip_tac
      >- gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> simp[local_region_def, FLOOKUP_UPDATE] >> strip_tac >>
  Cases_on `n1 = name` >> Cases_on `n2 = name` >> gvs[]
  >- (qpat_x_assum `!n b sz'. n <> _ /\ _ ==> _` irule >>
      simp[local_region_def] >> metis_tac[])
  >- (ONCE_REWRITE_TAC[regions_disjoint_sym] >>
      qpat_x_assum `!n b sz'. n <> _ /\ _ ==> _` irule >>
      simp[local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!n1 n2 b1 sz1 b2 sz2. _` irule >>
  simp[local_region_def] >> metis_tac[]
QED

(* A live local's region under cenv extended at name is either name's
   new one or was live before. *)
Theorem local_region_bind[local]:
  !cenv scopes ss ss' name p sz n b sz'.
    local_region
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      scopes ss' n b sz' /\
    (!q. q <> p ==> lookup_var q ss' = lookup_var q ss) /\
    (!q sq. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) /\
            lookup_scopes n scopes <> NONE ==> q <> p) ==>
    (n = name /\ sz' = sz /\ ?w. lookup_var p ss' = SOME w /\ b = w2n w) \/
    (n <> name /\ local_region cenv scopes ss n b sz')
Proof
  rw[local_region_def, FLOOKUP_UPDATE] >> Cases_on `n = name` >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `!q. q <> p ==> _` drule >> simp[]
QED

Theorem step_mstore_vars[local]:
  !id x y a v s.
    lookup_var x s = SOME a /\ lookup_var y s = SOME v ==>
    step_inst_base (mk_inst id MSTORE [Var x; Var y] []) s =
    OK (mstore (w2n a) v s)
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_write2_def, eval_operand_def]
QED

(* The ALLOCA and MSTORE of a stack-passed argument x, of value a, put it
   at the frontier in a region of its slot's size sz, bound to name. *)
Theorem materialize_stack_step[local]:
  !func cenv env s st x a name off sz entry.
    local_ptrs_rel func cenv [env] s /\ alloca_inv s /\
    (!inst n base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n n) /\
    fresh_vars_wrt st s /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
    fn_inst_ids_distinct func /\
    s.vs_alloca_next + sz < dimword (:256) /\
    not_fresh_at st x /\ lookup_var x s = SOME a /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
    FLOOKUP env name = SOME entry /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    32 <= sz /\
    (!b m. mem_word_at b m = a ==> val_in_memory entry.type entry.value b m) ==>
    ?s1.
      run_inst_seq
        [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
           [STRING #"%" (toString st.cs_next_var)];
         mk_inst (st.cs_next_id + 1) MSTORE
           [Var (STRING #"%" (toString st.cs_next_var)); Var x] []] s =
        OK s1 /\
      s1 = mstore s.vs_alloca_next a
             (update_var (STRING #"%" (toString st.cs_next_var))
                (n2w s.vs_alloca_next)
                (s with <| vs_allocas := s.vs_allocas |+
                             (st.cs_next_id, (s.vs_alloca_next, sz));
                           vs_alloca_next := s.vs_alloca_next + sz |>)) /\
      local_ptrs_rel func
        (cenv with ce_vars updated_by
           (\m. m |+ (name,
                      PtrVar (Var (STRING #"%" (toString st.cs_next_var)))
                        sz))) [env] s1 /\
      alloca_inv s1 /\
      (!inst n base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit n] /\
         FLOOKUP s1.vs_allocas inst.inst_id = SOME (base, sz) ==>
         sz = w2n n) /\
      not_local_ptr cenv [env] (STRING #"%" (toString st.cs_next_var))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `x0 = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `id0 = st.cs_next_id` >>
  qabbrev_tac `nxt = s.vs_alloca_next` >>
  `FLOOKUP s.vs_allocas id0 = NONE` by
    (simp[FLOOKUP_DEF, Abbr `id0`] >> strip_tac >>
     qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> simp[]) >>
  `sz < dimword (:256) /\ nxt < dimword (:256)` by decide_tac >>
  `x <> x0` by (fs[not_fresh_at_def, Abbr `x0`]) >>
  `not_local_ptr cenv [env] x0` by
    (simp[Abbr `x0`] >> irule local_ptrs_rel_fresh_not_local_ptr >>
     qexistsl_tac [`func`, `s`, `st`] >> simp[]) >>
  qabbrev_tac `sa = update_var x0 (n2w nxt)
                      (s with <| vs_allocas := s.vs_allocas |+
                                   (id0, (nxt, sz));
                                 vs_alloca_next := nxt + sz |>)` >>
  `exec_alloca (mk_inst id0 ALLOCA [Lit (n2w sz)] [x0]) s (n2w sz : bytes32) =
   OK sa` by
    simp[exec_alloca_def, mk_inst_def, Abbr `sa`, Abbr `nxt`,
         wordsTheory.w2n_n2w] >>
  `step_inst_base (mk_inst id0 ALLOCA [Lit (n2w sz)] [x0]) s = OK sa` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def] >>
     fs[mk_inst_def]) >>
  drule_at (Pos hd) local_ptrs_rel_exec_alloca_fresh >>
  disch_then (qspecl_then [`func`, `cenv`, `[env]`, `x0`] mp_tac) >>
  simp[mk_inst_def] >> strip_tac >>
  `w = n2w nxt` by gvs[Abbr `sa`, lookup_var_def, update_var_def,
                       FLOOKUP_UPDATE] >>
  gvs[] >>
  `w2n (n2w nxt : bytes32) = nxt /\ w2n (n2w sz : bytes32) = sz` by
    simp[wordsTheory.w2n_n2w] >>
  `lookup_var x sa = SOME a` by
    gvs[Abbr `sa`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id0 + 1) MSTORE [Var x0; Var x] []) sa =
   OK (mstore nxt a sa)` by
    (qspecl_then [`id0 + 1`, `x0`, `x`, `n2w nxt`, `a`, `sa`] mp_tac
       step_mstore_vars >>
     simp[Abbr `sa`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `(mstore nxt a sa).vs_vars = sa.vs_vars /\
   (mstore nxt a sa).vs_allocas = sa.vs_allocas /\
   (mstore nxt a sa).vs_alloca_next = sa.vs_alloca_next` by
    simp[mstore_def] >>
  `local_ptrs_rel func cenv [env] (mstore nxt a sa)` by
    (irule local_ptrs_rel_mstore >> simp[] >> rpt strip_tac >>
     disj2_tac >>
     `local_region cenv [env] s name' b sz'` by
       (fs[local_region_def, Abbr `sa`, lookup_var_def, update_var_def,
           FLOOKUP_UPDATE] >>
        rename1 `FLOOKUP cenv.ce_vars name' = SOME (PtrVar (Var q) sz')` >>
        `q <> x0` by (fs[not_local_ptr_def] >> metis_tac[]) >>
        gvs[] >> metis_tac[]) >>
     qspecl_then [`func`, `cenv`, `[env]`, `s`, `name'`, `b`, `sz'`] mp_tac
       local_region_below_next >>
     simp[Abbr `nxt`]) >>
  rpt conj_tac
  >- (fs[mk_inst_def] >> simp[run_inst_seq_def])
  >- (irule local_ptrs_rel_bind_ptr >> simp[lookup_scopes_def] >>
      rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!name b sz. local_region _ _ sa _ _ _ ==> _` irule >>
          fs[local_region_def, lookup_var_def] >> metis_tac[])
      >- (qpat_x_assum `!b m. mem_word_at b m = a ==> _` irule >>
          simp[mstore_mem_word_at_same]) >>
      simp[local_backed_def] >> disj1_tac >>
      qexists_tac `mk_inst id0 ALLOCA [Lit (n2w sz)] [x0]` >>
      simp[mk_inst_def] >> fs[mk_inst_def])
  >- (irule alloca_inv_fields >> qexists_tac `sa` >> simp[] >>
      qpat_x_assum `exec_alloca _ _ _ = OK sa`
        (irule o
         MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] alloca_inv_exec_alloca)) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_id = id0`
      >- (`inst = mk_inst id0 ALLOCA [Lit (n2w sz)] [x0]` by
            (irule fn_inst_ids_distinct_inj >> simp[mk_inst_def] >>
             qexists_tac `func` >> fs[mk_inst_def]) >>
          gvs[mk_inst_def, Abbr `sa`, update_var_def, FLOOKUP_UPDATE]) >>
      first_x_assum irule >>
      gvs[Abbr `sa`, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

Theorem internal_stack_size_update[local]:
  !l cenv name v.
    ~MEM name (MAP FST l) ==>
    internal_stack_size (cenv with ce_vars updated_by (\m. m |+ (name, v))) l =
    internal_stack_size cenv l
Proof
  Induct >- simp[internal_stack_size_def] >>
  PairCases >> rw[internal_stack_size_def, FLOOKUP_UPDATE]
QED

(* Stores above the call frontier cannot disturb a pending caller buffer. *)
Theorem pending_arg_mstore[local]:
  !ty v b sz f0 dst w s.
    val_in_memory ty v b s.vs_memory /\ val_wf ty v /\
    type_memory_size ty <= sz /\ b + sz <= f0 /\ f0 <= dst ==>
    val_in_memory ty v b (mstore dst w s).vs_memory
Proof
  rpt strip_tac >> irule mstore_keeps_val_in_memory >> simp[]
QED

(* Caller buffers are backed by their separation from all frame allocations. *)
Theorem caller_buffer_backed[local]:
  !func p s b sz f0.
    b + sz <= f0 /\
    (!aid base size. FLOOKUP s.vs_allocas aid = SOME (base, size) ==>
                     f0 <= base) ==>
    local_backed func p s b sz
Proof
  rpt strip_tac >> simp[local_backed_def] >> disj2_tac >>
  rpt strip_tac >> first_x_assum drule >>
  simp[compileEnvTheory.regions_disjoint_def]
QED

Theorem materialize_memory_bind[local]:
  !func cenv env s name entry p sz w f0 mr.
    local_ptrs_rel func cenv [env] s /\
    FLOOKUP env name = SOME entry /\
    (!q sq. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sq)) /\
    lookup_var p s = SOME w /\ mr name = SOME (w2n w, sz) /\
    w2n w + sz <= f0 /\ f0 <= s.vs_alloca_next /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) s.vs_memory /\
    (!aid b size. FLOOKUP s.vs_allocas aid = SOME (b, size) ==> f0 <= b) /\
    (!n b size. local_region cenv [env] s n b size ==>
                f0 <= b \/ mr n = SOME (b, size)) /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1, sz1) /\ mr n2 = SOME (b2, sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) ==>
    local_ptrs_rel func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      [env] s
Proof
  rpt gen_tac >> strip_tac >> irule local_ptrs_rel_bind_ptr >>
  simp[lookup_scopes_def] >> reverse conj_tac
  >- (irule caller_buffer_backed >> qexists_tac `f0` >> simp[] >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!n b size. local_region _ _ _ _ _ _ ==> _` drule >>
  strip_tac
  >- simp[compileEnvTheory.regions_disjoint_def] >>
  qpat_x_assum `!n1 n2 b1 sz1 b2 sz2. _` irule >> metis_tac[]
QED

(* The region partition is stable under either kind of parameter binding. *)
Theorem local_region_partition_bind[local]:
  !cenv env s s' name p sz f0 mr.
    (!n b size. local_region cenv [env] s n b size ==>
                f0 <= b \/ mr n = SOME (b, size)) /\
    (!q. q <> p ==> lookup_var q s' = lookup_var q s) /\
    (!n q sq. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) /\
              lookup_scopes n [env] <> NONE ==> q <> p) /\
    (!w. lookup_var p s' = SOME w ==>
         f0 <= w2n w \/ mr name = SOME (w2n w, sz)) ==>
    !n b size.
      local_region
        (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
        [env] s' n b size ==>
      f0 <= b \/ mr n = SOME (b, size)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule local_region_bind >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* Compact interfaces for the materialization induction. *)
Definition mat_pending_def:
  mat_pending cenv env st s f0 mr caps <=>
    EVERY (\c. ?p a off sz entry.
      SND (SND c) = Var p /\ not_fresh_at st p /\ lookup_var p s = SOME a /\
      FLOOKUP cenv.ce_vars (FST c) = SOME (MemLoc off sz) /\
      FLOOKUP env (FST c) = SOME entry /\
      type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
      if FST (SND c) then
        32 <= sz /\ !b m. mem_word_at b m = a ==>
                         val_in_memory entry.type entry.value b m
      else
        mr (FST c) = SOME (w2n a, sz) /\ w2n a + sz <= f0 /\
        val_in_memory entry.type entry.value (w2n a) s.vs_memory) caps
End

Definition mat_inv_def:
  mat_inv func cenv env st s f0 mr <=>
    local_ptrs_rel func cenv [env] s /\ alloca_inv s /\
    (!inst n base sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n n) /\
    fresh_vars_wrt st s /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) ==> f0 <= b) /\
    f0 <= s.vs_alloca_next /\
    (!n b sz. local_region cenv [env] s n b sz ==>
              f0 <= b \/ mr n = SOME (b, sz))
End

Definition mat_frame_def:
  mat_frame st s t <=>
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    t = s with <| vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                  vs_allocas := t.vs_allocas; vs_alloca_next := t.vs_alloca_next |>
End

Theorem mat_frame_refl[local]:
  !st s. mat_frame st s s
Proof
  simp[mat_frame_def, venom_state_component_equality]
QED

Theorem mat_frame_trans[local]:
  !st mid s t u.
    mat_frame st s t /\ mat_frame mid t u /\
    (!x. not_fresh_at st x ==> not_fresh_at mid x) ==>
    mat_frame st s u
Proof
  rpt gen_tac >> simp[mat_frame_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem mat_pending_bind[local]:
  !caps cenv env st s mid t f0 mr name loc.
    mat_pending cenv env st s f0 mr caps /\ ~MEM name (MAP FST caps) /\
    mat_frame st s t /\
    (!x. not_fresh_at st x ==> not_fresh_at mid x) /\
    (!ty v b sz. val_wf ty v /\ type_memory_size ty <= sz /\ b + sz <= f0 /\
                 val_in_memory ty v b s.vs_memory ==>
                 val_in_memory ty v b t.vs_memory) ==>
    mat_pending (cenv with ce_vars updated_by (\m. m |+ (name, loc)))
      env mid t f0 mr caps
Proof
  rpt gen_tac >> simp[mat_pending_def, EVERY_MEM, mat_frame_def] >>
  strip_tac >> rpt strip_tac >>
  `FST c <> name` by (gvs[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `!c. MEM c caps ==> _` drule >> strip_tac >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `FST (SND c)` >> gvs[] >>
  qpat_x_assum `!ty v b sz. _` irule >> simp[] >>
  qexists_tac `sz` >> simp[]
QED

Theorem mat_tail_stack_size[local]:
  !caps cenv name loc.
    ~MEM name (MAP FST caps) ==>
    internal_stack_size (cenv with ce_vars updated_by (\m. m |+ (name, loc)))
      (MAP (\c. (FST c, FST (SND c))) caps) =
    internal_stack_size cenv (MAP (\c. (FST c, FST (SND c))) caps)
Proof
  rpt strip_tac >> irule internal_stack_size_update >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem mat_inv_memory_bind[local]:
  !func cenv env st s f0 mr name entry p sz w off.
    mat_inv func cenv env st s f0 mr /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
    FLOOKUP env name = SOME entry /\ lookup_var p s = SOME w /\
    mr name = SOME (w2n w, sz) /\ w2n w + sz <= f0 /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) s.vs_memory /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1, sz1) /\ mr n2 = SOME (b2, sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) ==>
    mat_inv func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      env st s f0 mr
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `mat_inv _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  simp[mat_inv_def] >> conj_tac
  >- (irule materialize_memory_bind >> simp[] >>
      qexistsl_tac [`f0`, `mr`] >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> Cases_on `n = name`
  >- (gvs[local_region_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[local_region_def, FLOOKUP_UPDATE] >> strip_tac >>
  qpat_x_assum `!n b sz. local_region cenv _ _ _ _ _ ==> _` irule >>
  simp[local_region_def] >> metis_tac[]
QED

Theorem mat_stack_frame[local]:
  !st mid s t sz a.
    fresh_vars_wrt st s /\ mid.cs_next_var = st.cs_next_var + 1 /\
    t = mstore s.vs_alloca_next a
          (update_var (STRING #"%" (toString st.cs_next_var))
            (n2w s.vs_alloca_next)
            (s with <| vs_allocas := s.vs_allocas |+
                         (st.cs_next_id, (s.vs_alloca_next, sz));
                       vs_alloca_next := s.vs_alloca_next + sz |>)) ==>
    mat_frame st s t /\ fresh_vars_wrt mid t
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (simp[mat_frame_def, mstore_def, update_var_def,
           venom_state_component_equality] >>
      rpt strip_tac >> simp[lookup_var_def, FLOOKUP_UPDATE] >>
      fs[not_fresh_at_def]) >>
  gvs[fresh_vars_wrt_def, mstore_def, update_var_def] >>
  rpt strip_tac >> simp[] >>
  `n <> st.cs_next_var` by decide_tac >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Theorem mat_inv_stack_bind[local]:
  !func cenv env st s mid t f0 mr name x0 sz a.
    mat_inv func cenv env st s f0 mr /\
    x0 = STRING #"%" (toString st.cs_next_var) /\
    mid.cs_next_var = st.cs_next_var + 1 /\
    mid.cs_next_id = st.cs_next_id + 2 /\
    s.vs_alloca_next < dimword (:256) /\
    t = mstore s.vs_alloca_next a
          (update_var x0 (n2w s.vs_alloca_next)
            (s with <| vs_allocas := s.vs_allocas |+
                         (st.cs_next_id, (s.vs_alloca_next, sz));
                       vs_alloca_next := s.vs_alloca_next + sz |>)) /\
    local_ptrs_rel func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var x0) sz)))
      [env] t /\ alloca_inv t /\
    (!inst n base size.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\
       FLOOKUP t.vs_allocas inst.inst_id = SOME (base, size) ==> size = w2n n) /\
    not_local_ptr cenv [env] x0 ==>
    mat_inv func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var x0) sz)))
      env mid t f0 mr /\
    mat_frame st s t /\ t.vs_alloca_next = s.vs_alloca_next + sz
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `mat_inv _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  `mat_frame st s t /\ fresh_vars_wrt mid t` by
    (irule mat_stack_frame >> simp[] >> qexistsl_tac [`a`, `sz`] >> gvs[]) >>
  reverse conj_tac
  >- gvs[mstore_def, update_var_def] >>
  simp[mat_inv_def, IgnAsm `t = _`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> gvs[mstore_def, update_var_def] >>
      Cases_on `aid = st.cs_next_id` >> gvs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[mstore_def, update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `aid = st.cs_next_id` >> gvs[] >> metis_tac[]) >>
  conj_tac >- gvs[mstore_def, update_var_def] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `local_region _ _ _ _ _ _`) local_region_partition_bind >>
  disch_then (qspecl_then [`s`, `f0`, `mr`] mp_tac) >>
  (impl_tac
   >- (simp[] >> conj_tac
       >- (rpt strip_tac >>
           gvs[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
       conj_tac
       >- (rpt strip_tac >> gvs[not_local_ptr_def] >>
           Cases_on `lookup_scopes n' [env]` >> gvs[] >> metis_tac[]) >>
       rpt strip_tac >>
       gvs[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           wordsTheory.w2n_n2w])) >> simp[]
QED

Theorem mat_pending_stack_bind[local]:
  !caps cenv env st s mid t f0 mr name x0 sz a.
    mat_pending cenv env st s f0 mr caps /\ ~MEM name (MAP FST caps) /\
    mat_frame st s t /\ mid.cs_next_var = st.cs_next_var + 1 /\
    f0 <= s.vs_alloca_next /\
    t = mstore s.vs_alloca_next a
          (update_var x0 (n2w s.vs_alloca_next)
            (s with <| vs_allocas := s.vs_allocas |+
                         (st.cs_next_id, (s.vs_alloca_next, sz));
                       vs_alloca_next := s.vs_alloca_next + sz |>)) ==>
    mat_pending (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var x0) sz)))
      env mid t f0 mr caps
Proof
  rpt gen_tac >> strip_tac >> irule mat_pending_bind >>
  simp[] >> qexistsl_tac [`s`, `st`] >> simp[] >> conj_tac
  >- simp[not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> irule pending_arg_mstore >>
  simp[update_var_def] >> qexistsl_tac [`f0`, `sz'`] >> simp[]
QED

Theorem materialize_stack_split[local]:
  !cenv name off sz p caps st cenv' st'.
    FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
    materialize_internal_params cenv ((name,T,Var p)::caps) st = (cenv',st') ==>
    ?mid code.
      mid.cs_next_var = st.cs_next_var + 1 /\
      mid.cs_next_id = st.cs_next_id + 2 /\
      mid.cs_blocks = st.cs_blocks /\ mid.cs_current_bb = st.cs_current_bb /\
      code = [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
                [STRING #"%" (toString st.cs_next_var)];
              mk_inst (st.cs_next_id + 1) MSTORE
                [Var (STRING #"%" (toString st.cs_next_var)); Var p] []] /\
      mid.cs_current_insts = st.cs_current_insts ++ code /\
      materialize_internal_params
        (cenv with ce_vars updated_by
          (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
        caps mid = (cenv',st') /\
      DROP (LENGTH st.cs_current_insts) st'.cs_current_insts =
        code ++ DROP (LENGTH mid.cs_current_insts) st'.cs_current_insts
Proof
  rpt gen_tac >>
  simp[materialize_internal_params_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >>
  qpat_x_assum `FLOOKUP _ _ = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  fs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce caps mid` >>
  qexists_tac `mid` >> simp[Abbr `mid`, GSYM APPEND_ASSOC] >>
  drule materialize_internal_params_shape >> strip_tac >> gvs[] >>
  simp[DROP_APPEND, GSYM APPEND_ASSOC, DROP_LENGTH_TOO_LONG] >>
  `LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 2) = 0` by decide_tac >>
  simp[]
QED

Theorem mat_stack_head_run[local]:
  !func cenv env st s mid f0 mr name off sz p caps.
    mat_inv func cenv env st s f0 mr /\
    mat_pending cenv env st s f0 mr ((name,T,Var p)::caps) /\
    ~MEM name (MAP FST caps) /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
    mid.cs_next_var = st.cs_next_var + 1 /\ mid.cs_next_id = st.cs_next_id + 2 /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
    fn_inst_ids_distinct func /\ s.vs_alloca_next + sz < dimword (:256) ==>
    ?t. run_inst_seq
          [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
             [STRING #"%" (toString st.cs_next_var)];
           mk_inst (st.cs_next_id + 1) MSTORE
             [Var (STRING #"%" (toString st.cs_next_var)); Var p] []] s = OK t /\
        mat_inv func
          (cenv with ce_vars updated_by
            (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
          env mid t f0 mr /\
        mat_pending
          (cenv with ce_vars updated_by
            (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
          env mid t f0 mr caps /\
        mat_frame st s t /\ t.vs_alloca_next = s.vs_alloca_next + sz
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `mat_pending _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_pending_def, EVERY_DEF]) >> gvs[] >>
  `mat_pending cenv env st s f0 mr caps` by simp[mat_pending_def] >>
  qpat_assum `mat_inv _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] materialize_stack_step) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK s1` >>
  qpat_x_assum `EVERY _ caps` kall_tac >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `mat_inv func
      (cenv with ce_vars updated_by
        (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
      env mid s1 f0 mr /\ mat_frame st s s1 /\
      s1.vs_alloca_next = s.vs_alloca_next + sz` by
    (irule mat_inv_stack_bind >> simp[] >> conj_tac
     >- (first_assum ACCEPT_TAC) >>
     qexists_tac `a` >> simp[Abbr `s1`]) >>
  qexists_tac `s1` >> simp[] >> irule mat_pending_stack_bind >>
  simp[] >> qexists_tac `a` >> qexistsl_tac [`s`, `st`] >> simp[Abbr `s1`]
QED

Theorem materialize_run_compact:
  !caps cenv st cenv' st' func env s f0 mr.
    materialize_internal_params cenv caps st = (cenv',st') /\
    (!i. MEM i (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) ==>
         MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func /\ ALL_DISTINCT (MAP FST caps) /\
    mat_pending cenv env st s f0 mr caps /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) /\
    mat_inv func cenv env st s f0 mr /\
    s.vs_alloca_next + internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)
      < dimword (:256) ==>
    ?t. run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s = OK t /\
        mat_inv func cenv' env st' t f0 mr /\ mat_frame st s t /\
        t.vs_alloca_next = s.vs_alloca_next +
          internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)
Proof
  Induct
  >- (simp[materialize_internal_params_def, comp_return_def,
           internal_stack_size_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[run_inst_seq_def, mat_frame_refl]) >>
  PairCases >> rpt gen_tac >> strip_tac >>
  qpat_assum `mat_pending _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [mat_pending_def, EVERY_DEF]) >>
  simp[] >> strip_tac >>
  `mat_pending cenv env st s f0 mr caps` by simp[mat_pending_def] >>
  qpat_x_assum `EVERY _ caps` kall_tac >>
  Cases_on `h1`
  >- suspend "stack" >>
  suspend "memory"
QED

Resume materialize_run_compact[memory]:
  gvs[Once materialize_internal_params_def, internal_stack_size_def] >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce caps st` >>
  `internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) =
   internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)` by
    (simp[Abbr `ce`] >> irule mat_tail_stack_size >> simp[]) >>
  qpat_assum `internal_stack_size ce _ = _`
    (fn th => rewrite_tac[GSYM th]) >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (first_assum ACCEPT_TAC) >> conj_tac
  >- (simp[Abbr `ce`] >> irule mat_inv_memory_bind >>
      simp[] >> first_assum ACCEPT_TAC) >>
  simp[Abbr `ce`] >> irule mat_pending_bind >>
  simp[] >> qexistsl_tac [`s`, `st`] >> simp[mat_frame_refl]
QED
Resume materialize_run_compact[stack]:
  gvs[] >>
  drule_all materialize_stack_split >> strip_tac >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce caps mid` >>
  `~MEM h0 (MAP FST caps)` by gvs[] >>
  `s.vs_alloca_next + sz < dimword (:256)` by
    (gvs[internal_stack_size_def]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (qpat_x_assum `!i. MEM i _ ==> _` irule >> simp[]) >>
  drule_all mat_stack_head_run >> strip_tac >>
  `internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) =
   internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)` by
    (simp[Abbr `ce`] >> irule mat_tail_stack_size >> simp[]) >>
  `mat_inv func ce env mid t f0 mr /\
   mat_pending ce env mid t f0 mr caps` by simp[Abbr `ce`] >>
  `t.vs_alloca_next + internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
     < dimword (:256)` by gvs[internal_stack_size_def] >>
  `!i. MEM i (DROP (LENGTH mid.cs_current_insts) st'.cs_current_insts) ==>
       MEM i (fn_insts func)` by
    (rpt strip_tac >> qpat_x_assum `!i. MEM i _ ==> _` irule >> gvs[]) >>
  qpat_x_assum `!cenv st cenv' st' func env s f0 mr. _` drule_all >> strip_tac >>
  qexists_tac `t'` >> conj_tac
  >- (qpat_x_assum `DROP _ _ = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `run_inst_seq [_;_] s = OK t`
        (mp_then Any mp_tac run_inst_seq_append) >> disch_then (qspec_then
        `DROP (LENGTH mid.cs_current_insts) st'.cs_current_insts` mp_tac) >> simp[]) >>
  simp[internal_stack_size_def] >> irule mat_frame_trans >>
  qexistsl_tac [`mid`, `t`] >> simp[not_fresh_at_def]
QED
Finalise materialize_run_compact[local]

Theorem internal_args_local_memloc[local]:
  !cenv params env idx args frontier mem name entry.
    internal_args_rel cenv params env idx args frontier mem /\
    lookup_scopes name [env] = SOME entry ==>
    ?off sz. FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz)
Proof
  rpt gen_tac >> simp[internal_args_rel_def, lookup_scopes_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `name IN FDOM env` by fs[FLOOKUP_DEF] >>
  `MEM name (MAP FST params)` by gvs[] >>
  gvs[MEM_EL, EL_MAP] >>
  qpat_x_assum `!i. i < LENGTH params ==> _` drule >>
  metis_tac[]
QED

Theorem internal_args_initial_locals[local]:
  !cenv params env idx args frontier mem func s.
    internal_args_rel cenv params env idx args frontier mem ==>
    local_ptrs_rel func cenv [env] s /\
    (!name b sz. ~local_region cenv [env] s name b sz)
Proof
  rpt strip_tac >> fs[local_ptrs_rel_def, local_region_def] >>
  rpt strip_tac >> fs[local_region_def] >>
  drule_all internal_args_local_memloc >>
  strip_tac >> gvs[]
QED

(* The indexed caller-buffer specification has a name-indexed interface. *)
Theorem internal_args_regions[local]:
  !cenv params env base args frontier mem.
    internal_args_rel cenv params env base args frontier mem ==>
    ?mr.
      (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
         FLOOKUP cenv.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
         mr (FST (EL i params)) = SOME (w2n (EL (base + i) args), sz)) /\
      (!n1 n2 b1 sz1 b2 sz2.
         n1 <> n2 /\ mr n1 = SOME (b1, sz1) /\ mr n2 = SOME (b2, sz2) ==>
         regions_disjoint b1 sz1 b2 sz2)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `internal_args_rel cenv params env idx args frontier mem` >>
  `ALL_DISTINCT (MAP FST params)` by fs[internal_args_rel_def] >>
  `!i j. i < LENGTH params /\ j < LENGTH params /\
     FST (EL i params) = FST (EL j params) ==> i = j` by
    (fs[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> metis_tac[]) >>
  `?mr. !n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL (idx + i) args)` by
    (simp[GSYM SKOLEM_THM] >> gen_tac >>
     Cases_on `?i off sz. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz)`
     >- (pop_assum strip_assume_tac >>
         qexists_tac `SOME (w2n (EL (idx + i) args),sz)` >>
         rpt gen_tac >> eq_tac
         >- (strip_tac >> gvs[] >> metis_tac[]) >>
         strip_tac >> `i = i'` by metis_tac[] >> gvs[]) >>
     qexists_tac `NONE` >> simp[] >> metis_tac[]) >>
  qexists_tac `mr` >> conj_tac
  >- (rpt strip_tac >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[] >> fs[internal_args_rel_def] >>
  `i <> i'` by (strip_tac >> gvs[]) >>
  qpat_x_assum `!i j offi szi offj szj. _` drule_all >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem internal_args_materialization_pre[local]:
  !cenv params env idx args frontier mem caps st s func.
    internal_args_rel cenv params env idx args frontier mem /\
    LENGTH caps = LENGTH params /\
    (!i. i < LENGTH params ==>
      FST (EL i caps) = FST (EL i params) /\
      FST (SND (EL i caps)) = SND (EL i params) /\
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at st p /\
          lookup_var p s = SOME (EL (idx + i) args)) /\
    s.vs_memory = mem /\ s.vs_alloca_next = frontier /\
    s.vs_allocas = FEMPTY /\ fresh_vars_wrt st s ==>
    ?mr. mat_pending cenv env st s frontier mr caps /\
         mat_inv func cenv env st s frontier mr /\
         (!n1 n2 b1 sz1 b2 sz2.
           n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
           regions_disjoint b1 sz1 b2 sz2)
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_args_regions >> strip_tac >>
  drule internal_args_initial_locals >>
  disch_then (qspecl_then [`func`, `s`] strip_assume_tac) >>
  qexists_tac `mr` >> conj_tac
  >- (simp[mat_pending_def, EVERY_EL] >> rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH params ==> _` drule >>
      strip_tac >>
      fs[internal_args_rel_def] >>
      qpat_x_assum `!i. i < LENGTH params ==> ?off sz entry. _` drule >>
      strip_tac >>
      qexistsl_tac [`off`, `sz`, `entry`] >>
      Cases_on `SND (EL n params)` >> gvs[arithmeticTheory.ADD_COMM] >>
      qpat_x_assum `!i off sz. _` drule_all >>
      simp[arithmeticTheory.ADD_COMM]) >>
  simp[mat_inv_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def] >> metis_tac[]
QED

(* Capturing the return-PC after the ordinary PARAMs preserves the frame. *)
Theorem run_inst_seq_params_retpc[local]:
  !n id base nv s.
    base + n <= LENGTH s.vs_params /\ LENGTH s.vs_params < dimword (:256) /\
    (!k. nv <= k ==> STRING #"%" (toString k) NOTIN FDOM s.vs_vars) ==>
    ?t.
      run_inst_seq
        (GENLIST (\i. mk_inst (id + i) PARAM [Lit (n2w (base + i))]
                        [STRING #"%" (toString (nv + i))]) n ++
         [mk_inst (id + n) RETPC_PARAM [Lit (n2w (base + n))]
            [STRING #"%" (toString (nv + n))]]) s = OK t /\
      t = s with vs_vars := t.vs_vars /\
      (!k. nv + n + 1 <= k ==> STRING #"%" (toString k) NOTIN FDOM t.vs_vars) /\
      lookup_var (STRING #"%" (toString (nv + n))) t =
        SOME s.vs_return_pc_token /\
      (!i. i < n ==> lookup_var (STRING #"%" (toString (nv + i))) t =
                     SOME (EL (base + i) s.vs_params)) /\
      (!p. (!k. nv <= k ==> p <> STRING #"%" (toString k)) ==>
           lookup_var p t = lookup_var p s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_inst_seq_params >>
  disch_then (qspecl_then [`id`, `nv`] strip_assume_tac) >>
  fs[arithmeticTheory.ADD_COMM] >>
  qexists_tac `update_var (STRING #"%" (toString (nv + n)))
                        s.vs_return_pc_token s'` >>
  conj_tac
  >- (drule run_inst_seq_append >>
      disch_then (fn th => rewrite_tac[th]) >>
      simp[run_inst_seq_def] >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[mk_inst_def] >>
      qpat_x_assum `s' = _` SUBST1_TAC >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `s' = _` SUBST1_TAC >> simp[update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `lookup_var (STRING #"%" (toString k)) s' =
       lookup_var (STRING #"%" (toString k)) s` by
        (first_x_assum irule >> simp[ASCIInumbersTheory.toString_inj]) >>
      `STRING #"%" (toString k) NOTIN FDOM s.vs_vars` by
        (qpat_x_assum `!k. nv <= k ==> _` irule >> decide_tac) >>
      `lookup_var (STRING #"%" (toString k)) s = NONE` by
        simp[lookup_var_def, FLOOKUP_DEF] >>
      fs[lookup_var_def, FLOOKUP_DEF] >>
      gvs[update_var_def, ASCIInumbersTheory.toString_inj]) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_inj] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < n ==> _` drule >>
      simp[lookup_var_def]) >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString (nv + n))` by simp[] >>
  simp[] >>
  qpat_x_assum `!x. _ ==> lookup_var x s' = _` (qspec_then `p` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k. nv <= k ==> p <> _`
        (qspec_then `i + nv` mp_tac) >> simp[]) >>
  simp[lookup_var_def]
QED

Theorem capture_internal_params_run[local]:
  !params idx st caps next stp rpc stc s.
    compile_internal_param_decls params idx st = ((caps, next), stp) /\
    emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc, stc) /\
    idx + LENGTH params <= LENGTH s.vs_params /\
    LENGTH s.vs_params < dimword (:256) /\ fresh_vars_wrt st s ==>
    ?t x.
      run_inst_seq (emitted_insts st stc) s = OK t /\
      stc.cs_current_insts = st.cs_current_insts ++ emitted_insts st stc /\
      st.cs_next_var <= stc.cs_next_var /\
      t = s with vs_vars := t.vs_vars /\
      fresh_vars_wrt stc t /\
      rpc = Var x /\ not_fresh_at stc x /\
      lookup_var x t = SOME s.vs_return_pc_token /\
      (!i. i < LENGTH params ==>
        ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at stc p /\
            lookup_var p t = SOME (EL (idx + i) s.vs_params)) /\
      (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s)
Proof
  rpt gen_tac >> strip_tac >>
  `!k. st.cs_next_var <= k ==>
       STRING #"%" (toString k) NOTIN FDOM s.vs_vars` by
    fs[fresh_vars_wrt_def] >>
  drule_all run_inst_seq_params_retpc >>
  disch_then (qspec_then `st.cs_next_id` strip_assume_tac) >>
  drule compile_internal_param_decls_shape >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  qexists_tac `t` >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND,
       fresh_vars_wrt_def, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem capture_internal_return_buffer_run[local]:
  !has_rb st rb st' s.
    (if has_rb then
       do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st = (rb, st') /\
    fresh_vars_wrt st s /\ (has_rb ==> s.vs_params <> []) ==>
    ?t.
      run_inst_seq (emitted_insts st st') s = OK t /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      t = s with vs_vars := t.vs_vars /\ fresh_vars_wrt st' t /\
      (has_rb ==> ?p. rb = SOME (Var p) /\ not_fresh_at st' p /\
                     lookup_var p t = SOME (HD s.vs_params)) /\
      (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s)
Proof
  reverse Cases >> rpt gen_tac >>
  simp[comp_bind_def, comp_return_def, emit_op_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]
  >- (qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var))
                         (HD s.vs_params) s` >>
  conj_tac
  >- (simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def] >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      Cases_on `s.vs_params` >> gvs[mk_inst_def]) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND,
       update_var_def, fresh_vars_wrt_def, not_fresh_at_def,
       lookup_var_def, FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
  fs[fresh_vars_wrt_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* ===== The callee's entry ===== *)
Theorem internal_capture_materialization_entry[local]:
  !has_rb st0 rb stb params caps next stp rpc stc cenv cenv1
   env args caller func s0.
    (if has_rb then
       do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st0 = (rb, stb) /\
    compile_internal_param_decls params (if has_rb then 1 else 0) stb =
      ((caps,next),stp) /\
    emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,stc) /\
    setup_callee func args caller = SOME s0 /\
    internal_args_rel cenv params env (if has_rb then 1 else 0) args
      caller.vs_alloca_next caller.vs_memory /\
    cenv1.ce_vars = cenv.ce_vars ==>
    ?t mr x.
      run_inst_seq (emitted_insts st0 stc) s0 = OK t /\
      t = s0 with vs_vars := t.vs_vars /\
      mat_frame st0 s0 t /\
      fresh_vars_wrt stc t /\
      rpc = Var x /\ not_fresh_at stc x /\
      lookup_var x t = SOME s0.vs_return_pc_token /\
      (has_rb ==> ?p. rb = SOME (Var p) /\ not_fresh_at stc p /\
                     lookup_var p t = SOME (HD args)) /\
      mat_pending cenv1 env stc t caller.vs_alloca_next mr caps /\
      mat_inv func cenv1 env stc t caller.vs_alloca_next mr /\
      (!n1 n2 b1 sz1 b2 sz2.
        n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
        regions_disjoint b1 sz1 b2 sz2)
Proof
  rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt st0 s0 /\ s0.vs_params = args /\
   s0.vs_memory = caller.vs_memory /\
   s0.vs_alloca_next = caller.vs_alloca_next /\ s0.vs_allocas = FEMPTY` by
    (fs[setup_callee_def, AllCaseEqs()] >>
     gvs[fresh_vars_wrt_def]) >>
  `LENGTH args < dimword (:256) /\
   (if has_rb then 1 else 0) + LENGTH params <= LENGTH args` by
    fs[internal_args_rel_def] >>
  `has_rb ==> s0.vs_params <> []` by
    (strip_tac >> Cases_on `args` >> gvs[]) >>
  drule_all capture_internal_return_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 stb) s0 = OK sb` >>
  `sb.vs_params = args` by (qpat_x_assum `sb = _` SUBST1_TAC >> simp[]) >>
  `(if has_rb then 1 else 0) + LENGTH params <= LENGTH sb.vs_params /\
   LENGTH sb.vs_params < dimword (:256)` by fs[] >>
  drule_all capture_internal_params_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts stb stc) sb = OK sc` >>
  `sc = s0 with vs_vars := sc.vs_vars` by
    (qpat_x_assum `sc = _` SUBST1_TAC >>
     qpat_x_assum `sb = _` SUBST1_TAC >> simp[]) >>
  `LENGTH caps = LENGTH params /\
   (!i. i < LENGTH params ==> FST (EL i caps) = FST (EL i params) /\
                             FST (SND (EL i caps)) = SND (EL i params))` by
    (drule compile_internal_param_decls_shape >> simp[] >> metis_tac[]) >>
  `internal_args_rel cenv1 params env (if has_rb then 1 else 0) args
       caller.vs_alloca_next caller.vs_memory` by
    fs[internal_args_rel_def] >>
  `sc.vs_memory = caller.vs_memory /\
   sc.vs_alloca_next = caller.vs_alloca_next /\ sc.vs_allocas = FEMPTY` by
    (qpat_x_assum `sc = s0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `?mr. mat_pending cenv1 env stc sc caller.vs_alloca_next mr caps /\
        mat_inv func cenv1 env stc sc caller.vs_alloca_next mr /\
        (!n1 n2 b1 sz1 b2 sz2.
          n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
          regions_disjoint b1 sz1 b2 sz2)` by
    (irule internal_args_materialization_pre >> simp[] >>
     qexistsl_tac [`args`, `if has_rb then 1 else 0`, `params`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `st0.cs_next_var <= stb.cs_next_var` by
    (qpat_x_assum `(if has_rb then _ else _) st0 = _` mp_tac >>
     Cases_on `has_rb` >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  `mat_frame st0 s0 sc` by
    (simp[mat_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at stb x'` by fs[not_fresh_at_def] >> metis_tac[]) >>
     qpat_x_assum `sc = s0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`sc`, `mr`, `x`] >>
  conj_tac
  >- (drule_all run_inst_seq_chain >> simp[]) >>
  `sb.vs_return_pc_token = s0.vs_return_pc_token` by
    (qpat_x_assum `sb = _` SUBST1_TAC >> simp[]) >>
  fs[] >> reverse conj_tac >- (first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `has_rb ==> ?p. _` drule >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  fs[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. stb.cs_next_var <= n ==> _` irule >> decide_tac
QED


Theorem scratch_alloca_run[local]:
  !func cenv scopes st s n.
    local_ptrs_rel func cenv scopes s /\ alloca_inv s /\
    fresh_vars_wrt st s /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit n]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
    fn_inst_ids_distinct func ==>
    ?t.
      run_inst_seq [mk_inst st.cs_next_id ALLOCA [Lit n]
           [STRING #"%" (toString st.cs_next_var)]] s = OK t /\
      local_ptrs_rel func cenv scopes t /\ alloca_inv t /\
      (!inst w base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\
         FLOOKUP t.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
      fresh_vars_wrt (st with cs_next_var := st.cs_next_var + 1) t /\
      (!aid. aid IN FDOM t.vs_allocas ==> aid < st.cs_next_id + 1) /\
      mat_frame st s t /\ t.vs_memory = s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `id = st.cs_next_id` >>
  `FLOOKUP s.vs_allocas id = NONE` by
    (simp[FLOOKUP_DEF, Abbr `id`] >> strip_tac >>
     qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> simp[]) >>
  `not_local_ptr cenv scopes x` by
    (simp[Abbr `x`] >> irule local_ptrs_rel_fresh_not_local_ptr >>
     qexistsl_tac [`func`, `s`, `st`] >> simp[]) >>
  qabbrev_tac `t = update_var x (n2w s.vs_alloca_next)
    (s with <| vs_allocas := s.vs_allocas |+
                  (id, (s.vs_alloca_next, w2n n));
               vs_alloca_next := s.vs_alloca_next + w2n n |>)` >>
  `exec_alloca (mk_inst id ALLOCA [Lit n] [x]) s n = OK t` by
    simp[exec_alloca_def, mk_inst_def, Abbr `t`] >>
  `step_inst_base (mk_inst id ALLOCA [Lit n] [x]) s = OK t` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def] >>
     fs[mk_inst_def]) >>
  qexists_tac `t` >> rpt conj_tac
  >- simp[run_inst_seq_def, Abbr `id`, Abbr `x`]
  >- (drule_at (Pos hd) local_ptrs_rel_exec_alloca >>
      disch_then irule >> simp[mk_inst_def])
  >- (drule_all alloca_inv_exec_alloca >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_id = id`
      >- (`inst = mk_inst id ALLOCA [Lit n] [x]` by
            (irule fn_inst_ids_distinct_inj >> simp[mk_inst_def] >>
             qexists_tac `func` >> fs[mk_inst_def, Abbr `id`, Abbr `x`]) >>
          gvs[mk_inst_def, Abbr `t`, update_var_def, FLOOKUP_UPDATE]) >>
      first_x_assum irule >>
      gvs[Abbr `t`, update_var_def, FLOOKUP_UPDATE] >> metis_tac[])
  >- (gvs[fresh_vars_wrt_def, Abbr `t`, update_var_def, Abbr `x`] >>
      rpt strip_tac >> simp[] >>
      `n' <> st.cs_next_var` by decide_tac >>
      simp[] >> first_x_assum irule >> decide_tac)
  >- (simp[Abbr `t`, update_var_def, Abbr `id`] >> rpt strip_tac >>
      gvs[] >> qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> decide_tac)
  >- (simp[mat_frame_def, Abbr `t`, update_var_def,
           venom_state_component_equality] >>
      rpt strip_tac >> simp[lookup_var_def, FLOOKUP_UPDATE] >>
      fs[not_fresh_at_def, Abbr `x`]) >>
  simp[Abbr `t`, update_var_def]
QED

Theorem scratch_buffer_run[local]:
  !func cenv scopes st s n buf st'.
    compile_alloc_buffer n st = (buf, st') /\
    local_ptrs_rel func cenv scopes s /\ alloca_inv s /\
    fresh_vars_wrt st s /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
    (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func ==>
    ?t.
      run_inst_seq (emitted_insts st st') s = OK t /\
      local_ptrs_rel func cenv scopes t /\ alloca_inv t /\
      (!inst w base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\
         FLOOKUP t.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
      fresh_vars_wrt st' t /\
      (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id) /\
      mat_frame st s t /\ t.vs_memory = s.vs_memory /\
      st.cs_next_var <= st'.cs_next_var /\
      st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
      isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `st'.cs_next_var = st.cs_next_var + 1 /\
   st'.cs_next_id = st.cs_next_id + 1` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
         emit_def]) >>
  `emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >> simp[]) >>
  drule_all scratch_alloca_run >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  gvs[fresh_vars_wrt_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Theorem internal_scratch_run[local]:
  !func cenv scopes st s ret_type alloc_cenv st'.
    (case ret_type of
       SOME ty => if alloc_cenv.ce_returns_count > 0 then
                    do compile_alloc_buffer (type_memory_bytes alloc_cenv ty);
                       return () od
                  else return ()
     | NONE => return ()) st = ((), st') /\
    local_ptrs_rel func cenv scopes s /\ alloca_inv s /\
    fresh_vars_wrt st s /\
    (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
    (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func ==>
    ?t.
      run_inst_seq (emitted_insts st st') s = OK t /\
      local_ptrs_rel func cenv scopes t /\ alloca_inv t /\
      (!inst w base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\
         FLOOKUP t.vs_allocas inst.inst_id = SOME (base, sz) ==> sz = w2n w) /\
      fresh_vars_wrt st' t /\
      (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id) /\
      mat_frame st s t /\ t.vs_memory = s.vs_memory /\
      st.cs_next_var <= st'.cs_next_var /\
      st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
      isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rpt gen_tac >> Cases_on `ret_type`
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexists_tac `s` >>
      simp[emitted_insts_def, DROP_LENGTH_NIL, run_inst_seq_def, mat_frame_refl] >>
      first_assum ACCEPT_TAC) >>
  rename1 `SOME ty` >> Cases_on `alloc_cenv.ce_returns_count > 0`
  >- (simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_all scratch_buffer_run >> simp[]) >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qexists_tac `s` >>
  simp[emitted_insts_def, DROP_LENGTH_NIL, run_inst_seq_def, mat_frame_refl] >>
      first_assum ACCEPT_TAC
QED

Theorem materialize_nonptr_binding[local]:
  !caps cenv st cenv' st'.
    materialize_internal_params cenv caps st = (cenv', st') ==>
    !name loc. FLOOKUP cenv'.ce_vars name = SOME loc /\
               (!p sz. loc <> PtrVar p sz) ==>
               FLOOKUP cenv.ce_vars name = SOME loc
Proof
  Induct
  >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  Cases_on `h1`
  >- (Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >> simp[] >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_return_def,
           comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
      rpt strip_tac >> first_x_assum drule >>
      disch_then drule_all >> simp[FLOOKUP_UPDATE] >>
      Cases_on `name = h0` >> gvs[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> disch_then drule_all >>
  simp[FLOOKUP_UPDATE] >> Cases_on `name = h0` >> gvs[] >> metis_tac[]
QED

Theorem materialize_global_binding[local]:
  !caps cenv st cenv' st'.
    materialize_internal_params cenv caps st = (cenv', st') /\
    EVERY (\c. ?off sz. FLOOKUP cenv.ce_vars (FST c) = SOME (MemLoc off sz)) caps ==>
    !name loc. (!p sz. loc <> PtrVar p sz) /\
               (!off sz. loc <> MemLoc off sz) ==>
      (FLOOKUP cenv'.ce_vars name = SOME loc <=>
       FLOOKUP cenv.ce_vars name = SOME loc)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> eq_tac
  >- (strip_tac >> drule_all materialize_nonptr_binding >> simp[]) >>
  strip_tac >>
  `~MEM name (MAP FST caps)` by
    (fs[MEM_MAP, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule materialize_internal_params_shape >> strip_tac >> simp[]
QED

Theorem internal_body_state_rel[local]:
  !f func cenv cx vs caller cenv1 cenv2 rb rpc caps st st' env s0 s args st0.
    state_rel f cenv cx (vs with scopes := []) caller /\
    cenv1 = cenv with <| ce_return_buf := rb; ce_return_pc := rpc |> /\
    materialize_internal_params cenv1 caps st = (cenv2, st') /\
    EVERY (\c. ?off sz. FLOOKUP cenv1.ce_vars (FST c) = SOME (MemLoc off sz)) caps /\
    setup_callee func args caller = SOME s0 /\ mat_frame st0 s0 s /\
    local_ptrs_rel func cenv2 [env] s ==>
    state_rel func (cenv2 with ce_alloca_locals := T) cx (vs with scopes := [env]) s
Proof
  rpt gen_tac >> strip_tac >>
  drule materialize_global_binding >> simp[] >> disch_then assume_tac >>
  drule materialize_internal_params_shape >> strip_tac >>
  `s.vs_accounts = caller.vs_accounts /\ s.vs_transient = caller.vs_transient /\
   s.vs_call_ctx = caller.vs_call_ctx /\ s.vs_tx_ctx = caller.vs_tx_ctx /\
   s.vs_block_ctx = caller.vs_block_ctx /\ s.vs_logs = caller.vs_logs /\
   s.vs_outcomes = caller.vs_outcomes /\ s.vs_requests = caller.vs_requests /\
   s.vs_pending_deletions = caller.vs_pending_deletions /\
   s.vs_immutables = caller.vs_immutables /\ s.vs_data_section = caller.vs_data_section` by
    (fs[mat_frame_def, setup_callee_def, AllCaseEqs()] >>
     qpat_x_assum `s = _` SUBST1_TAC >> gvs[]) >>
  `local_ptrs_rel func (cenv2 with ce_alloca_locals := T) [env] s` by
    (fs[local_ptrs_rel_def, local_region_def, local_backed_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `state_rel _ _ _ _ _` mp_tac >>
  simp[state_rel_def] >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- fs[storage_rel_def, contract_storage_def]
  >- (fs[storage_vars_rel_def] >> metis_tac[])
  >- fs[transient_rel_def, contract_transient_def]
  >- (fs[transient_vars_rel_def] >> metis_tac[])
  >- fs[accounts_rel_def]
  >- (fs[immutables_rel_def] >> metis_tac[])
  >- fs[logs_rel_def, log_entry_equiv_def, LIST_REL_EL_EQN] >>
  simp[]
QED

Theorem compile_internal_prologue_shape[local]:
  !cenv params has_rb ret_type st cenv' rpc st'.
    compile_internal_prologue cenv params has_rb ret_type st = ((cenv',rpc),st') ==>
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id /\
    ?new. st'.cs_current_insts = st.cs_current_insts ++ new /\ new <> [] /\
          EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) new
Proof
  rpt gen_tac >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  dxrule compile_internal_param_decls_shape >> strip_tac >>
  dxrule materialize_internal_params_shape >> strip_tac >>
  Cases_on `has_rb` >> Cases_on `ret_type` >> Cases_on `cenv.ce_returns_count > 0` >>
  gvs[emit_op_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, compile_alloc_buffer_def] >>
  simp[is_terminator_def, EVERY_GENLIST] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i new ==> _` (qspec_then `i` mp_tac) >>
  simp[is_terminator_def] >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem internal_param_decls_projection[local]:
  !params idx st caps next st'.
    compile_internal_param_decls params idx st = ((caps,next),st') ==>
    MAP (\c. (FST c,FST (SND c))) caps = params /\
    MAP FST caps = MAP FST params /\
    st.cs_next_var <= st'.cs_next_var /\
    st.cs_next_id <= st'.cs_next_id /\
    st'.cs_blocks = st.cs_blocks /\
    st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_internal_param_decls_shape >> simp[] >> strip_tac >>
  `MAP (\c. (FST c,FST (SND c))) caps = params` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  simp[] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem internal_stack_size_vars[local]:
  !params cenv ce.
    ce.ce_vars = cenv.ce_vars ==>
    internal_stack_size ce params = internal_stack_size cenv params
Proof
  Induct >> simp[internal_stack_size_def] >>
  PairCases >> simp[internal_stack_size_def]
QED

Theorem setup_callee_frontier[local]:
  !func args caller s0.
    setup_callee func args caller = SOME s0 ==>
    s0.vs_alloca_next = caller.vs_alloca_next /\
    ~s0.vs_halted /\ s0.vs_inst_idx = 0 /\
    s0.vs_current_bb = (HD func.fn_blocks).bb_label
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem internal_scratch_shape[local]:
  !cenv ret_type st st'.
    (case ret_type of
       SOME ty => if cenv.ce_returns_count > 0 then
                    do compile_alloc_buffer (type_memory_bytes cenv ty);
                       return () od
                  else return ()
     | NONE => return ()) st = ((),st') ==>
    st'.cs_blocks = st.cs_blocks /\
    st'.cs_current_bb = st.cs_current_bb /\
    st.cs_next_var <= st'.cs_next_var /\
    st.cs_next_id <= st'.cs_next_id /\
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rpt gen_tac >> Cases_on `ret_type` >>
  simp[comp_return_def] >>
  Cases_on `cenv.ce_returns_count > 0` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_insts >> strip_tac >> simp[] >>
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def]
QED

Theorem internal_prologue_stages[local]:
  !cenv params has_rb ret_type st0 cenv2 rpc st1.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2,rpc),st1) ==>
    ?rb stb caps next stp sc ce sm.
      (if has_rb then
         do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
       else return NONE) st0 = (rb,stb) /\
      compile_internal_param_decls params (if has_rb then 1 else 0) stb =
        ((caps,next),stp) /\
      emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,sc) /\
      ce = cenv with
        <|ce_return_buf :=
            (case (rb,cenv.ce_return_buf) of
               (SOME p,SOME (MemLoc off sz)) => SOME (PtrVar p sz)
             | _ => cenv.ce_return_buf);
          ce_return_pc := SOME (PtrVar rpc 0)|> /\
      materialize_internal_params ce caps sc = (cenv2,sm) /\
      (case ret_type of
         SOME ty => if cenv.ce_returns_count > 0 then
                      do compile_alloc_buffer (type_memory_bytes cenv ty);
                         return () od
                    else return ()
       | NONE => return ()) sm = ((),st1)
Proof
  rpt gen_tac >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem internal_prologue_stage_shapes[local]:
  !has_rb st0 rb stb params caps next stp rpc sc ce cenv2 sm cenv ret_type st1.
    (if has_rb then
       do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st0 = (rb,stb) /\
    compile_internal_param_decls params (if has_rb then 1 else 0) stb =
      ((caps,next),stp) /\
    emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,sc) /\
    materialize_internal_params ce caps sc = (cenv2,sm) /\
    (case ret_type of
       SOME ty => if cenv.ce_returns_count > 0 then
                    do compile_alloc_buffer (type_memory_bytes cenv ty);
                       return () od
                  else return ()
     | NONE => return ()) sm = ((),st1) ==>
    MAP (\c. (FST c,FST (SND c))) caps = params /\
    MAP FST caps = MAP FST params /\
    st0.cs_next_var <= sc.cs_next_var /\
    sc.cs_next_var <= sm.cs_next_var /\
    sm.cs_next_var <= st1.cs_next_var /\
    sc.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_id <= st1.cs_next_id /\
    sc.cs_blocks = st0.cs_blocks /\
    sm.cs_blocks = st0.cs_blocks /\
    st1.cs_blocks = st0.cs_blocks /\
    sc.cs_current_bb = st0.cs_current_bb /\
    sm.cs_current_bb = st0.cs_current_bb /\
    st1.cs_current_bb = st0.cs_current_bb /\
    isPREFIX st0.cs_current_insts sc.cs_current_insts /\
    isPREFIX sc.cs_current_insts sm.cs_current_insts /\
    isPREFIX sm.cs_current_insts st1.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_param_decls_projection >> strip_tac >>
  drule materialize_internal_params_shape >> strip_tac >>
  drule internal_scratch_shape >> strip_tac >>
  qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
  Cases_on `has_rb` >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  fs[IS_PREFIX_APPEND] >> gvs[] >> simp[APPEND_ASSOC]
QED

Theorem internal_prologue_segment_members[local]:
  !st0 st1 func sc sm.
    fn_has_code st0 st1 func /\
    isPREFIX sm.cs_current_insts st1.cs_current_insts ==>
    (!i. MEM i (emitted_insts sc sm) ==> MEM i (fn_insts func)) /\
    (!i. MEM i (emitted_insts sm st1) ==> MEM i (fn_insts func))
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i st1.cs_current_insts ==> MEM i (fn_insts func)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
     irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `st1.cs_current_bb`] >> simp[]) >>
  fs[IS_PREFIX_APPEND, emitted_insts_def] >> gvs[] >>
  conj_tac >> rpt strip_tac >> first_x_assum irule
  >- (simp[] >> disj1_tac >>
      qpat_x_assum `MEM i (DROP _ _)` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[MEM_DROP, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `MEM i (DROP _ _)` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[MEM_DROP, MEM_EL, EL_APPEND_EQN] >>
  metis_tac[]
QED


(* A step of an instruction of func other than an INVOKE keeps the room in
   func's frame: a fresh ALLOCA moves its size from the pending sizes to
   the frontier, and nothing else moves either. *)
Theorem step_inst_base_alloca_room[local]:
  !func inst s s'.
    step_inst_base inst s = OK s' /\ MEM inst (fn_insts func) /\
    inst.inst_opcode <> INVOKE /\ alloca_room func s ==>
    alloca_room func s'
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[]
      >~ [`FLOOKUP s.vs_allocas inst.inst_id = SOME _`]
      >- (irule alloca_room_fields >> qexists_tac `s` >>
          simp[update_var_def]) >>
      `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      irule alloca_room_fields >>
      qexists_tac `s with <| vs_allocas := s.vs_allocas |+
                               (inst.inst_id, (s.vs_alloca_next, w2n alloc_size));
                             vs_alloca_next := s.vs_alloca_next + w2n alloc_size |>` >>
      simp[update_var_def]) >>
  irule alloca_room_fields >> qexists_tac `s` >> simp[] >>
  metis_tac[step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

Theorem run_inst_seq_alloca_room[local]:
  !is func s t.
    run_inst_seq is s = OK t /\
    EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) is /\
    alloca_room func s ==>
    alloca_room func t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  rename1 `run_inst_seq is s1 = OK t` >>
  qpat_x_assum `!func s t. _` irule >> simp[] >> qexists_tac `s1` >> simp[] >>
  irule step_inst_base_alloca_room >> metis_tac[]
QED

Theorem internal_prologue_run:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1 func args caller
   s0 f cx vs env.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
    setup_callee func args caller = SOME s0 /\
    state_rel f cenv cx (vs with scopes := []) caller /\
    internal_args_rel cenv params env (if has_rb then 1 else 0) args
      caller.vs_alloca_next caller.vs_memory /\
    caller.vs_alloca_next + internal_stack_size cenv params
      < dimword (:256) ==>
    ?t.
      run_inst_seq (emitted_insts st0 st1) s0 = OK t /\
      state_rel func (cenv2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) t /\ alloca_inv t /\
      (!inst n base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit n] /\
         FLOOKUP t.vs_allocas inst.inst_id = SOME (base, sz) ==>
         sz = w2n n) /\
      fresh_vars_wrt st1 t /\ mat_frame st0 s0 t /\
      (?x. return_pc = Var x /\ not_fresh_at st1 x /\
           lookup_var x t = SOME s0.vs_return_pc_token) /\
      (has_rb ==>
       ?rb. not_fresh_at st1 rb /\ lookup_var rb t = SOME (HD args) /\
            !off sz. cenv.ce_return_buf = SOME (MemLoc off sz) ==>
                     cenv2.ce_return_buf = SOME (PtrVar (Var rb) sz))
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_prologue_stages >> strip_tac >>
  drule_all internal_prologue_stage_shapes >> strip_tac >>
  `ce.ce_vars = cenv.ce_vars` by simp[] >>
  `internal_stack_size ce params = internal_stack_size cenv params` by
    (irule internal_stack_size_vars >> simp[]) >>
  qpat_x_assum `ce = _` (mk_asm "cenv_stage") >>
  drule_all internal_capture_materialization_entry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 sc) s0 = OK t` >>
  drule_all internal_prologue_segment_members >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `ALL_DISTINCT (MAP FST caps)` by fs[internal_args_rel_def] >>
  `t.vs_alloca_next = caller.vs_alloca_next` by
    (qpat_x_assum `t = s0 with vs_vars := _` SUBST1_TAC >>
     drule setup_callee_frontier >> simp[]) >>
  `t.vs_alloca_next +
    internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by
    simp[] >>
  `!i. MEM i (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts) ==>
       MEM i (fn_insts func)` by fs[emitted_insts_def] >>
  drule_all materialize_run_compact >> strip_tac >>
  rename1 `mat_inv func cenv2 env sm u _ _` >>
  qpat_x_assum `mat_inv func cenv2 env sm u _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  drule_all internal_scratch_run >> strip_tac >>
  `mat_frame st0 s0 t'` by
    (qpat_x_assum `mat_frame st0 s0 t` mp_tac >>
     qpat_x_assum `mat_frame sc t u` mp_tac >>
     qpat_x_assum `mat_frame sm u t'` mp_tac >>
     qpat_x_assum `st0.cs_next_var <= sc.cs_next_var` mp_tac >>
     qpat_x_assum `sc.cs_next_var <= sm.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `mat_frame sc t t'` by
       (irule mat_frame_trans >> qexistsl_tac [`sm`, `u`] >>
        simp[] >> fs[not_fresh_at_def]) >>
     irule mat_frame_trans >> qexistsl_tac [`sc`, `t`] >>
     simp[] >> fs[not_fresh_at_def]) >>
  qexists_tac `t'` >>
  conj_tac >- suspend "sequence" >>
  conj_tac >- suspend "relation" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> suspend "returns"
QED

Resume internal_prologue_run[sequence]:
  qpat_x_assum `run_inst_seq (emitted_insts st0 sc) s0 = _` mp_tac >>
  qpat_x_assum `run_inst_seq (DROP _ _) t = _` mp_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sm st1) u = _` mp_tac >>
  qpat_x_assum `isPREFIX st0.cs_current_insts sc.cs_current_insts` mp_tac >>
  qpat_x_assum `isPREFIX sc.cs_current_insts sm.cs_current_insts` mp_tac >>
  qpat_x_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  `sc.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 sc` by
    (qpat_x_assum `isPREFIX st0.cs_current_insts _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[IS_PREFIX_APPEND] >>
     strip_tac >> simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `sm.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sm` by
    (qpat_x_assum `isPREFIX sc.cs_current_insts _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[IS_PREFIX_APPEND] >>
     strip_tac >> simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `st1.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm st1` by
    (qpat_x_assum `isPREFIX sm.cs_current_insts _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[IS_PREFIX_APPEND] >>
     strip_tac >> simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts sc sm) t = OK u` by fs[emitted_insts_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts sc st1) t = OK t'` by metis_tac[] >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  metis_tac[]
QED
Resume internal_prologue_run[relation]:
  `EVERY (\c. ?off sz. FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz)) caps` by
    (qpat_x_assum `internal_args_rel _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `ce.ce_vars = _` mp_tac >>
     qpat_x_assum `MAP (\c. (FST c,FST (SND c))) caps = params` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
     fs[internal_args_rel_def, EVERY_MEM, MEM_MAP, MEM_EL, EL_MAP] >>
     rpt strip_tac >> gvs[] >>
     first_x_assum drule >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `state_rel _ _ _ _ _` mp_tac >>
  qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
  qpat_x_assum `materialize_internal_params ce caps sc = _` mp_tac >>
  qpat_x_assum `EVERY _ caps` mp_tac >>
  qpat_x_assum `mat_frame st0 s0 t'` mp_tac >>
  qpat_x_assum `local_ptrs_rel func cenv2 [env] t'` mp_tac >>
  qpat_x_assum `alloca_inv t'` mp_tac >>
  qpat_x_assum `!inst w base sz. _ ==> sz = w2n w` mp_tac >>
  asm_x "cenv_stage" mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule_all internal_body_state_rel >> simp[]
QED
Resume internal_prologue_run[returns]:
  qpat_x_assum `mat_frame sc t u` mp_tac >>
  qpat_x_assum `mat_frame sm u t'` mp_tac >>
  qpat_x_assum `sc.cs_next_var <= sm.cs_next_var` mp_tac >>
  qpat_x_assum `sm.cs_next_var <= st1.cs_next_var` mp_tac >>
  qpat_x_assum `lookup_var x t = _` mp_tac >>
  qpat_x_assum `not_fresh_at sc x` mp_tac >>
  qpat_x_assum `has_rb ==> ?p. _` mp_tac >>
  qpat_x_assum `materialize_internal_params ce caps sc = _` mp_tac >>
  asm_x "cenv_stage" mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 9 strip_tac >>
  `mat_frame sc t t'` by
    (irule mat_frame_trans >> qexistsl_tac [`sm`, `u`] >>
     simp[] >> fs[not_fresh_at_def]) >>
  conj_tac
  >- (conj_tac >- fs[not_fresh_at_def] >>
      fs[mat_frame_def]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `p` >> conj_tac >- fs[not_fresh_at_def] >>
  conj_tac >- fs[mat_frame_def] >>
  drule materialize_internal_params_shape >> strip_tac >> simp[]
QED
Finalise internal_prologue_run[local]

(* Running the prologue of an internal function func, compiled in cenv from
   st0, at the head of func's entry block, to st1, from the state
   setup_callee builds for an INVOKE of func with arguments args from the
   state caller, reaches the point where the prologue leaves off (before the
   immutables reservation of a constructor callee, the nonreentrant lock
   and the body) in a state
   s1 related at the scope env the source binds the parameters in:
   - each parameter is a local held through a pointer variable: a
     stack-passed one in a region of its own ALLOCA, holding its value, a
     memory-passed one in its argument buffer;
   - the return PC and the return buffer are in variables the body's code
     does not assign;
   - every result from s1 other than an Error is one from the callee's
     entry state.
   The global part of the relation (storage, transient, immutables, logs,
   contexts) is that of the caller's state in cenv, which the hypothesis
   on caller states with no scope.  alloca_room of the callee's entry
   state is a hypothesis: the caller's frontier carries over, so only the
   call site can establish it. *)
Theorem compile_internal_prologue_entry:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1 func ctx args caller
   s0 f cx vs env.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
    st0.cs_current_insts = [] /\
    st0.cs_current_bb = (HD func.fn_blocks).bb_label /\
    setup_callee func args caller = SOME s0 /\
    state_rel f cenv cx (vs with scopes := []) caller /\
    internal_args_rel cenv params env (if has_rb then 1 else 0) args
      caller.vs_alloca_next caller.vs_memory /\
    caller.vs_alloca_next + internal_stack_size cenv params
      < dimword (:256) /\
    alloca_room func s0 ==>
    ?s1.
      ~s1.vs_halted /\ s1.vs_current_bb = st1.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
      stmt_state_rel func (cenv2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) s1 /\
      fresh_vars_wrt st1 s1 /\
      (?x. return_pc = Var x /\ not_fresh_at st1 x /\
           lookup_var x s1 = SOME s0.vs_return_pc_token) /\
      (has_rb ==>
       ?rb. not_fresh_at st1 rb /\ lookup_var rb s1 = SOME (HD args) /\
            !off sz. cenv.ce_return_buf = SOME (MemLoc off sz) ==>
                     cenv2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
      !fuel r. run_from fuel ctx func s1 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all internal_prologue_run >> strip_tac >>
  drule setup_callee_frontier >> strip_tac >>
  drule compile_internal_prologue_shape >> strip_tac >>
  `frag_exec ctx st0 st1 (\s. s = s0)
     (\s. s = (t with vs_inst_idx := LENGTH st1.cs_current_insts))
     (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     simp[IS_PREFIX_APPEND, emitted_insts_def] >>
     qexists_tac `t` >> fs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  `alloca_room func t` by
    (irule run_inst_seq_alloca_room >>
     qexistsl_tac [`emitted_insts st0 st1`, `s0`] >> simp[] >>
     fs[EVERY_MEM, emitted_insts_def, DROP_LENGTH_APPEND] >>
     rpt strip_tac >> res_tac >> simp[] >>
     qpat_x_assum `fn_has_code st0 st1 func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `st1.cs_current_bb`] >>
     fs[IS_PREFIX_APPEND] >> gvs[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH st1.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, stmt_state_rel_def, fresh_vars_wrt_def,
       lookup_var_def] >>
  fs[fresh_vars_wrt_def, lookup_var_def] >> metis_tac[]
QED


Theorem compile_internal_prologue_reserved[local]:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    ALL_DISTINCT (MAP FST params) /\
    (!i. i < LENGTH params ==>
         ?off sz. FLOOKUP cenv.ce_vars (FST (EL i params)) =
                  SOME (MemLoc off sz)) /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                MEM n (MAP FST params)) /\
    (!n p sz. FLOOKUP cenv.ce_vars n <> SOME (PtrVar p sz)) ==>
    local_ptrs_reserved cenv2 st1
Proof
  rpt gen_tac >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> disch_then strip_assume_tac >>
  dxrule compile_internal_param_decls_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce caps sm = (cenv2',sn)` >>
  `MAP FST caps = MAP FST params` by
    (irule LIST_EQ >> simp[Abbr `caps`, EL_MAP] >>
     rpt strip_tac >> simp[]) >>
  `ALL_DISTINCT (MAP (SND o SND) caps)` by
    (simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> rpt strip_tac >>
     gvs[ASCIInumbersTheory.toString_inj]) >>
  `local_ptrs_reserved cenv2' sn` by
    (irule materialize_internal_params_reserved >>
     qexistsl_tac [`caps`,`ce`,`sm`] >> simp[] >>
     conj_tac
     >- (rpt gen_tac >> simp[MEM_EL] >> strip_tac >>
         gvs[Abbr `ce`] >>
         qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
         simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
              comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
         gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
     simp[Abbr `ce`] >> metis_tac[]) >>
  Cases_on `ret_type` >> Cases_on `cenv.ce_returns_count > 0` >>
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def, local_ptrs_reserved_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* The prologue's code is one open block of straight-line code, and it
   leaves the compile env the body is compiled in with each parameter held
   through a pointer variable of its own that the body's code does not
   assign, when cenv holds the parameters, all at MemLoc slots, and no
   other local.  build_compile_env gives every internal function such a
   cenv (package_internal_fn_prologue_code below): its locals get no slot,
   since ce_alloca_locals has each declaration allocate its own ALLOCA. *)
Theorem compile_internal_prologue_code:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    ALL_DISTINCT (MAP FST params) /\
    (!i. i < LENGTH params ==>
         ?off sz. FLOOKUP cenv.ce_vars (FST (EL i params)) =
                  SOME (MemLoc off sz)) /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                MEM n (MAP FST params)) /\
    (!n p sz. FLOOKUP cenv.ce_vars n <> SOME (PtrVar p sz)) ==>
    st1.cs_blocks = st0.cs_blocks /\
    st1.cs_current_bb = st0.cs_current_bb /\
    isPREFIX st0.cs_current_insts st1.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st0 st1) /\
    ~block_is_terminated st1 /\
    local_ptrs_reserved (cenv2 with ce_alloca_locals := T) st1
Proof
  rpt gen_tac >> disch_then strip_assume_tac >>
  drule compile_internal_prologue_shape >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  conj_tac
  >- (`~is_terminator (LAST new).inst_opcode` by
        (gvs[EVERY_MEM] >> metis_tac[MEM_LAST_NOT_NIL]) >>
      Cases_on `st0.cs_current_insts` >> Cases_on `new` >>
      gvs[block_is_terminated_def, LAST_APPEND] >>
      Cases_on `t'` >> gvs[LAST_DEF, LAST_APPEND]) >>
  drule_all compile_internal_prologue_reserved >> strip_tac >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* Integrity gate for preserved public prologue guarantees. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "CALLEE_FORCE_AUDIT OK\n"
     else raise Fail "callee consumer inherited admission"
  end) [compile_internal_function_prologue, compile_internal_param_decls_shape,
        compile_internal_prologue_shape, compile_internal_prologue_entry,
        compile_internal_prologue_reserved, compile_internal_prologue_code];
(* compile_internal_prologue_code at the compile env and parameters
   package_internal_fn gives every internal function, runtime and
   constructor callees alike. *)
Theorem package_internal_fn_prologue_code:
  !tops use_trans nkey_map is_ctor_context immutables_len mut nr rr fname
   fargs dflts ret body fn_lbl cenv params has_rb is_nr nkey use_tr is_view
   is_ctor imm_len body' ret_type st0 cenv2 return_pc st1.
    package_internal_fn tops use_trans nkey_map is_ctor_context immutables_len
      (mut, nr, rr, fname, fargs, dflts, ret, body) =
      (fn_lbl, cenv, params, has_rb, is_nr, nkey, use_tr, is_view, is_ctor,
       imm_len, body', ret_type) /\
    ALL_DISTINCT (MAP FST fargs) /\
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) ==>
    st1.cs_blocks = st0.cs_blocks /\
    st1.cs_current_bb = st0.cs_current_bb /\
    isPREFIX st0.cs_current_insts st1.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st0 st1) /\
    ~block_is_terminated st1 /\
    local_ptrs_reserved (cenv2 with ce_alloca_locals := T) st1
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compileVyperTheory.package_internal_fn_def,
      compileVyperTheory.update_cenv_nonreentrant_def] >>
  drule compile_internal_prologue_code >>
  disch_then irule >>
  qspecl_then [`tops`, `if is_ctor then Deploy else Internal`, `mut`, `fname`,
               `fargs`, `ret`, `body'`, `use_tr`]
    strip_assume_tac compileVyperTheory.build_compile_env_vars >>
  simp[MAP_ZIP, LENGTH_ZIP_MIN, EL_ZIP, EL_MAP,
       LENGTH_compute_pass_via_stack] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[MEM_MAP] >> metis_tac[MEM_EL]
QED
