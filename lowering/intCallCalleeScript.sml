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
 * relation for the scope push_function builds from the arguments, at the
 * point the body's code starts.
 *
 * TOP-LEVEL:
 *   compile_internal_prologue   — the prologue as one compile action
 *   compile_internal_function_prologue — compile_internal_function is the
 *                                 prologue, then the rest of it
 *   internal_args_rel           — the arguments an INVOKE passes, for
 *                                 the scope the callee's body starts in
 *   internal_stack_size         — the bytes the stack-passed arguments'
 *                                 ALLOCAs take
 *   compile_internal_prologue_shape — the prologue's code: one block, no
 *                                 terminator, no INVOKE
 *   compile_internal_prologue_reserved — the prologue's compile env holds
 *                                 every argument through a pointer handed
 *                                 out before the body (local_ptrs_reserved)
 *   compile_internal_prologue_entry — from setup_callee, the prologue
 *                                 reaches the body's start in
 *                                 stmt_state_rel, with the return PC bound
 *
 * No alloca_room: under INVOKE's semantics the callee inherits the
 * caller's allocation frontier (setup_callee keeps vs_alloca_next), so
 * the frontier is not bounded by the callee's own ALLOCAs.  The entry
 * lemma takes the one bound it needs as a hypothesis: the frontier at the
 * call plus internal_stack_size is below 2 ** 256, so the arguments'
 * ALLOCAs do not wrap.
 *)

Theory intCallCallee
Ancestors
  list rich_list finite_map indexedLists
  fragExec localPtrsProps exprLoweringProps loweringHalt
  moduleLowering stmtLowering exprLowering emitHelper context compileEnv
  valueEncoding valueEncodingProps venomMemDefs
  venomExecSemantics venomInst venomState vyperState

(* ===== The prologue ===== *)

(* compile_internal_function up to the code that is not the prologue's: the
   immutables reservation of a constructor callee, the nonreentrant lock and
   the body.  It returns the compile env the body is compiled in (before
   ce_alloca_locals is set) and the return-PC operand. *)
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

Theorem compile_internal_param_decls_shape:
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
Theorem run_inst_seq_params:
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

Theorem materialize_internal_params_shape:
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

(* Running the code materialize_internal_params emits for caps binds each
   parameter's name to a pointer at its value: a stack-passed one's in a
   fresh ALLOCA region at the frontier, a memory-passed one's at its
   argument buffer mr, below the frontier f0 at entry. *)
Theorem materialize_internal_params_run:
  !caps cenv st cenv' st' func env s f0 mr.
    materialize_internal_params cenv caps st = (cenv', st') /\
    (!i. MEM i (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) ==>
         MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func /\
    ALL_DISTINCT (MAP FST caps) /\
    EVERY (\c. ?p a off sz entry.
         SND (SND c) = Var p /\ not_fresh_at st p /\ lookup_var p s = SOME a /\
         FLOOKUP cenv.ce_vars (FST c) = SOME (MemLoc off sz) /\
         FLOOKUP env (FST c) = SOME entry /\
         type_memory_size entry.type <= sz /\
         val_wf entry.type entry.value /\
         if FST (SND c) then
           32 <= sz /\
           !b m. mem_word_at b m = a ==>
                 val_in_memory entry.type entry.value b m
         else
           mr (FST c) = SOME (w2n a, sz) /\ w2n a + sz <= f0 /\
           val_in_memory entry.type entry.value (w2n a) s.vs_memory) caps /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1, sz1) /\ mr n2 = SOME (b2, sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) /\
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
              f0 <= b \/ mr n = SOME (b, sz)) /\
    s.vs_alloca_next +
      internal_stack_size cenv (MAP (\c. (FST c, FST (SND c))) caps)
      < dimword (:256) ==>
    ?s'.
      run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s =
        OK s' /\
      local_ptrs_rel func cenv' [env] s' /\ alloca_inv s' /\
      (!inst n base sz.
         MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit n] /\
         FLOOKUP s'.vs_allocas inst.inst_id = SOME (base, sz) ==>
         sz = w2n n) /\
      fresh_vars_wrt st' s' /\
      (!aid. aid IN FDOM s'.vs_allocas ==> aid < st'.cs_next_id) /\
      (!x. not_fresh_at st x ==> lookup_var x s' = lookup_var x s) /\
      s' = s with <| vs_vars := s'.vs_vars; vs_memory := s'.vs_memory;
                     vs_allocas := s'.vs_allocas;
                     vs_alloca_next := s'.vs_alloca_next |>
Proof
  cheat
QED

(* ===== The callee's entry ===== *)

(* Running the prologue of an internal function func, compiled in cenv from
   st0, at the head of func's entry block, to st1, from the state
   setup_callee builds for an INVOKE of func with arguments args from the
   state caller, reaches the point where the body's code starts in a state
   s1 related at the scope env the source binds the parameters in:
   - each parameter is a local held through a pointer variable: a
     stack-passed one in a region of its own ALLOCA, holding its value, a
     memory-passed one in its argument buffer;
   - the return PC and the return buffer are in variables the body's code
     does not assign;
   - every result from s1 is one from the callee's entry state.
   The global part of the relation (storage, transient, immutables, logs,
   contexts) is that of the caller's state in cenv, which the hypothesis
   on caller states with no scope.  There is no assumption on the room
   left for allocations, beyond that the stack-passed parameters' regions
   fit a word: alloca_room fails at callee entry, as the caller's frontier
   carries over. *)
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
      < dimword (:256) ==>
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
  cheat
QED

(* The prologue's code is one open block of straight-line code, and it
   leaves the compile env the body is compiled in with each parameter held
   through a pointer variable of its own that the body's code does not
   assign, when cenv holds the parameters, all at MemLoc slots, and no
   other local.  build_compile_env gives internal functions such a cenv
   only when they have no locals besides their parameters: it still
   allocates MemLoc slots for the others (allocate_locals), which the body
   never uses, since ce_alloca_locals has declarations allocate their own
   ALLOCA. *)
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
  cheat
QED
