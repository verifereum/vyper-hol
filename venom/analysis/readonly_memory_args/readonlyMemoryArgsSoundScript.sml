(* Syntactic soundness boundary for readonly memory parameter analysis. *)
Theory readonlyMemoryArgsSound
Ancestors
  readonlyMemoryArgsDefs list rich_list indexedLists finite_map alist pred_set While

Theorem rma_is_readonly_iff:
  !rma name k. rma_is_readonly rma name k <=>
    ?state. FLOOKUP rma name = SOME state /\
            k < LENGTH state /\ EL k state
Proof
  simp[rma_is_readonly_def, rma_get_readonly_idxs_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP rma name` >> simp[] >>
  simp[MEM_FLAT, MEM_MAPi, PULL_EXISTS] >>
  simp[COND_RAND, COND_RATOR] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rma_is_readonly_callee_arg:
  !rma name k. rma_is_readonly rma name k =
    callee_arg_readonly rma name k
Proof
  simp[rma_is_readonly_iff, callee_arg_readonly_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP rma name` >> simp[]
QED

Theorem rma_fixpoint_fold_unchanged:
  !fns functions infos dfgs changed st st'.
    FOLDL (\(changed, st) fn.
      case (FLOOKUP infos fn.fn_name, FLOOKUP dfgs fn.fn_name) of
        (SOME info, SOME dfg) =>
          let new_state = rma_analyze_fn functions st dfg info fn in
          let old_state = case FLOOKUP st fn.fn_name of
                            NONE => [] | SOME s => s in
          if new_state = old_state then (changed, st)
          else (T, st |+ (fn.fn_name, new_state))
      | _ => (changed, st)) (changed, st) fns = (F, st') ==>
    ~changed /\ st' = st /\
    !fn info dfg. MEM fn fns /\
      FLOOKUP infos fn.fn_name = SOME info /\
      FLOOKUP dfgs fn.fn_name = SOME dfg ==>
      rma_analyze_fn functions st dfg info fn =
        (case FLOOKUP st fn.fn_name of NONE => [] | SOME s => s)
Proof
  Induct_on `fns` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`functions`, `infos`, `dfgs`] assume_tac) >>
  Cases_on `FLOOKUP infos h.fn_name` >>
  Cases_on `FLOOKUP dfgs h.fn_name` >> gvs[] >>
  (TRY IF_CASES_TAC) >> simp[] >> strip_tac >>
  qpat_x_assum `!changed st st'. _` drule >>
  strip_tac >> gvs[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rma_fixpoint_step_unchanged:
  !functions infos dfgs st st'.
    rma_fixpoint_step functions infos dfgs st = (F, st') ==>
    st' = st /\
    !fn info dfg. MEM fn functions /\
      FLOOKUP infos fn.fn_name = SOME info /\
      FLOOKUP dfgs fn.fn_name = SOME dfg ==>
      rma_analyze_fn functions st dfg info fn =
        (case FLOOKUP st fn.fn_name of NONE => [] | SOME s => s)
Proof
  rpt gen_tac >> rewrite_tac[rma_fixpoint_step_def] >> strip_tac >>
  drule rma_fixpoint_fold_unchanged >> simp[]
QED

Theorem rma_owhile_fixpoint:
  !functions infos dfgs init changed st.
    OWHILE (\(changed, _). changed)
      (\(_, st). rma_fixpoint_step functions infos dfgs st)
      (T, init) = SOME (changed, st) ==>
    rma_fixpoint_step functions infos dfgs st = (F, st)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. (~FST x ==> rma_fixpoint_step functions infos dfgs (SND x) = x) /\
       FST x ==>
       (~FST (rma_fixpoint_step functions infos dfgs (SND x)) ==>
        rma_fixpoint_step functions infos dfgs
          (SND (rma_fixpoint_step functions infos dfgs (SND x))) =
        rma_fixpoint_step functions infos dfgs (SND x))`
    by (gen_tac >> strip_tac >>
        Cases_on `rma_fixpoint_step functions infos dfgs (SND x)` >>
        simp[] >> strip_tac >> gvs[] >>
        drule rma_fixpoint_step_unchanged >> simp[] >> metis_tac[]) >>
  drule OWHILE_ENDCOND >> simp[] >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL
    [`\(changed, st). changed`,
     `\(_, st). rma_fixpoint_step functions infos dfgs st`, `(T, init)`]
    (OWHILE_INV_IND
      |> INST_TYPE [alpha |-> ``:bool # (string, bool list) fmap``]
      |> Q.INST [`P` |->
        `\x. ~FST x ==> rma_fixpoint_step functions infos dfgs (SND x) = x`])) >> simp[] >>
  impl_tac >- (gvs[pairTheory.FORALL_PROD] >> metis_tac[]) >>
  simp[]
QED

Theorem rma_analyze_fn_equation:
  !fn_meta ctx fn k.
    ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
    MEM fn ctx.ctx_functions /\
    rma_is_readonly (rma_analyze fn_meta ctx) fn.fn_name k ==>
    ?state.
      FLOOKUP (rma_analyze fn_meta ctx) fn.fn_name = SOME state /\
      rma_analyze_fn ctx.ctx_functions (rma_analyze fn_meta ctx)
        (dfg_build_function fn) (collect_param_info fn_meta fn) fn = state
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP (FOLDL (\fm f. fm |+ (f.fn_name, collect_param_info fn_meta f))
     FEMPTY ctx.ctx_functions) fn.fn_name =
     SOME (collect_param_info fn_meta fn)` by
    (rewrite_tac[FOLDL_FUPDATE_LIST] >> irule mem_to_flookup >>
     simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >> metis_tac[]) >>
  `FLOOKUP (FOLDL (\fm f. fm |+ (f.fn_name, dfg_build_function f))
     FEMPTY ctx.ctx_functions) fn.fn_name = SOME (dfg_build_function fn)` by
    (rewrite_tac[FOLDL_FUPDATE_LIST] >> irule mem_to_flookup >>
     simp[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >> metis_tac[]) >>
  fs[rma_analyze_def] >>
  qmatch_asmsub_abbrev_tac `OWHILE G step initial` >>
  Cases_on `OWHILE G step initial` >> gvs[rma_is_readonly_iff] >>
  PairCases_on `x` >> gvs[] >>
  `rma_fixpoint_step ctx.ctx_functions
     (FOLDL (\fm f. fm |+ (f.fn_name, collect_param_info fn_meta f))
       FEMPTY ctx.ctx_functions)
     (FOLDL (\fm f. fm |+ (f.fn_name, dfg_build_function f))
       FEMPTY ctx.ctx_functions) x1 = (F, x1)` by
    (irule rma_owhile_fixpoint >>
     gvs[Abbr `G`, Abbr `step`, Abbr `initial`] >> metis_tac[]) >>
  drule rma_fixpoint_step_unchanged >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem rma_analyze_fn_readonly:
  !functions rma dfg info fn k.
    k < LENGTH (rma_analyze_fn functions rma dfg info fn) /\
    EL k (rma_analyze_fn functions rma dfg info fn) ==>
    k < LENGTH info.fpi_invoke_params /\
    !bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
      k NOTIN
        (if inst.inst_opcode = INVOKE then
           rma_handle_invoke functions rma
             (root_param_indices_op dfg info.fpi_invoke_param_index
               (LENGTH info.fpi_invoke_params) {}) inst
         else case mem_write_ops inst of NONE => {} | SOME ops =>
           root_param_indices_op dfg info.fpi_invoke_param_index
             (LENGTH info.fpi_invoke_params) {} ops.iao_ofst)
Proof
  rpt gen_tac >>
  simp[rma_analyze_fn_def, LIST_TO_SET_MAP, IN_BIGUNION_IMAGE] >>
  IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[EL_GENLIST] >> metis_tac[]
QED

Theorem rma_analyze_fn_no_write:
  !functions rma dfg info fn k bb inst ops.
    k < LENGTH (rma_analyze_fn functions rma dfg info fn) /\
    EL k (rma_analyze_fn functions rma dfg info fn) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode <> INVOKE /\ mem_write_ops inst = SOME ops ==>
    k NOTIN root_param_indices_op dfg info.fpi_invoke_param_index
      (LENGTH info.fpi_invoke_params) {} ops.iao_ofst
Proof
  rpt strip_tac >> drule_all rma_analyze_fn_readonly >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem rma_handle_invoke_readonly:
  !functions rma root inst name args j k.
    inst.inst_operands = Label name :: args /\ j < LENGTH args /\
    k IN root (EL j args) /\
    k NOTIN rma_handle_invoke functions rma root inst ==>
    EXISTS (\fn. fn.fn_name = name) functions /\
    rma_is_readonly rma name j
Proof
  rpt gen_tac >> strip_tac >>
  `root (EL j args) <> {}` by metis_tac[NOT_IN_EMPTY] >>
  gvs[rma_handle_invoke_def, IN_BIGUNION, MEM_MAPi] >>
  qpat_x_assum `!s. _` (qspec_then `root (EL j args)` mp_tac) >>
  simp[] >> disch_then (qspec_then `j` mp_tac) >>
  Cases_on `EXISTS (\fn. fn.fn_name = name) functions` >>
  Cases_on `callee_arg_readonly rma name j` >>
  gvs[rma_is_readonly_callee_arg, EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem rma_analyze_fn_readonly_call:
  !functions rma dfg info fn k bb inst name args j.
    k < LENGTH (rma_analyze_fn functions rma dfg info fn) /\
    EL k (rma_analyze_fn functions rma dfg info fn) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\ j < LENGTH args /\
    k IN root_param_indices_op dfg info.fpi_invoke_param_index
      (LENGTH info.fpi_invoke_params) {} (EL j args) ==>
    EXISTS (\callee. callee.fn_name = name) functions /\
    rma_is_readonly rma name j
Proof
  rpt gen_tac >> strip_tac >>
  drule_all rma_analyze_fn_readonly >> strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  drule_all rma_handle_invoke_readonly >> simp[]
QED

(* A finite path may revisit SSA names (notably PHIs).  Such a revisit is
   conservative because the tracing function returns every parameter. *)
Theorem root_param_indices_path:
  !dfg param_idx n k path visited.
    k < n /\ path <> [] /\
    FLOOKUP param_idx (LAST path) = SOME k /\
    (!j. SUC j < LENGTH path ==>
      ?inst. dfg_get_def dfg (EL j path) = SOME inst /\
             MEM (EL (SUC j) path) (root_from_inst_ops inst) /\
             FLOOKUP param_idx (EL j path) = NONE) ==>
    k IN root_param_indices dfg param_idx n visited (HD path)
Proof
  Induct_on `path` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h IN visited`
  >- simp[Once root_param_indices_def] >>
  Cases_on `path`
  >- gvs[Once root_param_indices_def] >>
  rename1 `LAST (h::v::vs)` >>
  `?inst. dfg_get_def dfg h = SOME inst /\
          MEM v (root_from_inst_ops inst) /\ FLOOKUP param_idx h = NONE`
    by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[Once root_param_indices_def] >>
  `k IN root_param_indices dfg param_idx n (h INSERT visited) v`
    by (qpat_x_assum `!dfg param_idx n k visited. _`
          (mp_tac o Q.SPECL [`dfg`, `param_idx`, `n`, `k`, `h INSERT visited`]) >>
        simp[] >> disch_then irule >> gvs[] >>
        rpt strip_tac >>
        qpat_x_assum `!j. _` (qspec_then `SUC j` mp_tac) >> simp[]) >>
  qpat_x_assum `MEM v _` mp_tac >>
  SPEC_TAC (``root_from_inst_ops inst``, ``ops: string list``) >>
  Induct >> simp[CONJUNCT2 root_param_indices_def] >> metis_tac[]
QED
