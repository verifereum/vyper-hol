(*
 * Whitelist removal: for loops over a memory-valued array iterable other
 * than a local name (form 2 of whitelistForIter's survey).
 *
 * compile_stmt's For Array case compiles the iterable with compile_expr
 * and then runs the fixed or dynamic memory loop over the pointer it
 * returns: a temporary buffer (a list literal, an extcall result, an IfExp
 * copy) or a place inside a local (a struct member or a subscript).  The
 * source iterates the snapshot it read at loop entry, so the compiled loop
 * agrees only while the body leaves the iterable's bytes alone.
 *
 * Neither S1 interface says that yet:
 *   - for a temporary, stmt_post keeps no memory outside the locals, so a
 *     body's stmt_frag doesn't keep the buffer;
 *   - for a place, vv_post doesn't tie the pointer to the source place
 *     (only to some offset of a local of the same type), so
 *     "the body doesn't write the place" (iterator_unmodified) doesn't
 *     reach the bytes the loop reads.
 * So the loop is proved against a hook, and each kind of iterable reduces
 * the hook to the interface clause it lacks today, taken as an explicit
 * hypothesis:
 *
 *   stmt_frag_keep Q    - a statement fragment that also keeps the state
 *                         predicate Q from start to end
 *   expr_vv_sim_with Qe - expr_vv_sim with an extra postcondition Qe
 *   keep_stable Q sb b z - Q survives code that keeps the variables handed
 *                         out before sb and the bytes [b, b+z)
 *
 * TOP-LEVEL:
 *   compile_for_mem_frag      - the For case over a memory iterable, given
 *                               the hook (a pointer inside an allocation
 *                               made before the loop, and a body that keeps
 *                               the elements there)
 *   typed_stmts_place_frame   - source side: a body that writes nothing
 *                               containing the iterable's place keeps every
 *                               read below its attribute path
 *   for_keep_temp             - hook for a temporary: from a body that keeps
 *                               the bytes of the buffer's allocation
 *   for_keep_place            - hook for a place: from the pointer being the
 *                               place's (local pointer + mem_path_offset)
 *                               and the source frame
 *)
Theory whitelistForIterMem
Ancestors
  whitelistForIterDynFrag stmtSimForArrayFrame exprSimSubscriptMap exprSimDefs loweringPosts
  stmtSimDefs gasOutcome gasSummary supportedStmts vyperTypeSystem vyperState
  vyperInterpreter valueEncoding valueEncodingProps valueEncodingProofs
  stmtLowering exprLowering venomState exprSimPopImmutableTarget
  compileEnv exprLoweringProps list finite_map arithmetic words bodySimAugPlaceMemory

(* A statement fragment as stmt_frag says, that also keeps Q: started in a
   state where Q holds, it ends where Q holds.  stmt_frag_keep (K T) is
   stmt_frag. *)
Definition stmt_frag_keep_def:
  stmt_frag_keep Q ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      stmt_state_rel ctx func cenv cx es s0 /\ Q s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) source (es, s0)
        (\res ee t. stmt_post ctx func cx lctx cenv cenv' sa sb s0 res ee t /\
                    Q t)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

(* expr_vv_sim, whose post also has Qe of the compile states, the start
   state, and the source and Venom results.  expr_vv_sim_with (K ...) T is
   expr_vv_sim. *)
Definition expr_vv_sim_with_def:
  expr_vv_sim_with Qe ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          Qe sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

(* Q survives any code that keeps the variables handed out before sb and
   the bytes [b, b + z): the loop's own index, element copy and branches
   write only fresh variables and the loop variable's allocation. *)
Definition keep_stable_def:
  keep_stable Q (sb : compile_state) b z <=>
    !s s'. Q s /\
      (!x. not_fresh_at sb x ==> lookup_var x s' = lookup_var x s) /\
      mem_bytes_at b z s'.vs_memory = mem_bytes_at b z s.vs_memory ==>
      Q s'
End

(* The For case over a memory-valued iterable, fixed or dynamic.  The hook
   (the last premise) is asked of every end of the iterable's fragment: the
   pointer w lies inside an allocation (aid, b, z) made before the loop,
   the elements vs of the value v the source read sit at w, and the body,
   at every element, keeps a predicate Q that puts them there and that
   survives the loop's own code (keep_stable).  P is the source-side loop
   invariant, as in compile_for_dynarray_frag. *)
Theorem compile_for_mem_frag:
  !ctx func cx cenv lctx RetQ ty id et bd c n arr_e stmts tv es Qe.
  expr_type arr_e = ArrayT et bd /\ (bd = Fixed c \/ bd = Dynamic c) /\
  c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  (!st. vv_location (FST (compile_expr cenv (ArrayT et bd) arr_e st)) =
          SOME LocMemory) /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  expr_vv_sim_with Qe ctx func cenv cx (ArrayT et bd) arr_e es /\
  (!sa sb s0 es1 rv vv s1.
     compile_expr cenv (ArrayT et bd) arr_e sa = (vv, sb) /\
     vv_post ctx func cenv cx arr_e es sa sb s0 es1 rv vv s1 /\
     Qe sa sb s0 es1 rv vv s1 ==>
     ?v vs w aid b z Q P.
       read_result cx rv es1 = (INL v, es1) /\
       extract_elements (ArrayTV tv bd) v = SOME vs /\
       eval_operand (vv_operand vv) s1 = SOME w /\
       FLOOKUP s1.vs_allocas aid = SOME (b, z) /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + type_memory_size (ArrayTV tv bd) <= b + z /\
       b + z < dimword (:256) /\
       Q s1 /\ keep_stable Q sb b z /\
       (!s. Q s ==> val_in_memory (ArrayTV tv bd) v (w2n w) s.vs_memory) /\
       P es1 /\ lookup_scopes id es1.scopes = NONE /\
       (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
       (!st0 bc sd ex inc ei k.
          declare_local cenv id et st0 = (bc,sd) /\
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
          stmt_frag_keep Q ctx func cx (InLoop ex inc) RetQ bc
            (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
            (ei with scopes :=
              (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                                popped := []|>)) :: ei.scopes)) /\
       (!ei k gs r es2.
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
          eval_stmts cx stmts (ei with <| scopes :=
            (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                              popped := []|>)) :: ei.scopes; gas_obs := gs |>) =
            (r,es2) ==>
          (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
          ?sc rest. es2.scopes = sc :: rest /\
            (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
            ((r = INL () \/ r = INR ContinueException) ==>
              P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array arr_e) n stmts))
    (eval_stmt cx (For id et (Array arr_e) n stmts)) es
Proof
  cheat
QED

(* Source side for a place iterable: a body that writes nothing containing
   the place p (iterator_unmodified) keeps, at every scope, the root
   local's type and its sub-value at p's attribute path (the path up to
   p's first subscript, place_access).  The iterable is an array, so a
   well-typed target can't extend that path by another attribute before a
   subscript, which place_contains wouldn't see.
   typed_stmts_projection_frame is the case of an empty attribute path,
   where the whole root is kept. *)
(* Typing an attribute extension requires typing its base. *)
Theorem type_place_target_attribute_prefix[local]:
  !attrs env tgt vt.
    type_place_target env
      (FOLDL (\t a. AttributeTarget t a) tgt attrs) = SOME vt ==>
    ?base. type_place_target env tgt = SOME base
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem attribute_type_fold_none[local]:
  !xs D. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) NONE xs = NONE
Proof
  Induct >> simp[]
QED

Theorem attribute_type_fold_append[local]:
  !xs ys D ot.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot (xs ++ ys) =
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a))
      (FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs) ys
Proof
  Induct >> simp[]
QED

Theorem attribute_type_fold_inert[local]:
  !xs ys D ot t u.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs = SOME t /\
    (!a. attribute_type D t a = NONE) /\
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot (xs ++ ys) = SOME u ==>
    ys = []
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ys` >> gvs[attribute_type_fold_append, attribute_type_fold_none]
QED

Theorem place_access_attribute_chain[local]:
  !xs r ys.
    (r = NameTarget root \/ (?n. r = TopLevelNameTarget n)) ==>
    place_access (FOLDL (\t a. AttributeTarget t a) r xs) ys = (r,xs ++ ys)
Proof
  Induct_on `xs` using SNOC_INDUCT
  >- (rpt strip_tac >> gvs[place_access_def]) >>
  simp[FOLDL_SNOC, place_access_def, SNOC_APPEND] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`r`, `x::ys`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem place_access_chain_or_reset[local]:
  !p. (!r xs. place_access p [] = (r,xs) ==>
    (p = FOLDL (\t a. AttributeTarget t a) r xs /\
     !ys. place_access p ys = (r,xs ++ ys)) \/
    (!ys. place_access p ys = (r,xs)))
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- simp[place_access_def]
  >- simp[place_access_def]
  >- (rpt strip_tac >> gvs[place_access_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `place_access p []` >>
  first_x_assum (qspecl_then [`q`, `r'`] mp_tac) >> simp[] >>
  strip_tac >> simp[place_access_def] >>
  strip_tac >> gvs[GSYM SNOC_APPEND, FOLDL_SNOC]
QED

Theorem type_place_expr_not_local[local]:
  !e env vt p root xs.
    type_place_expr env e = SOME vt /\ expr_place e = SOME p ==>
    place_access p [] <> (NameTarget root,xs)
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[Once well_typed_expr_def, expr_place_def, place_access_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[Once well_typed_expr_def, place_access_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem typed_expr_access_endpoint[local]:
  !e env p root xs.
    well_typed_expr env e /\ expr_place e = SOME p /\
    place_access p [] = (NameTarget root,xs) ==>
    ?t. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type env.type_defs ty a))
          (FLOOKUP env.var_types root) xs = SOME t /\
        ((p = FOLDL (\t a. AttributeTarget t a) (NameTarget root) xs /\
          t = expr_type e) \/ ((!a. attribute_type env.type_defs t a = NONE) /\
          (!ys. place_access p ys = (NameTarget root,xs))))
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[expr_place_def, AllCaseEqs()]
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def,
                          vyperASTTheory.expr_type_def])
  >- (rpt strip_tac >> gvs[place_access_def])
  >- (rpt strip_tac >>
      gvs[Once well_typed_expr_def, place_access_def]
      >- (qpat_x_assum `!env'. well_typed_expr env' e ==> _`
            (qspec_then `env` mp_tac) >> simp[] >> strip_tac >>
          rename1 `FOLDL _ _ xs = SOME endpoint` >>
          qexists_tac `endpoint` >> simp[] >>
          Cases_on `expr_type e` >> gvs[subscript_type_ok_def, attribute_type_def]) >>
      metis_tac[type_place_expr_not_local]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def] >>
  Cases_on `place_access tgt []` >>
  drule place_access_chain_or_reset >> strip_tac >>
  gvs[]
  >- (`~(!ys:string list. ys = [])` by
        (strip_tac >> first_x_assum (qspec_then `[s]` mp_tac) >> simp[]) >>
      qpat_x_assum `!env'. _` (qspec_then `env` mp_tac) >> simp[] >>
      strip_tac >>
      gvs[attribute_type_fold_append, attribute_type_ok_def,
          GSYM SNOC_APPEND, FOLDL_SNOC, vyperASTTheory.expr_type_def]) >>
  qpat_x_assum `!env'. _` (qspec_then `env` mp_tac) >> simp[] >>
  strip_tac
  >- (qpat_x_assum `!ys. place_access _ ys = _`
        (qspec_then `[s]` mp_tac) >>
      simp[place_access_attribute_chain] >>
      disch_then (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[]) >>
  metis_tac[]
QED

Theorem typed_target_access_endpoint[local]:
  !w env vt root xs.
    type_place_target env w = SOME vt /\
    place_access w [] = (NameTarget root,xs) ==>
    ?t. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type env.type_defs ty a))
          (FLOOKUP env.var_types root) xs = SOME t /\
        ((w = FOLDL (\t a. AttributeTarget t a) (NameTarget root) xs /\
          vt = Type t) \/ (!ys. place_access w ys = (NameTarget root,xs)))
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def,
                           AllCaseEqs()])
  >- (rpt strip_tac >> gvs[place_access_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once well_typed_expr_def, place_access_def, AllCaseEqs()] >>
      rpt strip_tac >> first_x_assum drule >> simp[] >>
      strip_tac >> metis_tac[place_access_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `place_access w []` >>
  drule place_access_chain_or_reset >> strip_tac >>
  gvs[place_access_def]
  >- (qpat_x_assum `!ys. place_access _ ys = _`
        (qspec_then `[s]` assume_tac) >> gvs[] >>
      `~(!ys:string list. ys = [])` by
        (strip_tac >> first_x_assum (qspec_then `[s]` mp_tac) >> simp[]) >>
      qpat_x_assum `!env' vt'. _` drule >> simp[] >> strip_tac >>
      gvs[attribute_type_fold_append, GSYM SNOC_APPEND, FOLDL_SNOC]) >>
  qpat_x_assum `!env' vt'. _` drule >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem attribute_type_fold_separation[local]:
  !D ot xs ws t u.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs = SOME t /\
    (!a. attribute_type D t a = NONE) /\
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot ws = SOME u /\
    ~isPREFIX ws xs ==> ~isPREFIX xs ws
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all attribute_type_fold_inert >> strip_tac >> gvs[]
QED

Theorem typed_place_write_separation[local]:
  !env e et bd p root xs envw w vt ws.
    well_typed_expr env e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    type_place_target envw w = SOME vt /\
    envw.type_defs = env.type_defs /\
    FLOOKUP envw.var_types root = FLOOKUP env.var_types root /\
    ~place_contains w p /\ place_access w [] = (NameTarget root,ws) ==>
    ~isPREFIX ws xs /\ ~isPREFIX xs ws
Proof
  rpt gen_tac >> strip_tac >>
  `~isPREFIX ws xs` by gvs[place_contains_def] >> simp[] >>
  drule_all typed_expr_access_endpoint >>
  disch_then (qx_choose_then `endpoint` strip_assume_tac) >>
  `!a. attribute_type env.type_defs endpoint a = NONE` by
    gvs[attribute_type_def] >>
  drule_all typed_target_access_endpoint >> strip_tac >>
  irule attribute_type_fold_separation >> simp[] >>
  qexistsl_tac [`env.type_defs`, `FLOOKUP env.var_types root`, `endpoint`] >>
  gvs[] >> metis_tac[]
QED

Theorem assign_subscripts_divergent_attrs[local]:
  !xs ws tv v tail ao v'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    assign_subscripts tv v (MAP AttrSubscript ws ++ tail) ao = INL v' ==>
    evaluate_subscripts tv v' (MAP AttrSubscript xs) =
    evaluate_subscripts tv v (MAP AttrSubscript xs)
Proof
  Induct >> simp[] >> Cases_on `ws` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `v` >>
  gvs[assign_subscripts_def, AllCaseEqs()] >>
  Cases_on `h = h'`
  >- (gvs[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP] >>
      first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
      disch_then drule >> simp[] >> disch_then (fn th => rewrite_tac[th])) >>
  `h' <> h` by metis_tac[] >>
  simp[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP] >>
  Cases_on `ALOOKUP l h'` >> simp[]
QED

Theorem replace_memory_entry_divergent_attrs[local]:
  !xs ws entry tail v entry'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    replace_memory_entry entry (MAP AttrSubscript ws ++ tail) v = INL entry' ==>
    entry'.type = entry.type /\
    evaluate_subscripts entry'.type entry'.value (MAP AttrSubscript xs) =
    evaluate_subscripts entry.type entry.value (MAP AttrSubscript xs)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[replace_memory_entry_def, AllCaseEqs()] >>
  simp[] >> metis_tac[assign_subscripts_divergent_attrs]
QED

Theorem write_place_divergent_attrs[local]:
  !cx root xs ws tail v es res es'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    write_place cx (MemoryPlace root (MAP AttrSubscript ws ++ tail)) v es = (res,es') ==>
    LENGTH es'.scopes = LENGTH es.scopes /\
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `find_containing_scope root es.scopes`
  >- gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
         return_def, raise_def] >>
  rename1 `find_containing_scope root es.scopes = SOME found` >>
  PairCases_on `found` >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  rename1 `FLOOKUP local root = SOME entry` >>
  Cases_on `replace_memory_entry entry (MAP AttrSubscript ws ++ tail) v` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs(), FLOOKUP_UPDATE] >>
  drule_all replace_memory_entry_divergent_attrs >> simp[]
QED

Theorem eval_base_place_attribute_prefix[local]:
  !target cx es root path es' pending xs.
    eval_base_place cx target es = (INL (PlaceR (MemoryPlace root path)),es') /\
    place_access target pending = (NameTarget root,xs) ==>
    ?tail. path ++ MAP AttrSubscript pending = MAP AttrSubscript xs ++ tail
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
          place_access_def])
  >- (rpt strip_tac >>
      gvs[place_access_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      drule bodySimAugPlaceMemoryTheory.aug_place_extend_memory_inversion >>
      strip_tac >> gvs[place_access_def] >>
      first_x_assum drule >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> simp[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule bodySimAugPlaceMemoryTheory.aug_place_extend_memory_inversion >>
  strip_tac >> gvs[place_access_def] >>
  first_x_assum drule >> disch_then (qspec_then `s::pending` mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem eval_target_place_attribute_prefix[local]:
  !target cx es root path es'.
    eval_target_place cx target es = (INL (MemoryPlace root path),es') ==>
    ?xs tail. place_access target [] = (NameTarget root,xs) /\
              path = MAP AttrSubscript xs ++ tail
Proof
  rpt strip_tac >>
  drule eval_target_place_memory_root >> strip_tac >>
  Cases_on `place_access target []` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_base_place_attribute_prefix >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem typed_memory_write_attribute_projection[local]:
  !env e et bd p root xs envw w vt cx es path evaluated mid v res es'.
    well_typed_expr env e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    type_place_target envw w = SOME vt /\
    envw.type_defs = env.type_defs /\
    FLOOKUP envw.var_types root = FLOOKUP env.var_types root /\
    ~place_contains w p /\
    eval_target_place cx w es = (INL (MemoryPlace root path),evaluated) /\
    write_place cx (MemoryPlace root path) v mid = (res,es') ==>
    LENGTH es'.scopes = LENGTH mid.scopes /\
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) mid.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_target_place_attribute_prefix >> strip_tac >>
  drule_all typed_place_write_separation >> strip_tac >>
  gvs[] >> drule_all write_place_divergent_attrs >> simp[]
QED

Theorem scope_projection_observe[local]:
  !s t root f.
    MAP (\sc. FLOOKUP sc root) t.scopes = MAP (\sc. FLOOKUP sc root) s.scopes ==>
    MAP (\sc. f (FLOOKUP sc root)) t.scopes =
    MAP (\sc. f (FLOOKUP sc root)) s.scopes
Proof
  rpt strip_tac >>
  simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o]
QED

Theorem type_stmt_reference_transport[local]:
  !env ret_ty stmt next ref root.
    type_stmt env ret_ty stmt = SOME next /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM ref.var_types ==>
    next.type_defs = ref.type_defs /\
    FLOOKUP next.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM next.var_types
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperTypeEnvExtensionTheory.type_stmt_preserve_nonlocal_fields >>
  strip_tac >> gvs[] >>
  Cases_on `FLOOKUP ref.var_types root`
  >- gvs[FLOOKUP_DEF] >>
  drule vyperTypeEnvExtensionTheory.type_stmt_var_types_preserve >>
  disch_then drule >> simp[] >> gvs[FLOOKUP_DEF]
QED

Theorem typed_target_write_attribute_projection[local]:
  !ref e et bd p root xs env w vt tops bindings cx v es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    type_place_target env w = SOME vt /\ ~place_contains w p /\
    (supported_target tops bindings w \/
      (?pt. supported_target_info tops bindings w = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root w /\
    (do dest <- eval_target_place cx w; write_place cx dest v od) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  (gvs[bind_def, AllCaseEqs(), raise_def] >>
   imp_res_tac supported_any_target_place_scopes >> gvs[] >>
   rename1 `write_place cx dest v mid = (res,es')` >>
   Cases_on `?path. dest = MemoryPlace root path`
   >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
   `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
   drule_all write_guarded_place_projection >> strip_tac >> simp[] >>
   irule scope_projection_observe >> simp[])
QED

Theorem typed_base_assignment_attribute_projection[local]:
  !ref e et bd p root xs env bt ty tops bindings cx v es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_atarget env (BaseTarget bt) ty /\
    atarget_writes_ok (\w. ~place_contains w p) (BaseTarget bt) /\
    (supported_target tops bindings bt \/
      (?pt. supported_target_info tops bindings bt = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root bt /\
    assign_tuple_targets cx (BaseTarget bt) v es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  (gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
   qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
   simp[Once evaluate_def] >> strip_tac >>
   irule typed_target_write_attribute_projection >>
   goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Theorem typed_flat_targets_attribute_projection[local]:
  !targets tys ref e et bd p root xs env tops bindings cx vs es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
    EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                         | TupleTarget _ => F) targets /\
    EVERY (atarget_writes_ok (\w. ~place_contains w p)) targets /\
    ~supported_assignments_exists expr_internal_call_root targets /\
    assign_tuple_target_list cx targets vs es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Induct_on `targets` >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> gvs[] >>
  rename1 `well_typed_atarget env head head_ty` >>
  Cases_on `head` >> gvs[supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), raise_def] >>
  drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)
    typed_base_assignment_attribute_projection >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`tops`,`bindings`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem typed_assignment_attribute_projection[local]:
  !ref e et bd p root xs env target ty tops bindings rhs cx v es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\w. ~place_contains w p) target /\
    supported_assignment tops bindings target rhs /\
    ~supported_assignment_exists expr_internal_call_root target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `target` >> rpt gen_tac >> strip_tac
  >~ [`assign_tuple_targets _ (BaseTarget _) _ _ = _`]
  >- (rename1 `assign_tuple_targets cx (BaseTarget bt) v es = _` >>
      gvs[supported_assignment_def, AllCaseEqs(),
          supportedStmtTraverseTheory.supported_assignment_exists_def] >>
      irule typed_base_assignment_attribute_projection >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
      metis_tac[]) >>
  gvs[well_typed_atarget_def, supported_assignment_def, atarget_writes_ok_def,
      supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  Cases_on `v` >>
  gvs[Once evaluate_def, raise_def, vyperValueTheory.array_value_CASE_rator,
      AllCaseEqs()] >>
  irule typed_flat_targets_attribute_projection >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem assign_attribute_projection_frame[local]:
  !ref e et bd p root xs env target ty tops bindings rhs cx es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\w. ~place_contains w p) target /\
    supported_assignment tops bindings target rhs /\
    ~supported_assignment_exists expr_internal_call_root target /\
    (!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (Assign target rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `target` >> rpt gen_tac >> strip_tac
  >~ [`eval_stmt _ (Assign (BaseTarget _) _) _ = _`]
  >- suspend "base"
  >> suspend "tuple"
QED

Resume assign_attribute_projection_frame[tuple]:
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all typed_assignment_attribute_projection >> simp[]
QED

Resume assign_attribute_projection_frame[base]:
  rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def,
      supported_assignment_def,
      supportedStmtTraverseTheory.supported_assignment_exists_def, AllCaseEqs()] >>
  (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
   simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
   imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
   first_x_assum drule >> strip_tac >>
   imp_res_tac supported_any_target_place_scopes >>
   Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
   imp_res_tac supported_target_place_scopes >> gvs[] >>
   rename1 `write_place cx dest value mid = (res,es')` >>
   (Cases_on `?path. dest = MemoryPlace root path`
    >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
    `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
    drule_all write_guarded_place_projection >> strip_tac >> simp[] >>
    irule scope_projection_observe >> simp[]))
QED

Finalise assign_attribute_projection_frame

Theorem augassign_attribute_projection_frame[local]:
  !ref e et bd p root xs env bt ty bop rhs tops bindings cx es res es'.
    well_typed_expr ref e /\ expr_type e = ArrayT et bd /\
    expr_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_target env bt ty /\ ~place_contains bt p /\
    (supported_target tops bindings bt \/
      (?pt. supported_target_info tops bindings bt = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  (gvs[well_typed_target_def] >>
   qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
   simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
   imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
   imp_res_tac read_result_state >> imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
   imp_res_tac supported_any_target_place_scopes >>
   gvs[IgnAsm `!s r t. _`] >>
   first_x_assum drule >> strip_tac >> gvs[] >>
   rename1 `write_place cx dest value mid = (res,es')` >>
   Cases_on `?path. dest = MemoryPlace root path`
   >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
   `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
   drule_all write_guarded_place_projection >> strip_tac >> simp[] >>
   irule scope_projection_observe >> simp[])
QED

Theorem finally_pop_scope_observation[local]:
  !f es res es' q.
    es.scopes <> [] /\ finally f pop_scope es = (res,es') /\
    (!r t. f es = (r,t) ==>
      MAP q t.scopes = MAP q es.scopes /\
      LENGTH t.scopes = LENGTH es.scopes) ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `f es` >> rename1 `f es = (outcome,after)` >> fs[] >>
  `MAP q (TL after.scopes) = MAP q (TL es.scopes)` by metis_tac[MAP_TL] >>
  Cases_on `after.scopes` >- gvs[] >>
  Cases_on `outcome` >>
  gvs[finally_def, pop_scope_def, ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem handled_loop_body_observation[local]:
  !cx body q es res es'.
    es.scopes <> [] /\
    (!r t. eval_stmts cx body es = (r,t) ==>
      MAP q t.scopes = MAP q es.scopes /\ LENGTH t.scopes = LENGTH es.scopes) /\
    try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception es =
      (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts es` >>
  Cases_on `eval_stmts cx stmts es` >>
  rename1 `eval_stmts cx stmts es = (outcome,after)` >> gvs[] >>
  Cases_on `outcome` >>
  gvs[try_def, ignore_bind_def, bind_def, return_def] >>
  rename1 `handle_loop_exception exc after = _` >>
  Cases_on `exc` >> gvs[handle_loop_exception_def, return_def, raise_def]
QED

Theorem balanced_loop_body_observation[local]:
  !cx stmts q es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    finally (try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception)
      pop_scope es = (res,es') ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:bool``] finally_pop_scope_observation) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception`,
            `res`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule handled_loop_body_observation >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem eval_for_observation_frame[local]:
  !vs cx tyv id body q es res es'.
    (!s r s'. s.scopes <> [] /\ eval_stmts cx body s = (r,s') ==>
      MAP q s'.scopes = MAP q s.scopes /\ LENGTH s'.scopes = LENGTH s.scopes) /\
    eval_for cx tyv id body vs es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  Induct_on `vs` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `finally action pop_scope` >>
  qpat_x_assum `ignore_bind _ _ es = _` mp_tac >>
  pure_rewrite_tac [push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  strip_tac >> FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  qmatch_asmsub_abbrev_tac `bind (finally action pop_scope) continuation pushed` >>
  Cases_on `finally action pop_scope pushed` >>
  rename1 `finally action pop_scope pushed = (outcome,after)` >> fs[Abbr `action`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_loop_body_observation >>
  disch_then (qspec_then `q` mp_tac) >>
  (impl_tac >- (simp[Abbr `pushed`] >> metis_tac[])) >> strip_tac >>
  fs[IgnAsm `!cx tyv id body q es res es'. _`, Abbr `pushed`] >>
  Cases_on `outcome` >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac [bind_def, pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  simp[Abbr `continuation`, return_def] >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` kall_tac
  >~ [`(if broke then _ else _) _ = _`]
  >- (Cases_on `broke`
      >- (qpat_x_assum `!cx tyv id body q es res es'. _` kall_tac >>
          gvs[return_def]) >>
      FULL_SIMP_TAC std_ss [] >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!cx tyv id body q es res es'. _` kall_tac >> gvs[]
QED

Theorem balanced_conditional_observation[local]:
  !cx tv ss1 ss2 q es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    finally (switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2))
      pop_scope es = (res,es') ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:unit``] finally_pop_scope_observation) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2)`,`res`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) es = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >> gvs[raise_def] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem if_observation_frame[local]:
  !cx e ss1 ss2 q es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==> t.scopes = s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (If e ss1 ss2) es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       get_scopes_def, set_scopes_def, return_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >~ [`v = INR exc`]
  >- gvs[IgnAsm `!s r t. _`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_conditional_observation >>
  disch_then (qspec_then `q` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem for_observation_frame[local]:
  !cx id typ it n stmts q es res es'.
    (!s r t. eval_iterator cx it s = (r,t) ==> t.scopes = s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (For id typ it n stmts) es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  imp_res_tac vyperStatePreservationTheory.check_state >>
  gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_iterator _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`eval_for _ _ _ _ _ _ = _`]
  >- (drule_at (Pat `eval_for _ _ _ _ _ _ = _`) eval_for_observation_frame >>
      disch_then (qspec_then `q` mp_tac) >>
      (impl_tac >- metis_tac[]) >> simp[]) >>
  gvs[IgnAsm `!s r t. _`]
QED

Theorem typed_stmts_place_frame:
  supported_stmts tops bindings stmts /\
  type_stmts env ret_ty stmts = SOME env' /\
  well_typed_expr env arr_e /\ expr_type arr_e = ArrayT et bd /\
  expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
  root IN FDOM env.var_types /\
  stmts_writes_ok (\w. ~place_contains w p) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
  LENGTH es'.scopes = LENGTH es.scopes /\
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es'.scopes =
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es.scopes
Proof
  cheat
QED

(* Hook for a temporary buffer: a body that keeps the bytes of the
   buffer's allocation keeps the iterable's value in it.  The hypothesis
   is what stmt_post's frame on the memory of allocations made before the
   fragment and holding no local (the S1 interface piece on stmt_post)
   gives every body. *)
Theorem for_keep_temp:
  !ctx func cx lctx RetQ cenv m source es atv v w b z cs.
    (!bs. stmt_frag_keep (\s. mem_bytes_at b z s.vs_memory = bs)
            ctx func cx lctx RetQ cenv m source es) /\
    val_wf atv v /\ b <= w /\ w + type_memory_size atv <= b + z ==>
    stmt_frag_keep (\s. val_in_memory atv v w s.vs_memory)
      ctx func cx lctx RetQ cenv m source es /\
    keep_stable (\s. val_in_memory atv v w s.vs_memory) cs b z
Proof
  rpt gen_tac >> strip_tac >>
  `!m1 m2. mem_bytes_at b z m2 = mem_bytes_at b z m1 /\
           val_in_memory atv v w m1 ==> val_in_memory atv v w m2` by
    (rpt strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
     qexistsl_tac [`type_memory_size atv`, `m1`] >> simp[] >>
     drule (cj 1 mem_bytes_at_agree_window) >> disch_then irule >> simp[]) >>
  conj_tac >~ [`keep_stable`] >- (simp[keep_stable_def] >> metis_tac[]) >>
  simp[stmt_frag_keep_def] >>
  map_every qx_gen_tac [`sa`, `sb`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `!bs. stmt_frag_keep _ _ _ _ _ _ _ _ _ _`
    (qspec_then `mem_bytes_at b z s0.vs_memory` mp_tac) >>
  simp[stmt_frag_keep_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >> simp[] >>
  strip_tac >> irule gas_outcome_conseq >> first_assum (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* A projection of one name's entries that two scope lists agree on
   gives the same projection of its lookup. *)
Theorem scope_projection_lookup_map[local]:
  !a b n f.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) b ==>
    OPTION_MAP f (lookup_scopes n a) = OPTION_MAP f (lookup_scopes n b)
Proof
  Induct >- (Cases >> simp[lookup_scopes_def]) >>
  rpt gen_tac >> Cases_on `b` >> simp[lookup_scopes_def] >> strip_tac >>
  Cases_on `FLOOKUP h n` >> Cases_on `FLOOKUP h' n` >> gvs[]
QED

(* The same, for a name bound below the top scope. *)
Theorem scope_projection_lookup_below[local]:
  !a sc0 rest0 n f e.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) (sc0 :: rest0) /\
    n NOTIN FDOM sc0 /\ lookup_scopes n rest0 = SOME e ==>
    ?sc rest e'. a = sc :: rest /\ lookup_scopes n rest = SOME e' /\
      lookup_scopes n a = SOME e' /\ f e' = f e
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >> gvs[] >>
  `FLOOKUP sc0 n = NONE` by gvs[flookup_thm] >>
  `FLOOKUP h n = NONE` by gvs[] >>
  drule scope_projection_lookup_map >> simp[] >>
  Cases_on `lookup_scopes n t` >> simp[lookup_scopes_def]
QED

(* A path read that succeeds reads its prefix. *)
Theorem evaluate_subscripts_append_prefix[local]:
  !p tv a sfx r.
    evaluate_subscripts tv a (p ++ sfx) = INL r ==>
    ?x. evaluate_subscripts tv a p = INL x
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED

(* Two values with the same sub-value at a path read the same below it:
   the types a read passes through depend on the path alone. *)
Theorem sum_case_id[local]:
  !X. (case X of INL vj => INL vj | INR err => INR err) = X
Proof
  Cases >> simp[]
QED

Theorem evaluate_subscripts_prefix_agree[local]:
  !p tv a b sfx x.
    evaluate_subscripts tv a p = INL x /\
    evaluate_subscripts tv b p = INL x ==>
    evaluate_subscripts tv a (p ++ sfx) = evaluate_subscripts tv b (p ++ sfx)
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def] >>
      Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
      rpt strip_tac >>
      Cases_on `array_index tv a i` >> Cases_on `array_index tv a' i` >>
      gvs[] >> metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def] >>
  Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
  rpt strip_tac >> BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

(* Hook for a place inside a local: the iterable's pointer is the place's,
   the root local's pointer bw (in its variable q) plus the byte offset k
   of the place's path in the root's type tv0 (the vv_place_ptr clause of
   the S1 interface piece on vv_post), and the body writes nothing
   containing the place.  Then the body keeps q and the value v the place
   held at entry.

   The root is bound below the body's top scope (the loop variable's), and
   its value is well typed after every run of the body (the caller's
   state_well_typed).

   v is read from the root's value (evaluate_subscripts), not through
   read_memory_path's fallback to popped history: memory keeps only a
   local's value (local_ptrs_rel), so a body's stmt_frag says nothing of
   a popped element's bytes.  The checker gives the premise: it rejects a
   pop at any depth of a For iterable (expr_writes_ok (\_. F) in
   well_typed_iterator, the checker piece), and with no pop the place
   reads the value. *)
Theorem for_keep_place:
  !ctx func cx ex inc RetQ bc ty stmts ei tops bindings env ret_ty env' arr_e
   et bd p root attrs rest sc0 rest0 entry v q z bw tv0 k atv.
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei /\
    supported_stmts tops bindings stmts /\
    type_stmts env ret_ty stmts = SOME env' /\
    well_typed_expr env arr_e /\ expr_type arr_e = ArrayT et bd /\
    expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
    root IN FDOM env.var_types /\
    stmts_writes_ok (\w. ~place_contains w p) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    ei.scopes = sc0 :: rest0 /\ root NOTIN FDOM sc0 /\
    lookup_scopes root rest0 = SOME entry /\ entry.type = tv0 /\
    well_formed_type_value tv0 /\
    evaluate_subscripts tv0 entry.value (MAP AttrSubscript attrs ++ rest) =
      INL v /\
    FLOOKUP bc.ce_vars root = SOME (PtrVar (Var q) z) /\
    mem_path_offset tv0 (MAP AttrSubscript attrs ++ rest) = SOME (k, atv) /\
    (!gs res ee e.
       eval_stmts cx stmts (ei with gas_obs := gs) = (res, ee) /\
       lookup_scopes root ee.scopes = SOME e ==>
       value_has_type e.type e.value) ==>
    stmt_frag_keep
      (\s. lookup_var q s = SOME bw /\
           val_in_memory atv v (w2n bw + k) s.vs_memory)
      ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_keep_def] >>
  map_every qx_gen_tac [`sa`, `sb`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def, gas_marked_exec_def] >>
  strip_tac >> qexists_tac `marks`
  >| [
      disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
      qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings` >>
      qabbrev_tac `ee = es_end with gas_obs := []` >>
      `eval_stmts cx stmts (ei with gas_obs := gs) = (res,ee)` by
        (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
         simp[Abbr `ee`]) >>
      qpat_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE std_ss [stmt_post_def]) >>
      `not_fresh_at sa q` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var q t = SOME bw` by metis_tac[] >>
      simp[] >>
      mp_tac (Q.INST [`es` |-> `ei with gas_obs := gs`, `es'` |-> `ee`]
      typed_stmts_place_frame) >>
      impl_tac >- simp[] >> strip_tac >>
      qmatch_asmsub_abbrev_tac `MAP (\sc. OPTION_MAP f (FLOOKUP sc root))` >>
      `?sc rest' e'. ee.scopes = sc :: rest' /\ lookup_scopes root rest' = SOME e' /\
      lookup_scopes root ee.scopes = SOME e' /\ f e' = f entry` by
      (irule scope_projection_lookup_below >> gvs[] >> metis_tac[]) >>
      fs[Abbr `f`] >>
      `FLOOKUP cenv''.ce_vars root = SOME (PtrVar (Var q) z)` by
      (qpat_x_assum `cenv_top_ext _ _ _` mp_tac >>
      simp[cenv_top_ext_def] >> strip_tac >>
      first_x_assum (qspec_then `root` mp_tac) >> CCONTR_TAC >> gvs[]) >>
      `local_ptrs_rel func cenv'' ee.scopes t` by
      gvs[stmt_state_rel_def, state_rel_def] >>
      pop_assum mp_tac >> simp[local_ptrs_rel_def] >>
      disch_then (qspecl_then [`root`, `e'`, `q`, `z`] mp_tac o CONJUNCT1) >>
      simp[] >> strip_tac >> gvs[] >>
      `value_has_type entry.type e'.value` by metis_tac[] >>
      drule evaluate_subscripts_append_prefix >> strip_tac >>
      `evaluate_subscripts entry.type e'.value (MAP AttrSubscript attrs ++ rest) =
        INL v` by
      metis_tac[evaluate_subscripts_prefix_agree] >>
      disj1_tac >> once_rewrite_tac[ADD_COMM] >>
      irule imm_typed_path_memory >> metis_tac[],
      disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >> simp[],
      disj2_tac >> metis_tac[]]
QED
