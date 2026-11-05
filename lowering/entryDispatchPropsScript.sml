(*
 * Entry dispatch: the selector the source picks (#639)
 *
 * TOP-LEVEL:
 *   calldata_encodes_hits_selector — calldata that encodes a call hits the
 *     selector compute_selector gives the function
 *   linear_dispatch_selects_function — with distinct selectors, linear
 *     dispatch over the compiler's selector table picks the entry of the
 *     external function lookup_function selects
 *   linear_selectors_lt — every selector in the table is a 4-byte number,
 *     the side condition of compile_selector_dispatch_linear_correct
 *   linear_dispatch_target_fallback — calldata shorter than a selector, or
 *     hitting none in the table, goes to the fallback label
 *   fallback_package_lookup — the fallback the compiler packages is the
 *     function lookup_function selects for "__default__", payable exactly
 *     when the source's is (send_call_value's check)
 *   compile_fallback_body_entry — the fallback's entry part: with a
 *     nonpayable fallback, the CALLVALUE check falls through when no value
 *     is sent and reverts otherwise; then the guarded body
 *   payable_check_frag — that CALLVALUE check on its own
 *
 * Helpers: function_selector_length, calldata_method_id_append,
 *   calldata_method_id_lt, linear_dispatch_target_distinct,
 *   build_selectors_mem, lookup_function_external_mem,
 *   lookup_function_default
 *)
Theory entryDispatchProps
Ancestors
  list rich_list words
  moduleLoweringProps selectorDispatch compileVyper constSubst vyperInterpreter
  vyperTypeBytesCrypto contractABI moduleLowering compileEnv loweringStateRelDefs fragExec
  emitHelper emitHelperProps venomState vyperTypeContract vyperGetter
Libs
  wordsLib

(* ===== The 4-byte selector ===== *)

Theorem function_selector_length:
  !name args. LENGTH (function_selector name args) = 4
Proof
  simp[function_selector_def, LENGTH_TAKE_EQ, LENGTH_Keccak_256_w64]
QED

Theorem calldata_method_id_append:
  !bs rest. LENGTH bs = 4 ==>
            calldata_method_id (bs ++ rest) = calldata_method_id bs
Proof
  rw[calldata_method_id_def, EL_APPEND1]
QED

Theorem calldata_method_id_lt:
  !cd. w2n (calldata_method_id cd) < 2 ** 32
Proof
  rw[calldata_method_id_def] >>
  `!x:word8. w2n x < 256` by
    (gen_tac >> assume_tac (INST_TYPE [alpha |-> ``:8``] w2n_lt) >> fs[]) >>
  qabbrev_tac `X = 16777216 * w2n (HD cd) +
                   (65536 * w2n (EL 1 cd) + (w2n (EL 3 cd) + 256 * w2n (EL 2 cd)))` >>
  `X < 4294967296` by
    (unabbrev_all_tac >> first_assum (qspec_then `HD cd` assume_tac) >>
     first_assum (qspec_then `EL 1 cd` assume_tac) >>
     first_assum (qspec_then `EL 2 cd` assume_tac) >>
     first_x_assum (qspec_then `EL 3 cd` assume_tac) >> fs[]) >>
  `X < dimword (:256)` by fs[dimword_def] >> simp[]
QED

(* Calldata that encodes a call starts with the function's selector. *)
Theorem calldata_encodes_hits_selector:
  !tenv fname tys vals cd.
    calldata_encodes tenv fname tys vals cd ==>
    calldata_hits_selector cd
      (FST (compute_selector tenv fname (TAKE (LENGTH vals) tys)))
Proof
  rw[calldata_encodes_def, calldata_hits_selector_def,
     compute_selector_def] >>
  simp[calldata_method_id_append, function_selector_length]
QED

(* ===== The selector table ===== *)

(* With distinct selectors, the first selector the calldata hits is the
   one it hits. *)
Theorem linear_dispatch_target_distinct:
  !sels cd fb sel lbl.
    ALL_DISTINCT (MAP FST sels) /\ MEM (sel, lbl) sels /\
    calldata_hits_selector cd sel ==>
    linear_dispatch_target cd sels fb = lbl
Proof
  Induct >- simp[] >> Cases >>
  rw[linear_dispatch_target_def] >> gvs[calldata_hits_selector_def] >>
  fs[MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem build_selectors_mem:
  !tenv exts mut nr rr name args dflts ret body.
    MEM (mut, nr, rr, name, args, dflts, ret, body) exts ==>
    MEM (compute_selector tenv name (MAP SND args)) (build_selectors tenv exts)
Proof
  gen_tac >> Induct >> simp[] >> PairCases >>
  rw[build_selectors_def] >> metis_tac[]
QED

(* Inverse provenance does not require selector uniqueness. *)
Theorem build_selectors_mem_inv:
  !tenv exts sel lbl htz.
    MEM (sel, lbl, htz) (build_selectors tenv exts) ==>
    ?mut nr rr name args dflts ret body.
      MEM (mut, nr, rr, name, args, dflts, ret, body) exts /\
      compute_selector tenv name (MAP SND args) = (sel, lbl, htz)
Proof
  gen_tac >> Induct >- simp[build_selectors_def] >>
  PairCases >> rw[build_selectors_def] >> metis_tac[]
QED

Theorem linear_selectors_lt:
  !tenv exts.
    EVERY (\(sel, lbl). sel < 2 ** 32)
      (MAP (\(sel, lbl, _). (sel, lbl)) (build_selectors tenv exts))
Proof
  gen_tac >> Induct >> simp[build_selectors_def] >> PairCases >>
  simp[build_selectors_def, compute_selector_def] >>
  assume_tac calldata_method_id_lt >> fs[]
QED

(* An external function lookup_function selects is in the compiler's table
   of external functions, unless a public getter shadows it or it is the
   fallback. *)
Theorem lookup_function_external_mem:
  !tops src name mut nr args dflts ret body.
    lookup_function src name External tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    name <> "__default__" /\
    (!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops) /\
    (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops) ==>
    ?rr. MEM (subst_consts_fn (module_consts_env tops [])
               (mut, nr, rr, name, args, dflts, ret, body))
           (FST (classify_functions tops))
Proof
  `!tops src name mut nr args dflts ret body.
     lookup_function src name External tops =
       SOME (mut,nr,args,dflts,ret,body) /\
     name <> "__default__" /\
     (!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops) /\
     (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops) ==>
     ?rr. MEM (mut,nr,rr,name,args,dflts,ret,body)
       (FST (FOLDR classify_function ([],[],NONE,NONE) tops))`
    suffices_by
      (rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
       simp[classify_functions_def] >> pairarg_tac >> gvs[] >>
       simp[MEM_MAP] >> metis_tac[]) >>
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >>
  `?a1 a2 a3 a4. FOLDR classify_function ([],[],NONE,NONE) tops =
                 (a1,a2,a3,a4)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `h` >>
  gvs[lookup_function_def, classify_function_def, AllCaseEqs()] >>
  simp[classify_function_def, AllCaseEqs(), EXISTS_OR_THM]
  >>~- ([`case vis of External => _ | Internal => _ | Deploy => _`],
    Cases_on `vis` >> simp[] >> rw[] >> gvs[] >> metis_tac[])
  >>~- ([`lookup_function _ _ _ (VariableDecl vis _ _ _ _ :: _) = _`],
    Cases_on `vis` >> gvs[lookup_function_def] >> rw[] >> gvs[] >> metis_tac[])
  >>~- ([`lookup_function _ _ _ (HashMapDecl vis _ _ _ _ _ :: _) = _`],
    Cases_on `vis` >> gvs[lookup_function_def] >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

(* Dispatch depends only on membership and preserved ABI metadata. *)
Theorem linear_dispatch_selects_entry:
  !tenv exts mut nr rr name args dflts ret body vals cd fb.
    MEM (mut,nr,rr,name,args,dflts,ret,body) exts /\
    ALL_DISTINCT (MAP FST (build_selectors tenv exts)) /\
    calldata_encodes tenv name (MAP SND args) vals cd /\
    LENGTH vals = LENGTH args ==>
    linear_dispatch_target cd
      (MAP (\(sel,lbl,_). (sel,lbl)) (build_selectors tenv exts))
      fb = "fn_" ++ name
Proof
  rpt strip_tac >>
  drule build_selectors_mem >>
  disch_then (qspec_then `tenv` assume_tac) >>
  drule calldata_encodes_hits_selector >>
  `TAKE (LENGTH vals) (MAP SND args) = MAP SND args` by
    simp[TAKE_LENGTH_ID_rwt] >>
  simp[] >> strip_tac >>
  irule linear_dispatch_target_distinct >> conj_tac
  >- (`!l:(num # string # bool) list.
         MAP FST (MAP (\(sel,lbl,_). (sel,lbl)) l) = MAP FST l` by
        (Induct >> simp[] >> PairCases >> simp[]) >>
      simp[]) >>
  qexists_tac `FST (compute_selector tenv name (MAP SND args))` >>
  simp[MEM_MAP] >>
  qexists_tac `compute_selector tenv name (MAP SND args)` >>
  simp[compute_selector_def]
QED

(* Linear dispatch over the compiler's selector table picks the entry of
   the external function the source selects for calldata that encodes a
   call to it. *)
Theorem linear_dispatch_selects_function:
  !tops name mut nr args dflts ret body vals cd fb.
    lookup_function NONE name External tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    name <> "__default__" /\
    (!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops) /\
    (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops) /\
    ALL_DISTINCT
      (MAP FST (build_selectors (type_env tops)
                  (FST (classify_functions tops)))) /\
    calldata_encodes (type_env tops) name (MAP SND args) vals cd /\
    LENGTH vals = LENGTH args ==>
    linear_dispatch_target cd
      (MAP (\(sel, lbl, _). (sel, lbl))
         (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb = "fn_" ++ name
Proof
  rpt strip_tac >>
  drule_all lookup_function_external_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  drule_all linear_dispatch_selects_entry >> simp[]
QED

(* A declaration not exposing this name cannot intercept its lookup. *)
Theorem lookup_function_external_skip:
  !top name tops src.
    ~MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) top) ==>
    lookup_function src name External (top::tops) =
    lookup_function src name External tops
Proof
  Cases >> simp[external_name_keys_toplevel_def, lookup_function_def] >>
  rpt gen_tac
  >>~- ([`FunctionDecl vis _ _ _ _ _ _ _ _`],
    Cases_on `vis` >> simp[external_name_keys_toplevel_def, lookup_function_def])
  >>~- ([`VariableDecl vis _ _ _ _`],
    Cases_on `vis` >> simp[external_name_keys_toplevel_def, lookup_function_def])
  >>~- ([`HashMapDecl vis _ _ _ _ _`],
    Cases_on `vis` >> simp[external_name_keys_toplevel_def, lookup_function_def]) >>
  metis_tac[]
QED

Theorem lookup_function_external_unique_decl:
  !tops top name result.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
    MEM top tops /\
    MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) top) /\
    lookup_function NONE name External [top] = SOME result ==>
    lookup_function NONE name External tops = SOME result
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `top = h` >> gvs[]
  >- (Cases_on `h` >>
      gvs[external_name_keys_toplevel_def, lookup_function_def]
      >>~- ([`FunctionDecl vis _ _ _ _ _ _ _ _`],
        Cases_on `vis` >> gvs[external_name_keys_toplevel_def, lookup_function_def])
      >>~- ([`VariableDecl vis _ _ _ _`],
        Cases_on `vis` >> gvs[external_name_keys_toplevel_def, lookup_function_def])
      >>~- ([`HashMapDecl vis _ _ _ _ _`],
        Cases_on `vis` >> gvs[external_name_keys_toplevel_def, lookup_function_def])) >>
  `~MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) h)` by
    (qpat_x_assum `!top name result. _` kall_tac >>
     qpat_x_assum `lookup_function _ _ _ _ = _` kall_tac >>
     gvs[ALL_DISTINCT_APPEND] >>
     `MEM (NONE,name) (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
       (simp[MEM_FLAT, MEM_MAP] >>
        qexists_tac `external_name_keys_toplevel (NONE:num option) top` >>
        conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]) >>
     metis_tac[]) >>
  simp[lookup_function_external_skip] >> first_x_assum irule >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem public_getter_lookup_singleton:
  !top mut nr rr name args dflts ret body.
    public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,body) ==>
    MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) top) /\
    lookup_function NONE name External [top] =
      SOME (mut,nr,args,dflts,ret,body)
Proof
  Cases >> simp[public_getter_def] >> rpt gen_tac
  >>~- ([`VariableDecl vis _ id typ _`],
    Cases_on `vis` >> simp[public_getter_def] >>
    Cases_on `is_ArrayT typ`
    >- (qmatch_goalsub_abbrev_tac `getter flag ne kt vt` >>
        qabbrev_tac `g = (getter flag ne kt vt : function_mutability # bool # (string # type) list # expr list # type # stmt list)` >> PairCases_on `g` >>
        gvs[markerTheory.Abbrev_def] >>
        qpat_x_assum `(_,_,_,_,_,_) = getter _ _ _ _` (assume_tac o SYM) >>
        qpat_assum `getter _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
        strip_tac >>
        gvs[external_name_keys_toplevel_def, lookup_function_def]) >>
    simp[] >> strip_tac >> gvs[external_name_keys_toplevel_def, lookup_function_def])
  >>~- ([`HashMapDecl vis _ id kt vt _`],
    Cases_on `vis` >> simp[public_getter_def] >>
    qmatch_goalsub_abbrev_tac `getter flag ne key value` >>
    qabbrev_tac `g = (getter flag ne key value : function_mutability # bool # (string # type) list # expr list # type # stmt list)` >> PairCases_on `g` >>
    gvs[markerTheory.Abbrev_def] >>
        qpat_x_assum `(_,_,_,_,_,_) = getter _ _ _ _` (assume_tac o SYM) >>
        qpat_assum `getter _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
        strip_tac >>
    gvs[external_name_keys_toplevel_def, lookup_function_def])
QED

Theorem public_getter_lookup_agrees:
  !tops mut nr rr name args dflts ret body.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
    MEM (mut,nr,rr,name,args,dflts,ret,body) (public_getters tops) ==>
    lookup_function NONE name External tops =
      SOME (mut,nr,args,dflts,ret,body)
Proof
  rw[MEM_public_getters] >>
  drule public_getter_lookup_singleton >> strip_tac >>
  irule lookup_function_external_unique_decl >> metis_tac[]
QED

Theorem public_getter_classified_mem:
  !tops g.
    MEM g (public_getters tops) ==>
    MEM (subst_consts_fn (module_consts_env tops []) g)
      (FST (classify_functions tops))
Proof
  rpt strip_tac >> simp[classify_functions_def] >> pairarg_tac >>
  simp[MEM_MAP] >> metis_tac[MEM_APPEND]
QED

(* Source lookup and the selector dispatcher agree on the synthesized getter.
   The classified body/defaults are normalized, while ABI metadata is unchanged. *)
Theorem public_getter_dispatch_agrees:
  !tops mut nr rr name args dflts ret body vals cd fb.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
    MEM (mut,nr,rr,name,args,dflts,ret,body) (public_getters tops) /\
    ALL_DISTINCT
      (MAP FST (build_selectors (type_env tops)
                  (FST (classify_functions tops)))) /\
    calldata_encodes (type_env tops) name (MAP SND args) vals cd /\
    LENGTH vals = LENGTH args ==>
    lookup_function NONE name External tops =
      SOME (mut,nr,args,dflts,ret,body) /\
    MEM (subst_consts_fn (module_consts_env tops [])
           (mut,nr,rr,name,args,dflts,ret,body))
      (FST (classify_functions tops)) /\
    linear_dispatch_target cd
      (MAP (\(sel,lbl,_). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb = "fn_" ++ name
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule public_getter_lookup_agrees >> metis_tac[]) >>
  conj_asm1_tac >- (irule public_getter_classified_mem >> simp[]) >>
  gvs[subst_consts_fn_def] >>
  drule_all linear_dispatch_selects_entry >> simp[]
QED

(* ===== The fallback ===== *)

(* Calldata shorter than a selector, or hitting none of the table's
   selectors, goes to the fallback. *)
Theorem linear_dispatch_target_fallback:
  !sels cd fb.
    LENGTH cd < 4 \/
    (!sel lbl. MEM (sel, lbl) sels ==> ~calldata_hits_selector cd sel) ==>
    linear_dispatch_target cd sels fb = fb
Proof
  rpt strip_tac >- metis_tac[linear_dispatch_target_short] >>
  pop_assum mp_tac >> qid_spec_tac `sels` >>
  Induct >- simp[linear_dispatch_target_def] >> Cases >>
  rw[linear_dispatch_target_def] >> metis_tac[]
QED

(* lookup_function selects for "__default__" the External function the
   compiler classifies as the fallback, unless a public getter of that
   name shadows it. *)
Theorem lookup_function_default:
  !tops src.
    (!nr' mut typ x. ~MEM (VariableDecl (Public nr') mut "__default__" typ x) tops) /\
    (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b "__default__" kt vt x) tops) ==>
    case lookup_function src "__default__" External tops of
      NONE => FST (SND (SND (classify_functions tops))) = NONE
    | SOME (mut, nr, args, dflts, ret, fbody) =>
        ?rr. FST (SND (SND (classify_functions tops))) =
          SOME (subst_consts_fn (module_consts_env tops [])
            (mut, nr, rr, "__default__", args, dflts, ret, fbody))
Proof
  `!tops src.
     (!nr' mut typ x. ~MEM (VariableDecl (Public nr') mut "__default__" typ x) tops) /\
     (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b "__default__" kt vt x) tops) ==>
     case lookup_function src "__default__" External tops of
       NONE => FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) = NONE
     | SOME (mut,nr,args,dflts,ret,rawbody) =>
       ?rr. FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
         SOME (mut,nr,rr,"__default__",args,dflts,ret,rawbody)`
    suffices_by
      (rpt strip_tac >> first_x_assum drule_all >>
       disch_then (qspec_then `src` mp_tac) >>
       simp[classify_functions_def] >> pairarg_tac >>
       Cases_on `lookup_function src "__default__" External tops`
       >- simp[] >>
       PairCases_on `x` >> simp[] >> metis_tac[]) >>
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >>
  `?a1 a2 a3 a4. FOLDR classify_function ([],[],NONE,NONE) tops =
                 (a1,a2,a3,a4)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `h` >> gvs[lookup_function_def, classify_function_def]
  >>~- ([`case vis of External => _ | Internal => _ | Deploy => _`],
    Cases_on `vis` >> gvs[] >> rw[] >> gvs[] >> metis_tac[])
  >>~- ([`lookup_function _ _ _ (VariableDecl vis _ _ _ _ :: _)`],
    Cases_on `vis` >> gvs[lookup_function_def] >> rw[] >> gvs[] >> metis_tac[])
  >>~- ([`lookup_function _ _ _ (HashMapDecl vis _ _ _ _ _ :: _)`],
    Cases_on `vis` >> gvs[lookup_function_def] >> rw[] >> gvs[] >> metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED

(* The fallback the runtime lowering packages (lower_vyper_runtime_unit)
   is the function lookup_function selects for "__default__", and the
   package's payable flag is the source mutability being Payable, the
   condition send_call_value checks before running the body. *)
Theorem fallback_package_lookup:
  !tops src target ut nkm exts ints fb ctor.
    classify_functions tops = (exts, ints, fb, ctor) /\
    (!nr' mut typ x. ~MEM (VariableDecl (Public nr') mut "__default__" typ x) tops) /\
    (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b "__default__" kt vt x) tops) ==>
    case set_fallback_package_target target
           (package_fallback_fn tops ut nkm fb) of
      NONE => vyperInterpreter$lookup_function src "__default__" External tops = NONE
    | SOME (cenv, is_payable, nr, nkey, ut', iv, fbody, rt) =>
        ?mut args dflts ret rawbody.
          vyperInterpreter$lookup_function src "__default__" External tops =
            SOME (mut, nr, args, dflts, ret, rawbody) /\
          fbody = subst_consts_stmts (module_consts_env tops []) rawbody /\
          is_payable = (mut = Payable)
Proof
  rpt strip_tac >> drule_all lookup_function_default >>
  disch_then (qspec_then `src` mp_tac) >>
  Cases_on `lookup_function src "__default__" External tops`
  >- (simp[] >> strip_tac >> gvs[] >>
      simp[package_fallback_fn_def, set_fallback_package_target_def]) >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  simp[package_fallback_fn_def, set_fallback_package_target_def]
QED

(* The entry part of the fallback body.  A payable fallback goes straight
   to the guarded body.  A nonpayable one first runs CALLVALUE, ISZERO,
   ASSERT: it reaches the guarded body, having changed only fresh
   variables, when no value is sent, and reverts when some is. *)
Theorem fallback_check_prefix_structure[local]:
  emit_op CALLVALUE [] st0 = (cv, st1) /\
  emit_op ISZERO [cv] st1 = (nv, st2) /\
  emit_void ASSERT [nv] st2 = ((), st3) ==>
  st3.cs_blocks = st0.cs_blocks /\
  st3.cs_current_bb = st0.cs_current_bb /\
  isPREFIX st0.cs_current_insts st3.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st0 st3)
Proof
  strip_tac >>
  imp_res_tac exprLoweringPropsTheory.emit_op_extends >>
  drule exprLoweringPropsTheory.emit_void_extends >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[exprLoweringPropsTheory.same_blocks_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem fallback_check_run_frame[local]:
  emit_op CALLVALUE [] st0 = (cv, st1) /\
  emit_op ISZERO [cv] st1 = (nv, st2) /\
  emit_void ASSERT [nv] st2 = ((), st3) /\
  fresh_vars_wrt st0 s0 /\
  run_inst_seq (emitted_insts st0 st3) s0 = OK t ==>
  vars_pc_only s0 t /\
  (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s0)
Proof
  strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts st0 st3 =
    emitted_insts st0 st1 ++ emitted_insts st1 st2 ++
    emitted_insts st2 st3` by
    simp[exprLoweringPropsTheory.emitted_insts_def, APPEND_ASSOC,
         DROP_LENGTH_APPEND] >>
  gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[venomInstTheory.mk_inst_def] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_read0_def, venomExecSemanticsTheory.exec_gas_def,
       venomExecSemanticsTheory.exec_pure1_def,
       venomInstTheory.mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `s0.vs_call_ctx.cc_callvalue = 0w` >>
  simp[venomExecSemanticsTheory.bool_to_word_def] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- simp[vars_pc_only_def] >>
  rpt strip_tac >>
  gvs[not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The payable check (CALLVALUE is zero) on its own, as
   compile_payable_check_ok_or_revert has it, for the fallback and for
   compile_entry_checks. *)
Theorem payable_check_frag:
  emit_op CALLVALUE [] st0 = (cv, st1) /\
  emit_op ISZERO [cv] st1 = (nv, st2) /\
  emit_void ASSERT [nv] st2 = ((), st3) /\
  fresh_vars_wrt st0 s0 ==>
  frag_exec ctx st0 st3 (\s. s = s0)
    (\t. vars_pc_only s0 t /\ fresh_vars_wrt st3 t /\
         (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s0) /\
         s0.vs_call_ctx.cc_callvalue = 0w)
    (\r. ?t. r = Abort Revert_abort t /\
              s0.vs_call_ctx.cc_callvalue <> 0w)
Proof
  strip_tac >>
  drule_all fallback_check_prefix_structure >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all compile_payable_check_ok_or_revert >> strip_tac
  >- (disj1_tac >> goal_assum $ drule_at Any >>
      drule_all fallback_check_run_frame >> strip_tac >>
      simp[vars_pc_only_inst_idx, control_moves_keep_vars]) >>
  disj2_tac >> goal_assum $ drule_at Any >> simp[]
QED

Theorem compile_fallback_body_entry:
  !cenv is_payable nr nkey ut iv fbody rt st st'.
    compile_fallback_body cenv is_payable nr nkey ut iv fbody rt st =
      ((), st') ==>
    ?sm. compile_guarded_body cenv nr nkey ut iv fbody rt sm = ((), st') /\
         !ctx s0.
           fresh_vars_wrt st s0 ==>
           frag_exec ctx st sm (\s. s = s0)
             (\t. vars_pc_only s0 t /\ fresh_vars_wrt sm t /\
                  (!x. not_fresh_at st x ==>
                       lookup_var x t = lookup_var x s0) /\
                  (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w))
             (\r. ?t. r = Abort Revert_abort t /\ ~is_payable /\
                      s0.vs_call_ctx.cc_callvalue <> 0w)
Proof
  rpt gen_tac >> Cases_on `is_payable`
  >- (simp[compile_fallback_body_def, comp_ignore_bind_def,
           comp_bind_def, comp_return_def] >> strip_tac >> qexists_tac `st` >>
      simp[] >> rpt strip_tac >> irule frag_exec_refl >>
      simp[vars_pc_only_refl]) >>
  simp[compile_fallback_body_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `emit_op CALLVALUE [] st` >>
  rename1 `emit_op CALLVALUE [] st = (cv, st1)` >> simp[] >>
  Cases_on `emit_op ISZERO [cv] st1` >>
  rename1 `emit_op ISZERO [cv] st1 = (nv, st2)` >> simp[] >>
  Cases_on `emit_void ASSERT [nv] st2` >>
  rename1 `emit_void ASSERT [nv] st2 = (u, st3)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  goal_assum $ drule_at Any >> rpt strip_tac >>
  irule payable_check_frag >> goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >> simp[]
QED
