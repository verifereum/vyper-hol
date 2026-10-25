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
 *
 * Helpers: function_selector_length, calldata_method_id_append,
 *   calldata_method_id_lt, linear_dispatch_target_distinct,
 *   build_selectors_mem, lookup_function_external_mem
 *)
Theory entryDispatchProps
Ancestors
  list rich_list words
  moduleLoweringProps selectorDispatch compileVyper vyperInterpreter
  vyperTypeBytesCrypto contractABI
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
    (!mut' typ x. ~MEM (VariableDecl Public mut' name typ x) tops) /\
    (!b kt vt x. ~MEM (HashMapDecl Public b name kt vt x) tops) ==>
    ?rr. MEM (mut, nr, rr, name, args, dflts, ret, body)
           (FST (classify_functions tops))
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> fs[classify_functions_def] >>
  `?a1 a2 a3 a4. FOLDR classify_function ([],[],NONE,NONE) tops =
                 (a1,a2,a3,a4)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  fs[] >> Cases_on `h` >>
  TRY (qmatch_goalsub_rename_tac `FunctionDecl vis _ _ _ _ _ _ _ _` >>
       Cases_on `vis`) >>
  TRY (qmatch_goalsub_rename_tac `VariableDecl vis _ _ _ _` >>
       Cases_on `vis`) >>
  TRY (qmatch_goalsub_rename_tac `HashMapDecl vis _ _ _ _ _` >>
       Cases_on `vis`) >>
  gvs[lookup_function_def, classify_function_def] >> rw[] >> gvs[] >>
  TRY (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> rw[]) >>
  metis_tac[]
QED

(* Linear dispatch over the compiler's selector table picks the entry of
   the external function the source selects for calldata that encodes a
   call to it. *)
Theorem linear_dispatch_selects_function:
  !tops name mut nr args dflts ret body vals cd fb.
    lookup_function NONE name External tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    name <> "__default__" /\
    (!mut' typ x. ~MEM (VariableDecl Public mut' name typ x) tops) /\
    (!b kt vt x. ~MEM (HashMapDecl Public b name kt vt x) tops) /\
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
  drule build_selectors_mem >>
  disch_then (qspec_then `type_env tops` assume_tac) >>
  drule calldata_encodes_hits_selector >>
  `TAKE (LENGTH vals) (MAP SND args) = MAP SND args` by
    simp[TAKE_LENGTH_ID_rwt] >>
  simp[] >> strip_tac >>
  irule linear_dispatch_target_distinct >> conj_tac
  >- (`!l:(num # string # bool) list.
         MAP FST (MAP (\(sel,lbl,_). (sel,lbl)) l) = MAP FST l` by
        (Induct >> simp[] >> PairCases >> simp[]) >>
      simp[]) >>
  qexists_tac `FST (compute_selector (type_env tops) name (MAP SND args))` >>
  simp[MEM_MAP] >>
  qexists_tac `compute_selector (type_env tops) name (MAP SND args)` >>
  simp[compute_selector_def]
QED
