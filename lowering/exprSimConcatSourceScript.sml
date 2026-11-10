(*
 * Source side of concat(...): with the typing bound
 * SUM (MAP bytelike_type_bound ts) <= n, operands of their static types
 * concatenate without the "concat bound" error, to the flattened payload.
 *
 * TOP-LEVEL:
 *   evaluate_concat_typed_bytes  — all-Bytes operands
 *   evaluate_concat_typed_string — all-String operands
 *)
Theory exprSimConcatSource
Ancestors
  vyperTyping vyperTypeSystem vyperValueOperation vyperValue vyperAST
  list rich_list arithmetic

Theorem evaluate_concat_loop_bytes_flat:
  !bss n b1 sa ba.
    LENGTH (FLAT (b1 :: REVERSE ba ++ bss)) <= n ==>
    evaluate_concat_loop n (BytesV b1) sa ba (MAP BytesV bss) =
    INL (BytesV (FLAT (b1 :: REVERSE ba ++ bss)))
Proof
  Induct >>
  simp[evaluate_concat_loop_def, LET_THM, compatible_bound_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`n`, `b1`, `sa`, `h::ba`] mp_tac) >>
  simp[]
QED

Theorem evaluate_concat_loop_string_flat:
  !ss n s1 sa ba.
    LENGTH (FLAT (s1 :: REVERSE sa ++ ss)) <= n ==>
    evaluate_concat_loop n (StringV s1) sa ba (MAP StringV ss) =
    INL (StringV (FLAT (s1 :: REVERSE sa ++ ss)))
Proof
  Induct >>
  simp[evaluate_concat_loop_def, LET_THM, compatible_bound_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`n`, `s1`, `h::sa`, `ba`] mp_tac) >>
  simp[]
QED

(* A Bytes operand's value is within its static bound. *)
Theorem typed_bytes_operands:
  !ts vs.
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts /\
    LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
      ts vs ==>
    ?bss. vs = MAP BytesV bss /\
          LENGTH (FLAT bss) <= SUM (MAP bytelike_type_bound ts)
Proof
  Induct >> simp[PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  rename1 `evaluate_type _ (BaseT (BytesT bd)) = SOME tv` >>
  rename1 `value_has_type tv v` >>
  Cases_on `bd` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `MAP BytesV bss` >> rename1 `BytesV bs` >>
  qexists_tac `bs::bss` >> simp[bytelike_type_bound_def, bound_length_def]
QED

Theorem typed_string_operands:
  !ts vs.
    EVERY (\t. ?m. t = BaseT (StringT m)) ts /\
    LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
      ts vs ==>
    ?ss. vs = MAP StringV ss /\
         LENGTH (FLAT ss) <= SUM (MAP bytelike_type_bound ts)
Proof
  Induct >> simp[PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  rename1 `value_has_type tv v` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `MAP StringV ss` >> rename1 `StringV s` >>
  qexists_tac `s::ss` >> simp[bytelike_type_bound_def]
QED

Theorem evaluate_concat_typed_bytes:
  EVERY (\t. ?bd. t = BaseT (BytesT bd)) ts /\ 2 <= LENGTH ts /\
  SUM (MAP bytelike_type_bound ts) <= n /\
  LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
    ts vs ==>
  ?bss. vs = MAP BytesV bss /\ LENGTH (FLAT bss) <= n /\
        evaluate_concat n vs = INL (BytesV (FLAT bss))
Proof
  strip_tac >> drule_all typed_bytes_operands >> strip_tac >>
  qexists_tac `bss` >> simp[] >>
  `LENGTH bss = LENGTH ts` by
    (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `?x1 x2 rest. bss = x1::x2::rest` by
    (Cases_on `bss` >> fs[] >> rename1 `LENGTH tl` >> Cases_on `tl` >> fs[]) >>
  qpat_x_assum `bss = _` SUBST_ALL_TAC >>
  simp[evaluate_concat_def, init_concat_output_def] >>
  qspecl_then [`x2::rest`, `n`, `x1`, `[]`, `[]`] mp_tac evaluate_concat_loop_bytes_flat >>
  simp[] >> fs[]
QED

Theorem evaluate_concat_typed_string:
  EVERY (\t. ?m. t = BaseT (StringT m)) ts /\ 2 <= LENGTH ts /\
  SUM (MAP bytelike_type_bound ts) <= n /\
  LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
    ts vs ==>
  ?ss. vs = MAP StringV ss /\ LENGTH (FLAT ss) <= n /\
       evaluate_concat n vs = INL (StringV (FLAT ss))
Proof
  strip_tac >> drule_all typed_string_operands >> strip_tac >>
  qexists_tac `ss` >> simp[] >>
  `LENGTH ss = LENGTH ts` by
    (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `?x1 x2 rest. ss = x1::x2::rest` by
    (Cases_on `ss` >> fs[] >> rename1 `LENGTH tl` >> Cases_on `tl` >> fs[]) >>
  qpat_x_assum `ss = _` SUBST_ALL_TAC >>
  simp[evaluate_concat_def, init_concat_output_def] >>
  qspecl_then [`x2::rest`, `n`, `x1`, `[]`, `[]`] mp_tac evaluate_concat_loop_string_flat >>
  simp[] >> fs[]
QED
