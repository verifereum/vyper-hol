(* The compiler's counter indexes non-external keys in declaration order. *)
Theory linkedFunctionIds
Ancestors
  compileUnit list arithmetic pair option

Theorem build_func_ids_mods_11:
  !mods n src1 tops1 vis1 mut1 nr1 rr1 f1 a1 d1 r1 b1
             src2 tops2 vis2 mut2 nr2 rr2 f2 a2 d2 r2 b2.
    MEM (src1,tops1) mods /\ MEM (src2,tops2) mods /\
    vis1 <> External /\ vis2 <> External /\
    MEM (FunctionDecl vis1 mut1 nr1 rr1 f1 a1 d1 r1 b1) tops1 /\
    MEM (FunctionDecl vis2 mut2 nr2 rr2 f2 a2 d2 r2 b2) tops2 /\
    build_func_ids_mods n mods (nsid_to_string (src1,f1)) =
    build_func_ids_mods n mods (nsid_to_string (src2,f2)) ==>
    nsid_to_string (src1,f1) = nsid_to_string (src2,f2)
Proof
  qabbrev_tac `names = \src top. case top of
    FunctionDecl vis _ _ _ name _ _ _ _ =>
      [if vis = External then NONE else SOME (nsid_to_string (src,name))]
    | _ => []` >>
  `!tops src. LENGTH (FLAT (MAP (names src) tops)) = count_function_decls tops` by
    (Induct >> simp[count_function_decls_def] >> gen_tac >> Cases_on `h` >>
     simp[count_function_decls_def, Abbr `names`]) >>
  `!xs ys (k:string) n. INDEX_FIND n ($= (SOME k)) (xs ++ ys) =
     case INDEX_FIND n ($= (SOME k)) xs of
       NONE => INDEX_FIND (n + LENGTH xs) ($= (SOME k)) ys
     | SOME hit => SOME hit` by
    (Induct >> simp[INDEX_FIND_def] >> rpt gen_tac >>
     Cases_on `SOME k = h` >> simp[INDEX_FIND_def] >>
     `LENGTH xs + SUC n = n + SUC (LENGTH xs)` by decide_tac >>
     asm_rewrite_tac[]) >>
  `!tops src n rest k.
     build_func_ids_src n src tops rest k =
     case INDEX_FIND n ($= (SOME k)) (FLAT (MAP (names src) tops)) of
       NONE => rest k
     | SOME (i,_) => i` by
    (Induct >> simp[build_func_ids_src_def, INDEX_FIND_def] >>
     rpt gen_tac >> Cases_on `h` >>
     simp[build_func_ids_src_def, INDEX_FIND_def, Abbr `names`, LET_THM,
          GSYM arithmeticTheory.ADD1] >>
     IF_CASES_TAC >> simp[] >>
     IF_CASES_TAC >> simp[]) >>
  qabbrev_tac `keys = \modules. FLAT
    (MAP (\(src,tops). FLAT (MAP (names src) tops)) modules)` >>
  `!modules n k.
    build_func_ids_mods n modules k =
      case INDEX_FIND n ($= (SOME k)) (keys modules) of
        NONE => 0
      | SOME (i,_) => i` by
    (Induct >> simp[build_func_ids_mods_def, Abbr `keys`, INDEX_FIND_def] >>
     qx_gen_tac `m` >> PairCases_on `m` >> rpt gen_tac >>
     simp[build_func_ids_mods_def] >>
     Cases_on `INDEX_FIND n ($= (SOME k)) (FLAT (MAP (names m0) m1))` >>
     simp[ELIM_UNCURRY]) >>
  `!src tops vis mut nr rr name args dflts ret stmts modules.
    MEM (src,tops) modules /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    MEM (SOME (nsid_to_string (src,name))) (keys modules)` by
    (rpt strip_tac >> simp[Abbr `keys`, MEM_FLAT, MEM_MAP] >>
     qexists_tac `FLAT (MAP (names src) tops)` >>
     conj_tac >- (qexists_tac `(src,tops)` >> simp[]) >>
     simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `names src (FunctionDecl vis mut nr rr name args dflts ret stmts)` >>
     conj_tac >-
       (qexists_tac `FunctionDecl vis mut nr rr name args dflts ret stmts` >> simp[]) >>
     simp[Abbr `names`]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `k1 = nsid_to_string (src1,f1)` >>
  qabbrev_tac `k2 = nsid_to_string (src2,f2)` >>
  `MEM (SOME k1) (keys mods) /\ MEM (SOME k2) (keys mods)` by
    (simp[Abbr `k1`, Abbr `k2`] >>
     qpat_assum `!src tops vis mut nr rr name args dflts ret stmts modules. _`
       (fn th => mp_tac (Q.SPECL [`src1`,`tops1`,`vis1`,`mut1`,`nr1`,`rr1`,
                    `f1`,`a1`,`d1`,`r1`,`b1`,`mods`] th) >>
                 mp_tac (Q.SPECL [`src2`,`tops2`,`vis2`,`mut2`,`nr2`,`rr2`,
                    `f2`,`a2`,`d2`,`r2`,`b2`,`mods`] th)) >>
     simp[]) >>
  `!k i. INDEX_OF (SOME k) (keys mods) = SOME i ==>
    build_func_ids_mods n mods k = i + n` by
    (rpt gen_tac >>
     `INDEX_FIND n ($= (SOME k)) (keys mods) =
        OPTION_MAP (\(j,x). (j+n,x)) (INDEX_FIND 0 ($= (SOME k)) (keys mods))` by
       irule INDEX_FIND_add >>
     simp[INDEX_OF_def] >>
     Cases_on `INDEX_FIND 0 ($= (SOME k)) (keys mods)` >>
     simp[] >> PairCases_on `x` >> simp[]) >>
  Cases_on `INDEX_OF (SOME k1) (keys mods)`
  >- fs[INDEX_OF_eq_NONE] >>
  Cases_on `INDEX_OF (SOME k2) (keys mods)`
  >- fs[INDEX_OF_eq_NONE] >>
  rename1 `INDEX_OF (SOME k1) (keys mods) = SOME i1` >>
  rename1 `INDEX_OF (SOME k2) (keys mods) = SOME i2` >>
  `build_func_ids_mods n mods k1 = i1+n /\
   build_func_ids_mods n mods k2 = i2+n` by
    (conj_tac >> qpat_assum `!k i. INDEX_OF _ _ = SOME i ==> _` irule >> simp[]) >>
  `i1 = i2` by
    (qpat_x_assum `build_func_ids_mods n mods k1 = build_func_ids_mods n mods k2`
       mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  fs[INDEX_OF_eq_SOME] >> gvs[]
QED
