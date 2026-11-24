(* At an in-range index, read the extended path in the actual covered row. *)
Theory bodyArrayMemoryDynamicChildMods
Ancestors
  exprSimProps vyperPlaceResultTyping

Theorem array_memory_dynamic_child_mods:
  read_result cx (PlaceR (MemoryPlace id path)) fin =
    (INL (ArrayV (DynArrayV vs)),fin) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  w2n a = w2n B + j /\
  mem_path_offset entry.type path = SOME (j,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
  lookup_var root u = SOME B /\
  ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
  (!r k t. (?v0. evaluate_subscripts initial.type initial.value r = INL v0) /\
           live_memory_result fin (PlaceR (MemoryPlace id r)) /\
           mem_path_offset entry.type r = SOME (k,t) ==> 
    ?v. read_result cx (PlaceR (MemoryPlace id r)) fin = (INL v,fin) /\
        value_has_type t v /\ k + type_memory_size t <= ssz /\
        !m. mem_agree_outside tn.t_mem u.vs_memory m ==> 
            val_in_memory t v (w2n B + k) m) /\
  (0 <= i /\ Num i < LENGTH vs /\
   read_result cx (PlaceR (MemoryPlace id path)) fin =
     (INL (ArrayV (DynArrayV vs)),fin) ==>
   (?v0. evaluate_subscripts initial.type initial.value
          (path ++ [ValueSubscript (IntV i)]) = INL v0) /\
   live_memory_result fin (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))) ==>
  0 <= i /\ Num i < LENGTH vs ==>
  ?v root ssz base rt k.
    read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
      (INL v,fin) /\ value_has_type tv v /\
    (!m. mem_agree_outside tn.t_mem u.vs_memory m ==> 
      val_in_memory tv v (w2n a + 32 + Num i * type_memory_size tv) m) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
    lookup_var root u = SOME base /\
    ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
    mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv) /\
    w2n a + 32 + Num i * type_memory_size tv = w2n base + k /\
    k + type_memory_size tv <= ssz
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH vs <= cap` by fs[vyperTypingTheory.value_has_type_def] >>
  `Num i < cap` by intLib.COOPER_TAC >>
  qabbrev_tac `k = j + (32 + Num i * type_memory_size tv)` >>
  `mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv)` by
    (simp[Abbr `k`] >> irule mem_path_offset_snoc >> simp[loweringPostsTheory.mem_step_offset_def]) >>
  qpat_x_assum `0 <= i /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!r off t. _ ==> ?v. _`
    (qspecl_then [`path ++ [ValueSubscript (IntV i)]`,`k`,`tv`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  qpat_x_assum `w2n a = _` SUBST1_TAC >>
  qexistsl [`v`,`root`,`ssz`,`B`,`rt`,`k`] >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!m. _ ==> _`
        (qspecl_then [`m`] drule_all) >>
      `j + (w2n B + (Num i * type_memory_size tv + 32)) = w2n B + k` by
        (rw[Abbr `k`] >> intLib.COOPER_TAC) >>
      pop_assum (fn th => rewrite_tac [th]) >>
      first_x_assum ACCEPT_TAC)
  >- (rw[Abbr `k`] >> intLib.COOPER_TAC)
QED
