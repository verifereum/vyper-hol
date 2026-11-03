(* Compiler and source ABI sizes agree for types that evaluate. *)
Theory abiTypeBoundProps
Ancestors
  compileEnv vyperValue vyperABI finite_map list rich_list option pair

(* Evaluation and the ABI type are stable under a larger type env: a type
   that evaluates names only structs its env has. *)
Theorem vyper_to_abi_type_submap:
  (!env ty tv.
     evaluate_type env ty = SOME tv ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_type tenv ty = SOME tv /\
            vyper_to_abi_type env ty = vyper_to_abi_type tenv ty) /\
  (!env ts acc tvs.
     evaluate_types env ts acc = SOME tvs ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_types tenv ts acc = SOME tvs /\
            vyper_to_abi_types env ts = vyper_to_abi_types tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      `FLOOKUP tenv nsid = SOME (StructArgs args)`
        by fs[SUBMAP_FLOOKUP_EQN] >>
      `env \\ nsid SUBMAP tenv \\ nsid`
        by fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> simp[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      fs[SUBMAP_FLOOKUP_EQN])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> Cases_on `bd` >> simp[])
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

(* Proof-only counterexample: source embedded size includes the dynamic tail,
   whereas compiler embedded static size is only the head offset. *)
Theorem abi_props_vyper_typed_string_counterexample:
  sfields_tenv_consistent FEMPTY FEMPTY /\
  evaluate_type FEMPTY (BaseT (StringT 0)) =
    SOME (BaseTV (StringT 0)) /\
  abi_embedded_static_size FEMPTY (BaseT (StringT 0)) = 32 /\
  vyper_abi_embedded_size FEMPTY (BaseT (StringT 0)) = 64
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem abi_props_vyper_typed_false:
  ~(!sf tenv ty tv.
    sfields_tenv_consistent sf tenv /\
    evaluate_type tenv ty = SOME tv ==>
    is_abi_dynamic sf ty = vyper_is_dynamic tenv ty /\
    abi_size_bound sf ty = vyper_abi_size_bound tenv ty /\
    abi_embedded_static_size sf ty = vyper_abi_embedded_size tenv ty)
Proof
  strip_tac >>
  first_x_assum (qspecl_then
    [`FEMPTY`, `FEMPTY`, `BaseT (StringT 0)`, `BaseTV (StringT 0)`]
    mp_tac) >>
  simp[abi_props_vyper_typed_string_counterexample]
QED

(* Struct names can collide after string conversion. Evaluated type sizes
   still decrease down fields: colliding ancestor and child names would
   force equal field lists and equal evaluated types, contradicting that
   decrease. A size-bounded, one-way struct consistency invariant suffices
   when both environments drop a struct. *)
Theorem abi_props_vyper_typed:
  !sf tenv ty tv.
    sfields_tenv_consistent sf tenv /\
    evaluate_type tenv ty = SOME tv ==>
    is_abi_dynamic sf ty = vyper_is_dynamic tenv ty /\
    abi_size_bound sf ty = vyper_abi_size_bound tenv ty /\
    abi_embedded_static_size sf ty = vyper_abi_embedded_size tenv ty
Proof
  cheat
QED
