(* Delayed capture is a proposed proof interface, not an operand hypothesis. *)
Theory exprSimExtCallOperands
Ancestors
  exprSim exprSimHyps compileEnv context finite_map list arithmetic
  venomState vyperState vyperValueOperation exprSimOps freshWrites exprSimPop

Definition operand_frame_def:
  operand_frame cenv es s cut es' s' <=>
    (!x w. not_fresh_at cut x /\ lookup_var x s = SOME w ==>
       lookup_var x s' = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP s'.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < cut.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s'.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    locals_kept cenv es s s'
End

Definition delayed_capture_def:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s <=>
    !es' s' hi' v.
      stmt_state_rel ctx func cenv cx es' s' /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
      operand_frame cenv es s hi es' s' /\
      read_result cx tv es' = (INL v,es') ==>
      vv_holds cenv cx ty tv vv es' s' /\
      vv_at cenv cx ty lo hi' es' tv vv s'
End

Theorem delayed_capture_holds[local]:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s /\
  stmt_state_rel ctx func cenv cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame cenv es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_holds cenv cx ty tv vv es' s'
Proof
  simp[delayed_capture_def] >> metis_tac[]
QED

Theorem delayed_capture_at[local]:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s /\
  stmt_state_rel ctx func cenv cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame cenv es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_at cenv cx ty lo hi' es' tv vv s'
Proof
  simp[delayed_capture_def] >> metis_tac[]
QED

Theorem vv_post_operand_frame[local]:
  vv_post ctx func cenv cx e es lo hi s0 es' tv vv s ==>
  operand_frame cenv es s0 lo es' s
Proof
  simp[vv_post_def, operand_frame_def] >> strip_tac >> simp[]
QED

Theorem vv_post_equal_state[local]:
  vv_post ctx func cenv cx e es lo hi s0 es' tv vv s ==>
  vv_holds cenv cx (expr_type e) tv vv es' s /\
  vv_at cenv cx (expr_type e) lo hi es' tv vv s
Proof
  simp[vv_post_def] >> metis_tac[]
QED

(* A stack witness records the value at capture time, not its provenance.
   If a place later reads a different word, the same literal is invalid. *)
Theorem changed_read_invalidates_stack[local]:
  read_result cx tv es' = (INL v,es') /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  is_word_type ty /\ typed_val_to_w256 tvt v <> w ==>
  ~vv_holds ce cx ty tv (StackValue ty (Lit w)) es' s'
Proof
  simp[vv_holds_def, expr_val_rel_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem storage_capture_read[local]:
  read_result cx (PlaceR (StoragePlace tr slot tvt)) es =
  read_storage_slot cx tr slot tvt es
Proof
  simp[read_result_def, read_place_def]
QED

Theorem memory_capture_read[local]:
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,entry)]) =
  (INL entry.value, es with scopes := [FEMPTY |+ (name,entry)])
Proof
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lookup_scopes_def, lift_option_type_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, lift_sum_def,
       FLOOKUP_UPDATE]
QED

Theorem memory_mutation_probe[local]:
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV F; popped := [] |> )]) =
    (INL (BoolV F), es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV F; popped := [] |> )]) /\
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV T; popped := [] |> )]) =
    (INL (BoolV T), es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV T; popped := [] |> )]) /\
  read_result cx (Value (BoolV F)) es = (INL (BoolV F),es)
Proof
  simp[memory_capture_read, read_result_def, return_def]
QED

Theorem storage_mutation_probe[local]:
  read_result cx (PlaceR (StoragePlace T 0w (BaseTV BoolT)))
    (es with tStorage := (\a. (\k. 0w))) =
    (INL (BoolV F), es with tStorage := (\a. (\k. 0w))) /\
  read_result cx (PlaceR (StoragePlace T 0w (BaseTV BoolT)))
    (es with tStorage := (\a. (\k. 1w))) =
    (INL (BoolV T), es with tStorage := (\a. (\k. 1w)))
Proof
  simp[storage_capture_read, read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, bind_def, return_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vyperStorageTheory.decode_value_def, vyperStorageTheory.read_slot_def,
       vyperStorageTheory.decode_base_from_slot_def, lift_option_def,
       vyperStorageTheory.slot_to_bool_def, vfmStateTheory.lookup_storage_def]
QED

(* This implication applies to PlaceR as well as Value.  Thus the
   current-state holds interface admits a literal witness for a place. *)
Theorem bool_read_stack_probe[local]:
  read_result cx tv es = (INL (BoolV b),es) ==>
  (vv_holds ce cx (BaseT BoolT) tv
     (StackValue (BaseT BoolT) (Lit 0w)) es s <=> ~b)
Proof
  strip_tac >>
  simp[vv_holds_def, expr_val_rel_def, eval_operand_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       valueEncodingTheory.typed_val_to_w256_def] >>
  Cases_on `b` >> simp[valueEncodingTheory.val_to_w256_def]
QED

Theorem compile_name_ptr_probe[local]:
  FLOOKUP ce.ce_vars name = SOME (PtrVar ptr_op sz) ==>
  compile_name_vv ce ty name st =
    (LocatedValue ty (mk_ptr ptr_op LocMemory),st)
Proof
  simp[exprLoweringTheory.compile_name_vv_def, compileEnvTheory.comp_return_def]
QED

(* Producer audit (C1.P.2.1; not a proved capture theorem).

   Source paths returning PlaceR, and compiler paths (line references refer
   to vyperInterpreterScript, vyperStateScript, exprLoweringScript):
   - Name: interpreter 1502-1505 -> MemoryPlace id [].  Lowering 2766,
     1481-1493 -> LocatedValue LocMemory, literal MemLoc or PtrVar operand.
     Needs local layout/region correspondence from stmt_state_rel.
   - TopLevelName: interpreter 1507-1508, state 465-483 -> StoragePlace,
     ImmutablePlace, or HashMapRef (not itself readable). Lowering 2820-2829
     -> literal Storage/Transient/Code pointer from ce_module_vars.
     Needs module layout and immutable sub-layout correspondence.
   - IfExp: interpreter 1510-1513, state 1054-1068 -> retains ONLY memory
     aggregate places; other places are forced to Value. Lowering 2767-2789
     -> nonword LocatedValue LocMemory PHI, word StackValue PHI.
     Needs chosen-branch provenance for a retained place, and branch operand
     stability; condition/branch vv_post alone only relates current values.
   - Subscript: interpreter 1524-1528, state 1166-1203 -> extends a place
     (or HashMapRef), but selects Value from immediate Value bases.
     Lowering 2268-2316 -> LocatedValue at the base location (memory default
     for StackValue); pointer is tuple offset, hashed mapping key, or
     array element pointer. Needs base provenance, captured index value,
     and correct per-location offset/stride/metadata. Dynamic bounds are
     checked at capture time, not rechecked in a future state.
   - Attribute: interpreter 1530-1533 uses the same select_result; lowering
     2321-2342 adds field offset to the recursively compiled base pointer.
     Needs base provenance and correct field layout; Value bases instead
     need snapshot-buffer framing, not mutable-place transport.
   - Pop: interpreter 1548-1551, state 1217-1260 -> retained storage element
     address or MemoryPlace path to the removed element, backed by popped
     history; immutable pop returns Value. Lowering 2832 onwards uses target
     pointer, loads/decrements length, returns LocatedValue element pointer.
     Needs target provenance and old length, plus retained element bytes /
     popped-history agreement after later operations.
   Literal, FlagMember, StructLit, Builtin (including Len), TypeBuiltin and
   Calls do not introduce PlaceR: interpreter 1509,1515-1522,1534-1546,
   1552-1556,1558-1692 and their call helpers return Value or exceptions.

   Recursive trace: Subscript(Name a, Name i) first captures MemoryPlace a[],
   then reads i and appends ValueSubscript v to the captured path.  Compilation
   first obtains a's pointer, then lower_value of i, then computes an element
   pointer with the captured index and a capture-time length check.  Replaying
   the expression in a future state is invalid if i changes.  The missing
   induction premise must relate the retained a pointer and captured path,
   not merely the current value of a or a future evaluation of this syntax.

   Candidate boundary (UNPROVED): under expr_body_pre and existing operand
   judgments, actual successful eval_expr/compile_expr fragment execution
   admits a relational post containing source-place/compiled-address identity
   (or framed Value snapshot), with frozen selection indices and base
   metadata.  Eliminating that relation in future related states would give
   delayed_capture.  stmt_state_rel supplies root layouts and vv_post supplies
   current reads/frames; neither supplies recursive path identity.  For
   Subscript/Attribute/IfExp/Pop a structural producer premise for the base,
   chosen branch or target remains unproved. Existing expr_vv_case/results_case
   supply no such recursive premise. No global induction or strengthened IH
   is asserted here. Changing lengths and popped history must be covered by
   the producer relation, not silently excluded as equal-state transport.
*)

Theorem operand_frame_trans:
  local_ptrs_rel func ce es0.scopes s0 /\ local_ptrs_reserved ce cut0 /\
  operand_frame ce es0 s0 cut0 es1 s1 /\
  operand_frame ce es1 s1 cut1 es2 s2 /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  cut0.cs_next_var <= cut1.cs_next_var /\
  cut0.cs_next_id <= cut1.cs_next_id ==>
  operand_frame ce es0 s0 cut0 es2 s2
Proof
  pure_rewrite_tac[operand_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at cut1 x` by metis_tac[not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `aid < cut1.cs_next_id` by decide_tac >>
      `!n b sz'. local_region ce es1.scopes s1 n b sz' ==>
         off + sz <= b \/ b + sz' <= off` by
        (rpt strip_tac >>
         `local_region ce es0.scopes s0 n b sz'` by
           (irule local_region_frame >>
            conj_tac >- metis_tac[] >>
            qexistsl_tac [`cut0`, `es1.scopes`, `s1`] >> simp[]) >>
         metis_tac[]) >>
      metis_tac[]) >>
  irule locals_kept_trans >>
  qexistsl_tac [`es1`, `cut0`, `s1`] >> simp[]
QED

Theorem delayed_capture_rebase:
  delayed_capture ctx func ce cx ty tv vv lo hi es s /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce hi /\
  operand_frame ce es s hi es1 s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  hi.cs_next_var <= hi1.cs_next_var /\ hi.cs_next_id <= hi1.cs_next_id ==>
  delayed_capture ctx func ce cx ty tv vv lo hi1 es1 s1
Proof
  pure_rewrite_tac[delayed_capture_def] >> rpt strip_tac >>
  `operand_frame ce es s hi es' s'` by
    (irule operand_frame_trans >>
     conj_tac >- simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`hi1`, `es1`, `s1`] >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by metis_tac[] >>
  `hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id`
    by decide_tac >>
  metis_tac[]
QED

(* Future typing is supplied by source operand preservation, not vv_post. *)
Definition typed_capture_def:
  typed_capture ctx func ce cx env ty tv vv lo hi es s <=>
    !es' s' hi' v.
      expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' s' /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
      operand_frame ce es s hi es' s' /\
      read_result cx tv es' = (INL v,es') ==>
      vv_holds ce cx ty tv vv es' s' /\
      vv_at ce cx ty lo hi' es' tv vv s'
End

Theorem typed_capture_holds:
  typed_capture ctx func ce cx env ty tv vv lo hi es s /\
  expr_sim_inv ce cx env es' /\
  stmt_state_rel ctx func ce cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame ce es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_holds ce cx ty tv vv es' s'
Proof
  simp[typed_capture_def] >> metis_tac[]
QED

Theorem typed_capture_at:
  typed_capture ctx func ce cx env ty tv vv lo hi es s /\
  expr_sim_inv ce cx env es' /\
  stmt_state_rel ctx func ce cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame ce es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_at ce cx ty lo hi' es' tv vv s'
Proof
  simp[typed_capture_def] >> metis_tac[]
QED

Theorem typed_capture_rebase:
  typed_capture ctx func ce cx env ty tv vv lo hi es s /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce hi /\
  operand_frame ce es s hi es1 s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  hi.cs_next_var <= hi1.cs_next_var /\ hi.cs_next_id <= hi1.cs_next_id ==>
  typed_capture ctx func ce cx env ty tv vv lo hi1 es1 s1
Proof
  pure_rewrite_tac[typed_capture_def] >> rpt strip_tac >>
  `operand_frame ce es s hi es' s'` by
    (irule operand_frame_trans >>
     conj_tac >- simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`hi1`, `es1`, `s1`] >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by metis_tac[] >>
  `hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id`
    by decide_tac >>
  metis_tac[]
QED

Theorem compile_name_typed_capture:
  expr_body_pre ce cx env (Name ann name) es /\
  stmt_state_rel ctx func ce cx es s /\
  local_ptrs_reserved ce hi /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
  compile_expr ce ann (Name ann name) lo = (vv,hi) /\
  eval_expr cx (Name ann name) es = (INL tv,es1) ==>
  typed_capture ctx func ce cx env ann tv vv lo hi es1 s
Proof
  rpt strip_tac >>
  gvs[exprLoweringTheory.compile_expr_def] >>
  drule compile_name_ptr_probe >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, bind_def, get_scopes_def,
       return_def, type_check_def, assert_def, check_def, ignore_bind_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  pure_rewrite_tac[typed_capture_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Name ann name)` by gvs[expr_body_pre_def] >>
  `?entry. lookup_scopes name es'.scopes = SOME entry /\
       evaluate_type (get_tenv cx) ann = SOME entry.type /\
       value_has_type entry.type entry.value` by
    (`env_consistent env cx es' /\ state_well_typed es'` by
       fs[expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       fs[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
     gvs[] >> goal_assum drule >> simp[]) >>
  `?w. lookup_var p s' = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s'.vs_memory` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `ce.ce_var_type name = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeSystemTheory.well_typed_expr_def] >>
  simp[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def, eval_operand_def] >>
  gvs[vyperASTTheory.expr_type_def, read_result_def, read_place_def,
      bind_def, get_scopes_def, lift_option_type_def, lift_sum_def,
      return_def, read_memory_path_def, evaluate_subscripts_def] >>
  conj_tac >- metis_tac[val_in_memory_word_type] >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`name`, `w2n w`, `sz`] >>
  asm_simp_tac (srw_ss()) [local_region_def, dynarray_local_def] >>
  drule val_footprint_le >> decide_tac
QED

(* Bounded diagnostic: the retained path survives a Pop in source history.
   This does not claim that an arbitrary related heap is reachable. *)
Theorem retained_subscript_before_pop[local]:
  lookup_scopes a es.scopes = SOME entry /\
  entry.type = ArrayTV (BaseTV (UintT 256)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [IntV 7]) ==>
  select_result cx ty (PlaceR (MemoryPlace a []))
    (ValueSubscript (IntV 0)) es =
    (INL (PlaceR (MemoryPlace a [ValueSubscript (IntV 0)])), es)
Proof
  rpt strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, array_index_def,
       extend_memory_place_def, subscripts_type_def,
       listTheory.oEL_THM, vyperASTTheory.bound_length_def]
QED

Theorem retained_subscript_pop_trace[local]:
  find_containing_scope a es.scopes = SOME (pre, sc, entry, rest) /\
  entry.assignable /\
  entry.type = ArrayTV (BaseTV (UintT 256)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [IntV 7]) ==>
  pop_place cx (MemoryPlace a []) es =
    (INL (PlaceR (MemoryPlace a [ValueSubscript (IntV 0)])),
     es with scopes := pre ++ sc |+ (a, pop_name_entry entry [IntV 7]) :: rest)
Proof
  rpt strip_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, return_def,
       lift_sum_def, read_memory_path_def, evaluate_subscripts_def,
       check_def, popped_value_def, pop_element_def, assign_subscripts_def,
       set_scopes_def, record_pop_def, pop_name_entry_def]
QED

Theorem retained_subscript_history_read[local]:
  read_memory_path
    (entry with <|type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
                  value := ArrayV (DynArrayV []);
                  popped := [([ValueSubscript (IntV 0)], IntV 7)]|>)
    [ValueSubscript (IntV 0)] = INL (IntV 7)
Proof
  EVAL_TAC >> simp[]
QED

(* The live-array clause of local_ptrs_rel sees just the length when empty.
   In particular it does not constrain mem_word_at (b+32) mem. *)
Theorem empty_array_representation_projection[local]:
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
    (ArrayV (DynArrayV [])) b mem <=> mem_word_at b mem = 0w
Proof
  simp[valueEncodingTheory.val_in_memory_def]
QED

(* Crucially operand_frame includes locals_kept: even dead tail words are
   protected.  An arbitrary heap changing the removed element is therefore
   NOT a countermodel to typed_capture's premises. *)
Theorem retained_subscript_frame_bytes[local]:
  operand_frame ce es s cut es' s' /\
  local_region ce es.scopes s a b sz /\ 64 <= sz ==>
  mem_bytes_at (b + 32) 32 s'.vs_memory =
  mem_bytes_at (b + 32) 32 s.vs_memory
Proof
  simp[operand_frame_def] >> rpt strip_tac >>
  fs[locals_kept_def] >> first_x_assum irule >>
  qexistsl_tac [`b`, `a`, `sz`] >> simp[]
QED

(* Diagnostic staging sequent (not a new theorem assumption):
   expr_body_pre ce cx env e es0, stmt_state_rel ... es0 s0,
   compile_expr ce ty e lo = (vv,hi), eval_expr cx e es0 = (INL tv,es1),
   capture fragment executes s0 -> s1,
   suffix fragment executes s1 -> s2 matching suffix source es1 -> es2,
   read_result cx tv es2 = (INL v,es2)
   must imply vv_holds ce cx ty tv vv es2 s2 and vv_at ... lo hi2 es2 tv vv s2.

   results_case supplies expr_vv_case for e (and subsequent operands after
   successful evaluation); exprs_case supplies the keyword judgments.
   Their successful vv_post supplies operand_frame, and the existing frame
   composition/rebase laws transport a capture ONCE PRODUCED.  The final
   expr_sim_inv is supplied by successful operand postconditions.
   The missing general theorem is initial typed_capture production for actual
   compile/eval of e, including frozen selection indices/branch provenance.
   The concrete Pop trace above does NOT refute that theorem: although the
   final live-array relation ignores the removed word, operand_frame's
   locals_kept conjunct preserves that entire word (frame_bytes above).
   This protection is stronger than preservation of only live elements.
   General source mutation/history compatibility and recursive production
   dependency closure are still unproved; do not infer either from this test.
*)
