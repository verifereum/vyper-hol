(* Delayed capture is a proposed proof interface, not an operand hypothesis. *)
Theory exprSimExtCallOperands
Ancestors
  exprSim exprSimHyps compileEnv context finite_map list arithmetic
  venomState vyperState vyperValueOperation exprSimOps freshWrites exprSimPop
  exprPlaceTransport exprTypedOperand exprStorageOrigin

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

(* Captured footprints are protected either by a private allocation or by
   the local frame (which excludes mutable dynamic-array headers). *)
Theorem operand_frame_footprint:
  operand_frame cenv es s hi es2 s2 /\
  (lo:compile_state).cs_next_id <= hi.cs_next_id /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      lo.cs_next_id <= aid /\ aid < hi.cs_next_id /\
      b <= off /\ off + len <= b + sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
         b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\
      b <= off /\ off + len <= b + sz /\
      (dynarray_local cenv n ==> b + 32 <= off)) \/ len = 0) ==>
  mem_bytes_at off len s2.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  pure_rewrite_tac[operand_frame_def] >> strip_tac
  >- (`mem_bytes_at b sz s2.vs_memory = mem_bytes_at b sz s.vs_memory`
        by metis_tac[] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> metis_tac[])
  >- metis_tac[locals_kept_def] >>
  simp[valueEncodingTheory.mem_bytes_at_def]
QED

Theorem vv_at_nondynamic_memory_frame:
  vv_at cenv cx t lo hi es tv (LocatedValue t' p) s /\
  ~dynarray_type t /\ p.ptr_location = LocMemory /\
  operand_frame cenv es s hi es2 s2 /\
  lo.cs_next_id <= hi.cs_next_id /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\
  eval_operand p.ptr_operand s = SOME w ==>
  mem_bytes_at (w2n w) (val_footprint tvt v) s2.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory
Proof
  simp[vv_at_def] >> rpt strip_tac >>
  gvs[] >>
  irule operand_frame_footprint >>
  goal_assum (drule_at (Pat `operand_frame _ _ _ _ _ _`)) >>
  qexists_tac `hi with cs_next_id := 0` >> simp[] >> metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Operand footprint dependency: " ^ name) else ()
  end)
  [("operand_frame_footprint", operand_frame_footprint),
   ("vv_at_nondynamic_memory_frame", vv_at_nondynamic_memory_frame)];

Theorem inv_dynamic_local_type[local]:
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\ dynarray_local cenv id ==>
  ?et n. entry.type = ArrayTV et (Dynamic n)
Proof
  strip_tac >>
  `env_scopes_consistent env cx es` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def] >>
  `?ty. FLOOKUP env.var_types id = SOME ty /\
        evaluate_type (get_tenv cx) ty = SOME entry.type` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
     fs[vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     strip_tac >> Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
     qpat_x_assum `!id ty entry. _` drule >>
     disch_then drule >> simp[]) >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  gvs[dynarray_local_def, dynarray_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem operand_local_window_frame[local]:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  stmt_state_rel ctx func cenv cx es2 s2 /\
  es2.scopes = es.scopes /\ local_ptrs_reserved cenv hi /\
  operand_frame cenv es s hi es2 s2 /\
  local_region cenv es.scopes s id b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s2.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\
   local_ptrs_rel func cenv es.scopes s2` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  irule local_window_frame_well_typed >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  qexists_tac `func` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `?w. lookup_var p s = SOME w` by
        (fs[local_ptrs_rel_def] >>
         qpat_x_assum `!name entry p sz. _ ==> ?w. _`
           (qspecl_then [`id'`, `entry`, `p`, `sz'`] mp_tac) >>
         simp[] >> metis_tac[]) >>
      `not_fresh_at hi p` by metis_tac[local_ptrs_reserved_def] >>
      fs[operand_frame_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[inv_dynamic_local_type] >>
  conj_tac >- fs[expr_sim_inv_def] >> fs[operand_frame_def]
QED

Theorem vv_at_memory_frame:
  vv_at cenv cx t lo hi es tv (LocatedValue t' p) s /\
  p.ptr_location = LocMemory /\
  operand_frame cenv es s hi es2 s2 /\
  lo.cs_next_id <= hi.cs_next_id /\
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  stmt_state_rel ctx func cenv cx es2 s2 /\
  es2.scopes = es.scopes /\
  local_ptrs_reserved cenv hi /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\
  eval_operand p.ptr_operand s = SOME w ==>
  mem_bytes_at (w2n w) (val_footprint tvt v) s2.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory
Proof
  simp[vv_at_def] >> rpt strip_tac >> gvs[]
  >- (irule operand_frame_footprint >>
      qexistsl_tac [`cenv`, `es`, `ARB`, `hi`, `lo`] >>
      conj_tac >- decide_tac >>
      conj_tac >- (disj1_tac >> metis_tac[]) >>
      fs[operand_frame_def] >> metis_tac[])
  >- (irule operand_local_window_frame >>
      goal_assum (drule_at (Pat `operand_frame _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      metis_tac[]) >>
  simp[valueEncodingTheory.mem_bytes_at_def]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Operand memory integration dependency: " ^ name) else ()
  end)
  [("inv_dynamic_local_type", inv_dynamic_local_type),
   ("operand_local_window_frame", operand_local_window_frame),
   ("vv_at_memory_frame", vv_at_memory_frame)];

Theorem word_val_footprint[local]:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==>
  val_footprint tv v = 32
Proof
  Cases_on `t` >> simp[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
       simp[is_word_type_def] >>
       TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
            simp[is_word_type_def])) >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `v` >>
  simp[val_footprint_def, valueEncodingTheory.type_memory_size_def]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Operand scalar dependency: " ^ name) else ()
  end)
  [("word_val_footprint", word_val_footprint)];

Theorem vv_at_effect_free_frame:
  vv_at ce cx ty lo hi es tv vv s /\
  operand_frame ce es s hi es2 s2 /\
  hi.cs_next_id <= hi2.cs_next_id /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce hi /\
  es2.scopes = es.scopes /\ es2.immutables = es.immutables /\
  (!tr. get_storage cx es2 tr = get_storage cx es tr) /\
  (case vv of StackValue _ op => eval_operand op s2 = eval_operand op s
   | LocatedValue _ p => eval_operand p.ptr_operand s2 = eval_operand p.ptr_operand s) ==>
  vv_at ce cx ty lo hi2 es2 tv vv s2
Proof
  strip_tac >>
  `!v. read_result cx tv es2 = (INL v,es2) ==>
       read_result cx tv es = (INL v,es)` by
    (rpt strip_tac >> irule read_result_preserved_fields >> metis_tac[]) >>
  `!n b sz. local_region ce es2.scopes s2 n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
            operand_frame_def] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     fs[operand_frame_def] >> metis_tac[]) >>
  Cases_on `vv` >>
  fs[vv_at_def, expr_val_at_def] >> rpt strip_tac >>
  `read_result cx tv es = (INL v,es)` by metis_tac[] >>
  last_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  rpt strip_tac >>
  fs[operand_frame_def] >>
  TRY (rename1 `aid < hi.cs_next_id` >> suspend "allocation") >>
  metis_tac[]
QED

Resume vv_at_effect_free_frame[allocation]:
  markerLib.RESUME_TAC >>
  `aid < hi2.cs_next_id` by decide_tac >>
  `FLOOKUP s2.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise vv_at_effect_free_frame

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag vv_at_effect_free_frame) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "Operand placement dependency" else ()
end;

Theorem compile_expr_operand_frame:
  compile_expr ce ty e lo = (vv,hi) /\ local_ptrs_reserved ce lo /\
  operand_frame ce es s hi es2 s2 /\ s2.vs_labels = s.vs_labels /\
  eval_operand (vv_operand vv) s = SOME w ==>
  eval_operand (vv_operand vv) s2 = SOME w
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at hi x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  Cases_on `vv_operand vv` >> gvs[eval_operand_def] >>
  fs[operand_frame_def] >> metis_tac[]
QED

Theorem vv_holds_operand_defined:
  vv_holds ce cx ty tv vv es s ==>
  ?w. eval_operand (vv_operand vv) s = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_def, vv_operand_def, expr_val_rel_def] >>
  metis_tac[]
QED

val _ = List.app (fn (n,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Operand execution boundary dependency: " ^ n) else ()
  end)
  [("compile_expr_operand_frame", compile_expr_operand_frame),
   ("vv_holds_operand_defined", vv_holds_operand_defined)];

Theorem compile_expr_operand_frame_no_label:
  compile_expr ce ty e lo = (vv,hi) /\ local_ptrs_reserved ce lo /\
  operand_frame ce es s hi es2 s2 /\
  ~is_label_operand (vv_operand vv) /\
  eval_operand (vv_operand vv) s = SOME w ==>
  eval_operand (vv_operand vv) s2 = SOME w
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at hi x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  Cases_on `vv_operand vv` >>
  gvs[eval_operand_def, stackPlanTypesTheory.is_label_operand_def] >>
  fs[operand_frame_def] >> metis_tac[]
QED

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag compile_expr_operand_frame_no_label) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "Non-label operand frame dependency" else ()
end;

Theorem expr_sim_inv_typed_local_no_label:
  expr_sim_inv ce cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
  ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))
Proof
  strip_tac >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  simp[]
QED

Theorem compile_name_vv_typed_no_label:
  expr_sim_inv ce cx env es /\ well_typed_expr env (Name ann id) /\
  compile_name_vv ce ty id lo = (vv,hi) ==>
  ~is_label_operand (vv_operand vv)
Proof
  strip_tac >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (fs[vyperTypeSystemTheory.well_typed_expr_def, expr_sim_inv_def] >> metis_tac[]) >>
  gvs[exprLoweringTheory.compile_name_vv_def, comp_return_def, vv_operand_def, mk_ptr_def,
      stackPlanTypesTheory.is_label_operand_def]
QED

val _ = List.app (fn (n,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Typed operand label exclusion dependency: " ^ n) else ()
  end)
  [("expr_sim_inv_typed_local_no_label", expr_sim_inv_typed_local_no_label),
   ("compile_name_vv_typed_no_label", compile_name_vv_typed_no_label)];

Theorem compile_expr_typed_no_label:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  compile_expr ce ty e lo = (vv,hi) ==> ~is_label_operand (vv_operand vv)
Proof
  strip_tac >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 compile_expr_not_label) >>
     goal_assum (drule_at Any) >> qexists_tac `env` >> simp[] >>
     metis_tac[expr_sim_inv_typed_local_no_label]) >>
  Cases_on `vv_operand vv` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem lower_value_typed_no_label:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  lower_value compile_expr ce ty e lo = (op,hi) ==> ~is_label_operand op
Proof
  strip_tac >>
  `!l. op <> Label l` by
    (irule lower_value_compile_expr_not_label >>
     goal_assum (drule_at Any) >> qexists_tac `env` >> simp[] >>
     metis_tac[expr_sim_inv_typed_local_no_label]) >>
  Cases_on `op` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem compile_expr_typed_operand_frame:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  compile_expr ce ty e lo = (vv,hi) /\ local_ptrs_reserved ce lo /\
  operand_frame ce es s hi es2 s2 /\
  eval_operand (vv_operand vv) s = SOME w ==>
  eval_operand (vv_operand vv) s2 = SOME w
Proof
  strip_tac >> irule compile_expr_operand_frame_no_label >>
  conj_tac >- metis_tac[compile_expr_typed_no_label] >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

val _ = List.app (fn (n,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Typed compiler operand framing dependency: " ^ n) else ()
  end)
  [("compile_expr_typed_no_label", compile_expr_typed_no_label),
   ("lower_value_typed_no_label", lower_value_typed_no_label),
   ("compile_expr_typed_operand_frame", compile_expr_typed_operand_frame)];

Theorem storage_holds_live_suffix:
  storage_holds cx tr ty tv w es s /\
  es2.scopes = es.scopes /\ es2.immutables = es.immutables /\
  (!tr'. get_storage cx es2 tr' = get_storage cx es tr') /\
  stmt_state_rel ctx func ce cx es2 s2 /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
     storage_read_live cx tr (get_storage cx es2 tr) w tvt) ==>
  storage_holds cx tr ty tv w es2 s2
Proof
  strip_tac >>
  qpat_x_assum `storage_holds _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [storage_holds_def]) >>
  `read_result cx tv es2 = (INL v,es2)` by
    (irule read_result_preserved_fields >> metis_tac[]) >>
  `read_storage_slot cx tr w tvt es2 = (INL v,es2)` by
    (fs[read_storage_slot_def,
        vyperStorageBackendTheory.get_storage_backend_eq,
        bind_def, lift_option_def, return_def, raise_def,
        vyperMiscTheory.option_CASE_rator, AllCaseEqs()]) >>
  `storage_agree (storage_dead cx tr (get_storage cx es2 tr))
    (get_storage cx es2 tr)
    (if tr then contract_transient s2 else contract_storage s2)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `tr` >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
        storage_rel_def, transient_rel_def, vyperStorageBackendTheory.get_storage_def,
        vfmStateTheory.lookup_account_def]) >>
  `storage_range_agree (get_storage cx es2 tr)
     (if tr then contract_transient s2 else contract_storage s2) w tvt` by
    (irule accountsRelPropsTheory.storage_range_agree_of_live >>
     conj_tac
     >- fs[accountsRelPropsTheory.storage_range_agree_def] >>
     qexistsl_tac [`cx`, `tr`] >> simp[]) >>
  qpat_x_assum `!tr'. get_storage _ _ _ = _`
    (qspec_then `tr` assume_tac) >>
  gvs[storage_holds_def]
QED

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag storage_holds_live_suffix) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "Live storage suffix dependency" else ()
end;

(* Interface diagnostic only: these quotations are typechecked signatures,
   NOT theorems or assumptions.  The first implication is still open.
   storage_place_region (capacity-only paths) is not enough for dynamic
   element liveness: a successful index check at the captured state is needed.

   Shared compiler cuts: a0 -> a1 lowers the address; a1 -> a2 compiles raw
   positional values; a2 -> a3 evaluates kwargs.  The delayed-read endpoint
   is a3 (before optional GAS at a5 and before call-buffer allocation).
   Q must consume these exact raw values at MAP (lowered_value_type ce) ps;
   compile_multi_vvs itself calls compile_expr at expr_type, not at that map.
   T starts from compile_external_call_kwargs at a5 and must preserve the
   resulting stage relation, not re-evaluate positional operands. *)
val _ = ``
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot tvt)), es1) ==>
  storage_read_live cx tr (get_storage cx es1 tr) slot tvt /\
  slots_in_range (get_storage cx es1 tr) (w2n slot) tvt
``;

(* Typechecked successful payload/cuts only; the actual simulation theorem
   must wrap this payload in frag_exec and send failing prefixes to expr_exit.
   In particular, it must DERIVE, not assume, final holds for captured places. *)
val _ = ``
  lower_value compile_expr ce (BaseT AddressT) addr a0 = (addr_op,a1) /\
  compile_multi_vvs compile_expr ce ps a1 = (vvs,a2) /\
  compile_ext_call_kwargs compile_expr ce ret_ty opts ks a2 =
    ((value_opt,gas_opt,default_opt),a3) /\
  eval_exprs cx [addr] es0 = (INL target,esA) /\
  eval_expr_results cx ps esA = (INL rs,esP) /\
  eval_exprs cx ks esP = (INL kwargs,esK) /\
  read_results cx rs esK = (INL vs,esK) /\
  tys = MAP (lowered_value_type ce) ps /\
  LENGTH rs = LENGTH vvs /\ LENGTH rs = LENGTH tys /\
  LENGTH rs = LENGTH los /\ LENGTH rs = LENGTH his /\
  (!i. i < LENGTH rs ==>
    compile_expr ce (expr_type (EL i ps)) (EL i ps) (EL i los) =
      (EL i vvs,EL i his) /\
    vv_holds ce cx (EL i tys) (EL i rs) (EL i vvs) esK sK /\
    vv_at ce cx (EL i tys) (EL i los) a3 esK (EL i rs) (EL i vvs) sK) /\
  stmt_state_rel ctx func ce cx esK sK /\ expr_sim_inv ce cx env esK /\
  fn_has_code a0 a3 func /\ local_ptrs_reserved ce a3
``;

Theorem expr_body_pre_storage_origin_live:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot tv)),es') ==>
  storage_read_live cx tr (get_storage cx es' tr) slot tv /\
  slots_in_range (get_storage cx es' tr) (w2n slot) tv
Proof
  strip_tac >>
  `contract_storage_well_formed cx es` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_all eval_expr_storage_result_live >> simp[storage_result_live_def]
QED

val _ =
  let val (ors,axs) = Tag.dest_tag (Thm.tag expr_body_pre_storage_origin_live) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Body expression origin dependency" else ()
  end;

(* Joint S/Q/T interface draft, NOT a theorem or an added simulation premise.
   StageValidate must test these proposed conclusions against primitive consumers.

   Canonical cuts:
     a0 -- lower_value address --> a1 -- compile_multi_vvs ps --> a2
        -- compile_ext_call_kwargs opts ks --> a3 -- optional GAS --> a5
        -- compile_external_call_kwargs --> a6.
   Q introduces an internal q cut immediately BEFORE CALL/STATICCALL; T starts
   at q (and includes the call). Neither q nor its buffers is known at a3.

   The source prefix includes read_results. Its errors map to expr_exit just
   like errors from target, positional, and keyword evaluation. The success
   witnesses retain the three source evaluation equations: the conditional
   frozen hypotheses must be specialized from those equations, not asserted
   unconditionally. The stage predicate below intentionally has no request
   agreement or final call postcondition in its input.

   Pending semantic owners:
     S.Compose: all fragment execution and capture-history reconstruction;
     Representation: raw vv_holds/vv_at at lowered_value_type (not expr_type);
     Q: optional GAS frame, tuple materialization, encoder, precheck, request;
     T: oracle step, revert/void/default/decode, final frame projections.

   Keyword policy: ext_call_kwarg and compile_ext_call_kwargs both select the
   first occurrence, not the last. well_typed_expr additionally supplies
   ALL_DISTINCT opts and matching keyword lengths. Default's materialized
   type is lowered_value_type ce e only in the nonword-return branch; the
   word branch returns ret_ty as its type. These facts must be proved from
   the two recursions, not guessed from an option membership test.
*)
val _ = ``
  let call = Call ann (ExtCall stat skip sig opts) (addr::rest) dflt;
      ps = TAKE (LENGTH (FST (SND sig))) rest;
      ks = DROP (LENGTH (FST (SND sig))) rest;
      ret_ty = SND (SND sig)
  in
  expr_body_pre ce cx env call es0 /\
  exprs_case nocalls ctx func ce cx [addr] /\
  (!es target esA. eval_exprs cx [addr] es = (INL target,esA) ==>
     results_case nocalls ctx func ce cx ps) /\
  (!es target esA esP0 rs esP.
     eval_exprs cx [addr] es = (INL target,esA) /\
     eval_expr_results cx ps esP0 = (INL rs,esP) ==>
     exprs_case nocalls ctx func ce cx ks) /\
  lower_value compile_expr ce (BaseT AddressT) addr a0 = (addr_op,a1) /\
  compile_multi_vvs compile_expr ce ps a1 = (vvs,a2) /\
  compile_ext_call_kwargs compile_expr ce ret_ty opts ks a2 =
    ((value_opt,gas_opt,default_opt),a3) /\
  (do target <- eval_exprs cx [addr];
      rs <- eval_expr_results cx ps;
      kwargs <- eval_exprs cx ks;
      vs <- read_results cx rs;
      vyperState$return (target,rs,kwargs,vs)
   od) es0 = (res,esK) /\
  expr_res_ok (case res of INL _ => INL NoneV | INR ex => INR ex) /\
  fn_has_code a0 a3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a0 ==>
  frag_exec ctx a0 a3
    (\s. s = s0 /\ stmt_state_rel ctx func ce cx es0 s)
    (\sK. ?target rs kwargs vs esA esP los his.
      res = INL (target,rs,kwargs,vs) /\
      eval_exprs cx [addr] es0 = (INL target,esA) /\
      eval_expr_results cx ps esA = (INL rs,esP) /\
      eval_exprs cx ks esP = (INL kwargs,esK) /\
      read_results cx rs esK = (INL vs,esK) /\
      LENGTH target = 1 /\
      expr_val_rel cx (BaseT AddressT) (HD target) addr_op sK /\
      expr_val_at ce cx (BaseT AddressT) a0 a3 esK (HD target) addr_op sK /\
      LENGTH rs = LENGTH vvs /\ LENGTH rs = LENGTH ps /\
      LENGTH rs = LENGTH los /\ LENGTH rs = LENGTH his /\
      (!i. i < LENGTH rs ==>
        compile_expr ce (expr_type (EL i ps)) (EL i ps) (EL i los) =
          (EL i vvs,EL i his) /\
        vv_holds ce cx (lowered_value_type ce (EL i ps))
          (EL i rs) (EL i vvs) esK sK /\
        vv_at ce cx (lowered_value_type ce (EL i ps)) (EL i los) a3
          esK (EL i rs) (EL i vvs) sK) /\
      LENGTH kwargs = LENGTH opts /\ LENGTH kwargs = LENGTH ks /\
      (case ext_call_kwarg EKValue opts kwargs of
         NONE => value_opt = NONE
       | SOME v => ?op. value_opt = SOME op /\
           expr_val_rel cx (BaseT (UintT 256)) v op sK) /\
      (case ext_call_kwarg EKGas opts kwargs of
         NONE => gas_opt = NONE
       | SOME v => ?op. gas_opt = SOME op /\
           expr_val_rel cx (BaseT (UintT 256)) v op sK) /\
      (case ext_call_kwarg EKDefault opts kwargs of
         NONE => default_opt = NONE
       | SOME v => ?op ty i. default_opt = SOME (op,ty) /\
           i < LENGTH ks /\ EL i opts = EKDefault /\
           ty = (if is_word_type ret_ty then ret_ty
                 else lowered_value_type ce (EL i ks)) /\
           expr_val_rel cx ty v op sK /\
           expr_val_at ce cx ty a0 a3 esK v op sK) /\
      stmt_state_rel ctx func ce cx esK sK /\ expr_sim_inv ce cx env esK /\
      operand_frame ce es0 s0 a0 esK sK /\ local_ptrs_reserved ce a3)
    (expr_exit res)
``;

(* Q/T draft. q is before emit_op CALL/STATICCALL, not after it. The two
   compiler computations below are literally the prefix and suffix of
   compile_external_call_kwargs_def. Their equations are proposed cut
   equations, NOT an asserted factorization theorem.

   The Q input `payload` is the success payload of S at a3. In particular
   raw representations at tys, the keyword representations and default
   placement are obligations, not consequences of operand_frame alone.
   Optional GAS belongs to Q. T includes the oracle instruction: splitting
   after CALL would lose the failure outcome before the revert branch.
*)
val _ = ``
  let tys = MAP (lowered_value_type ce) ps;
      am = SUM (MAP (type_memory_bytes ce) tys);
      az = abi_size_bound ce.ce_struct_fields (TupleT tys);
      wrapped = if needs_external_call_wrap ret_ty then TupleT [ret_ty]
                else ret_ty;
      rz = abi_size_bound ce.ce_struct_fields wrapped;
      rmin = abi_static_size ce.ce_struct_fields wrapped;
      rm = type_memory_bytes ce ret_ty;
      mid = ce.ce_method_id name arg_tys;
      enc = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys);
      dec = type_to_abi_dec_info ce.ce_struct_fields ce wrapped;
      value_op = case value_opt of NONE => Lit 0w | SOME v => v;
      hdflt = IS_SOME default_opt;
      dop = case default_opt of NONE => Lit 0w | SOME (v,ty) => v;
      dty = case default_opt of NONE => ret_ty | SOME (v,ty) => ty;
      prefix =
        (do ba <- compile_alloc_buffer (MAX az rz + 32);
            let bp = ba.buf_operand in
            do emit_void MSTORE [bp; Lit (n2w mid)];
               len <- (if vvs = [] then return (Lit 4w) else
                 do aa <- compile_alloc_buffer am;
                    compile_extcall_store_values ce (ZIP (vvs,tys))
                      aa.buf_operand 0;
                    dst <- emit_op ADD [bp; Lit 32w];
                    len <- compile_abi_encode_to_buf dst aa.buf_operand enc;
                    emit_op ADD [len; Lit 4w]
                 od);
               off <- emit_op ADD [bp; Lit 28w];
               (if ret_ty = NoneT /\ ~skip then
                  compile_extcodesize_check addr_op else return ());
               return (bp,off,len)
            od
         od);
      suffix = (\(bp,off,len).
        do success <- (if stat then
             emit_op STATICCALL [gas_op;addr_op;off;len;bp;Lit (n2w rz)]
           else emit_op CALL [gas_op;addr_op;value_op;off;len;bp;Lit (n2w rz)]);
           fail_lbl <- fresh_label "extcall_fail";
           cont_lbl <- fresh_label "extcall_cont";
           emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [];
           new_block fail_lbl;
           rds <- emit_op RETURNDATASIZE [];
           fa <- compile_alloc_buffer 0;
           emit_void RETURNDATACOPY [fa.buf_operand;Lit 0w;rds];
           emit_inst REVERT [fa.buf_operand;rds] [];
           new_block cont_lbl;
           if ret_ty = NoneT then comp_return (Lit 0w)
           else if hdflt then
             do ra <- compile_alloc_buffer rm;
                compile_default_return_path ce ret_ty dty bp ra.buf_operand dop
                  addr_op skip rmin rz dec
             od
           else
             do ra <- compile_alloc_buffer rm;
                hi <- compile_return_value_decode bp rmin rz;
                compile_abi_decode_to_buf ra.buf_operand bp MLOAD hi dec;
                return ra.buf_operand
             od
        od);
      payload = (\s.
        stmt_state_rel ctx func ce cx esK s /\ expr_sim_inv ce cx env esK /\
        expr_val_rel cx (BaseT AddressT) target_v addr_op s /\
        LENGTH rs = LENGTH ps /\ LENGTH vvs = LENGTH ps /\
        read_results cx rs esK = (INL vs,esK) /\
        (?los. LENGTH los = LENGTH rs /\
          (!i. i < LENGTH rs ==>
            vv_holds ce cx (EL i tys) (EL i rs) (EL i vvs) esK s /\
            vv_at ce cx (EL i tys) (EL i los) a3
              esK (EL i rs) (EL i vvs) s)) /\
        (case ext_call_kwarg EKValue opts kwargs of
           NONE => value_opt = NONE
         | SOME v => ?op. value_opt = SOME op /\
             expr_val_rel cx (BaseT (UintT 256)) v op s) /\
        (case ext_call_kwarg EKGas opts kwargs of
           NONE => gas_opt = NONE
         | SOME v => ?op. gas_opt = SOME op /\
             expr_val_rel cx (BaseT (UintT 256)) v op s) /\
        (case ext_call_kwarg EKDefault opts kwargs of
           NONE => default_opt = NONE
         | SOME v => ?op ty. default_opt = SOME (op,ty) /\
             expr_val_rel cx ty v op s /\
             expr_val_at ce cx ty a0 a3 esK v op s) /\
        operand_frame ce es0 s0 a0 esK s);
      ready = (\s.
        ?aw vw ow lw bw gw target value calldata.
          eval_operand addr_op s = SOME aw /\
          eval_operand value_op s = SOME vw /\
          eval_operand off s = SOME ow /\ eval_operand len s = SOME lw /\
          eval_operand bp s = SOME bw /\ eval_operand gas_op s = SOME gw /\
          dest_AddressV target_v = SOME target /\ w2w aw = target /\
          value = (if stat then NONE else
            SOME (case ext_call_kwarg EKValue opts kwargs of
                    NONE => 0 | SOME v => THE (dest_NumV v))) /\
          w2n vw = (case value of NONE => 0 | SOME n => n) /\
          stat = IS_NONE value /\
          build_ext_calldata (get_tenv cx) name arg_tys vs = SOME calldata /\
          read_memory (w2n ow) (w2n lw) s = calldata /\
          request_agree cx (call_outcome_request target calldata value esK)
            (venom_call_request s aw vw ow lw stat) /\
          ext_call_precheck_ok skip ret_ty target esK.accounts /\
          stmt_state_rel ctx func ce cx esK s /\
          expr_sim_inv ce cx env esK /\ local_ptrs_reserved ce q /\
          operand_frame ce es0 s0 a0 esK s /\
          (!bytes. LENGTH bytes <= rz ==>
            local_ptrs_rel func ce esK.scopes
              (write_memory_with_expansion (w2n bw) bytes s) /\
            immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor esK
              (write_memory_with_expansion (w2n bw) bytes s)) /\
          (case ext_call_kwarg EKDefault opts kwargs of
             NONE => T
           | SOME v => expr_val_rel cx dty v dop s /\
               expr_val_at ce cx dty a0 q esK v dop s))
  in
    expr_body_pre ce cx env call es0 /\
    call = Call ann (ExtCall stat skip (name,arg_tys,ret_ty) opts)
             (addr::rest) dflt /\
    ps = TAKE (LENGTH arg_tys) rest /\ ks = DROP (LENGTH arg_tys) rest /\
    LENGTH kwargs = LENGTH opts /\ LENGTH kwargs = LENGTH ks /\
    (case gas_opt of NONE => emit_op GAS [] a3 | SOME g => (g,a3)) =
      (gas_op,a5) /\
    prefix a5 = ((bp,off,len),q) /\ suffix (bp,off,len) q = (result_op,a6) /\
    fn_has_code a0 a6 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce a3 /\
    eval_ext_call cx stat skip (name,arg_tys,ret_ty) opts
      (target_v::(vs ++ kwargs)) esK = (res,esF) /\
    expr_res_ok (case res of INL _ => INL NoneV | INR ex => INR ex) ==>
    (* Q: precheck failures already exit; ready is only for reaching CALL. *)
    frag_exec ctx a3 q (\s. s = sK /\ payload s) ready (expr_exit res) /\
    (* T: generic oracle call, revert, void, default, decoder success/reject. *)
    frag_exec ctx q a6 ready
      (\s. ?v. res = INL (Value v) /\
        expr_post ctx func ce cx call es0 a0 a6 s0 esF v result_op s)
      (expr_exit res)
``;

(* S-output / Q-T-input gap inventory (all proposed, not discharged here):

   S output/input carried       Q or T consumer                 Owner / gap
   original expr_body_pre       am, MAX az rz +32 <2**64         Q: extract
     ext_call_alloc_ok has syntactic bounds on the ORIGINAL call, not new
     assumptions on esK. rm is a type_alloc_ok obligation; encoder/decoder
     numeric/layout bounds also need typing and compile-env projections.
   address + kwargs reps        CALL operand evaluation          S.Compose
     Q preserves addr/value/gas and default through GAS/alloc/store/encode.
   raw vvs + read_results       store_values at tys, ABI encode   Representation
     lowered types are not expr_type; runtime typing alone is insufficient.
   declared arg_tys vs tys      build_ext_calldata equality       Q
     ABI selector uses declared types, memory tuple uses lowered types.
   default rep + expr_val_at    default after CALL and decode     Q, T
     Requires buffer separation plus call-frame preservation, not just
     preserving operand words. Nonword default can alias a source local.
   stmt_state_rel at esK        request_agree + oracle step       Q, T
     Q derives exact-length calldata; T uses exec_ext_call_oracle_step and
     outcomes_accounts_typed. Q's universally bounded write frame is intended
     to discharge that lemma's local_ptrs_rel/immutables_rel premises.
   original cumulative frame    expr_post at a6                   Q, T
     No operand_frame across adoption is asserted: the source changes at the
     call. Preserve its explicit fresh-var/alloca/memory/local projections.
   source prefix equations      residual eval_ext_call equation   S.Compose
     Prefix errors from target/results/kwargs/read_results use expr_exit;
     on success residual errors include precheck, oracle failure and decode.
     Q must link its precheck abort to the residual source error. T must
     propagate RevertData before adoption on failure; NoneT uses the void
     path, empty returndata may use the default (with post-call code check),
     otherwise decoder success or the sole allowed reject admission.
   fn_has_code, reservations    a3/a5/q/a6 cuts                   Q, T
     Exact compiler factorization and frame transitivity remain unproved.

   Missing input ownership is explicit: the draft carries original pre at
   es0, not expr_body_pre at esK. Later typing, liveness and allocation facts
   must be derived by the designated components. No quotation above is a
   theorem and no diagnostic quotation is a usable assumption in assembly.
*)

(* StageValidate: primitive compatibility report (no simulation asserted).

   1. a3 -> materialization (MISMATCH, Representation/Q).
      compile_extcall_store_values_def uses unwrap_value ce vv, whose type
      is carried by vv, then dispatches the store on lowered_value_type ce e.
      unwrap_value_sim (exprSimUnwrap:665-679) consumes a FULL vv_post for
      (Value v), at expr_type e, and scope-domain equality, cut monotonicity,
      vv_operand freshness and the nonword size/evaluate_type equation.
      The draft payload only has vv_holds/vv_at at tys, not this vv_post or
      the connection between tys and vv's carried type. The read-result
      wrapper (exprSimUnwrap:766-782) is local and still uses expr_type e.
      Thus direct drule/irule cannot consume the quoted payload. A boundary
      must relate actual raw compile_expr results to the actual unwrap/store
      run; merely retyping an evaluated operand does not do that. There is
      currently no semantic theorem for compile_extcall_store_values (only
      compiler monotonicity and shape theorems). Representation.Probe must
      test this interface before its universal proof; Q owns list storage.

   2. stored tuple -> encoding (MISSING DERIVATION, Q).
      abi_encoder_correct_run (abiEncoderCorrect:42-58) requires:
        abi_encoder_pre ei at av start src dst sb source_cap d b cap s,
        abi_decoder_budget first last b cap s, fresh_vars_wrt limit_st s,
        compiler-id/var bounds, current block/index, nonhalted and phi facts.
      Its result is exact bytes enc at av AND the emitted length word.
      abi_encoder_pre additionally requires abi_encoder_input for the actual
      memory, source/destination/scratch separation, operand liveness and
      nonwrapping ranges (abiEncoderCorrect:9-18). The S payload cannot
      directly supply these: Q must allocate, materialize, establish input
      and allocator resources, then apply correctness. abi_tuple_encode_input
      (abiTupleEncodeInput:8-19) similarly demands encoder_input for nonwords,
      not just val_in_memory or source typing. Original-call ext_call_alloc_ok
      bounds static sizes only, not current runtime addresses or scratch.
      Exact calldata follows only after proving enc at av is the declared
      parameter encoding in build_ext_calldata, plus selector placement and
      the ADD 4 result. The zero-argument branch must bypass tuple encoding.

   3. q -> oracle (PARTIAL MATCH, Q/T).
      exec_ext_call_oracle_step (extCallOracleStep:159-184) requires state_rel,
      a singleton output instruction, target/value word equations,
      stat = IS_NONE value_opt, and a successful take_call_outcome equation.
      ready explicitly supplies the word equations and stmt_state_rel (which
      projects state_rel), but not the take equation or actual instruction.
      Compiler cut factorization supplies the singleton CALL/STATICCALL;
      source take must be obtained using esK's outcomes invariant and the
      exact calldata equation. This is not a new premise on the frozen case.
      The generic lemma already provides the bounded write equation and
      returndata; reuse it, do not add an extcall-specific oracle lemma.
      Its final state_rel implication needs local_ptrs_rel/immutables_rel.
      ready's forall bytes frame supplies these for TAKE rz returnData once
      rz < 2**256 is extracted from original allocation bounds. The generic
      lemma's other changed fields do not affect those two relations; use
      local_ptrs_rel_oracle_fields and the immutable field projections.
      On failure use the taken source state before adoption; matching
      RevertData is a T obligation, not the success state_rel implication.

   4. q -> default (MISMATCH, Q/T).
      ready pins default representation and placement only BEFORE CALL.
      Neither generic oracle correctness nor the ready write-frame proves
      that representation after the return write: the frame only speaks
      about local_ptrs_rel/immutables_rel, not arbitrary earlier temporary
      buffers. Need default footprint separation from the shared buffer,
      operand preservation, and composition with decoder/result allocations.
      Nonword default may alias locals. vv_at plus actual fresh allocations
      is the proposed derivation, but not an existing application here.
      Source default also checks code using POST-adoption accounts
      (vyperInterpreter:1057-1062); precheck at esK is not that check.

   5. oracle -> decoder (DIFFERENT ENTRY, T).
      lower_abi_decode_valid_source (abiBuiltinValidSource:105-123) compiles
      lower_abi_decode, with a length-prefixed BytesV input. The extcall suffix
      instead compiles compile_return_value_decode followed by
      compile_abi_decode_to_buf. It is not a direct consumer of that builtin
      theorem. abi_decoder_valid_decode (abiDecoderValidRecursive:86-102)
      matches the latter compiler operation, but needs abi_decoder_valid_pre,
      budgets, freshness, entry block/index and phi facts. valid_pre
      (abiDecoderValidContract:17-29) needs coherent wrapped metadata, valid
      source bytes, window ranges and operand liveness. T must connect
      evaluate_abi_decode_return to those facts for the WRAPPED type, copying
      only bounded returndata and constructing hi. Generic oracle correctness
      alone supplies neither decode windows nor allocation resources. Reject
      is owned solely by extcall_returndata_decode_reject, not a success lemma.

   6. exits/composition (UNPROVED, S.Compose/Q/T).
      S carries target/results/kwargs/read_results equations. On prefix
      failure, source bind propagation identifies the overall exception;
      expr_exit is insensitive to the success type. On success Q's residual
      eval_ext_call input is target_v::(vs++kwargs), and source typing gives
      the lengths/options/address/precheck classification. Q still needs a
      precheck-abort fragment theorem. T needs actual CALL/JNZ/revert/default/
      decode fragments and their frame projections. No quoted fragment has
      been proved, and no source-prefix preservation theorem can replace it.

   Verdict: NOT semantically validated for assembly. The draft records the
   right source order and compiler cuts, but the current primitive interfaces
   do not directly consume its representations or establish its resources.
   No counterexample is asserted by this report. StageValidate is complete
   as a bounded diagnostic; Representation/Q/T need reviewed interface work
   before the shared anchor or Compose can claim validated compatibility.
*)
