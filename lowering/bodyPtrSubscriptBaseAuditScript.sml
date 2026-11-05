(* Architectural probes only: neither theorem below refutes the frozen target.
   No new execution predicate is introduced: the missing interface has not yet
   been justified from the target's operand hypotheses. *)
Theory bodyPtrSubscriptBaseAudit
Ancestors
  vyperTypeSystem finite_map

Theorem mapping_root_not_well_typed_expr:
  FLOOKUP env.toplevel_vtypes nsid = SOME (HashMapT kt vt) /\
  FLOOKUP env.bare_globals nsid = NONE ==>
  ~well_typed_expr env (TopLevelName NoneT nsid)
Proof
  Cases_on `nsid` >> simp[well_typed_expr_def]
QED

Theorem mapping_key_place_typing:
  FLOOKUP env.toplevel_vtypes nsid = SOME (HashMapT kt (HashMapT kt' vt)) /\
  well_typed_expr env key /\ expr_type key = kt /\ hashmap_key_type kt ==>
  type_place_expr env (Subscript NoneT (TopLevelName NoneT nsid) key) =
    SOME (HashMapT kt' vt)
Proof
  Cases_on `nsid` >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, subscript_vtype_def]
QED

(* C1.7.4 audit: successful source result classes, exhaustive over expr.
   References use source line numbers at this checkpoint.

   Name: PlaceR MemoryPlace (vyperInterpreter 1538-1542).
   TopLevelName: PlaceR ImmutablePlace/StoragePlace or HashMapRef, by actual
     declaration (vyperState lookup_global_def 483-503).
   Subscript: Value remains Value; PlaceR extends to PlaceR; HashMapRef
     extends to HashMapRef or PlaceR StoragePlace. Mapping only accepts a
     ValueSubscript. See select_result_def 1240, extend_place_def 1210.
   Attribute: same selection dispatch; Value remains Value, PlaceR extends;
     HashMapRef cannot successfully take AttrSubscript (extend_place 1230).
   IfExp: selected Value remains Value; selected MemoryPlace aggregate may
     remain PlaceR; primitive and non-memory places become Value; HashMapRef
     is rejected (conditional_result_def 1098-1113). Thus a conditional
     aggregate base is NOT excluded by expression typing.
   Pop: MemoryPlace and StoragePlace yield PlaceR, including the retained
     popped-element path; ImmutablePlace yields Value (pop_place_def 1261).
     It can return an aggregate element and so can be an outer subscript base.
   Literal, FlagMember, StructLit, Builtin, TypeBuiltin: Value only.
     eval_expr_def 1545,1551-1559,1570-1585,1590-1595.
   Call: successful IntCall, ExtCall, Send, raw calls, raw log, selfdestruct,
     create return Value; raw revert has no success. See eval_expr 1596-1735,
     eval_raw_call 914-954, eval_ext_call 1058-1095, eval_send 1111-1143,
     and eval_create in vyperCreate. Located compiler outputs for aggregates
     do not change these SOURCE result classes.
   This classification is not an execution theorem or a proof of pointer
   checks. well_typed_expr imposes types but no operand pointer judgments.

   Minimal unsupported recursive branch:
     outer base = Subscript NoneT (TopLevelName NoneT nsid) key
     outer index = idx, mapping root type = HashMapT kt (HashMapT kt' vt).
   The checked mapping_key_place_typing permits an arbitrary well-typed key.
   well_typed_expr's mapping alternative uses type_place_expr, not a
   well_typed_expr premise for the mapping-valued base (type system 754-758).
   The checked mapping_root_not_well_typed_expr illustrates why applying
   body_expr_ptr_ok to that root need not yield any execution theorem.
   compile_subscript_def 2280,2286 executes compile_expr root then lower_value
   key; nested outer execution needs both before it can run lower_value idx.
   Frozen hypotheses give body_expr_ptr_ok ONLY for the entire base and
   conditionally for idx, not for key or the root. A syntax induction might
   supply a strengthened mapping-base auxiliary for the root, but supplies
   no expr_sim_ptr for arbitrary embedded key from those hypotheses. Whole-
   base expr_vv_sim_ptr cannot be invoked for its successful HashMapRef,
   which expr_vv_res_ok rejects (checked in bodyPtrSubscriptTiming).

   Other recursive callbacks / provenance:
   - Name and TopLevelName: no recursive expression; concrete address relation
     could be proved directly, but this does not cover arbitrary bases.
   - Subscript and Attribute bases: compile_expr callback needs recursively
     strengthened identity. Internal subscript key/index needs its own ptr
     execution, absent from frozen hypotheses. Attribute itself adds ADD.
   - IfExp: compiler lower_value condition and compile_expr chosen arm
     (exprLowering 2942-2969) need pointer executions of condition/arm, neither
     supplied by the whole-base judgment. Value/place semantic distinction
     must survive compile_ifexp_arm and PHI as well.
   - Pop: compile_get_target_ptr callback on target indices then pop suffix
     (3012-3029). Body judgment for Pop is not a judgment for those indices.
   - Value-only constructors: existing whole-base judgment can be consumed
     at admissible call sites for captured values; it cannot establish a
     stronger identity theorem for the PlaceR constructors above.
   - Outer idx: its judgment DOES follow from the frozen conditional premise
     after any successful outer-base evaluation. That does not grant inner
     keys or indices. C1.7.2 retains coverage, not source-place identity.

   Target interfaces are distinct:
   targetPlaceSimCases.target_subscript_case 305-311 requires expression S1
   judgments for EACH target index. target_case_all 318 requires target_idx_case;
   target_idx_case_ok 336 additionally requires expr_ok for every index and
   no internal calls. target_place_sim 349 consumes target_sim and executes
   compile_get_target_ptr against eval_target_place, yielding uncounted
   frag_exec plus target_post/place_ptr_rel, not compile_expr or ptr paths.
   place_ptr_rel_vars_frame 186 transports identity only after it exists.
   No interface inspected supplies the missing expression ptr execution.
   placeTypingProps place_type_checked_place(_on_defined) connects dispatch
   metadata to type_place_expr; it is a typing, not execution, boundary.
   S1 reference exprSimPlaces compile_subscript_case 104 delegates map and
   array to exprSimSubscriptMap/Array, whose reference proofs remain admitted.
   Their comments explicitly identify this same missing strengthening.

   Decision: syntax-directed strengthening from only the frozen operand
   judgments is NOT closed under its proposed recursion. Do not implement
   a broad auxiliary or more conditional suffix lemmas on that assumption.
   This is a missing-premise/interface result, NOT a counterexample to the
   frozen implication. Further strategy must justify stronger execution from
   independent existing theorems, or authorize a checked target-falsification
   probe; no change to frozen source or task is justified by this audit.
*)
