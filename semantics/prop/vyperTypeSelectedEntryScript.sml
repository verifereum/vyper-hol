(*
 * Selected external-entry boundary (#591, first piece of #420).
 *
 * selected_entry am tx mods sel says that call_external's three setup
 * lookups succeed for tx: the target has sources mods, and
 * lookup_exported_function selects sel = (mut,nr,args,dflts,ret,body).  Under
 * it, call_external is exactly the selected call_external_function step;
 * otherwise call_external fails with a RuntimeError and leaves the machine
 * unchanged.  Defaults, argument binding and deployment constants are other
 * pieces of #420.
 *
 * TOP-LEVEL: selected_entry_def, selected_entry_module_code,
 *            call_external_selected_entry, call_external_not_selected_entry,
 *            selected_entry_checked_cases, selected_entry_unique.
 *)

Theory vyperTypeSelectedEntry
Ancestors
  alist option pair
  vyperContext vyperInterpreter
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractGetter

val _ = Parse.hide "body";

Definition selected_entry_def:
  selected_entry am tx mods sel <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx
         (find_function_module am tx.target tx.function_name))
      am tx.function_name = SOME sel
End

(* A successful export lookup already found the selected module's code, so
   the boundary needs no separate get_module_code premise. *)
Theorem selected_entry_module_code:
  selected_entry am tx mods sel /\
  src = find_function_module am tx.target tx.function_name ==>
  ?ts.
    get_module_code
      (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
    ALOOKUP mods src = SOME ts
Proof
  rw[selected_entry_def] >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  gvs[lookup_exported_function_def, find_function_module_def,
      get_self_code_def, get_module_code_def,
      initial_evaluation_context_def, AllCaseEqs()]
QED

Theorem call_external_selected_entry:
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  ALOOKUP mods src = SOME ts ==>
  call_external orc gobs am tx =
    case call_external_function orc gobs am cx nr mut ts mods args dflts tx.args
           body ret of
      (INL value, am', rqs) => (INL value, finalize_pending_deletions am', rqs)
    | failure => failure
Proof
  rw[selected_entry_def] >>
  simp[Once call_external_def] >>
  Cases_on `find_function_module am tx.target tx.function_name` >>
  gvs[get_self_code_def, get_module_code_def, initial_evaluation_context_def]
QED

(* Outside the boundary call_external is a setup failure: a RuntimeError with
   the machine unchanged and no requests. *)
Theorem call_external_not_selected_entry:
  ~(?mods sel. selected_entry am tx mods sel) ==>
  ?msg. call_external orc gobs am tx = (INR (Error (RuntimeError msg)), am, [])
Proof
  rw[selected_entry_def] >>
  simp[Once call_external_def] >>
  Cases_on `ALOOKUP am.sources tx.target` >> gvs[] >>
  Cases_on `lookup_exported_function
              (initial_evaluation_context am.sources am.layouts tx
                 (find_function_module am tx.target tx.function_name))
              am tx.function_name` >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> metis_tac[]
QED

(* For a checked contract the selected tuple is an explicit external function
   of the selected module or a public getter's generated tuple. *)
Theorem selected_entry_checked_cases:
  check_contract F am.layouts tx.target mods = SOME art /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name ==>
  ?ts.
    ALOOKUP mods src = SOME ts /\
    ((?raw.
        MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret
               body) ts) \/
     (?decl.
        MEM decl ts /\
        is_public_getter_decl tx.function_name decl /\
        external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body)))
Proof
  strip_tac >>
  drule_all selected_entry_module_code >> strip_tac >>
  qexists `ts` >> simp[] >>
  irule lookup_exported_function_checked_cases_selected >>
  gvs[selected_entry_def] >> metis_tac[]
QED

Theorem selected_entry_unique:
  selected_entry am tx mods sel /\ selected_entry am tx mods' sel' ==>
  mods' = mods /\ sel' = sel
Proof
  rw[selected_entry_def] >> gvs[]
QED
