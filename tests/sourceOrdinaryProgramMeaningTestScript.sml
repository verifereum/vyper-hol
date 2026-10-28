(* Finite #543 composition only: 36 ordinary programs, 40 original bodies,
   and the nine already certified ordinary compiler successes. *)
Theory sourceOrdinaryProgramMeaningTest
Ancestors
  sourceOrdinaryProgramWitnessTest sourceOrdinaryProgramParityTest
  sourceMeaningLocationWitnessTest sourceMeaningLocationBody
  sourceOrdinaryProgram sourceSyntax sourceModuleDefs
  vyperInterpreter vyperContext vyperAST finite_map list

(* Shared names, return type, original body and runtime body are parameters of
   ONE rule. Concrete membership premises below are proved by kernel EVAL;
   neither the source derivation nor the evaluator equality is assumed. *)
Theorem source_ordinary_function_body_meaning:
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained /\
  program = SourceProgram (SourceModule declarations) imports /\
  MEM (SD_Function name decorators args defaults annotation original) declarations /\
  MEM (src,tops) (retained_executable retained) /\
  MEM (FunctionDecl visibility mutability nr raw name params runtime_defaults ret runtime_body) tops /\
  source_location_bodies_source refs type_ids ctx ret original meanings final_refs final_ctx /\
  source_location_bodies_code FEMPTY meanings runtime_body ==>
  source_ordinary_program fuel trust policies keys contexts program claims = SM_Ok retained /\
  retained_source retained = program /\
  program = SourceProgram (SourceModule declarations) imports /\
  MEM (SD_Function name decorators args defaults annotation original) declarations /\
  MEM (src,tops) (retained_executable retained) /\
  MEM (FunctionDecl visibility mutability nr raw name params runtime_defaults ret runtime_body) tops /\
  source_location_bodies_source refs type_ids ctx ret original meanings final_refs final_ctx /\
  source_location_bodies_code FEMPTY meanings runtime_body /\
  (!cx st. get_tenv cx = FEMPTY ==>
    eval_stmts cx runtime_body st = source_location_runs cx meanings st)
Proof
  strip_tac >>
  drule source_ordinary_program_retains_source >> strip_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT2 (SPEC ``FEMPTY:nsid |-> type_args``
    source_location_body_code_evaluates)) >>
  disch_then (qspec_then `cx` mp_tac) >> simp[]
QED

fun optional_fields expected tm = let val (h,args) = strip_comb tm in
  if is_const h andalso fst (dest_const h) = expected then SOME args else NONE end;
fun fields expected tm = case optional_fields expected tm of SOME args => args
  | NONE => raise Fail ("ordinary meaning: expected " ^ expected);
fun items tm = #1 (listSyntax.dest_list tm);
fun member x xs = EQT_ELIM (EVAL ``MEM ^x ^xs``);
fun fetch thy name = DB.fetch thy name;
val ordinary_owner = "sourceOrdinaryProgramWitnessTest";
val meaning_owner = "sourceMeaningLocationWitnessTest";
val parity_owner = "sourceOrdinaryProgramParityTest";
(* Read the finite inventory from the existing kernel exports, not a second
   loader run or an assertion comparing two ML ASTs. *)
val suffix = "_ordinary_phase";
val phases = List.filter (fn (name,_) => String.isSuffix suffix name)
  (DB.thms ordinary_owner);
val bodies = ref 0;
val compiled = ref 0;
val compiler_names = ref ([]:string list);
val compiler_suffix = "_ordinary_python_parity";
val compiler_exports = List.filter (fn (name,_) => String.isSuffix compiler_suffix name)
  (DB.thms parity_owner);

fun certify (export,phase) = let
  val name = String.substring (export,0,size export - size suffix)
  val retained = hd (fields "SM_Ok" (rhs (concl phase)))
  val phase_args = fields "source_ordinary_program" (lhs (concl phase))
  val program = List.nth (phase_args,5)
  val [syntax,imports] = fields "SourceProgram" program
  val [declarations] = fields "SourceModule" syntax
  val modules = rhs (concl (EVAL ``retained_executable ^retained``))
  val [(src,tops)] = map pairSyntax.dest_pair (items modules)
  fun body declaration = case optional_fields "SD_Function" declaration of NONE => ()
  | SOME [id,decorators,args,defaults,annotation,original] => let
      val label = stringSyntax.fromHOLstring id
      val stem = name ^ "_" ^ label
      val source = fetch meaning_owner (stem ^ "_original_body")
      val code = fetch meaning_owner (stem ^ "_body_code")
      val candidates = List.filter (fn tl => case optional_fields "FunctionDecl" tl of
        SOME args => aconv (List.nth (args,4)) id | NONE => false) (items tops)
      val [runtime] = candidates
      (* MATCH_MP below unifies the original/meaning pair in source, the
         meaning/runtime pair in code, the common name/return type, and BOTH
         concrete declarations in the actual ordinary retained artifact. *)
      val facts = [REFL program,member declaration declarations,
        EQT_ELIM (EVAL ``MEM (^src,^tops) (retained_executable ^retained)``),
        member runtime tops,source,code]
      fun compose phase = MATCH_MP source_ordinary_function_body_meaning
        (LIST_CONJ (phase::facts))
      val certificate = compose phase
      val _ = save_thm (stem ^ "_ordinary_body_meaning",certificate)
      val _ = bodies := !bodies + 1
      val _ = print ("ORDINARY_ORIGINAL_BODY_MEANING " ^ name ^ "." ^ label ^ "\n")
      val compiler = List.find (fn (export,_) => export = name ^ compiler_suffix) compiler_exports
      val _ = case compiler of NONE => () | SOME (_,compilation) => let
        (* Derive the phase afresh FROM this actual compile equation. Applying
           the same rule to the same membership facts kernel-links the compile
           input/output artifact to this original and runtime body. *)
        val equations = MATCH_MP source_ordinary_compile_equations compilation
        val compiled_body = compose (CONJUNCT1 equations)
        val _ = save_thm (stem ^ "_ordinary_compile_body_meaning",
          CONJ compilation (CONJ equations compiled_body))
        in compiled := !compiled + 1; compiler_names := name :: !compiler_names end
      in () end
  | SOME _ => raise Fail "ordinary source function arity"
  in List.app body (items declarations) end;

val () = if length phases = 36 andalso length compiler_exports = 9 then ()
  else raise Fail "ordinary composition program/compiler inventory changed";
val () = List.app certify phases;
val () = if !bodies = 40 andalso !compiled = 9 andalso
    List.all (fn name => length (List.filter (fn other => name = other)
      (!compiler_names)) = 1) (!compiler_names) then ()
  else raise Fail "ordinary composition body inventory incomplete";
(* Audit every export, including the general helper, and every input theory.
   Only disk provenance is allowed: no hypotheses, axioms, or cheat oracles. *)
fun audit thy = let val exports = DB.thms thy in
  List.app (fn (name,th) => let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (hyp th) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("ordinary meaning kernel audit: " ^ thy ^ "." ^ name) end) exports;
  print ("ORDINARY_MEANING_KERNEL_CLOSED " ^ thy ^ " exports=" ^
    Int.toString (length exports) ^ "\n") end;
val () = if length (DB.thms "sourceOrdinaryProgramMeaningTest") = 50 then ()
  else raise Fail "ordinary meaning export inventory changed";
val () = List.app audit [ordinary_owner,meaning_owner,parity_owner,
  "sourceOrdinaryProgramMeaningTest"];
val () = print "ORDINARY_MEANING_TOTAL programs=36 bodies=40 compile_bodies=9 remaining=0\n";
