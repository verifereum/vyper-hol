(* Emit the existing CV translation of run_test, without changing its semantics. *)
Theory vyperTestEmit
Ancestors
  vyperTestRunner cv jsonToVyper vyperState vyperValueOperation
  jsonToVyperCV
Libs
  EmitML cv_transLib cv_repLib cv_typeLib cv_miscLib wordsLib

fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_outputs
  [".emit/RunTestML.sig", ".emit/RunTestML.sml",
   ".emit/JsonConstructors.sml", ".emit/json-libs.mlb",
   ".emit/json/JSON.sml", ".emit/json/JSONSource.sml",
   ".emit/json/JSONParser.sig", ".emit/json/JSONParser.sml",
   ".emit/json/JSONErrors.sig", ".emit/json/JSONErrors.sml",
   ".emit/json/JSONUtil.sig", ".emit/json/JSONUtil.sml",
   ".emit/json/JSONDecode.sig", ".emit/json/JSONDecode.sml"];
val () = OS.FileSys.mkDir ".emit" handle OS.SysErr _ => ();

(* Unlike cv_compute, SML evaluates function arguments eagerly. *)
Theorem cv_if_native:
  cv_if p x y = if cv$c2n p = 0 then y else x
Proof
  Cases_on `p` >| [
    rename1 `cv_if (cv$Num n) _ _` >> Cases_on `n` >>
    simp[cv_if_def, c2n_def],
    simp[cv_if_def, c2n_def]]
QED

Definition test_result_summary_def:
  test_result_summary (res : unit + vyperState$exception) =
    case res of
      INL _ => (T, "")
    | INR ex => (F,
        case ex of
          Error (RuntimeError message) => "RuntimeError: " ++ message
        | Error (TypeError message) => "TypeError: " ++ message
        | Error (RevertData _) => "RevertData"
        | AssertException message => "AssertException: " ++ message
        | BreakException => "BreakException"
        | ContinueException => "ContinueException"
        | ReturnException _ => "ReturnException")
End

val () = cv_auto_trans test_result_summary_def;

val entry = prim_mk_const {Thy = "vyperTestRunner", Name = "cv_run_test"};
val frontend = prim_mk_const
  {Thy = "jsonToVyperCV", Name = "cv_translate_annotated_ast"};
val summary = prim_mk_const
  {Thy = "vyperTestEmit", Name = "cv_test_result_summary"};
fun head_of th = fst (strip_comb (lhs (concl (SPEC_ALL th))));
fun add_equation (th,acc) =
  if List.exists (aconv (head_of th) o head_of) acc then acc else th :: acc;
(* Word translations can retain closed DIMINDEX arithmetic inside Num.
   EVAL alone leaves DIMINDEX unchanged; DEPTH_CONV repeats successful conversions,
   so require progress as well as using the word-aware kernel conversion. *)
fun normalize_cv_literals (i,{thm = DefnBase.STDEQNS th,...}
                              : DefnBase.defn_presentation) = let
      val normalized = CONV_RULE (DEPTH_CONV (fn tm =>
        if cvSyntax.is_cv_num tm andalso null (free_vars (rand tm)) andalso
           not (numSyntax.is_numeral (rand tm))
        then RAND_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) tm
        else NO_CONV tm)) th
    in
      if aconv (concl th) (concl normalized) then () else let
        val name = "native_cv_literals_" ^ Int.toString i
        val _ = save_thm (name,normalized)
      in DefnBase.register_defn {tag = "user",thmname = name} end
    end
  | normalize_cv_literals _ = ();
val () = List.app normalize_cv_literals (Lib.enumerate 0
  (List.concat (map (fn thy => DefnBase.thy_userdefs {thyname = thy})
    ["jsonToVyperTypeCV","jsonToVyperExprCV","jsonToVyperCV"])));

val equations = List.foldl add_equation []
  (cv_eqs_for entry @ cv_eqs_for frontend @ cv_eqs_for summary);
val () = print ("Emitting run_test: " ^ Int.toString (length equations) ^
                " CV equations\n");

(* Stable distinct SML names also avoid punctuation in record accessor names. *)
fun register (i,th) = let
  val c = head_of th
in
  ConstMapML.prim_insert
    (c, (false, "RunTest", "cvfun" ^ Int.toString i, type_of c))
end;
val () = List.app register (Lib.enumerate 0 equations);
fun number c name =
  ConstMapML.prim_insert (c, (false, "num", name, type_of c));
val () = List.app (fn (c,n) => number c n)
  [(``$+ : num -> num -> num``, "add"),
   (``$- : num -> num -> num``, "sub"),
   (``$* : num -> num -> num``, "mul"),
   (``$DIV``, "divide"), (``$MOD``, "modulo"),
   (``$< : num -> num -> bool``, "less"), (``SUC``, "suc")];

val primitives =
  [cv_fst_def, cv_snd_def, cv_ispair_def, c2n_def,
   cv_add_def, cv_sub_def, cv_mul_def, cv_div_def, cv_mod_def,
   cv_eq_def, cv_lt_def];
val normalize = REWRITE_RULE [cv_if_native, GSYM arithmeticTheory.ONE];
(* EmitML's DEFN path builds its nonfix declaration from HOL names, ignoring
   ConstMapML renaming. Print the private equations with its public printer
   instead, so dotted record-accessor names never enter that declaration. *)
fun register_primitive constructor c =
  ConstMapML.prim_insert
    (c, (constructor, "RunTest", #Name (dest_thy_const c), type_of c));
val () = List.app (register_primitive false o head_of)
  (List.concat (map (CONJUNCTS o SPEC_ALL) primitives));
val () = List.app (fn name => register_primitive true
  (prim_mk_const {Thy = "cv", Name = name})) ["Num","Pair"];
val runtime_equations = let
  val chunks = ref []
  val th = !EmitML.reshape_thm_hook (LIST_CONJ (map normalize equations))
  val () = PP.prettyPrint (fn s => chunks := s :: !chunks,75)
    (EmitML.pp_defn_as_ML ["RunTest","num"] (concl th))
in String.concat (List.rev (!chunks)) end;
val () = emitML ".emit" ("RunTest",
  [OPEN ["num"], MLSIG "type num = numML.num",
   DATATYPE `cv = Num num | Pair cv cv`] @
  map (DEFN o normalize) primitives @
  [MLSTRUCT runtime_equations,
   MLSIG "val run_test : cv -> cv",
   MLSTRUCT ("val run_test = " ^ #3 (ConstMapML.apply entry)),
   MLSIG "val translate_annotated_ast : cv -> cv",
   MLSTRUCT ("val translate_annotated_ast = " ^ #3 (ConstMapML.apply frontend)),
   MLSIG "val test_result_summary : cv -> cv",
   MLSTRUCT ("val test_result_summary = " ^ #3 (ConstMapML.apply summary))]);

(* Derive constructor encoders from the actual registered CV representations.
   In particular, large records must not be encoded by guessing field order. *)
val constructors_out = TextIO.openOut ".emit/JsonConstructors.sml";
fun put s = TextIO.output (constructors_out,s);
fun quoted s = "\"" ^ String.toString s ^ "\"";
fun result_type ty =
  case total dom_rng ty of NONE => ty | SOME (_,r) => result_type r;
fun argument_types ty =
  case total dom_rng ty of NONE => [] | SOME (a,r) => a :: argument_types r;
fun key c = let val {Thy,Name,...} = dest_thy_const c
  in Thy ^ "." ^ Name end;
fun symbolic vars value = let
  val cvs = List.map (fn (i,_) => mk_var ("cvarg" ^ Int.toString i,cvSyntax.cv))
    (Lib.enumerate 0 vars)
  (* cv_rep_for translates variables trivially, before consulting its hypotheses.
     Abstract their from-functions in the resulting kernel-derived encoding. *)
  fun assumption (v,cv) =
    ASSUME (mk_eq (mk_comb (cv_typeLib.from_term_for (type_of v),v),cv))
  val assumptions = ListPair.map assumption (vars,cvs)
  val th = CONV_RULE (cv_rep_cv_tm_conv (PURE_REWRITE_CONV assumptions))
    (cv_rep_for [] value)
  val expr = cv_rep_cv_tm (concl th)
  fun tree tm =
    List.exists (aconv tm) cvs orelse
    (cvSyntax.is_cv_num tm andalso numSyntax.is_numeral (rand tm)) orelse
    (cvSyntax.is_cv_pair tm andalso
     let val (a,b) = cvSyntax.dest_cv_pair tm in tree a andalso tree b end)
  val () = if tree expr then ()
    else raise Fail ("non-constructor CV encoding: " ^ term_to_string expr)
in (cvs,expr) end;
fun encoder (vars,expr) = (
  put ("fn [" ^ String.concatWith "," (map (fst o dest_var) vars) ^ "] => ");
  PP.prettyPrint (fn s => put s,100)
    (EmitML.pp_term_as_ML ["RunTest"] RIGHT expr);
  put " | _ => raise Fail \"constructor argument count\"");
val constructors = List.filter TypeBase.is_constructor
  (List.concat (map constants ["jsonAST","vyperTestRunner","contractABI","vyperAST"]));
val () = put "structure JsonConstructors = struct\nopen RunTestML\nval nodes = [\n";
val first_node = ref true;
fun emit_constructor c = let
  val tys = argument_types (type_of c)
  val vars = map (fn (i,ty) => mk_var ("arg" ^ Int.toString i,ty))
    (Lib.enumerate 0 tys)
  val () = ignore (cv_typeLib.from_to_thm_for (result_type (type_of c)))
  val encoded = symbolic vars (list_mk_comb (c,vars))
in
  if !first_node then first_node := false else put ",\n";
  put ("(" ^ quoted (key c) ^ ", "); encoder encoded; put ")"
end;
val () = List.app emit_constructor constructors;
val () = put "\n]\nval records = [\n";
val first_record = ref true;
fun emit_record c = let
  val ty = result_type (type_of c)
in if not (TypeBase.is_record_type ty) then () else let
  val fields = TypeBase.fields_of ty
  val vars = map (fn (i,(_,info)) =>
    mk_var ("field" ^ Int.toString i,#ty info)) (Lib.enumerate 0 fields)
  val labels = map #1 fields
  val value = TypeBase.mk_record (ty,ListPair.zip (labels,vars))
  val encoded = symbolic vars value
  val {Thy,Tyop,...} = dest_thy_type ty
in
  if !first_record then first_record := false else put ",\n";
  put ("(" ^ quoted (Thy ^ "." ^ Tyop) ^ ", [" ^
       String.concatWith "," (map quoted labels) ^ "], ");
  encoder encoded; put ")"
end end;
val () = List.app emit_record constructors;
val () = put "\n]\nend\n";
val () = TextIO.closeOut constructors_out;

(* Compile against the portable JSON implementation from the pinned HOL. *)
val () = OS.FileSys.mkDir ".emit/json" handle OS.SysErr _ => ();
val json_files =
  ["JSON.sml","JSONSource.sml","JSONParser.sig","JSONParser.sml",
   "JSONErrors.sig","JSONErrors.sml","JSONUtil.sig","JSONUtil.sml",
   "JSONDecode.sig","JSONDecode.sml"];
fun copy_json name = let
  val source = TextIO.openIn
    (OS.Path.concat (Globals.HOLDIR,"src/portableML/json/" ^ name))
  val content = TextIO.inputAll source
  val () = TextIO.closeIn source
  val dest = TextIO.openOut (".emit/json/" ^ name)
in TextIO.output (dest,content); TextIO.closeOut dest end;
val () = List.app copy_json json_files;
val json_mlb = TextIO.openOut ".emit/json-libs.mlb";
val () = TextIO.output (json_mlb,
  "$(SML_LIB)/basis/basis.mlb\n" ^
  String.concat (map (fn name => "json/" ^ name ^ "\n") json_files));
val () = TextIO.closeOut json_mlb;
