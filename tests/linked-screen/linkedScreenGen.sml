(* Generator of the linked units the screen evaluates.

   A unit is three modules: main (0, src NONE), module 1 (allocated) and
   module 2 (unallocated: its storage pin "s" has no slot). One site in
   module D refers to a name "x" (or "S", "F", "E", "Er", "__init__") with
   an absolute qualifier t: NONE, SOME 1, SOME 2 or the missing SOME 9.
   Every declaration of the name carries a value distinct per module
   (100 + m), so a body that resolves to another declaration shows a
   different value, slot, selector or memory layout.

   Axes enumerated: site (D, whether module 2's site is called), caller
   visibility, place, qualifier, presence (which modules declare the name)
   and kind. Units are plain strings of HOL syntax; the runner parses them. *)
structure linkedScreenGen = struct

val u256 = "(BaseT (UintT 256))"
val u8 = "(BaseT (UintT 8))"
fun i n = Int.toString n
fun lit n = "(Literal " ^ u256 ^ " (IntL " ^ i n ^ "))"
fun litT ty n = "(Literal " ^ ty ^ " (IntL " ^ i n ^ "))"
fun qs t = if t = 0 then "(NONE:num option)" else "(SOME " ^ i t ^ ")"
fun nsid t x = "(" ^ qs t ^ ", \"" ^ x ^ "\")"
fun lst xs = "[" ^ String.concatWith "; " xs ^ "]"
fun str s = "\"" ^ s ^ "\""

datatype kind =
    KIntInt | KIntExt | KIntDep
  | KSto of bool | KTra of bool | KHm of bool  (* true: write then read *)
  | KImm | KConst | KChain of int              (* x = t2.y *)
  | KStructLit | KFlag | KLog | KRaise | KAssert
  | KStructT | KFlagT

datatype place = PBody | PDefault | PConstInit | PFieldStruct | PFieldEvent
               | PFieldError

datatype vis = VExt | VInt | VDep

fun kind_name k = case k of
    KIntInt => "IntCall_Internal" | KIntExt => "IntCall_External"
  | KIntDep => "IntCall_Deploy"
  | KSto w => if w then "Storage_write" else "Storage_read"
  | KTra w => if w then "Transient_write" else "Transient_read"
  | KHm w => if w then "HashMap_write" else "HashMap_read"
  | KImm => "Immutable" | KConst => "Constant"
  | KChain t => "ConstChain_" ^ (if t = 0 then "NONE" else "SOME" ^ i t)
  | KStructLit => "StructLit" | KFlag => "FlagMember" | KLog => "Log"
  | KRaise => "Raise_custom" | KAssert => "Assert_custom"
  | KStructT => "StructT" | KFlagT => "FlagT"

fun place_name p = case p of
    PBody => "body" | PDefault => "default_arg" | PConstInit => "const_init"
  | PFieldStruct => "struct_field" | PFieldEvent => "event_field"
  | PFieldError => "error_field"

fun vis_name v = case v of VExt => "External" | VInt => "Internal" | VDep => "Deploy"
fun vis_term v = vis_name v

val expr_kinds = [KIntInt, KIntExt, KSto false, KTra false, KHm false, KImm,
  KConst, KChain 0, KChain 1, KChain 2, KChain 9, KStructLit, KFlag]
val stmt_kinds = [KIntDep, KSto true, KTra true, KHm true, KLog, KRaise, KAssert]
val type_kinds = [KStructT, KFlagT]

fun is_expr_kind k = List.exists (fn k' => k = k') expr_kinds
fun is_type_kind k = k = KStructT orelse k = KFlagT

(* ===== Declarations of the target name in module m ===== *)

fun struct_fields m =
  case m of 0 => [("a",1),("b",2)] | 1 => [("b",2),("a",1)]
          | _ => [("a",1),("b",2),("c",3)]
fun flag_members m = case m of 0 => ["A","B"] | 1 => ["B","A"] | _ => ["A","B","C"]
fun event_fields m = case m of
    0 => [("a",u256,"F")] | 1 => [("a",u256,"T")]
  | _ => [("a",u256,"F"),("b",u256,"F")]
fun error_fields m = case m of
    0 => [("a",u256)] | 1 => [("a",u8)] | _ => [("a",u256),("b",u256)]

fun storage_slot m = if m < 2 then "(SOME " ^ i (10 + m) ^ ")" else "NONE"

(* imm_off: offset of module m's immutable; presence-ordered *)
fun target_decls kind m imm_off = case kind of
    KIntInt => ["FunctionDecl Internal View F F \"x\" [] [] " ^ u256 ^
                " [Return (SOME " ^ lit (100 + m) ^ ")]"]
  | KIntExt => ["FunctionDecl External View F F \"x\" [] [] " ^ u256 ^
                " [Return (SOME " ^ lit (100 + m) ^ ")]"]
  | KIntDep => []   (* the module's __init__, assembled below *)
  | KSto _ => ["VariableDecl Private Storage \"x\" " ^ u256 ^ " " ^ storage_slot m]
  | KTra _ => ["VariableDecl Private Transient \"x\" " ^ u256 ^ " " ^ storage_slot m]
  | KHm _ => ["HashMapDecl Private F \"x\" " ^ u256 ^ " (Type " ^ u256 ^ ") " ^
              storage_slot m]
  | KImm => ["VariableDecl Private Immutable \"x\" " ^ u256 ^ " (SOME " ^
             i imm_off ^ ")"]
  | KConst => ["VariableDecl Private (Constant " ^ lit (100 + m) ^ ") \"x\" " ^
               u256 ^ " NONE"]
  | KChain t2 => ["VariableDecl Private (Constant (TopLevelName " ^ u256 ^ " " ^
                  nsid t2 "y" ^ ")) \"x\" " ^ u256 ^ " NONE"]
  | KStructLit => struct_decl m
  | KStructT => struct_decl m
  | KFlag => flag_decl m
  | KFlagT => flag_decl m
  | KLog => ["EventDecl \"E\" " ^ lst (map (fn (n,ty,ix) =>
               "((" ^ str n ^ ", " ^ ty ^ "), " ^ ix ^ ")") (event_fields m))]
  | KRaise => error_decl m
  | KAssert => error_decl m
and struct_decl m = ["StructDecl \"S\" " ^
  lst (map (fn (n,_) => "(" ^ str n ^ ", " ^ u256 ^ ")") (struct_fields m))]
and flag_decl m = ["FlagDecl \"F\" " ^ lst (map str (flag_members m))]
and error_decl m = ["ErrorDecl \"Er\" " ^
  lst (map (fn (n,ty) => "(" ^ str n ^ ", " ^ ty ^ ")") (error_fields m))]

(* Every module declares y for the constant chains. *)
fun chain_y m = "VariableDecl Private (Constant " ^ lit (200 + m) ^ ") \"y\" " ^
  u256 ^ " NONE"

(* ===== The reference itself, typed after the declaration t names ===== *)

fun intended_struct t = struct_fields (if t > 2 then 0 else t)
fun intended_error t = error_fields (if t > 2 then 0 else t)
fun intended_event t = event_fields (if t > 2 then 0 else t)

fun ref_expr kind t = case kind of
    KIntInt => "(Call " ^ u256 ^ " (IntCall " ^ nsid t "x" ^ ") [] NONE)"
  | KIntExt => "(Call " ^ u256 ^ " (IntCall " ^ nsid t "x" ^ ") [] NONE)"
  | KSto _ => "(TopLevelName " ^ u256 ^ " " ^ nsid t "x" ^ ")"
  | KTra _ => "(TopLevelName " ^ u256 ^ " " ^ nsid t "x" ^ ")"
  | KHm _ => "(Subscript " ^ u256 ^ " (TopLevelName NoneT " ^ nsid t "x" ^ ") " ^
             lit 1 ^ ")"
  | KImm => "(TopLevelName " ^ u256 ^ " " ^ nsid t "x" ^ ")"
  | KConst => "(TopLevelName " ^ u256 ^ " " ^ nsid t "x" ^ ")"
  | KChain _ => "(TopLevelName " ^ u256 ^ " " ^ nsid t "x" ^ ")"
  | KStructLit => let val n = nsid t "S" in
      "(Attribute " ^ u256 ^ " (StructLit (StructT " ^ n ^ ") " ^ n ^ " " ^
      lst (map (fn (f,v) => "(" ^ str f ^ ", " ^ lit v ^ ")") (intended_struct t)) ^
      ") \"b\")" end
  | KFlag => let val n = nsid t "F" in
      "(TypeBuiltin " ^ u256 ^ " Convert (FlagT " ^ n ^ ") [FlagMember (FlagT " ^
      n ^ ") " ^ n ^ " \"B\"])" end
  | _ => raise Fail "ref_expr: not an expression kind"

fun write_target kind t = case kind of
    KHm _ => "(BaseTarget (SubscriptTarget (TopLevelNameTarget " ^ nsid t "x" ^
             ") " ^ lit 1 ^ "))"
  | _ => "(BaseTarget (TopLevelNameTarget " ^ nsid t "x" ^ "))"

fun custom_error t = "(CustomError " ^ nsid t "Er" ^ " " ^
  lst (List.tabulate (length (intended_error t), fn j =>
         litT (#2 (List.nth (intended_error t, j))) (5 + j))) ^ " [])"

(* Statements and the value the site returns. *)
fun ref_stmts kind t = case kind of
    KIntDep => (["Expr (Call NoneT (IntCall " ^ nsid t "__init__" ^ ") [] NONE)"],
                lit 1)
  | KSto true => (["Assign " ^ write_target kind t ^ " " ^ lit 77],
                  ref_expr (KSto false) t)
  | KTra true => (["Assign " ^ write_target kind t ^ " " ^ lit 77],
                  ref_expr (KTra false) t)
  | KHm true => (["Assign " ^ write_target kind t ^ " " ^ lit 77],
                 ref_expr (KHm false) t)
  | KLog => (["Log " ^ nsid t "E" ^ " " ^
              lst (List.tabulate (length (intended_event t), fn j => lit (5 + j)))],
             lit 1)
  | KRaise => (["Raise (RaiseCustomError " ^ custom_error t ^ ")"], lit 1)
  | KAssert => (["Assert (Literal (BaseT BoolT) (BoolL F)) (AssertCustomError " ^
                 custom_error t ^ ")"], lit 1)
  | _ => ([], ref_expr kind t)

fun ref_type kind t = case kind of
    KStructT => "(StructT " ^ nsid t "S" ^ ")"
  | KFlagT => "(FlagT " ^ nsid t "F" ^ ")"
  | _ => raise Fail "ref_type"

(* ===== Units ===== *)

type unit_spec =
  {id : string, axes : (string * string) list,
   mods : string, exps : string, sl : string, tl : string,
   fname : string, sel : string, hm : bool}

fun site_name v = if v = VDep then "__init__" else "f"

fun build {d, called, v, place, t, pres, kind} = let
  val mods_ix = [0, 1, 2]
  fun present m = List.exists (fn m' => m = m') pres
  val imm_rank = let fun r m = length (List.filter (fn m' => m' < m) pres) in r end
  val s_slot = fn m => if m < 2 then "(SOME " ^ i m ^ ")" else "NONE"
  fun selfq m = m
  (* The site's own pieces. *)
  val (site_extra, site_stmts, site_args, site_dflts) = let
      fun finish (stmts, e) =
        if v = VDep then stmts @ ["Assign (BaseTarget (TopLevelNameTarget " ^
                                   nsid (selfq d) "s" ^ ")) " ^ e]
        else stmts @ ["Return (SOME " ^ e ^ ")"]
    in case place of
         PBody => ([], finish (ref_stmts kind t), "[]", "[]")
       | PDefault => ([], finish ([], "(Name " ^ u256 ^ " \"a\")"),
                      "[(\"a\", " ^ u256 ^ ")]", "[" ^ ref_expr kind t ^ "]")
       | PConstInit => (["VariableDecl Private (Constant " ^ ref_expr kind t ^
                         ") \"c\" " ^ u256 ^ " NONE"],
                        finish ([], "(TopLevelName " ^ u256 ^ " " ^
                                    nsid (selfq d) "c" ^ ")"), "[]", "[]")
       | PFieldStruct => (["StructDecl \"W\" [(\"w\", " ^ ref_type kind t ^ ")]"],
                          finish ([], lit 1), "[]", "[]")
       | PFieldEvent => (["EventDecl \"EW\" [((\"w\", " ^ ref_type kind t ^ "), F)]"],
                         finish ([], lit 1), "[]", "[]")
       | PFieldError => (["ErrorDecl \"ErW\" [(\"w\", " ^ ref_type kind t ^ ")]"],
                         finish ([], lit 1), "[]", "[]")
    end
  val site_ret = if v = VDep then "NoneT" else u256
  val site_fn = "FunctionDecl " ^ vis_term v ^ " Nonpayable F F " ^
    str (site_name v) ^ " " ^ site_args ^ " " ^ site_dflts ^ " " ^ site_ret ^
    " " ^ lst site_stmts
  (* __init__ parts of module m (besides main's calls). *)
  fun own_init m =
    (if kind = KImm andalso present m then
       ["Assign (BaseTarget (TopLevelNameTarget " ^ nsid m "x" ^ ")) " ^ lit (100 + m)]
     else []) @
    (if kind = KIntDep andalso present m andalso not (v = VDep andalso m = d) then
       ["Assign (BaseTarget (TopLevelNameTarget " ^ nsid m "s" ^ ")) " ^ lit (100 + m)]
     else [])
  val site_is_init = fn m => v = VDep andalso m = d
  fun init_called m =
    m <> 0 andalso ((kind = KImm andalso present m) orelse
                    (v = VDep andalso m = d andalso called))
  val main_calls = List.mapPartial (fn m =>
      if init_called m then
        SOME ("Expr (Call NoneT (IntCall " ^ nsid m "__init__" ^ ") [] NONE)")
      else NONE) [1, 2]
  fun module_decls m = let
      val pin = ["VariableDecl Private Storage \"s\" " ^ u256 ^ " " ^ s_slot m]
      val targets = if present m then target_decls kind m (32 * imm_rank m) else []
      val ys = case kind of KChain _ => [chain_y m] | _ => []
      val site = if m = d then site_extra @ (if site_is_init m then [] else [site_fn])
                 else []
      val init_body = (if m = 0 then main_calls else []) @ own_init m
      val init =
        if site_is_init m then
          (* the site is this module's constructor; prepend the other parts *)
          ["FunctionDecl Deploy Nonpayable F F \"__init__\" " ^ site_args ^ " " ^
           site_dflts ^ " NoneT " ^ lst (init_body @ site_stmts)]
        else if null init_body then []
        else ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT " ^
              lst init_body]
      val entry = if m <> 0 then [] else let
          val body = if v = VInt andalso called
                     then "Return (SOME (Call " ^ u256 ^ " (IntCall " ^
                          nsid d "f" ^ ") [] NONE))"
                     else "Return (SOME " ^ lit 0 ^ ")"
        in ["FunctionDecl External Nonpayable F F \"entry\" [] [] " ^ u256 ^
            " [" ^ body ^ "]"] end
    in pin @ ys @ targets @ site @ init @ entry end
  val mods = "([" ^ String.concatWith ";\n " (map (fn m =>
      "(" ^ qs m ^ ", " ^ lst (module_decls m) ^ ")") mods_ix) ^
    "] : (num option # toplevel list) list)"
  val exps = if v = VExt andalso d <> 0 andalso called
             then "[(\"f\", " ^ i d ^ ")]" else "([] : (string # num) list)"
  val is_sto = case kind of KSto _ => true | KHm _ => true | _ => false
  val is_tra = case kind of KTra _ => true | _ => false
  fun xslots b = if b then List.mapPartial (fn m =>
        if m < 2 andalso present m
        then SOME ("((" ^ qs m ^ ", \"x\"), " ^ i (10 + m) ^ ")") else NONE) [0, 1]
      else []
  val sl = "(" ^ lst (["((NONE:num option, \"s\"), 0)", "((SOME 1, \"s\"), 1)"] @
                      xslots is_sto) ^ " : storage_layout)"
  val tl = "(" ^ lst (xslots is_tra) ^ " : storage_layout)"
  val fname = if v = VExt andalso (d = 0 orelse called) then "f" else "entry"
  val dtag = i d ^ (if d = 2 then (if called then "c" else "dead") else "")
  val ptag = String.concat (map (fn m => if present m then i m else "-") mods_ix)
  val ttag = if t = 0 then "NONE" else if t = 9 then "SOME9" else "SOME" ^ i t
  val qrel = if t = 9 then "missing" else if t = d then "self" else "other"
  val id = String.concatWith "." [dtag, vis_name v, place_name place, ttag, ptag,
                                  kind_name kind]
  val axes = [("site", dtag), ("vis", vis_name v), ("place", place_name place),
              ("qualifier", ttag), ("qual_rel", qrel), ("presence", ptag),
              ("target_declared", if t < 3 andalso present t then "yes" else "no"),
              ("target_alloc", if t = 9 then "n/a" else if t = 2 then "unalloc"
                               else "alloc"),
              ("kind", kind_name kind)]
in
  {id = id, axes = axes, mods = mods, exps = exps, sl = sl, tl = tl,
   fname = fname, sel = fname, hm = (case kind of KHm _ => true | _ => false)} : unit_spec
end

(* ===== The enumeration ===== *)

val sites = [(0, true), (1, true), (2, false), (2, true)]
val viss = [VExt, VInt, VDep]
val quals = [0, 1, 2, 9]
val presences = [[], [0], [1], [2], [0,1], [0,2], [1,2], [0,1,2]]

(* Pruned: statement kinds outside a body (a default or constant
   initializer is an expression; a field holds a type); type kinds outside
   a field declaration; expression kinds in field declarations. *)
fun kinds_of place = case place of
    PBody => expr_kinds @ stmt_kinds
  | PDefault => expr_kinds
  | PConstInit => expr_kinds
  | _ => type_kinds

val places = [PBody, PDefault, PConstInit, PFieldStruct, PFieldEvent, PFieldError]

fun base_units () =
  List.concat (map (fn (d, called) =>
  List.concat (map (fn v =>
  List.concat (map (fn place =>
  List.concat (map (fn kind =>
  List.concat (map (fn t =>
  map (fn pres =>
    build {d = d, called = called, v = v, place = place, t = t, pres = pres,
           kind = kind}) presences) quals)) (kinds_of place))) places)) viss)) sites)


(* ===== Hand-shaped families: exports, collisions, topology ===== *)

fun pin m = "VariableDecl Private Storage \"s\" " ^ u256 ^ " " ^
  (if m < 2 then "(SOME " ^ i m ^ ")" else "NONE")
val entry0 = "FunctionDecl External Nonpayable F F \"entry\" [] [] " ^ u256 ^
  " [Return (SOME " ^ lit 0 ^ ")]"
fun entry_calling e = "FunctionDecl External Nonpayable F F \"entry\" [] [] " ^
  u256 ^ " [Return (SOME " ^ e ^ ")]"
fun ext_fn name v = "FunctionDecl External View F F " ^ str name ^ " [] [] " ^
  u256 ^ " [Return (SOME " ^ lit v ^ ")]"
fun int_fn name v = "FunctionDecl Internal View F F " ^ str name ^ " [] [] " ^
  u256 ^ " [Return (SOME " ^ lit v ^ ")]"
fun call_expr t name = "(Call " ^ u256 ^ " (IntCall " ^ nsid t name ^ ") [] NONE)"
val sl0 = "([((NONE:num option, \"s\"), 0); ((SOME 1, \"s\"), 1)] : storage_layout)"
val tl0 = "([] : storage_layout)"

fun mk {id, family, axes, mods, exps, sl, tl, fname, sel} : unit_spec = let
    val all = ["site", "vis", "place", "qualifier", "qual_rel", "presence",
               "target_declared", "target_alloc"]
    val ax = map (fn a => (a, case List.find (fn (b, _) => a = b) axes of
                                SOME (_, x) => x | NONE => "-")) all
  in {id = family ^ "." ^ id, axes = ax @ [("kind", family)], mods = mods,
      exps = exps, sl = sl, tl = tl, fname = fname, sel = sel, hm = false} end

fun modlist ms = "([" ^ String.concatWith ";\n " (map (fn (q, ds) =>
    "(" ^ q ^ ", " ^ lst ds ^ ")") ms) ^ "] : (num option # toplevel list) list)"
fun std_mods d0 d1 d2 = modlist [(qs 0, pin 0 :: d0), (qs 1, pin 1 :: d1),
                                 (qs 2, pin 2 :: d2)]

(* Exports: an entry of module src (1 allocated, 2 not, 9 missing) of each
   kind, exported as name, optionally colliding with a main external. *)
val export_kinds = ["External", "public_getter", "__default__", "Internal",
                    "Deploy", "missing"]
fun export_units () = List.concat (map (fn src => List.concat (map (fn k =>
  map (fn collide => let
    val name = case k of "__default__" => "__default__" | "Deploy" => "__init__"
                       | _ => "g"
    fun decl m = case k of
        "External" => [ext_fn "g" (100 + m)]
      | "public_getter" => ["VariableDecl (Public F) Storage \"g\" " ^ u256 ^ " " ^
                            (if m = 1 then "(SOME 12)" else "NONE")]
      | "__default__" => ["FunctionDecl External Nonpayable F F \"__default__\" [] [] NoneT [Pass]"]
      | "Internal" => [int_fn "g" (100 + m)]
      | "Deploy" => ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT [Pass]"]
      | _ => []
    val main_extra = if collide then
        (if name = "__default__"
         then ["FunctionDecl External Nonpayable F F \"__default__\" [] [] NoneT [Pass]"]
         else if name = "__init__" then []
         else [ext_fn name 100]) else []
    val sl = if k = "public_getter" andalso src = 1
             then "([((NONE:num option, \"s\"), 0); ((SOME 1, \"s\"), 1); ((SOME 1, \"g\"), 12)] : storage_layout)"
             else sl0
    val (fname, sel) = case name of
        "g" => ("g", "g") | "__default__" => ("__default__", "zzz") | _ => ("entry", "entry")
  in mk {id = String.concatWith "." ["src" ^ i src, k, if collide then "collide" else "alone"],
         family = "exports",
         axes = [("site", i src), ("vis", k), ("qualifier", "SOME" ^ i src),
                 ("place", if collide then "collides_main" else "alone"),
                 ("target_alloc", if src = 1 then "alloc" else if src = 2 then "unalloc" else "n/a")],
         mods = std_mods (main_extra @ [entry0])
                         (if src = 1 then decl 1 else []) (if src = 2 then decl 2 else []),
         exps = "[(" ^ str name ^ ", " ^ i src ^ ")]", sl = sl, tl = tl0,
         fname = fname, sel = sel}
  end) [false, true]) export_kinds)) [1, 2, 9]

(* Dotted names: a declaration spelled "1.x" against module 1's "x". *)
fun dotted_units () = List.concat (map (fn cls => List.concat (map (fn loc =>
  map (fn (rname, rt) => let
    val v = 999
    val dotted = case cls of
        "Constant" => "VariableDecl Private (Constant " ^ lit v ^ ") \"1.x\" " ^ u256 ^ " NONE"
      | "Storage" => "VariableDecl Private Storage \"1.x\" " ^ u256 ^ " (SOME " ^
                     (if loc = 0 then "20" else "21") ^ ")"
      | _ => int_fn "1.x" v
    val plain = case cls of
        "Constant" => "VariableDecl Private (Constant " ^ lit 101 ^ ") \"x\" " ^ u256 ^ " NONE"
      | "Storage" => "VariableDecl Private Storage \"x\" " ^ u256 ^ " (SOME 11)"
      | _ => int_fn "x" 101
    val refe = if cls = "Function" then call_expr rt rname
               else "(TopLevelName " ^ u256 ^ " " ^ nsid rt rname ^ ")"
    val sto = cls = "Storage"
    val sl = if sto then "(" ^ lst ["((NONE:num option, \"s\"), 0)", "((SOME 1, \"s\"), 1)",
                                    "((SOME 1, \"x\"), 11)",
                                    "((" ^ qs loc ^ ", \"1.x\"), " ^
                                    (if loc = 0 then "20" else "21") ^ ")"] ^
                         " : storage_layout)" else sl0
    val m0 = (if loc = 0 then [dotted] else []) @ [entry_calling refe]
    val m1 = plain :: (if loc = 1 then [dotted] else [])
  in mk {id = String.concatWith "." [cls, "at" ^ i loc, if rt = 0 then "ref_NONE_1.x" else "ref_SOME1_x"],
         family = "dotted", axes = [("site", "0"), ("place", "body"),
           ("qualifier", if rt = 0 then "NONE" else "SOME1"), ("presence", "dotted_at_" ^ i loc)],
         mods = std_mods m0 m1 [], exps = "([] : (string # num) list)",
         sl = sl, tl = tl0, fname = "entry", sel = "entry"}
  end) [("1.x", 0), ("x", 1)]) [0, 1])) ["Constant", "Storage", "Function"]

(* One name in two declaration classes of one module. *)
val decl_classes = ["Storage", "Constant", "Immutable", "Function", "HashMap",
                    "Struct", "Flag", "Event", "Error"]
fun class_decl c m = case c of
    "Storage" => "VariableDecl Private Storage \"x\" " ^ u256 ^ " (SOME " ^ i (10 + m) ^ ")"
  | "Constant" => "VariableDecl Private (Constant " ^ lit (100 + m) ^ ") \"x\" " ^ u256 ^ " NONE"
  | "Immutable" => "VariableDecl Private Immutable \"x\" " ^ u256 ^ " (SOME 0)"
  | "Function" => int_fn "x" (100 + m)
  | "HashMap" => "HashMapDecl Private F \"x\" " ^ u256 ^ " (Type " ^ u256 ^ ") (SOME " ^
                 i (20 + m) ^ ")"
  | "Struct" => "StructDecl \"x\" [(\"a\", " ^ u256 ^ ")]"
  | "Flag" => "FlagDecl \"x\" [\"A\"]"
  | "Event" => "EventDecl \"x\" [((\"a\", " ^ u256 ^ "), F)]"
  | _ => "ErrorDecl \"x\" [(\"a\", " ^ u256 ^ ")]"
fun class_slots c m = case c of
    "Storage" => ["((" ^ qs m ^ ", \"x\"), " ^ i (10 + m) ^ ")"]
  | "HashMap" => ["((" ^ qs m ^ ", \"x\"), " ^ i (20 + m) ^ ")"]
  | _ => []
fun class_ref c m = case c of
    "Function" => SOME (call_expr m "x")
  | "Storage" => SOME ("(TopLevelName " ^ u256 ^ " " ^ nsid m "x" ^ ")")
  | "Constant" => SOME ("(TopLevelName " ^ u256 ^ " " ^ nsid m "x" ^ ")")
  | "Immutable" => SOME ("(TopLevelName " ^ u256 ^ " " ^ nsid m "x" ^ ")")
  | "HashMap" => SOME ("(Subscript " ^ u256 ^ " (TopLevelName NoneT " ^ nsid m "x" ^ ") " ^
                       lit 1 ^ ")")
  | _ => NONE
fun pairs [] = [] | pairs (x :: xs) = map (fn y => (x, y)) xs @ pairs xs
fun crossclass_units () = List.concat (map (fn (c1, c2) => map (fn m => let
    val ds = [class_decl c1 m, class_decl c2 m]
    val imm = c1 = "Immutable" orelse c2 = "Immutable"
    val init = if imm then ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT [" ^
                 "Assign (BaseTarget (TopLevelNameTarget " ^ nsid m "x" ^ ")) " ^ lit 7 ^ "]"]
               else []
    val refe = case class_ref c1 m of SOME e => e | NONE =>
               (case class_ref c2 m of SOME e => e | NONE => lit 0)
    val main_init = if imm andalso m = 1
      then ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT " ^
            "[Expr (Call NoneT (IntCall (SOME 1, \"__init__\")) [] NONE)]"] else []
    val m0 = (if m = 0 then ds @ init else main_init) @ [entry_calling refe]
    val m1 = if m = 1 then ds @ init else []
    val sl = "(" ^ lst (["((NONE:num option, \"s\"), 0)", "((SOME 1, \"s\"), 1)"] @
                        class_slots c1 m @ class_slots c2 m) ^ " : storage_layout)"
  in mk {id = String.concatWith "." [c1 ^ "+" ^ c2, "in" ^ i m], family = "crossclass",
         axes = [("site", "0"), ("place", "body"), ("qualifier", if m = 0 then "NONE" else "SOME1"),
                 ("presence", c1 ^ "+" ^ c2)],
         mods = std_mods m0 m1 [], exps = "([] : (string # num) list)", sl = sl, tl = tl0,
         fname = "entry", sel = "entry"} end) [0, 1]) (pairs decl_classes))

(* Selector collisions: gsf() and tgeo() share a 4-byte selector. *)
fun selector_units () = map (fn (id, m0, m1, exps) =>
    mk {id = id, family = "selector", axes = [("site", "0")],
        mods = std_mods (m0 @ [entry0]) m1 [], exps = exps, sl = sl0, tl = tl0,
        fname = "entry", sel = "entry"})
  [("both_in_main", [ext_fn "gsf" 100, ext_fn "tgeo" 100], [], "([] : (string # num) list)"),
   ("both_in_m1", [], [ext_fn "gsf" 101, ext_fn "tgeo" 101], "([] : (string # num) list)"),
   ("both_in_m1_exported_one", [], [ext_fn "gsf" 101, ext_fn "tgeo" 101], "[(\"tgeo\", 1)]"),
   ("main_and_export", [ext_fn "gsf" 100], [ext_fn "tgeo" 101], "[(\"tgeo\", 1)]"),
   ("main_and_unexported", [ext_fn "gsf" 100], [ext_fn "tgeo" 101], "([] : (string # num) list)"),
   ("two_exports", [], [ext_fn "gsf" 101, ext_fn "tgeo" 101], "[(\"gsf\", 1); (\"tgeo\", 1)]")]

(* Call cycles, a constructor calling itself, duplicate and missing ids. *)
fun calling name t callee = "FunctionDecl Internal View F F " ^ str name ^ " [] [] " ^
  u256 ^ " [Return (SOME " ^ call_expr t callee ^ ")]"
fun topology_units () = let
    val e = "([] : (string # num) list)"
    fun u id ms = mk {id = id, family = "topology", axes = [("site", "-")], mods = ms,
                      exps = e, sl = sl0, tl = tl0, fname = "entry", sel = "entry"}
  in [
    u "cycle_main_m1" (std_mods [calling "h" 1 "f", entry_calling (call_expr 1 "f")]
                                [calling "f" 0 "h"] []),
    u "cycle_m1_internal" (std_mods [entry_calling (call_expr 1 "f")]
                                    [calling "f" 1 "g", calling "g" 1 "f"] []),
    u "cycle_m1_m2" (std_mods [entry_calling (call_expr 1 "f")] [calling "f" 2 "g"]
                              [calling "g" 1 "f"]),
    u "self_call_m1" (std_mods [entry_calling (call_expr 1 "f")] [calling "f" 1 "f"] []),
    u "ctor_self_call_main" (std_mods ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT [Expr (Call NoneT (IntCall " ^ nsid 0 "__init__" ^ ") [] NONE)]", entry0] [] []),
    u "ctor_self_call_m1" (std_mods ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT [Expr (Call NoneT (IntCall " ^ nsid 1 "__init__" ^ ") [] NONE)]", entry0]
       ["FunctionDecl Deploy Nonpayable F F \"__init__\" [] [] NoneT [Expr (Call NoneT (IntCall " ^ nsid 1 "__init__" ^ ") [] NONE)]"] []),
    u "duplicate_m1" (modlist [(qs 0, [pin 0, entry_calling (call_expr 1 "x")]),
                               (qs 1, [pin 1, int_fn "x" 101]), (qs 1, [pin 1, int_fn "x" 111])]),
    u "duplicate_main" (modlist [(qs 0, [pin 0, entry0]), (qs 0, [pin 0, entry0])]),
    u "missing_main" (modlist [(qs 1, [pin 1, ext_fn "entry" 101]), (qs 2, [pin 2])]),
    u "missing_main_exported" (mk_missing ())]
  end
and mk_missing () = modlist [(qs 1, [pin 1, ext_fn "entry" 101])]

fun family_units () = export_units () @ dotted_units () @ crossclass_units () @
  selector_units () @ topology_units ()

fun all_units () = base_units () @ family_units ()

end
