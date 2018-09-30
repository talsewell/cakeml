structure ml_progLib :> ml_progLib =
struct

open preamble;
open ml_progTheory astSyntax packLib;

(* state *)

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

(* helper functions *)

val reduce_conv =
  (* this could be a custom compset, but it's easier to get the
     necessary state updates directly from EVAL
     TODO: Might need more custom rewrites for env-refactor updates
  *)
  EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC
  EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL;

fun prove_assum_by_eval th = let
  val (x,y) = dest_imp (concl th)
  val lemma = reduce_conv x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma)) th
  in MP lemma TRUTH
     handle HOL_ERR e => let
       val _ = print "Failed to reduce:\n\n"
       val _ = print_term x
       val _ = print "\n\nto T. It only reduced to:\n\n"
       val _ = print_term (lemma |> concl |> dest_eq |> snd)
       val _ = print "\n\n"
       in failwith "prove_assum_by_eval: unable to reduce term to T"
     end
  end;

fun is_const_str str = can prim_mk_const {Thy=current_theory(), Name=str};

fun find_name name = let
  val ns = map (#1 o dest_const) (constants (current_theory()))
  fun aux n = let
    val str = name ^ "_" ^ int_to_string n
    in if mem str ns then aux (n+1) else str end
  in aux 0 end

fun ok_char c =
  (#"0" <= c andalso c <= #"9") orelse
  (#"a" <= c andalso c <= #"z") orelse
  (#"A" <= c andalso c <= #"Z") orelse
  mem c [#"_",#"'"]

val ml_name = String.translate
  (fn c => if ok_char c then implode [c] else "c" ^ int_to_string (ord c))

(* timing output *)

val trace_timing_to = ref (NONE : string option)

fun timing_comment s = case ! trace_timing_to of
  SOME fname => let
    val f = TextIO.openAppend fname
  in
    TextIO.output (f, s ^ "\n");
    TextIO.closeOut f
  end | NONE => ()

fun start_timing nm = case ! trace_timing_to of
  SOME fname => let
    val time = Portable.timestamp ()
    val f = TextIO.openAppend fname
    val time_s = Portable.time_to_string time
  in TextIO.output (f, time_s ^ ": began " ^ nm ^ "\n");
    TextIO.closeOut f;
    SOME (fname, nm, time)
  end | NONE => NONE

fun end_timing t = case t of
  SOME (fname, nm, start_time) => let
    val time = Portable.timestamp ()
    val f = TextIO.openAppend fname
    val time_s = Portable.time_to_string time
    val dur_s = Portable.time_to_string (time - start_time)
  in TextIO.output (f, time_s ^ ": finished " ^ nm ^ "\n");
    TextIO.output (f, "  -- duration of " ^ nm ^ ": " ^ dur_s ^ "\n");
    TextIO.closeOut f
  end | NONE => ()

fun do_timing nm f x = let
    val start = start_timing nm
    val r = f x
  in end_timing start; r end

(* abbrevs/wrapper definitions *)

fun define_abbrev for_eval name tm = let
  val name = ml_name name
  val name = (if is_const_str name then find_name name else name)
  val tm = if List.null (free_vars tm) then
             mk_eq(mk_var(name,type_of tm),tm)
           else let
             val vs = free_vars tm |> sort
               (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
             val vars = foldr mk_pair (last vs) (butlast vs)
             val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
             in mk_eq(mk_comb(n,vars),tm) end
  val def_name = name ^ "_def"
  val def = (*Definition.*)new_definition(def_name,tm)
  val _ = if for_eval then computeLib.add_persistent_funs [def_name] else ()
  in def end

fun cond_abbrev dest conv eval name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val th = CONV_RULE (conv eval) th
       val tm = dest th
       val def = define_abbrev true (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       in (th,[def]) end end

exception EnvConstNotFound of string
exception CannotLookupEnv of term

val head_const = total (fst o dest_const) o fst o strip_comb
val restr_eval_conv = computeLib.RESTR_EVAL_CONV [``Bin``]

fun eval_map_conv i j tm = if j = 0 then raise UNCHANGED
  else case head_const tm of
    SOME "Bin" => if is_const tm then raise UNCHANGED
        else COMB2_CONV (eval_map_conv i j, eval_map_conv i (j - 1)) tm
  | SOME _ => let
    fun next tm = if head_const tm = SOME "Bin" then eval_map_conv i i tm
      else raise UNCHANGED
  in (restr_eval_conv THENC next) tm end
  | _ => raise UNCHANGED

local
  val lookup_eq_thms = ref ([]:(string * thm) list);
  fun add_thm nm thm
    = (lookup_eq_thms := (nm, thm) :: (! lookup_eq_thms))
in
  fun get_lookup_map_thm_for_const_nm nm = case AList.lookup (op =)
        (! lookup_eq_thms) nm
    of SOME thm => thm | NONE => raise (EnvConstNotFound nm)
  fun get_lookup_map_thm term = let
      val (hd, xs) = strip_comb term
      val (thm, specs, sub_envs) = case (fst (dest_const hd), xs) of
          ("write", [nm, v, env]) => (lookup_eq_map2_write,
                [(`n`, nm), (`v`, v)], [env])
        | ("write_cons", [nm, c, env]) => (lookup_eq_map2_write_cons,
                [(`n`, nm), (`c`, c)], [env])
        | ("empty_env", []) => (lookup_eq_map2_empty_env, [], [])
        | ("merge_env", [env1, env2]) => (lookup_eq_map2_merge_env,
                [], [env1, env2])
        | ("write_mod", [mn, mod_env, env]) => (lookup_eq_map2_write_mod,
                [(`mn`, mn), (`mod_env`, mod_env)], [env])
        | (env_nm, []) => (get_lookup_map_thm_for_const_nm env_nm, [], [])
        | _ => raise (CannotLookupEnv term)
      val thm = foldl (fn ((nm, term), thm) => SPEC term (Q.GEN nm thm))
        thm specs
      val sub_env_thms = map get_lookup_map_thm sub_envs
    in foldl (fn (env_thm, thm) => MATCH_MP thm env_thm) thm sub_env_thms end
  fun add_lookup_eq_thm def = let
      val (env_const, def_rhs) = def |> concl |> dest_eq
      val th = get_lookup_map_thm def_rhs
      val th = CONV_RULE (RAND_CONV (REWR_CONV (GSYM def))) th
      val th = CONV_RULE (RATOR_CONV (RAND_CONV (eval_map_conv 3 3))) th
      val _ = timing_comment ("lookup_eq_thm: " ^ Parse.thm_to_string th)
      val nm = fst (dest_const env_const)
      val _ = save_thm ("lookup_eq_map2_" ^ nm, th)
      val compute_th = MATCH_MP lookup_eq_map2_compute_imps th
      val thm_name = "nsLookup_via_map_" ^ fst (dest_const env_const)
      val _ = save_thm (thm_name ^ "[compute]", compute_th)
    in add_thm nm th end
end;

fun cond_env_abbrev dest conv name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val def = define_abbrev false (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       val eq_thm = add_lookup_eq_thm def
       in (th,[def]) end end

(*
val (ML_code (ss,envs,vs,th)) = (ML_code (ss,envs,v_def :: vs,th))
*)

fun clean (ML_code (ss,envs,vs,th)) = let
  val start = start_timing "cleaning"
  val (th,new_ss) = do_timing "cond_abbrev" (cond_abbrev (rand o concl)
                      RAND_CONV reduce_conv "auto_state") th
  val dest = (rand o rator o concl)
  val conv = (RATOR_CONV o RAND_CONV)
  val name = "auto_env"
  val (th,new_envs) = do_timing "cond_env_abbrev"
    (cond_env_abbrev dest conv name) th
  val th = do_timing "REWRITE_RULE" (REWRITE_RULE [ML_code_env_def]) th
  in ML_code (new_ss @ ss, new_envs @ envs, vs, th) end

(* --- *)

val unknown_loc = locationTheory.unknown_loc_def |> concl |> dest_eq |> fst;
val loc = unknown_loc;

val init_state =
  ML_code ([SPEC_ALL init_state_def],[init_env_def],[],ML_code_NIL);

fun open_module mn_str (ML_code (ss,envs,vs,th)) =
  ML_code
    (ss,envs,vs,
     MATCH_MP ML_code_new_module th
     |> SPEC (stringSyntax.fromMLstring mn_str))
  handle HOL_ERR _ => failwith("open_module failed for " ^ thm_to_string th)

fun close_module sig_opt (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_close_module th
(*val v = th |> concl |> dest_forall |> fst
  val sig_tm = (case sig_opt of
                  NONE => mk_const("NONE",type_of v)
                | SOME tm => optionSyntax.mk_some(tm))
  val th = SPEC sig_tm th *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype loc tds_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dtype th
  val th = SPECL [tds_tm,loc] th |> prove_assum_by_eval
  val tm = th |> concl |> rator |> rand |> rator |> rator |> rand
  val th = th |> CONV_RULE ((* (RATOR_CONV o RAND_CONV) *)
            (REWRITE_CONV [EVAL tm] THENC
             SIMP_CONV std_ss [write_tdefs_def,MAP,FLAT,FOLDR,REVERSE_DEF,
                               write_conses_def,ML_code_env_def,LENGTH,
                               semanticPrimitivesTheory.build_constrs_def,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

(*
val loc = unknown_loc
val n_tm = ``"bar"``
val l_tm = ``[]:ast_t list``
*)

fun add_Dexn loc n_tm l_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dexn th
  val th = SPECL [n_tm,l_tm,loc] th
  val tm = th |> concl |> rand |> rator |> rand |> rand |> rator |> rand
  val th = th |> CONV_RULE ((* (RATOR_CONV o RAND_CONV) *)
            (REWRITE_CONV [EVAL tm] THENC
             SIMP_CONV std_ss [MAP,ML_code_env_def,
                               FLAT,FOLDR,REVERSE_DEF,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dtabbrev loc l1_tm l2_tm l3_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dtabbrev th
  val th = SPECL [l1_tm,l2_tm,l3_tm,loc] th
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dlet eval_thm var_str v_thms (ML_code (ss,envs,vs,th)) = let
  val start = start_timing "add_Dlet"
  val th = MATCH_MP ML_code_Dlet_var th
           |> REWRITE_RULE [ML_code_env_def]
  val th = do_timing "add_Dlet(2nd MP)" (MATCH_MP th) eval_thm
           handle HOL_ERR _ => failwith "add_Dlet eval_thm does not match"
  val th = do_timing "add_Dlet(SPECL)"
    (SPECL [stringSyntax.fromMLstring var_str,unknown_loc]) th
  val st2 = do_timing "add_Dlet(clean)" clean (ML_code (ss,envs,v_thms @ vs,th))
  val _ = end_timing start
  in st2 end

(*
val (ML_code (ss,envs,vs,th)) = s
val (n,v,exp) = (v_tm,w,body)
*)

fun add_Dlet_Fun loc n v exp v_name (ML_code (ss,envs,vs,th)) = let
  val start = start_timing "add_Dlet_Fun"
  fun timing s = do_timing ("add_Dlet_Fun(" ^ s ^ ")")
  val th = MATCH_MP ML_code_Dlet_Fun th
           |> REWRITE_RULE [ML_code_env_def]
  val th = timing "SPECL" (SPECL [n,v,exp,loc]) th
  val tm = th |> concl |> rator |> rand |> rator |> rand
  val v_def = timing "define_abbrev" (define_abbrev false v_name) tm
  val th = timing "CONV_RULE"
    (CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                   (REWR_CONV (GSYM v_def)))) th
  val st2 = timing "clean" clean (ML_code (ss,envs,v_def :: vs,th))
  val _ = end_timing start
  in st2 end

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> SPEC_ALL |> concl |> rand |> rand |> rand |> rator |> rand
  |> dest_exists |> snd
  |> dest_exists |> snd
  |> dest_exists |> snd |> rand

fun add_Dletrec loc funs v_names (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dletrec th
           |> REWRITE_RULE [ML_code_env_def]
  val th = SPECL [funs,loc] th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                  (SIMP_CONV std_ss [write_rec_def,FOLDR,
                    semanticPrimitivesTheory.build_rec_env_def]))
  val tms = rev (find_terms (can (match_term Recclosure_pat)) (concl th))
  val xs = zip v_names tms
  val v_defs = map (fn (x,y) => define_abbrev false x y) xs
  val th = REWRITE_RULE (map GSYM v_defs) th
  in clean (ML_code (ss,envs,v_defs @ vs,th)) end

fun get_mod_prefix (ML_code (ss,envs,vs,th)) = let
  val tm = th |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none tm then "" else
       (tm |> rand |> rator |> rand |> stringSyntax.fromHOLstring) ^ "_"
  end

(*
val dec_tm = dec1_tm
*)

fun add_dec dec_tm pick_name s =
  if is_Dexn dec_tm then let
    val (loc,x1,x2) = dest_Dexn dec_tm
    in add_Dexn loc x1 x2 s end
  else if is_Dtype dec_tm then let
    val (loc,x1) = dest_Dtype dec_tm
    in add_Dtype loc x1 s end
  else if is_Dtabbrev dec_tm then let
    val (loc,x1,x2,x3) = dest_Dtabbrev dec_tm
    in add_Dtabbrev loc x1 x2 x3 s end
  else if is_Dletrec dec_tm then let
    val (loc,x1) = dest_Dletrec dec_tm
    val prefix = get_mod_prefix s
    fun f str = prefix ^ pick_name str ^ "_v"
    val xs = listSyntax.dest_list x1 |> fst
               |> map (f o stringSyntax.fromHOLstring o rand o rator)
    in add_Dletrec loc x1 xs s end
  else if is_Dlet dec_tm
          andalso is_Fun (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val (w,body) = dest_Fun f
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (stringSyntax.fromHOLstring v_tm) ^ "_v"
    in add_Dlet_Fun loc v_tm w body v_name s end
  else if is_Dmod dec_tm then let
    val (name,(*spec,*)decs) = dest_Dmod dec_tm
    val ds = fst (listSyntax.dest_list decs)
    val name_str = stringSyntax.fromHOLstring name
    val s = open_module name_str s handle HOL_ERR _ =>
            failwith ("add_top: failed to open module " ^ name_str)
    fun each [] s = s
      | each (d::ds) s = let
           val s = add_dec d pick_name s handle HOL_ERR e =>
                   failwith ("add_top: in module " ^ name_str ^
                             "failed to add " ^ term_to_string d ^ "\n " ^
                             #message e)
           in each ds s end
    val s = each ds s
    val spec = (* SOME (optionSyntax.dest_some spec)
                  handle HOL_ERR _ => *) NONE
    val s = close_module spec s handle HOL_ERR e =>
            failwith ("add_top: failed to close module " ^ name_str ^ "\n " ^
                             #message e)
    in s end
  else failwith("add_dec does not support this shape: " ^ term_to_string dec_tm);

fun remove_snocs (ML_code (ss,envs,vs,th)) = let
  val th = th |> PURE_REWRITE_RULE [listTheory.SNOC_APPEND]
              |> PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC]
              |> PURE_REWRITE_RULE [listTheory.APPEND]
  in (ML_code (ss,envs,vs,th)) end

fun get_thm (ML_code (ss,envs,vs,th)) = th
fun get_v_defs (ML_code (ss,envs,vs,th)) = vs

fun get_env s = let
  val th = get_thm s
  val th = MATCH_MP ML_code_Dlet_var th
  val th = REWRITE_RULE [ML_code_env_def] th
  in th |> SPEC_ALL |> concl |> dest_imp |> fst
        |> rator |> rator |> rator |> rand end

fun get_state s = get_thm s |> concl |> rand

fun get_next_type_stamp s =
  semanticPrimitivesTheory.state_component_equality
  |> ISPEC (get_state s)
  |> SPEC (get_state s)
  |> concl |> rand |> rand |> rand |> rand |> rator |> rand |> rand
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun get_next_exn_stamp s =
  semanticPrimitivesTheory.state_component_equality
  |> ISPEC (get_state s)
  |> SPEC (get_state s)
  |> concl |> rand |> rand |> rand |> rand |> rand |> rand
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x,y) => add_dec x pick_name y) s ts) end

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) =
  pack_4tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (ss,envs,vs,th)

fun unpack_ml_prog_state th =
  ML_code (unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
    (unpack_list unpack_thm) unpack_thm th)

fun clean_state (ML_code (ss,envs,vs,th)) = let
  fun FIRST_CONJUNCT th = CONJUNCTS th |> hd handle HOL_ERR _ => th
  fun delete_def def = let
    val {Name,Thy,Ty} =
      def |> SPEC_ALL |> FIRST_CONJUNCT |> SPEC_ALL |> concl
          |> dest_eq |> fst |> repeat rator |> dest_thy_const
    in if not (Thy = Theory.current_theory()) then ()
       else Theory.delete_binding (Name ^ "_def") end
  fun split x = ([hd x], tl x) handle Empty => (x,x)
  fun dd ls = let val (ls,ds) = split ls in app delete_def ds; ls end
  val () = app delete_def vs
  in (ML_code (dd ss, dd envs, [], th)) end

fun pick_name str =
  if str = "<" then "lt" else
  if str = ">" then "gt" else
  if str = "<=" then "le" else
  if str = ">=" then "ge" else
  if str = "=" then "eq" else
  if str = "<>" then "neq" else
  if str = "~" then "uminus" else
  if str = "+" then "plus" else
  if str = "-" then "minus" else
  if str = "*" then "times" else
  if str = "/" then "div" else
  if str = "!" then "deref" else
  if str = ":=" then "assign" else
  if str = "@" then "append" else
  if str = "^" then "strcat" else
  if str = "<<" then "lsl" else
  if str = ">>" then "lsr" else
  if str = "~>>" then "asr" else str (* name is fine *)

(*

val s = init_state
val dec1_tm = ``Dlet (ARB 1) (Pvar "f") (Fun "x" (Var (Short "x")))``
val dec2_tm = ``Dlet (ARB 2) (Pvar "g") (Fun "x" (Var (Short "x")))``
val prog_tm = ``[^dec1_tm; ^dec2_tm]``

val s = (add_prog prog_tm pick_name init_state)

val th = get_env s

*)

end
