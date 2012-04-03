structure Ast =
struct
    type id = int
    type name = string

    datatype knd =
        KTy
      | KSig
      | KArr of knd * knd

    (* Kinds in the sig definition allows for checking instead of inference on
     * kind level; may disappear at some point *)
    datatype ty =
        TyId of name
      | TyVar of id
      | TyPoly of id
      | TyApp of ty * ty
      | TySig of dec list
      | TyArrow of ty * ty
      | TyImpArr of ty * ty
      | TyLam of name * knd * ty
      | TyLongName of name list * name
      (* int added (temporarily?) to have some observables *)
      | TyInt
    and dec =
        DTyDef  of name * ty * knd option
      | DTyDec  of name * knd
      | DValDec of name * ty
      | DData   of name * knd * (name * ty) list
	
    datatype arg =
	Expl of name * ty option
      | Impl of name * ty

    (* Only very simple patterns considered now *)
    type pat = name * name list

    datatype exp =
        Fn of arg * exp * ty option
      | Var of name * ty option
      | App of exp * exp * ty option
      | Ann of exp * ty
      | Let of def list * exp * ty option
      | LongName of name list * name * ty option
      | Struct of def list * ty option
      | Case of exp * (pat * exp) list * ty option
      (* same as for types *)
      | VInt of int
    and def =
        ValBind of name * ty option * exp
      | ValRecBind of name * ty option * exp
      | TyDef of name * ty * knd option
      | Data  of name * knd * (name * ty) list
      | StructDec of name * exp * ty option
      | SigDec of name * (name * knd) option * ty
    
    val ppid = Int.toString

    fun substinty (TyId n) th (t as TyId x) =
            (*if n = x then th else*) t
      | substinty (TyVar n) th (t as TyVar x) =
            if n = x then th else t
      | substinty tn th (TyApp (t1,t2)) = 
            TyApp (substinty tn th t1, substinty tn th t2)
      | substinty tn th (TyArrow (t1,t2)) =
            TyArrow (substinty tn th t1, substinty tn th t2)
      | substinty (tn as TyVar x) th (t as TyLam (y, k, tb)) =
	    (*if x = y then t else*) TyLam (y, k, substinty tn th tb)
      | substinty (tn as TyId n) th (t as TyLam (y, k, tb)) =
	    if n = y then t else TyLam (y, k, substinty tn th tb)
      | substinty tn th t = t

    fun occursin (tx as TyVar t1) t2 =
           (case t2 of 
                TyArrow (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyApp (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyVar t2' => t1 = t2'
	      | TyLam (x, k, tb) => (*if x = t1 then false else*) occursin tx tb
              | _ => false)
      | occursin _ _ = raise Fail ("Invalid argument to occursin")

    fun foldO s n (SOME v) = s v
      | foldO s n NONE = n

    fun paren s = "(" ^ s ^ ")"

    fun ppknd k =
	let fun ppknd' _ KTy = "*"
	      | ppknd' _ KSig = "&"
	      | ppknd' n (KArr (k1, k2)) =
		let val s = ppknd' 1 k1 ^ " -> " ^ ppknd' 0 k2
		in if n > 0 then paren s else s
		end
	in ppknd' 0 k end

    fun ppty t =
	let fun pp' _ (TyId n) = n
	      | pp' _ (TyVar i) = "?X" ^ ppid i
	      | pp' _ (TyPoly i) = "'" ^ str (chr (ord #"a" + i))
	      | pp' n (TyApp (t1, t2)) =
		let val s = pp' 1 t1 ^ " " ^ pp' 2 t2
		in if n > 1 then paren s else s end
	      | pp' _ (TySig ds) = 
		"sig\n   " ^
		String.concatWith "\n   " (map ppdec ds) ^
		"\nend\n"
	      | pp' n (TyArrow (t1, t2)) =
		let val s = pp' 1 t1 ^ " -> " ^ pp' 0 t2
		in if n > 0 then paren s else s end
	      | pp' n (TyImpArr (t1, t2)) =
		let val s = pp' 1 t1 ^ " >-> " ^ pp' 0 t2
		in if n > 0 then paren s else s end
	      | pp' n (TyLam (x, k, tb)) = "(\\ " ^ x ^ " :: " ^ ppknd k ^ ". " ^ pp' 0 tb ^ ")"
	      | pp' _ (TyLongName (xs, x)) = String.concatWith "." xs ^ "." ^ x
	      | pp' _ TyInt = "int"
	in pp' 0 t end
    and ppdec (DTyDef (n, t, ok)) = "type " ^ n ^ " = " ^ ppty t ^
			      foldO (fn k => " : " ^ ppknd k) "" ok
      | ppdec (DTyDec (n, k)) = "type " ^ n ^ " : " ^ ppknd k
      | ppdec (DValDec (n, t)) = "val " ^ n ^ " : " ^ ppty t
      | ppdec (DData (x, k, cs)) =
	"datatype " ^ x ^ " : " ^ ppknd k ^ " = "
	^ String.concatWith " | " (List.map (fn (n, t) => n ^ " : " ^ ppty t) cs)

    fun ppann NONE = ""
      | ppann (SOME t) = " : " ^ ppty t

    fun pppat (n, args) = String.concatWith " " (n :: args)

    fun ppexp' pd (Fn (Expl (x, ot),e,t)) = "(fn " ^ x ^ ppann ot ^
					   " => " ^ ppexp' pd e ^ ")" ^ ppann t
      | ppexp' pd (Fn (Impl (x, tx), e, t)) = "(fn {" ^ x ^ ppann (SOME tx) ^
					  "} => " ^ ppexp' pd e ^ ")" ^ ppann t
      | ppexp' pd (Var (n,t)) = "(" ^ n ^ ppann t ^ ")"
      | ppexp' pd (App (e1,e2,t)) = ppexp' pd e1 ^ " " ^ ppexp' pd e2 ^ ppann t
      | ppexp' pd (Ann (e,t)) = "(" ^ ppexp' pd e ^ " : " ^ ppty t ^ ")"
      | ppexp' pd (Let (l,e,t)) = 
        "let\n   " ^
            String.concatWith "\n   " (map pd l) ^
        "\nin\n   " ^ ppexp' pd e ^ "\nend"
      (*| ppexp' pd (Literal t) = "#" ^ ppty t*)
      | ppexp' pd (LongName (xs, x, t)) = String.concatWith "." xs ^ "." ^ x ^ ppann t
      | ppexp' pd (Case (e, cs, t)) =
	       "case " ^ ppexp' pd e ^ " of\n       "
	       ^ String.concatWith "\n    | " (List.map (fn (p, e) => pppat p ^ " => " ^ ppexp' pd e) cs)
	       ^ "\nend" ^ ppann t
      | ppexp' pd (Struct (l,t)) =
            "struct\n   " ^ 
                String.concatWith "\n   " (map pd l) ^
            "\nend" ^ ppann t
      | ppexp' pd (VInt n) = Int.toString n

    fun ppexpnt n pd (Fn (Expl (x, ot),e,t)) =
	let val s = "fn " ^ x ^ ppann ot ^ " => " ^ ppexpnt 0 pd e
	in if n > 0 then paren s else s end
      | ppexpnt n pd (Fn (Impl (x, tx), e, t)) =
	let val s = "fn {" ^ x ^ ppann (SOME tx) ^ "} => " ^ ppexpnt 0 pd e
	in if n > 0 then paren s else s end
      | ppexpnt _ pd (Var (x, t)) = x
      | ppexpnt n pd (App (e1, e2, t)) = 
	let val s = ppexpnt 2 pd e1 ^ " " ^ ppexpnt 3 pd e2
	in if n > 2 then paren s else s end
      | ppexpnt n pd (Ann (e,t)) = 
	let val s = ppexpnt 2 pd e ^ " : " ^ ppty t
	in if n > 1 then paren s else s end
      | ppexpnt n pd (Let (l, e, t)) = 
        let val s = "let\n   " ^ String.concatWith "\n   " (map pd l) ^
		    "\nin\n   " ^ ppexpnt 0 pd e ^ "\nend"
	in if n > 0 then paren s else s end
      (*| ppexpnt pd (Literal t) = "#" ^ ppty t*)
      | ppexpnt _ pd (LongName (xs, x, t)) = String.concatWith "." xs ^ "." ^ x
      | ppexpnt n pd (Case (e, cs, t)) =
	let val cs' = List.map (fn (p, e) => pppat p ^ " => " ^ ppexpnt 0 pd e) cs
	    val s = "case " ^ ppexpnt 0 pd e ^ " of\n       " ^
		    String.concatWith "\n    | " cs' ^ "\nend"
	in if n > 0 then paren s else s end
      | ppexpnt _ pd (Struct (l, t)) =
            "struct\n   " ^ 
                String.concatWith "\n   " (map pd l) ^
            "\nend"
      | ppexpnt _ pd (VInt n) = Int.toString n

    fun ppdef' pe (ValBind (n,t,e)) = "val " ^ n ^ ppann t ^ " = " ^ pe e
      | ppdef' pe (ValRecBind (n,t,e)) = 
            "val rec " ^ n ^ ppann t ^ " = " ^ pe e
      | ppdef' pe (TyDef (n, t, ok)) = "type " ^ n ^ " = " ^ ppty t ^
			      foldO (fn k => " : " ^ ppknd k) "" ok
      | ppdef' pe (Data (x, k, cs)) =
	"datatype " ^ x ^ " : " ^ ppknd k ^ " = "
	^ String.concatWith " | " (List.map (fn (n, t) => n ^ " : " ^ ppty t) cs)
      | ppdef' pe (StructDec (n,d,t)) =
        "structure " ^ n ^ ppann t ^ " = " ^ pe d
      | ppdef' pe (SigDec (n, ps, t)) =
        "signature " ^ n ^
	foldO (fn (x, k) => " (" ^ x ^ " : " ^ ppknd k ^ ")") "" ps ^
	" = " ^ ppty t

    fun ppexp e = ppexpnt 0 (ppdef' ppexp) e
    val ppdef = ppdef' ppexp

end
