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
      | Case of exp * (pat * exp) list
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

    fun ppexp (Fn (Expl (x, ot),e,t)) = "(fn " ^ x ^ ppann ot ^
					" => " ^ ppexp e ^ ")" ^ ppann t
      | ppexp (Fn (Impl (x, tx), e, t)) = "(fn {" ^ x ^ ppann (SOME tx) ^
					  "} => " ^ ppexp e ^ ")" ^ ppann t
      | ppexp (Var (n,t)) = "(" ^ n ^ ppann t ^ ")"
      | ppexp (App (e1,e2,t)) = ppexp e1 ^ " " ^ ppexp e2 ^ ppann t
      | ppexp (Ann (e,t)) = "(" ^ ppexp e ^ " : " ^ ppty t ^ ")"
      | ppexp (Let (l,e,t)) = 
        "let\n   " ^
            String.concatWith "\n   " (map ppdef l) ^
        "\nin\n   " ^ ppexp e ^ "\nend"
      (*| ppexp (Literal t) = "#" ^ ppty t*)
      | ppexp (LongName (xs, x, t)) = String.concatWith "." xs ^ "." ^ x ^ ppann t
      | ppexp (Case (e, cs)) =
	       "case " ^ ppexp e ^ " of\n       "
	       ^ String.concatWith "\n    | " (List.map (fn (p, e) => pppat p ^ " => " ^ ppexp e) cs)
	       ^ "\nend"
      | ppexp (Struct (l,t)) =
            "struct\n   " ^ 
                String.concatWith "\n   " (map ppdef l) ^
            "\nend" ^ ppann t
      | ppexp (VInt n) = Int.toString n
    and ppdef (ValBind (n,t,e)) = "val " ^ n ^ ppann t ^ " = " ^ ppexp e
      | ppdef (ValRecBind (n,t,e)) = 
            "val rec " ^ n ^ ppann t ^ " = " ^ ppexp e
      | ppdef (TyDef (n, t, ok)) = "type " ^ n ^ " = " ^ ppty t ^
			      foldO (fn k => " : " ^ ppknd k) "" ok
      | ppdef (Data (x, k, cs)) =
	"datatype " ^ x ^ " : " ^ ppknd k ^ " = "
	^ String.concatWith " | " (List.map (fn (n, t) => n ^ " : " ^ ppty t) cs)
      | ppdef (StructDec (n,d,t)) =
        "structure " ^ n ^ ppann t ^ " = " ^ ppexp d
      | ppdef (SigDec (n, ps, t)) =
        "signature " ^ n ^
	foldO (fn (x, k) => " (" ^ x ^ " : " ^ ppknd k ^ ")") "" ps ^
	" = " ^ ppty t

end
