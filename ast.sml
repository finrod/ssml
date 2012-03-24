structure Ast =
struct
    type id = string

    datatype knd =
        KTy
      | KSig
      | KArr of knd * knd

    (* Kinds in the sig definition allows for checking instead of inference on
     * kind level; may disappear at some point *)
    datatype ty =
        TyId of id
      | TyVar of id
      | TyPoly of id
      | TyApp of ty * ty
      | TySig of dec list
      | TyArrow of ty * ty
      | TyLam of id * knd * ty
      | TyLongName of id list * id
    and dec =
        DTyDef of id * ty * knd option
      | DTyDec of id * knd
      | DValDec of id * ty
	
    datatype arg =
	Expl of id * ty option
      | Impl of id * ty

    datatype exp =
        Fn of arg * exp * ty option
      | Var of id * ty option
      | App of exp * exp * ty option
      | Ann of exp * ty
      | Let of def list * exp * ty option
      | Literal of ty
      | LongName of id list * id * ty option
    and def =
        ValBind of id * ty option * exp
      | ValRecBind of id * ty option * exp
      | TyDef of id * ty * knd option
      | Struct of def list * ty option
      | StructDec of id * def * ty option
      | SigDec of id * (id * knd) option * ty
    
    val ppid = fn x => x

    fun substinty (TyId n) th (t as TyId x) =
            if n = x then th else t
      | substinty (TyVar n) th (t as TyVar x) =
            if n = x then th else t
      | substinty tn th (TyApp (t1,t2)) = 
            TyApp (substinty tn th t1, substinty tn th t2)
      | substinty tn th (TyArrow (t1,t2)) =
            TyArrow (substinty tn th t1, substinty tn th t2)
      | substinty (tn as TyVar x) th (t as TyLam (y, k, tb)) =
	    if x = y then t else TyLam (y, k, substinty tn th tb)
      | substinty (tn as TyId n) th (t as TyLam (y, k, tb)) =
	    if n = y then t else TyLam (y, k, substinty tn th tb)
      | substinty tn th t = t

    fun occursin (tx as TyVar t1) t2 =
           (case t2 of 
                TyArrow (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyApp (t1',t2') => occursin tx t1' orelse occursin tx t2'
              | TyVar t2' => t1 = t2'
	      | TyLam (x, k, tb) => if x = t1 then false else occursin tx tb
              | _ => false)
      | occursin _ _ = raise Fail ("Invalid argument to occursin")

    fun foldO s n (SOME v) = s v
      | foldO s n NONE = n

    fun ppknd KTy = "*"
      | ppknd KSig = "&"
      | ppknd (KArr (k1, k2)) = "( " ^ ppknd k1 ^ " -> " ^ ppknd k2 ^ " )"

    (* BUG: nested arrows don't get parens *)
    fun ppty (TyId i) = "t" ^ ppid i
      | ppty (TyVar i) = "?X" ^ ppid i
      | ppty (TyPoly i) = ppid i
      | ppty (TyApp (a,b)) = ppty a ^ " " ^ ppty b
      | ppty (TySig ds) = 
            "sig\n   " ^
	    String.concatWith "\n    " (map ppdec ds) ^ "\n    " ^
	    "\nend\n"
      | ppty (TyArrow (t1,t2)) = ppty t1 ^ " -> " ^ ppty t2
      | ppty (TyLam (x, k, tb)) = "(\\ t" ^ ppid x ^ " :: " ^ ppknd k ^ ". " ^ ppty tb ^ ")"
      | ppty (TyLongName (xs, x)) = "v" ^ String.concatWith ".v" (map ppid xs) ^ ".t" ^ ppid x
    and ppdec (DTyDef (i, t, ok)) = "type t" ^ ppid i ^ " = " ^ ppty t ^
			      foldO (fn k => " : " ^ ppknd k) "" ok
      | ppdec (DTyDec (i, k)) = "type t" ^ ppid i ^ " : " ^ ppknd k
      | ppdec (DValDec (i, t)) = "val v" ^ ppid i ^ " : " ^ ppty t

    fun ppann NONE = ""
      | ppann (SOME t) = " : " ^ ppty t

    fun ppexp (Fn (Expl (x, ot),e,t)) = "(fn v" ^ ppid x ^ ppann ot ^
					" => " ^ ppexp e ^ ")" ^ ppann t
      | ppexp (Fn (Impl (x, tx), e, t)) = "(fn {v" ^ ppid x ^ ppann (SOME tx) ^
					  "} => " ^ ppexp e ^ ")" ^ ppann t
      | ppexp (Var (i,t)) = "v" ^ ppid i ^ ppann t
      | ppexp (App (e1,e2,t)) = ppexp e1 ^ " " ^ ppexp e2 ^ ppann t
      | ppexp (Ann (e,t)) = "(" ^ ppexp e ^ " : " ^ ppty t ^ ")"
      | ppexp (Let (l,e,t)) = 
        "let\n   " ^
            String.concatWith "\n   " (map ppdef l) ^
        "\nin\n   " ^ ppexp e ^ "\nend"
      | ppexp (Literal t) = "#" ^ ppty t
      | ppexp (LongName (xs, x, t)) =
	"v" ^ String.concatWith ".v" (map ppid xs) ^ ".v" ^ ppid x ^ ppann t
    and ppdef (ValBind (i,t,e)) = "val v" ^ ppid i ^ ppann t ^ " = " ^ ppexp e
      | ppdef (ValRecBind (i,t,e)) = 
            "val rec v" ^ ppid i ^ ppann t ^ " = " ^ ppexp e
      | ppdef (TyDef (i, t, ok)) = "type t" ^ ppid i ^ " = " ^ ppty t ^
			      foldO (fn k => " :: " ^ ppknd k) "" ok
      | ppdef (Struct (l,t)) =
            "struct\n   " ^ 
                String.concatWith "\n   " (map ppdef l) ^
            "\nend"
      | ppdef (StructDec (i,d,t)) =
        "structure s" ^ ppid i ^ ppann t ^ " = " ^ ppdef d
      | ppdef (SigDec (i, ps, t)) =
        "signature S" ^ ppid i ^
	foldO (fn (x, k) => " (t" ^ ppid x ^ " :: " ^ ppknd k ^ ")") "" ps ^
	" = " ^ ppty t

end
