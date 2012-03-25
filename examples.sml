structure Examples =
struct

    val Sum.INR example1 = SSParse.parseDef "fun id x = x"
        (*= Ast.ValRecBind (a, NONE, 
            Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))*)

    val Sum.INR example2 = SSParse.parseDef "val a = fn x => x x"
      (*= Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (x, NONE), Ast.Var (x, NONE), NONE), NONE))*)

    val Sum.INR example3 = SSParse.parseExp "let val id = fn x => x in id id end"
      (*= Ast.Let ([Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))],
		 Ast.App (Ast.Var (a, NONE), Ast.Var (a, NONE), NONE), NONE)*)

    val Sum.INR example4 = SSParse.parseDef "fun loop x = loop x"
      (*= Ast.ValRecBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (a, NONE), Ast.Var (x, NONE), NONE), NONE))*)

    val ldec = ("list", TyEval.CPair (TyEval.TDec (Ast.KArr (Ast.KTy, Ast.KTy)), []))
    val lconss = [("nil", TyEval.CPair (TyEval.VDec (Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0)), [ldec])),
		  ("cons", TyEval.CPair (TyEval.VDec (Ast.TyArrow (Ast.TyPoly 0, Ast.TyArrow (Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0), Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0)))), [ldec]))]
    val lenv = ldec :: lconss

    val initEnv = ("map", TyEval.CPair (TyEval.VDec (Ast.TyArrow (Ast.TyArrow (Ast.TyPoly 0, Ast.TyPoly 1), Ast.TyArrow (Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0), Ast.TyApp (Ast.TyId "list", Ast.TyPoly 1)))), lenv)) ::
		  ("concat", TyEval.CPair (TyEval.VDec (Ast.TyArrow (Ast.TyApp (Ast.TyId "list", Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0)), Ast.TyApp (Ast.TyId "list", Ast.TyPoly 0))), lenv)) :: lenv

    (* Monad typeclass definition and instance for the case of lists req's the environment above *)
    val Sum.INR monadLst = SSParse.parseDefList "signature MONAD (m : * -> *) = sig\n  val return : 'a -> m 'a\n  val bind : m 'a -> ('a -> m 'b) -> m 'b\nend\nstructure ListMonad : MONAD list = struct\n  fun return x = cons x nil\n  fun bind xs f = concat (map f xs)\nend"

(*    fun run' e =
        let
            val s = HM.reset ()
            val e' = HM.constrDec e
        in
            (print "===========================================\n";
             print ("Pre-constr: " ^ (Ast.ppdec e) ^ "\n");
             HM.constrDec e;
             print ((HM.printConstr ()) ^ "\n");
             print ("Post-constr: " ^ (Ast.ppdec e') ^ "\n");
	     print (HM.printConstr' (HM.unify (!HM.constraints)) ^ "\n");
	     print ("Post-uni: " ^ (Ast.ppdec e') ^ "\n");
             print "===========================================\n";
             ())
         end

    fun run () = 
        (run' example1;
         ())*)
end


